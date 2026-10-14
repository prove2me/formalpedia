-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1950
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:16:13.507702+00:00
-- url     : https://prove2.me/submissions/3a34d730-5bbb-49bd-ab55-8c80060c1714

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350539568 ≤ n < 350719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350540818 1250 350539568 350539577
    0x1b0a03081f03061e060b0430030f030f050f04050d030905060a0c050403020d030c03090806010e01030807020621101e09091403040b090406090b010c0201031a09090d 72
    0x14403080c41c80600c806900740c188401400031070640c2c2e64000503003265203038001580308001d40c48071808014040c00340107161001c4213642c0c4908045002550101030342c049030b988a2038803070302d01300882e2440000740781503003501c0e00300c0c09170103084403c41c060690003c0052110382890103020704000b1644c0f0090013503200b0b008552500f05080c0c0705606403000724401078116001000010840d0003a07800c03000b4000b16602d4580d00e416220760010b40c04480005058000511807a000c0080540214451001d071400c0c070010501503241c00c0c8403048860050000800e51300010a0140840d200c100680c0d840010800402c031704401601d41e40358043c141200c4500880c18142d500103584810300c14405d41d0704c4046001807551030700741031204c001340080390401c580d404051803500120000c1440900007502518010742c0e500c1c080d202c01c01c0107544507504a4208a46004c104290981e0450301201c92294282800308110385689403908c115440b80b100a42c22084e110100310300780798041b0368914851501d858 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350542068 1250 350540818 350540821
    0x903070c14010f170f0903070204050a0515150403060c050408010e060603060a0903021203091606180b0405030a02040f021b100e0f0304060507060f02070f02040c0305060f060904021b0a0308 83
    0x80c04c4078000c40391680507044111034400300c0d00c2d0b000721180303096001641c2c50403685000c40b203a01090495104580007841181d07204203000c5000e0070b80503100100e20086520149060310340c24079116603c51484001e1a40c1d60b10480d032034115018400790740003413140200030031850822442484c0c031742104940c2d0b00d00c80e000700400a074841c40944180b0b00c1140e00365000340400ca08060506019500140080520344190b2081128038020701c247e0f28090f00d070310f9603090700800188204a82e62410754120203a43d110a100502c120f8500041c0c29140d01c3c1c040b40d02003842c0e03640c130101c00000c1c0b01d15201060075400900300c0703801031000001e0520380010040b400b003221700490000d0a071240c0070700d881c92071a0740041208221807441440030348025030080ca80001e907900791f918028101c0c0d02c4584100c50b000e04038024101549014403402c1d8200b652400d00f0f100d10f2070440c001a20300d1244444103841000c01142a04440d1203a605681c0c1003d06400c5000b24035210b15880c82d92100d00c41c0003180010300800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350543318 1250 350542068 350542097
    0x150e1804020103050f15130b030304080d2d0302160204060906050a080604020120011803091712090d0305040e0403080f090106031109060d12030e010b03190206030903070c1401 77
    0x2d11a209074034010000c80c414130b040c0704010341c80c2403006100b00201c0e10f81c40080d1289d50280010001800544010305940c03102290140010b0080c080c01540107140050070300c042c0107110021a4584d4180c940183d490320381005c4c1e080f4500400cbc40180d082480c01390b000c108118641d101000b91802100c01c000b09955580155944110882c0c0c000e0015100401703079112020103200340c90700d8201c0440003044039900350300600071845401500741c0c0000d003a020b04118451030311560801e1040c500c006440f038140822481c6ca2544100344455019580c000c0d0000c0c281441541920064841000700d50349504050134010820541580e481c0a041444070118110a50501c1486c04603a0b11580c1304803407041c07480402c1840a4010100384c1c0280f4200c01100005e00d02c6440310703400e81020b850020703490080c100514211541405524002c0d030001d417000e0400d404590500070b080e68101c40c603564a0341d40d238442e503085003d900b40041500c00c440703074081480384082000052116081c6d032142c29881580 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350544568 1250 350543318 350543341
    0x110109030e130615031e0207080711040902010f0e42030f0106181205010906050a0e120a050c060901020903010c080c12060402040b0c060105150a0504150e180402010305 74
    0x6214038030014010301004c50095001c3d1b00202a02c40302d59248401d004d8007000100241e900880d0221141030000440008003d41003850001050080c0c03010403603044e4550010707005a50700070001c41808118006065590303143d07283d480820540340103402d82e401c111011031103401085008880314010800643d614403500c81c0549100361841ea100030803e9103020340544040715400303000b40300c0e10b402c4200426582d6901311610510b078810400080c401e401804c29004448000c0c0004038100d0619100c825030920029510040243e0710000039901c400002b41950140f00d4903012903007034010001004891101075020b07003002d000031f80017800b44142c1d040d0111401001107034502498035041c40003079000080c0040d4141e1002014000500d040d44945109000350015001e401e4aa44075200501450420740ea1840c41c0c6800d9412250820700ba003003002e4564000e602494100408092207070856500c0b03400301890408000d09505144c0f0303140c0740100c481c8802100c00303902107806c00e0080368041030503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350545818 1250 350544568 350544581
    0xc0f0314190f1811062706040b07030e011106010b070602031e01120b100e16020c091005130b0607140a08030c0c0c0a08030405061303061b02100b010806040c110109030e13 75
    0x240b6100a410141d124006c25269000485039800940c01e0002180d1004543e000f4203540e4020749889540e40c1c40040018008400d0301500303000d80c2c000c10010003440302c100d81560802ca5118101688950f142090201208248800019603c8507900000b6600c400c09030914025401503030307031841c0e581c1d56908140d010640d622580c90321480c9200080d2402070300c003c0741c504801a07441641d40340140031002455013030b4196061844849852404c22aa240030340c141c5004000180003449a43c2c0c10000251450160000c0505201c01c680111100140140080c0000541c8028119182d0510140c1d401030764100c070f01040341d144500c51443c000b0b850100391401c111005c0200461a01e070802060105a4101841c51a00c5150080b800700c00903000c0d001e0001907400c818a05042510196002440c0014030105c0514282c607140009511b42d80c8042d040390301c044295000f254220300100111040c0b00401c0d8940b0040d4a004595000c065028040101d181801c9a01400510801810718101c400c0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350547068 1250 350545818 350545837
    0xf070c02090c030a14100f050316060c150207050309040506030a0b061e030303130b0c1e0304030504081b0910121103030702130c0f0314190f181106 65
    0x292400042e401c6981500110f0784007000200101c1c804c0f1041e000c0c178036004e905803105210788a040c00f0901040c500706540c84e004190490041107841002001120401d0aa000345070401c11004c4003003090248210240011550b0345204640d12401414001d03241d400180909100d50f00b000b02084c0f140c500098000d0f80700e0f400c582032010701d490b00702c100b10300c1e507081c0981c802202081103040c0c01d55580510155102d1c0300401e100d40480202ea00d89030421030401403403021001028070540000c100981d10082c0e5004000d6030f01c44c0d40380c03640c3c2000e885500035540140c4407417007440500100e40803900c3d01b1001040c01030320048469110306000f41410b00031409120420381e0524005c502254a03042282e0f58440c0180569140220307540106040c0002a07054030302d251b07186c2c012540107503800094004520b41070f01c1c3c10800384440d580c214010381000f40400407501c42103081a120074015601500e21480522010845403030b1084c48151105841c80040d904200f0307508088502d81060302c102c500120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350548318 1250 350547068 350547079
    0x60b15092103122205030403020909030412030e040204050901091509020a020a02011b0203060c0703020610121101030f020318070909051c020a0501050a020c010c02070b03011503090506010e0f070c02 87
    0x486400f43c5081d52180102010509081c40301840074141142c480c0700e003040c3c0140080c580e102d00314014002582400b5007182002c0c5c1c010071042280b001d0304c007560f00c0fa650f458030b000c0820204000000c3d001e4000c940000e41e00c008003900009550a142c0e00c18001e041d1039120280409030b0355091170080780181c41031360b800750700442c484900540c40750320090651b02c61031141200000641c0c000c40d20300f880449051240190000d100c10a060301040f005500019080504070200e042c6501c081e000400040010031204d07003802c4140090380282c011008007805600d0464891400f61241980001a41000d100f607000340280890001c1d22401102e5555800c00001c04d0728112061894a402c50403901c00421030198018000000b5000c3c055280140d640f070001684805802480b5800c44401002e6001554440c650410624188509903411540c071940007018005020300e090700681882c0000a0041c01008000b0070204902c0e01c038140a601c46804507a903543c1c0360b540c15142c2d07064141c0e0103544107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350549568 1250 350548318 350548327
    0xa0b010f230d09080316090f06020307150f0e0319090521070315060306051302011706010201110705060f07050c0303011203030b100201051504091509060b15092103 72
    0x4030740400003030210800c10a000103072030310740e51925180e0b40c105580b0541c503030100b000d4580c8081c0c1c0c011003842c09805402620f00f4105d241c981c0296aa20a17200b00404e00000c82007088070250180c0d0068101501c8280c081c0110103c40d41c01c180c403a4420303e40f042d0081d16104410481c5803040e0000420741c0c0c0041c01c2615010900340103502c1c20a8400c680c1041031259000110000b51998101448900c0c60703140862410306500e00303102074071001000b0b1030b040b41050a0003005031b0f910030420100110362035406030541d110540102e001d4000018020203480d000120902000030004001c1d01c50400b008102110340ca514108441502c640003010700140d20600050040003500c1c1c03d400b0085120307080c0000e07010003490100319250b03640411080540d5448080080c2d2003405e0807840c620b5001150704000350482561a88060402000100012940c42540c80c0c00c108069104804e0360303100405402d1620514101c02420750b0000c1000340c01032a00840d80303a508078805070818010820702c4042d6050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350550818 1250 350549568 350549627
    0x906090b0a081504020f0d0b0a0b250309050307061e2c01030b04050a090507080c0d0303321b070b0402010f0e041e0e0a0f020909150a0b010f 62
    0x10711151142ca44d005034208901900ca0319644020451003400e070710f02041c0340c0e5040d01000840c0c0b1281e400051070701c0d0104001c4540f2144440502200b041e02c10306200071902a041c100c80c162240e401c840e0f0588603a00c3d020071820740022044c00c440c03c110b01100c000c40da00c2201100d030821001d000c00381c0c001c491409030008650350b411740d41c080c3d203040c50009550f288420029081d81d5080d00c15417841540c0d11601d1040c04018050380000d0400d00f001401d4030600708001c1045a0440d2501508050b607503801030b0030014482420002528211002501800b5455140c84500d08291142840240084d418000e40c50b91001912a201c1e08501070310882d17992a001500c2c52403254000c0410881c00110f11070032640c891050110b68403841381c00c48043c1180151003001c840705c4252035101f80e4016918400042c50031410500c0300348e4151407040c1d5640750042e2061400410708603980d191000d501c100050241194407030184240240d0b2541041110b20405403802200745d19008011141c0a41c4800d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350552068 1250 350550818 350550841
    0x1b07060806130f050705090102011a010e1c080c0c011106040302280501090b010915030206030604090203031b16050603100e0919080304170f0d050604060e04030906090b0a08 76
    0x6071080d6900100f902d44001a18104840d41111001d0210380081944451035078240b00b41e20785501e4004000d510094140c002a20702b615211010344500c2403001031030ba041c0b08401e44000034543c00022940c0b46d00d0b5000400f0703140d000c4154100d00141c100f4000c05103161002800a0189401d0b40203004101da0b401604c40d041089010b2040c2c1c5401c4070310410001036401d20900e404140992031965007941840c40313041c0ce40321a42c00003a40600e040f00144056555141101d400800494000600c110f05202103030450080c038050200100310881c08558034280443c00800400b098100340980e1b546800c108001404144d501883c6c03440c0c0128103019600301b60009075001210071701160803020107200c0c50010305039642c070101c0350301d04084107000400403d05800110810090111824140300c91000c860754010121400c0c03c8075141c4000c1910344c0c4039070303000300041d100100303514a080c80d16040c060074898052050500080e804c40b80050000e00d002e0030384001e41c14943d05d0b1700c59516050940310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350553318 1250 350552068 350552089
    0x80301140904170901300c02011a06030405150c0903120c250909050c03060a0902060d02071e061e0c0f0e0a08070e1e01030314031f06051b07060806 65
    0x14148406154003214000214844d00004246c80b0320740c0c2c04005900c00c8010a560080030f60000756030410f034651940000c0316540101507241600d0054590340c0b18184245440310b005100b4004a034501c1c280050248107000030080500294221031045c462110196100c0c031805030000f400d030300840d901800c2410000c0440d2032403c51180510030544d03e44544c94103c070740c401812100e6910804c031556490605202281c2c0c0031a11100401103000142c0100b14580f103a0000f090f11954009844020010464041500b0080060560444814500c0c02c003000b070208102c04c80c03420348050b0146054000710b0060805d0840e0541c2e807a20418411b020070303140403941c4241290700080022001c560950704010002c0140740110100329141000c8032001e0320701c1d01003541d18070034451240040c008207402194281c80c0040540c0959a40da40d1040841841c02414845d101c0340c0c2401c030400114140d00c030002d858264200e0070341c090b1020441c4001e0340e80d8070b42440f41d000420f00100010b11540303040203100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350554568 1250 350553318 350553337
    0xa110d0b0606032502071716031e080d06050103050a0b03030a050906120a0c09060504030c14180c0d15180e030c0706090e0f24060c0a08030114090417 66
    0xa0404140713034003c20510307500071520750050740100700c104008503140e04800700e009058000781c0303076910407a40d038000c0c0c0d44801d000140142c8070a0308100c8548030340d8140f690792240c0002c0c9043c1c60f090030100c030001403c1c01c3e110b4140002d06020210f8807500385485034223112200140150302d4900c0301401a1015040807580d1a40000240300c040082060310201d00d210340c403541c0d00040d0550884002810220f001d801c140c3c10001c0c01e001c1840040c4100c01c9003819030740440f1540e245070000c0000140614000825814214060f40c14803586060b00d4019141120824605100d072a050103049910301001c0d1164920755541d00c48070402035030f6564088031001d100003045d02d00c4d11908000c8a4605000b95100302c0c00600c8a0701c0c2007050300313001d844242d00040c1d1110101c284d801d00404030744000154000f2814801c06055036001613039246411070700600d24140986090041c54248003007590400d218885229854400070b01540c901006120700c110382c0030b0f01120f800d050744032082800341c0013804034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350555818 1250 350554568 350554591
    0x11701050628050d08030f0708040c0e1b1305010f02030c1002030c04081f0c0c020906010e040e07090603020f0d051f0b060f0d06080c03070303110309040e0a110d0b060603 75
    0x3ca02c2c3c1c1c41d025014074103035004406442c2e40741402e2407584000200108540c0811440c1018480042c900610150803a185690412810307155038145494107800031b2004040c048001a0701d036540d54140c43c040d411200f09882d03841c030410300018103a03100d2085421143b0550030010410310744051503406940c11800903c2201e0600746c42ea80321504c0c00c00070b0030038010342856610340c280889615000d011f003102c0540c175207101e4112141c0e0114404031006070559042c841c0310b40c000c0286440d203a105d030240068050840b50f14540c2c0d1030344840200072902040c0d01a0302c210900f4003103800d090703445c10b101c954003400501c0c5d00c40a52161815485589100f070b91040d4803801c4500d92a42e80f000908014001203072002e5035a020800d206044032247e602035031054100d00a03d6440d035801040c00b400f165010300707010240404503a0020706521411040720b52041c9080c20070016181c00192200c8114440c01d800c00c03440c05854200000c901d03103108010b0402143c600011040d0030603034041e42d0002081b625 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350557068 1250 350555818 350555899
    0x50301090c03050d2f10060f050310051005150720040f06080706050f0705070e040302060906010503030d180c060509030c09090a02010c02190e0117010506 68
    0x9003591000282526001c00080091082c42818018103891110508001e2110b08850f51280a6000c050007148048294131521a00020080c002210040c1006c0c50170465262110800f6040f25018043c1d1400f91043c800964801c6419109850091740e5a42c07207555160700d010204105a0082e10b0107009108044c00300700001504c0c00c480400e0212080d54655083c070005c400e01080b51a070b8000075891504148040100e82804100c0c0810b603980c034503145503030f505c060300550080c0c03003a104010f0040c411040001100402440d086009500c43d07401d45125880c0d68148a0392402c0038000c035580340c1c00400568201c0c1d80d40707601203400b80c441c0344201c151642041d00c0d400e500304030550141c008520300217406119407a040c04070048518003203d0140072401e2808406a481640f00341c0207041c0a0b021001809540c2c8000f403091600840d0180c0b0100251516400c0c1d002041c203104100e1039010310503c41d01c00407010302800b4032840000c0c00a1202d81088801840c445103852920002c0c0d00c01030781c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350558318 1250 350557068 350557079
    0x21b011a060f070f0309030611030f071d04020d1116030e091b0d1e0b130911042004090905060f011203030f0209030703050703170405010c170f03040501051b090105040e10 75
    0x10881d501c4604600c2a868bca413041c1008900e80000701400c0810403000060241010f070481c0c0c1840c00d585c10b07140140c50380311410b0002e008000c408040000241d022800050b0b001c086111880d400d4400d039254580001e8038020310a440e6003c0d1089a04603250402401d0108000005025031071400038000c5a0540e9004a4040842030860035888064071102800c080b1305090282c54a14007008100300100701440c0c03070310140e020750b0041040c030854450f0b0540701d420442c2140040740c4414441d0385541d036542d50440d5001861700c20b030100d0340340c0100000950407402e4030200604844078002400c9503480e07a903504030020030b04802ea20400913800d000030642c0340c5080dc20b050166109034020400c890450501c0c810001d8803180c800080841040140f08590f4410300c02040e161f8000211202e03015407001101c101d0280a0320084452030101c20130050100541100b40a80c9107182850303241001c4034180c00140c0320b08200c150114500300010010b0103117142116610041240c285242c582c1c490 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350559568 1250 350558318 350558321
    0x90a050726070908030406050f030915070f080c030601090e04030c120c1407080c1908010c0903110103050402060313050f07080109140d020a1401021b011a060f070f03090306 76
    0x82260205030326000401242030f800058a4025000c4080158246460000c00a11610895040c1c010740840032001c5411100c0c10440c0c0c5110040c10240f8881510303103054018007405400c05900d00240c018408100203900080449004400c180d40e20054213040024030800031002034011000c0002c1030b42008040f540c1d4045802d40c4218a6944079203030f90490500410400c40c0740d01c84906a0071400040000c0d80340014811030403034099640000d848058951901201603a41c401031065003003c035422101c0d98032801680541b4411104d040c2c07500c205000460884408617002500500100f01147d012111440041040c1e4401c9084903400e214a0349101d060081d180c0c000701c2c041e9120220726080101100c101c04900140f0b800400c6841c042d030b4002075a829041c600030b4060b4410b031081d416141000e40441e03095010006802d0302e511168032041e0700800350154005901c4050041c04200780c40d10104032580c03840b140701c41c4c90034a03e568072505d103000c0054808a050081c0046d0020014145 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350560818 1250 350559568 350559617
    0x303070506271c110a0b06040b0301141807030503120a0c0309030e040519110d0b0306090d05031e180106050a0e0c090604080f0a0209011403060a0c03021e0c15010302090a0507 77
    0x181075818801d00340700d0148016170b10b9440d002c8ac441d904045818200e00c650b454610f91041c21102c840740030402228209007010301070340014040740400511040b00a01401c8154022104103c0030050034982c014100c0450f4011320000700055a0f0108121039486d00b03400050700003d4408012000c4002910345808440c42e0000e03100c000000442d251841c3e0303140340b05101c54054141d02820f0145488002552100c3c0030700300e07843c20f0100100104501140070000e40079802341c0c019004c00c480c20982c00007a42c40c041d55000c05035541c01d010020441b428260000b0086074410202c190440d1101c55405a054000d8a1000d1b0424824003000484400c00c1045442555410000c0e0541010600502082901c160064118031b039140c000b10003e45c800140c9694800d85483c0005404010154200e020388580346549049020442c103250b82580c5040041040485100849198206c0c1e41154403049409210180d405842400010780500040c1c2240e0b42c40f480724a050900030001ca042032501101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350562068 1250 350560818 350560823
    0xf090f250e151c050a0605060304050703030c080412030206160e0a05011101020d061d0c12070302180604080115080a020a031704120609140105060f010c030e0303070506271c110a 78
    0x4c5643c2030000180441c8115005031105481280c034600c0e25455190351044c10784402020040c660b00028180542c80b415140545030710544103081c032034035040095803a141507500051a032130b00c62002c00924050200c4d2000403202031b1041080360304d040b00548000b80012050300055400b00308404007400785102c0d0002608091030f04015150303043c040031004840003864466140302c108140b0300081178901c030306a44111546009a69503610030450480740e001240c1154020302c022401250306801904502d07210342d01c0c444140300309603454001075510800304c08040d4005064001c10b002140040b50000003100030f000c4002e00e00713a95945803400341b180f84201030319070b181c2c1c0303c01c181c1c200500c0048a80d0032002800c024082c6092550006107440130844800381030103140a0034804060050110741155079005050349d464034005e08080303460b420121944408a1170305d200c1080614801c4551030701c030000311002010102c18529459030007203060b244140502c40031040040101d801000b86160051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350563318 1250 350562068 350562071
    0x30c0b09130c020c0f0a03060c0302030417090105120402031c050306120c060403030c1b06050d05060301021201150c02031606142b1b1106011d0f060f090f250e151c 72
    0x50b203070920b482000c0ec00a1142400079041103c200da81c0c0e4084c087d039a15010075a01c82815031140c0c80000d1426981883c0f4807203068803001c584109580000c040e500c10001991901c504021021110780c07104101d602082c1d0043c0280000d0000c00d228910f07200005105010a940c0c01042c070108107003c00746035000000041000556807110110741c0142074110300150000e500300304810500b9909584140100801d240316032688140b19881840c40e4105503801505403000e14005003070b04400742089025004c08241d40e00041582400f005e812210201c0744030a20f5000801d1178201010b45a0b002d5441d00445c81e19200515004808210384440e01c0d17005890b0b108002e8900700c0c0340e50400c001680b107020036862281c403000c020a1466001c641c085036003022102951f9070342e03000520504080c1c0c6c5858000745010100440d034080081d003d401081c8611501e0b400350705840300005042528604800090200d428100c00b038180001c40c1079405003400322072400d1069a1080000040f00c16440000e00e9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350564568 1250 350563318 350563321
    0x714040e0f071d0f0604090302030f07030c02040b0f0904121404120605010f080c28030b0a050c030606070b04020a031203020a081003020f090a0204030c0b09130c020c0f0a03060c030203 81
    0x5901200d800c0743c90700d100980260305407038070701eaa03001c41c124004d00d080e0040d6221400903040500c01e20444540240100000b40c84401c2030800030920780319050b082340120b24102e162345082c54400035210007000c00030404d60f4a5503450340c1381113044101501c444240704500025150050040d005080540075503a040e03034048007242000820381e20186e1003401c100b901c4041c03d00c05030001043d02c080011003983c421110340c518404201c3d510000080d40e80000350781000201c10446c0c0070b9030903805680b00c040217020540f0303910114001d034401942c42f69484802004140000382858070250f6110340010501452103070303281c0f103040c030741c0d840121400300090340024071020582c0c0044046401209007512b2400d11800c60f80480c410140c054061407042d000c0000184404000c0c1e0100c50282d607000080f00e41880c0e4400800d8200d81001701e507a8441c031807460315213000300024480c203800046980d009040340d1854809000908440640407508000005000b001003035140c0a0706901000a98005949 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350565818 1250 350564568 350564579
    0x618030d02040306140f060105270301021303050f0c0117040302150a060828260a020115061107090c030b09040b0405070e04030504151e2106080714040e0f07 69
    0x3a03500080080c80046d52802c01d1000c80e0b68800241c0d1000320400b80311040d00e100b82d180b001c421605461585a144d0f000040c03180034a034107217005104991084080364010f40300c1c00511071b10b0f555032803e45800079080401d000c0b60340c01c09051198226009005480c20f08800c1010555107036000c0710140c1030325440b08020016500104220040700c02c909501401141c01000003402d11711b103240300a0300c400c5031400c1c004801d10b182c0500c89074804002c410340c3d0b82da850786c5030040e001e400c18110403091541c41d103c0008010f8050b2010b881d107100c107074019000709400c0c500310a0040902680440070150384224115954503105883d0380031707a0203003100320448d26007840c205240446540000d4a03a000703040c10302c00065000401d640a032030b62615000d4502039003800c21100c1d00080003c113404c2003200146109001c0d00081c910510301c40c0e05410140038120a4440707811742c0c42c0e40c071460700c09a11a03041042180103000d00c50011000081012070b0754400c945000d0301c0c20380c450b0800f285036000800c04024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350567068 1250 350565818 350565851
    0x3040b090606030a020306150a170a0b100b0a14091e0a06050a02030318210a0f030e030d02070c0801060803030a2f13032001120504050618030d02040306 67
    0x14000012001030050071110390210351200700181031001900234440b03020300d581d9100034226014101002c4011040300b43d1000c10b40c1e413002200d0342500c00d503602c9008100c0408044281c0c9081d100d0380c0c100b00e450700d43c4c039410403038103000a8005131055480a0146500540d00da142e544d41d048076100018203034252400c208408821b143c0d1129051004c00c0080588160300402560390241c403c0301000d6042011400e118142210707443d507220396036006007122040141d0500a0041c0e0f00704c0d80d851030700707905021506504803901031038062056807040c403040c130101503039800400480344600e907120280303551694010309486140c0c100008540000c030070840030b09180d11034a10711070745421110841403050408545403a0442c0540018408000f515003122890354501c18000e50b4801d1103221a182c5041c0142c5d000e060701340e24140024420000c95088141501619024582060191603d81c4071150a200c4c04009109900e810b03010038000380c5514202d82c809030009500561010808a881910015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350568318 1250 350567068 350567071
    0x6010503010b15070507051302070317060108160e120606011202030c0304060f0b03160f1d0609270c09060607050601090f151205071a0901030f090803040b0906 70
    0x18080d038500340e0b1802c2c2c50364403510070081c55000c41d071140d0303591012420000d0602c2425005250081009107510000c0c8195a00419804d8041d54480805001031484030080c04420341d9000e00051405000c28003030701c01c00020f1500e1510034145000400b00500100d6400074a0300c250b260b5640113041040801c0d600300c01c00b0b611092030030108505e58a0300080482d1035020182c406044140c0d5210344003281075840e804000b24860040c21079540442c02d40c500003100c4c0301c901582c8100c02c4980000104000d00d148040030070b885280200b822662004d050181014000f030610f000c0014018514440143d03180c0d072031341220000c001401400310940140202e1440c081d02842c061041084076001066000c203042c0d041d1824018040f940030030054000010701128040c0d04d01350102803800040401b0b4100d80440400d104605407900c09584903042d100b0466180284800c0c14010840700b4290f601c03a074005844080420350004072030045440b4070406401c11541210086a18001d101074000100180f5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350569568 1250 350568318 350568329
    0xc09050c0403030f18090e072c1602031c02030106030b101d041b0504050f040207050a08090303120c0705250e04050f0d1d01020a0c0329180601 63
    0x3441c092541c0d07001001c0d520300c400d5020402036040e000c0031607550b00d500001300601d102d030300500040c03024100c81c0d170720b81120f803240303c1c400204054134500d000d101c1100310500c00701410030b08ca656a550204041450066a540002c6010030840c07884444055140c001c1101d03180e070340040e1a50704040001c0e0844a00c0c056843c404c18a5a000c0d03c2c034140d01041103141c0004a580d09015030180c40082405015094003080d88940b183d41e00650956000010700103c42003222084041c003400d1003803004034480d95601404940104a445010410386401003581d400d024080340c2c5003158a0342002c0b2603500c150750041ca00400012602e060203002c200740300841ca211704013121a1842d0020000415496120f10074031003001c0b600007028070901344000c181c031550032000c0c1c03194003081003030042c82400d100340c0210450200f0f08080c0140e520004806480b190720241895409040da1140500445407950f4480c0321845a0440038600c501001071601070001c010500c4001c542d0000780c40c3c2030001c1600507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350570818 1250 350569568 350569591
    0xf0c0c06090a0620010c020a0309090501080303011217070614072d02030f030702030319060e06010507020f040c050a0f030e280b010e01090b01110c1003060e01030c0905 74
    0x51800c555034600c4007204640c014240400a213141021100264490710907004842d40303400150941c268020401d4600b26100e0750314005050303107078a803880c2220741c2030040240b40c0d4014401071101c031045031010700d01e0a009040b501202c1e1002200a031070342d8810786040303c42c030361205684800e03404082c82d25a00001641000746205e03009c040307140148495104400100f05090f0700140c0d507907000340119819440c5000e141c6649260010703001e56039610540e400000f2101400741c1040c1c0c44080d114020540d0300030000040c00d42c440030300445864000400030b0380c0c13003004c995055032555114482d54040c04950384516413a07045032a4060300c0c0807008a207180c1418103043ea010110074021a019030001c4110300d580b0050b40c61a11401020007680c10b00405150202d0000304442003c007298a04071a0b09000c2031202480100046426441980d0b04060a80c091600b20003585888004030400c403246240c002441d9940b43d00d2205003000030b03441900c20031a100024450342d05180695903001c0c02101c80d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350572068 1250 350570818 350570827
    0xe011401110105071d011101020f0a020d05190305040201171005040e1b1c0b100801110901170a0b0d0602070b0603070e0a020705070e070f0f0806010e04150306020f0c0c06 75
    0x180c003a100500d00c00c0c000502e04038103010342e0387c0985010704802d003e1000840d12002c129076050142c2d80300c03030303088400340c4201481452031610074011500004031074040c0f200107801c08042074015000181c4105d06002e05540c903064245a1507881a10a51209440741040c03443c1000b070000316160007140144681082c82c0c910b40d9501d0302c500441038490b055900000e0900d00341c0c076400d15011000b80081c1404242000e00c1a9843c4007110507050711914402003140c0f03440c203140c0c0701d4644a01008640458500c4c0c0d601039151030581141a404141504041382844160300065a1510f406604403541d5501049030400c0c003c81f00d05940e44144150020100d09042100501c00b10384010074140c2c80302c2d00082c100c0b04000090003c00001c0000e0002105c00c0d080c42c0d14060441c8040780a0880024407015504541e81e20524615020b0030b410385891454500c250240f001a04080410411448d41144000006007551000340f10342285040c60a40b5003400040740760500060050781c0e0702c00d0b0780600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350573318 1250 350572068 350572081
    0x4060c0815010516051518030301060e0402070f02041104090b040c0207051908010606051b060609181218090f040b070804050a050619060801110a030b0a0e011401110105 74
    0x1c1e0300d0001001c2401c0054603842c46801c98100d407001c04000400b0b078040d810f1015000e040c02071504d4007c4c1d0342c51170a120014a61400c3d07640e02e000900c1100000381d0f000c0324254050800354001c009480c041c13021041592090b401082c10350300c0010000411030310001c0c2c1000b2511140c880c3e9211100e04035024090a0201d01002b55078031521700681e8030412604c52400c056494900903039000f800303608020b0000d9551224007a0254000d0500074580c8202e0001e43c1c040b07594049007141c03103848020021002030b25104560800c8104858141d2230700e214030710808201029542c040c001d0042c0c4000154040c494080a10203440c6014140c1509084000c0a00c000580c084010550140c580e1804410545c1c4900b000c0b0310301045039402900350b0041500703011001c1324000070300000c070000c20380501c031455642282908a0300c5200502a02047c2441310700b2a66120713810451094000404d480b9080e034940c03c44860f600380030b03030180c2c0b800708080c0703000d883c5941c0001e00340c0c12541c5038100030000c0740307050f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350574568 1250 350573318 350573341
    0x30f1103040b0406260405061501020c090c030c04090e070321020a0213021204060b3321090f060705090f0910080d0e03011410091a04020a0804060c08 66
    0xa00078001440b50005d01c082c800d0b0130100c0041a04485500850454182070504503100c44003600c10380c041400c00558130a0a5000041105c20f4820103002204655a90082d044003600007078100c250000040000203101f940b5405072001484480016000c02451807030071a4071150092240d00c003610398525011052900407036000707592501a9015156000741b9101100284141500e107014014803200740070611105138004013131154151b0382600560009001180c100c0d07881c14202c400d210340090103c2d000c01242c4041c0000340e92002d506100c10404001c1c40034409800c0f14905110707071040180003010f441c02c000054224060f4200180340200c0100811f110b1030514541500800460020a8624140c13040b40c00041c2072010640e00c0d0100b24220085c00407450804040c031960910341c2d1614510681101c20b03001d04041d00103448418503200316580644030044030b1280700c118050002c042c0e61114001005240c100e43d442110a140619003401114074580407042001511403c020451501c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350575818 1250 350574568 350574577
    0x105010212040909031b060c11030306030c06070503070b0c130f0609140a0513140c1204020d11030a2d110103020c030d06030f0302150705040302010311090d030f1103040b 75
    0x10f0350030104034030307a1070304050ba10814404440c100d04007601d03032440b0501c42d50b42e10030142040d1a80c0d0310f0740683c0002018556a00045d80c000d681600081c800802c5031420400170b06100e031041041d00e040c061300d902c4007603807244216511015034800140c5500c41c2c100100302c0e407001e4888030050680050511800034050681e500a14211003940c2d82400c020f0740d100e8642000900380245400d07400c241c131042c110040e05080c202c40b64111030100c04506403030030307800680d1070341072040d10302032103507580d54080000b181c2078104191980c41c4944108400c070b440034440030800360701a01000e2001002c41c12142c560311005024485c5103c40c04504000158544100d03070740000d000d00e009610755018560715401d611446020206248c81c00c20000204200c4142c0360400d40e010f5029a100c000003022080030f00502240d5280019100708014801036001e03a1141a501103d04039050410300c2402c04034404020704030080e00410400d50201040c55409075400002ca4030200c0910300b41890300b980b04005004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350577068 1250 350575818 350575829
    0x21204061b140f0f0705060702150f0c010501120209010e0601020a140f0715030501061803020d0609060f0f05100605041505070f060e060a060b09040c1421010501021204 74
    0x10003036101d8240103000301010380400c280801d89440b00414202d0680e103d600145a1426001d40c900004036460000300340e95400c3c2d00540010611210032071444850b502020b545401e00109211010340e600c02486400e01910000382c507030780561818010010f601805900960110151704100700707850b640031443e95065980005a4049003114007085400c011215070b1041161168000010368000e20100c014094891505d0070011a621008100d407511842154040e800e083c1260400c01410203a41d41c0d9900c0740958ac00184442442d503506090341d00c5219031008098940b1840000c801ca1440340641014050301010748103881c101d13024215001e28410842c8070910071312201724003405882281c04040d4402030119031249546803a8004110042c0c43c041c05100c1d10700000c090700e903107100d01406e460560040d10708140b034000c05c100162040410b8802000030440b00070010304903090140000f40146141c0700310b08404a415000c000c001607202e00c3c115840303480c500c10034070002c00840382601d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350578318 1250 350577068 350577107
    0xd060905091507120e0a0b0a06060822060203070e040501090e1b0a120804080c0405010302060f18061b100207020109051014070b071112032a0c0a020102120406 70
    0x596003070301035039002d071180c500c5882c1c1420b05000c00b449905c0420300c00907641c8601415513958031500d544c00c003240c2c0b00d8050070300403502c2403001c14050207901c1d040300c0107148050f060003042c442917510203003660000d444400c042000708222000c03507c3d10340a03007805800b6101c000c00190900c030030300340d9580402051612000c41e245803200d089840340b01038070001e005140c510030b804031000e1900483c5c6500c248120b00481c000d00c540610b45141500585040300d4008042d2828901d031554900003d500c0001c4044e81c4040c0b11120902644072600502a02d0072aa805502140c500480140c10701c03a83d6130548130134034810007400e0f005070b82005d40c0c10152001a10012491000c16005940e5194403c40403207840402242200400115003440b6100741d400d07540301110700045124060b511043c0295030390030040b06000159542004845151140e609400c50b400c0a06108000f92540d6008100414440c0c0203804004150751b010400c6502406e86001c1940c50107191400c005c0214808082c083c60b80c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350579568 1250 350578318 350578321
    0x14040603110405040603081306030605010212030901140a150605031009020306010c0501051f170d030b0415080d0305010501050412031412130b06041109040e010e0709020d0609050915 80
    0x1c40341c481c290340151070050b0003040135580744d0130f00300d105800403801641848105600817800c40d01c80c0c080d200855006030005d049078104891583ea05400003065003407290341e42c0300e10200001c0104201ca0140448001c00100f003915146806481d0103540c001c281484001c00900c18034426103085842154501d00380181c4944134200100d4a000e03a00c40041c0466080c0b90910142d04074a001504207001c00d0300745c60142a83e10b01c042a01c02c40108202c100036007200e480100c18900035000084202002800001c04e003082c80d1840110050f56042104c4690010a0744070480340c0500c1041d0141c042400c046003003910700b0315841e841d44200c0b6001010407491859031011102c0000558000100c003804d1000c003860a40701b04141d840354076200f600d002c0a943c01041290405200d000d40f0350b82d00e100c1c840c0c071700a0420144400f802d0b07180764040e900d660717440d003e14110320188516000790070400d1025a64141c1201807405072566a0411013110380741c1010f1000d01c0c403001507480e0680c80101c8075007099 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350580818 1250 350579568 350579591
    0x30f110316020a0b0c12010f081005060a1e1403030405150715050c03040302010b040209030d0305040503120108060117161e09050c0c0f0604020a030b04060609020f0306040c14040603 80
    0x601044500040010f04904c05000b110f50300c150182c802005443c0c60b01d0040d82e6141840e548146880c401d407503c6030049446244001c405070410f5900c1440a844c9120081e40e880700c407081c0d0b0b824021404900307824180c080c0405443c0f419000d45c00c50084005500342400c1c00001490801904003007030b080580011035408200381c10a03000086a41c9901c00c110f94508040d000c1c1076503100301c034110019440c01d0107140151505109403058000064010428000e010100350011300c4084c0003650b10b4802030040041d0400d003403d04501a100b0b99029040341d52600701d54404100782c41409000682100300c0d4004108590403c0008907003418283e0101034003407400b050a1000300c1e4001041c528141000c0084907880e2000a240c0d100c40f140031215185040c2110585444090310b0095025108400c100045030810380e8540e00f05010300e0300040d49030303601c111b210120381c09840c2090342002d010041000d1403405200f2907100c00620f04100c941c1803070304140f0181740e10940c0640400c2c580c1d1801c0c40090b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350582068 1250 350580818 350580823
    0x120a050703020c0d12110109170c0715090317040303021203060402070606060f0f0e0a26030d09120206040b0c0d0204090f0207020411040608280504030e01030f11031602 74
    0x80400001e066110440c201e800d101c803410f450f00b04a45e0109094510356007100034144a40041242c00800706050302103844103c003a554004850015903101c0d04601103218041032102100c20710080e12440f0342607165140c11258441e41040b507030120407060000700302081d004220201412403081c0b210f50741c0d54030a00098001c0c0a40070020300901d180590116086d07401c440c403503860b5146520b41c00545412400c04852110640782c03000d800c20090310742040038800a0102c1c0d21204900e503230342d41e81c11000c0c0a4241ca075810001750180d000c2c1d200d82002d018441a15250300e1842c4491002c0e200500c0c10b620b0303030b08038814080c0282441c00c0780000c1c00d021f050340f198151030181011144c240504541111780401075000f1500c1a44107030700c0e06000000300d10348101100c08452441c1ca411280d5614015034154281101c4804507a10110f014400f101400718403070144100d100751550b951544001c00010203c8038803042c660041c0340340c560741e11150400042030f241e00c140200301c00004180c038410100d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350583318 1250 350582068 350582083
    0x6250609050f011505030a201c08070210050f07031d03070303120f090b040b0403120c0c15020a0e24030907031406060915030a050d0309020102060603120a05070302 72
    0xa00740d0003845074085526a040d00901c40701411402d1480c50300e0f48030410143c5410449074028040135640284017900c0b2940d140c0940502001041e201031a000141c0025071400490412039010f00c0001c0c0d40411454100c180c1c071045c45c3c0b2407500f00d042c02c0015107210041e1043c800058284a15000b62003550701d031814040c0d800c0b460250a80750070320b580e40340180c0321203041d441402c985030820a03040c103060b00a11a0510086e003000d040302742510355480d1202c0c1c0c070364050425410441407030403e92480f21640180b0340c90000c1c42d5510540b00410b82044c500400e448141d05100600402014250320340c440c0f0324030302000c004c4400c9070b0003a01c1901842d501122070b16541311005404410007150341008500c03101240e01403119005070758000d05419896040c01c45010343c0c0050568045140c1111200c01c91204940c041c0031140c801c1032503220103160200c40c100c07050020b40c43d20002d4007196030600520790031072001e900521207011a080d8450b19401030001c20703000c1200100e01c101c1803510802040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350584568 1250 350583318 350583323
    0x60302040f23040e0f121e0a0e0a060e0306060d0203100b01120e010c120504080a0f0201020d1406150909040209071b050c010906020303091209040605040f061406250609 74
    0x412600e07020400080e2114200052036100e401034081000508068078201d80c54480700a83c450f004c1070000381a0f031088c0c0c200300300c00c1e800c10007a0740341d00c1403580b00c501010011341403503103500c2004100c0c603040509d82000100424007816082d4668030040e100040c29100c0505402c0001ca031000c40d01d00101e400340c4410265000407402e201507040e18100c1035028840007422030303031500c00f80c2d40040406030a0b1203050314000d0403008100042400c02e4864800d1030120b50a610025181182d03c10008003946c20202440c0503048821080c0041f9107464004040940381c00c201d0b00b82400080c400180c554503004001030b0003501d01c0c42c005a0081c0c41400c01c0d07040c00282d00b210110815050401c250f88034030041405022440761000415514000800c1c0c9201c2d1a09000404188640c06440a0181c102c000b007190820381303a2314041500d83d6280201c144141700703414002203241c40c00c96036502c04c00b2104030a41c05600300704240c154818402c0c030444c000480305841c682162049140a000500180001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350585818 1250 350584568 350584571
    0x2010e061e0304060e1b01031d01020c010507020f010e03030f06010c02030d0302220509042a090504050724050306031c110d0914130e0304080703060501060302040f2304 74
    0x300300751603040201450003603014200800400b48048100b603550703146101060403100b202483c88140e0f41c403c1e0030226014152039011070303c1c2c03200d0f042030b1400c2e40c000c407540c0c0036103944480802801035030400c000c4100542c1c500080c000b103507032401682c1e180d2001030071400c4040320100c0000d40c10390040010407040b56010b000c84001c3e0340352002c001c00035041320702841140303454803415044444a406626040d180010600d0a613600e407650f5000a040449907120f8441d144000800e0301c00301820701c804000d01030311101045516040c5492800e000c01f582240503252035136090360a11240c0344650000b40c00f13041c14640d680740c03182c10000f450800c0c40c030740c1c0303081e0260840807840c0070a80c031a810704100000d201c00c42d1f1480c107280c2c501395078003002d41c0034031884032a0040c03170500140f820712254030800700500c50004141129a0a69045500640003410ba9612084040040101502c41c403401800c0c10300c0d0840c2010308100d2030074210412032249281210507909131b8151101901c102d00c102a400620 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350587068 1250 350585818 350585857
    0x90a2d060908150609131a16020c271b0a031a090c0f072a0e010602010b0a0303030b0102010e0601090e0f120f0309070e190e160302010e06 61
    0x1002004a4140c1c0100d903003901807101080f4442c0514044240141d10041880c0001c5d6103103400304000c100f03070003001c0d5900c685400d010300c1311181c8403511380c0c09002001001c10b040c01101901070718062226a403140107208c01d89107070403058a00720201d00d020114500d6401540c45008414617410741c0c8100802d034070100003c01e000300e181c26511a0310604441903504403028204810402c0d10b690440b0b980c039241404000d83c040031040341e8020302d00c030352041300e4a0246140618183c800c9043c1c03036072090a20754a01034180102142149042d0040100348024420800454081a072030a510b110080038075403101c0500e20668000c0d040f441425a086040310800d680d100364441c06010441a030907440d010f0612816016500440c42941c1052958000b40c94018028540c03200e0341c1c001002029180a60000031540103014043d0b940a140901c025540c6016030980c00400c1300c1140c40300b450694490607000400c55550210a0202c903024204a011301840001141c0103128030003c0920030140c121 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350588318 1250 350587068 350587079
    0x203010b03010e0c0c070905180304081e07060903032f0a02040b040903050403080304020d080703020303060102010f0e060601080a0605150c07080a080d0c02011806021806090a2d 78
    0x1400395040f02c034044100d00b0f05480b03003141d040319485402c1d040b007015042050207010401d81604600d4001c91025144072130706411009860540d0481e40007800385401141000030074040000b2590220540031024000d96880c1c0600036001c015103210080c00d001103540000003180c00d502d01000800a04220011040030b80c8031050b40360b00c805c1104904c070303d281c01c0d02c00001c3d00741440792035415507250702c5051a06007591290001038000038401c99105483c1140d05000680b941c0240403842d1103600290b8a900b4808006803d44150766141d20015140c0074005926100004540d034012800313007400d01c0c0940300d400e07074500034200c030f504180d80009803500303e080074882000c014146001c5800c1a2203c0f981c07140354060b165a491440a0036030f5900b40b203e001043e10540c000c1000601764000040c00207415200a0491407102d1025034007250301061040710441c02d5500074030300440448660b0b180c076010100081c209150b0317005041d000710761290306544d030318503244260701052000c9040f56580c07551007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350589568 1250 350588318 350588339
    0x603110a231603113f0705060403030e0604030c020f0a08070803090a09140c1303060914160303120e0a0807080a11070b070624030b061008100302150c01020301 70
    0x44004900061102a02c01c0c0c4042c0080303005000c5c528240d1040d854031100c44002903a018540491041d5241c5091141000703440d07640c000d0103030500c1980030341120320301414044d0403651030a10b00101c80d00302c4420400082d03407001000c0c03860391341262100b05d03010302c40002c07403401c0e100f81c0c000419501c591540425503410000242205010494552280b2500c0701c0c00201914005803121f01d50007000d2010844031004c0b0005001071031010f003a030445072690703901c80f107007518a640410ba80d1485800e18408a050041c0300c4d0901c19650181501e002d1441d43d035004000040704400b45100325900c0d411000d1520041c081c80308455000400d01c1d446100d01d0804280301d41c440060703440414444a80b99080c0301f4041050000c403000003050606003000c0d0345442c00601801300f82c0c030108003001140f250500c00b2503207201010b94066030f00302e0010f00d400b074184040356146026075802d01917030310304014403c2d001c900e40c1d8040d0b80e07040d92040352410000d081c0301c1060044100b2021294004000413030540c0301d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350590818 1250 350589568 350589607
    0xb030606040222081b0103020405090403110f15011d1603200d050a05010519060f090803190908120304080c0703080d0b03011b05030f07020316030e0a0603110a23 71
    0x170700340907507402c60700d10064040f4401c521615411200d0b0400040c08203000380c0c0c203201c1c040302e8442902c0741c5c2c007901c1c2e84150801c80c0300da4122581d005035800522091019040c00003010300504480340c030504000b150441010488004803042585a0141410038032904000112120b52140034035241c031910f017110409020100c82c018a013900d0f0030000102d41c80e03c2c1110800345c078480308a582006003022021900c0b85080c0c8484820f00004c03900000710310b20200700502c40c424900f0700d180c881c8000132000074104442d660020a0316400441070003510340c108800c994010303501a40360b41e41c5080c0c40c1d604c0d50500c849540041e0036a0b4003c2071106e0a850381d034002407a0000708400030030420302c917900c01120700303e88601c84000007103044c0000380e001110600420341260440c01128200722100d111030007200c100f9a4104d000668020b5061450705001c1d0088000d0045401d0600059131000e840007954050a5000e4040085a00c29011130440c0c441c0e205030a00700e01c000c40e582c0c0d0302c071310005248603926 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350592068 1250 350590818 350590843
    0x3040803130e1303050a0507020120061e240d0203120301150206040305070b04030314010b070303060b04080c1909090818090c0405041a0901080f07090b03060604022208 74
    0x20907000403403904101249900c9644d26440304ca00700601400100c3e0103400c00e03102213040c00302e10080e80d800001c0000003540015080c500600311841c003840c1c2296a015000c045200342801078090101c40d078008240c068a500fa0101094070f1701c0c0d44000000c44001c007459019415001c2c94100d41100803590000f14141c409138240e0000c10240c10504070794900301110f001c1c3c00204203010840c0000e2000161542180c060f2402181b403019549000ea210f02d000e07440030791841c6001540e24105609030090f080103282c0e03c0149401c1030700e805041c94640050034584c5109102c001e00c0001c02200e480312070009001d07072901c10000b0030348a29299400c0d80c80520b4002040b81f4480d0043d85070320303258030702510407142c4110031030500345000d00380405449440700300e50300c0c10300c01c1440b00d860b0b48072601d0a40c02000e04400802d01c1c120669071090408045c0d80102840508114040100d51400260150000c05c10b9900503581d500d2884024141e2003142c800c8010030300e00c858005241000015603810044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350593318 1250 350592068 350592089
    0x1020d02161b0807030201050c030c0d021014162006070203040905150d021c0f0c030c060503010803070803060111010f14060105090306011815030b040c09020a0503180304080313 78
    0x40919612008041640c031440401340d000c0b40e010f1005510540140010f0b04804003200d0400b90820f0145040c00400a01040181e0180c80d00480b01c04071070280810345018850940440c3c2000039404c21a038020303102d07803024050ba00c044507003c00f807143d41c40000e0480900a44500e400d02d0070f8001d46952041c4a588002d03428100441d4400703030b0702c50041e4501e84006203c91102410b507030910600100281420f502d8240c0503a03054082000c2c89220800c4912404440d0072042c15403501e5080c90356141c0080c0204070b814001404245800411079200f0750f00094516140d903100320048403982c90319075150409508060700c00e51500d005800000300c00d5840c15080d8031b960340342d4004442c14000d6079074095041e40084010410142c0038414024240d10404001c01c2c043d0310340c0c41030340d81e01610303510464200c0351100400091182e00007102006c0c1103000b1080d80380483c002801405800089d1070342d5580e4030340d02e00540000000300304071002001e9145c1501d803100480d00c0c0c4414003161a01c0742c1c00b0f101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350594568 1250 350593318 350593343
    0x90c120e150c0306130506010507030c0302070f03061b020307050a03050919180b0102012708070209160e0114040e090c090108030d1a010f080c0403020a0f08010f090506060105070501020d0216 84
    0x417110380c0220303480f501d01030307607094203010481d181115031a420620a80a42c02490400300c6d030f4810b14100c40010314007803070b004120300020b040c400f084d55114800c810215082480200d000900c0403401c9450380b03030103260082d00c0c0c90211002518240c102038503000d030121000c0c400101644101d440994050480e0000c100350841a801603091720256140a1205020400d02c0225640f9001d9070002450007074234070f0f43c20720100c0e42c00304216041c2035076a501001508100100c0160340503224020825007841d01100d00c107201c42110302c8500460051441103512540000d403e10310400c426540f00c031000b002425256911140c8a881c0d5014010004285080050070304201000f0075805803407500680d5042a990b100a80840701d003040035016204e80c2008000010150365040c03a810060b2040013000703102c0740c3c5040c0c8040c2c01c4640040c00080c01c18140900f55000c00d801181d05a070100083c00c1c100c1d9204103a2402d90300900c12801c00b0b8080b2440410b541808010307074030070040308500c510b0740d0f04c808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350595818 1250 350594568 350594599
    0x504090f0b13050309010f090e090114010f0b0f0304080c011104080c0105090a060813050a030302030628170109150b091f140604030605041506090c120e150c0306 71
    0x142d07100c0401601e01d620401401c140782d442848080842580d91524404080d242d109490350311905440603030090b91111652021145900d1406005241040390b48078094580f0700c0403011401000c941c0d204080d0080700007000d0100a5080320f600040080007081070f90740407402d203581d60708a80210b42d002e01c244200c00703403d54043d078119141082d00500001043e480c0020494038254005d00f40011240182040400102d0400c84502458807a480242c1c59103455014000c0c17100344001404040c16070b1042c01c6008202011041b025110000304202079206441c61240c090041c0400061075110000100689216240e019a28111049031a9082c0e9152500b02c03403c89400446003560545905504010484440c2541d21020710301400f0b01f402c0503901d031a03060444804a4065a0b28000c0d010030403500d041c5882800d01900d071555040006e4000083c00503d40c0071000341e07000b0750554818064102500820004010600089090300c16180c16241002c154009032000e501684154296601 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350597068 1250 350595818 350595841
    0xc07060902090a09051e060a0b1212071a0712050c1e0408010507020d021902130c020c0306060a1203050706020705010603210527240c150f0c070503040504090f0b 71
    0x9000c06c000000d20440e181e0b143da100003060396514650744080b4201210f00c299809000d20394000009041c038a031104440c0c100f031408200582c1c0d030000e491202d0010010065003041c1300103403007500010000b070190788035500c0c8146446084010308611890300c01085024510000a00507203c0c000002d01c61526000c500b6690b07140c00520074009600140618140c68102480e0f2020860004226840751900c2d01c090004550b541d070703203001c0141c0200d600002c86090800100381c0124043d218002101c0c0f410b16a070800305517000000341003200006501c1706210098041c3c6840680050003000000e6492600114910440621404140310b0b11041c0e15a140a4002d4074901010624207001c01d800710001000c0848504601c240d1160a80000300c4000c1c0140170b16614050580c52102e5a6a40501c0d66914244242c00b0108540c1c80b21030810804408240f40c80781c0090340004016140c82c01c61807d5801d502858202940280c03802481d031040c04865152190341320b020b10f2440880317880f0a0710202 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350598318 1250 350597068 350597113
    0x90b010e031b1215180d0206070212131707050a0b180f030f0d0206010f09060b0a030c270e060d0b2d0108031306050309060c07060902090a0905 63
    0x140c940381c40c01002101410050105030114404209441d540200f503034208130604025100078545a0588410341c0c069402000340003180c0c203a40c001040396251450b40250354500b9070b0744000c5c00d24008507141242d40c2d02c0390030fa540034120042100443c0c40e84504516138402031886031a108201540c00058650119812648102c08916500c44000b8822050280b1000c02030022a054412803c0804600c41c080c400240d126019902038038055145c0840c0504480007600021441071501c0f00811080c0403032012981070302210304006c144051010416268034078522010f503604d00c80140000c1c1400c5983c6540c0c000d492040c04946d4190300c40b001803043c41108207000410b071480302008109424181c9040c40d840b1812001103c3c1c5800b8a01711508442c1c03c283d1100c0030b641d10220701c1081c800c601e04175540140c82c6070325140e8190f2405107201a9510b9010f4030304140000300107085000c1c0540f9800c450710f4160050708100c400e003010384070305006055043c0259214000d071500a54010225102c46 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350599568 1250 350598318 350598343
    0x3050708090304300501050f07170f101d220f0213060f0806150f0102060c03090a0c172b1101091a070e0307030804090f15090b010e03 59
    0x314105420a144d2000854400d1560461040320621110714064a50070318a40d051040d00049a9400c10b842c00056004003c1c0110341400106100100948050301040d68030640c035004080d0940c03070320800d0340ba007aa02074020340c80507486258000002c0c0760f81d46c0000d0062400c0c1d0318a04d01c41c4818103a8640320b04560100800300d484404041d0b016103010b0201c55030340180d611000400350b640c1c8804100180180e804802d10341c00400400c100d172290300d0046180c2a0003540c00b4101c2c040b1200000303466050003000d81c1415400400841d1342c544007041828111039111300c0051348551184a001c1c4500f0781020440313000d10548004200c0300202c683c840e65800500c880d0210504200b4a0a5607400500103403020503660320302c2403601081e1008809100c1000201c100c841900303003000b0080c00e506040c080f050099200400420000b0070900450703040380c500780000500c080e04242030302c0261020204080f00c1c408d03451301c0440c0500031940103104445090301e5080d021001441803544a00b80160325 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350600818 1250 350599568 350599573
    0xc0b03070c0b1b04080c01030f020c03090904060b0607030305090609010603031e030b04020d0204050a0806010501020615190602060106090e01050904020f120d0903060605030a2d0b090109030305070809 88
    0x2014009004050110b0300015124400f00095990030455036464100354003100c415440002900e0300d41d40c052068004210340b1400a5141088030300c00e141c3e44c1d22501103030350301031301706100042d091200c0d55101d2070700210010066559605103003002800f45c181078803000100d020b82c4000c980c1290381403040b08226541501d4800f201203c02a83c1105901c070188114103154036405401c5840e070783c0b480113100007800b43d140182c4860405080c08810081c1340c02c06421640500c006000307982c1c00080f02648858400c0c00c400c0708804450101d0710381490b540c4030b0080c1680122380070503403940200b00c4c00d043c0c40c007a03522200210b80e20900c5145419007842041e800400b1318000c40c0c090f0800021040d902200a0318840c8c1d00c1011000c1c8524080482c01c591000503440d00c418001c0090900600004080c201c00914005c0d06584880b112200354070f0800d0641a14044c07031100e00f1000b4101c2c10340c0d168002e441c501d0103240c00b000b140d01034180c65500701c4c0007a02d41000585c00034041c0c07030359901407a0407800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350602068 1250 350600818 350600837
    0x10050d0b060907050f040e10120c050907050405040513120504050f0907020102070b0a060306140906070e2b0605090a0b010e04060609020a020a020a081b1e0306070c0c0b0307 76
    0x922600202c06441c080420804000841d840014000148014500034103000c64a191000080110800a0704080c03103c0820940c1000881c81d400e81700015110101c6040c0c10a031601c91064415229641c0081d41103801c140420030f41d05006503c3c03d1400c0e000d400758481002c4902011207092280b40107242d80708852403580402c50030040d0740d041d80301d045800018505002501c2d2005991805c40f038009109441d0002071007008068003d2003d0301a2803946085281081c0103500d80341c28004164100b0084002400b4600e59074402c400960b50525038980c41100c2c002019841000d01d00500030f0f20b040d0304003004074802480008155600c01d81000140b05564200b01c8007182480001c0c006480c4661603100c0802c9001e0390303100600e102d0400f03800801c0480103610500132824a00e901050640c1c20070141d8903845601c1007103046103e0740803a0241507920101600c01c00d0800c1030000d264162090408205440360051840d440c814050050001240e56803901c04011b40320885072840040c01224 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350603318 1250 350602068 350602081
    0x90e010f0c110304260105090a03021009150216140c19060c0222050112050f1b011209051002040e010b030c0d0207030318030201020d0c02030304021c03170f10050d0b 73
    0x1405140044004001e04c0c480c00c0c00c05400c1741c01e6030740a0350b000c0d0468111401d0b103030416404001400e50400c00d28014030003000035032215440210583ca41c501c1d855000601c0703a0226a522515100941d400058a070f000100e0181190b6030300381c1c00541034018005800c49410305e20030360320304030704440d415034500015601c0c0b60f080c0141a400c00909403a0415580705c8585039201900525003e4244902d840382c040703207241010b914001c680c0069600540082b10004845040031519041d94102800e00c408003030080c005500041812040140807805840d580115180c11038008104a540380c1504100701c0c0d0f252140c510240c4025244d00024003410003160901c08a01d03006803036018003e044c0042e00000580085051034040b8104a0042c1d5002074064424030107441005100200ea1000703500f1850254049090700301f41e900c80301e20311003d0a40880400d0b204032480d50f04011301840c200d03038501302140d05100f924815118000c1150300450027141c6800d10003011212a9080240c0c0e502030348804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350604568 1250 350603318 350603339
    0x60e040e1c09080109030f1416030f0203040f0909020a0618030b041403030a090302070f0501050702130204120303090209010e060d0f03030b04020f0d150509010915090e010f0c110304 80
    0x6404607040c01240d0000050265084c450280041c1c0291a10b4001c802d02d0500200b00d0000c0d1200a116102c00340151100d1415040030a00c00b5681418241045039402e40c050340b45010300d5002d4070b40d2a00e00440400c81c44483e42250254a1081d6420820a0780f0740c5000d84102c000200c00740210040c81804002090320740c0d92136030300207005248044081c0c1048000609551045034141155900d4500c0e68040607810000c08005266041003500160304200000344076101d1094003a100d903800c2558511705038400c1d030444006000521203005641090701d00075000d4150484242e1040d0030b420000250b03103c03524038545c030034400100076403820795103075551000c04440f4650980801d5a1141114000d44846c401007007540d00c0c150b0019100e6820114a038241c81030541d03144021414100108415118041440d056900082010034500a05501000004440e034003182e03030141081203500f205801035021880c40fa00810b0213025948031100d0940d0546240b51016200fa80204020000503214 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350605818 1250 350604568 350604613
    0x30f09040f0504030305040b010803030c220509090a150605010f05130e0705180d02090408071403030c03010303030c09180b270f0115080f04140f0601060e040e 70
    0x380001481d8110380354190031103504807400c80c0801d41d04c3c420305c414003c440fa000d9004003e401c00540c910b00d00600b5184880c0201e00c00442100103080414502d05007220092016000190019203149407100303686940305071220068600f44011821021400091300481d004d40720180c480d0218030490340c5040b1a41c1c0e01182d01480b03104c140c8100400c50b81d1030000e400e4007c4800740e961b40e846402a04a81c04c4c0c480c210084240b00368102801c02005846020341d196200390007500980e00e49140341070181405582052030a810f010000810401401d2800a14180d0f4000ea4007080000c20195056911043c2c80c0642c8400c0c01e110300c4058004002c1d0380120140100c0900314481e0f03c11104090070119401d20709080883d82d28908000c18402141c040074010040b14001511582c000e4a0103401d11002405210fa000300220001d002c0c00342c02c103114a82c0001c40d004544d0300900402185031201b42c2070082a000440800040c1414a85801a204010008006016107032058142d460700a1503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350607068 1250 350605818 350605837
    0x204030c0b071b0905161803061503060905030a1e211103130b0705070309210b04050106060206070c0209161107090605040f0e060601360e0a0e030f 65
    0x241ca40c0c0e04451550101d0203c401010400c001103a81d041c0b03940c07198441e2040b51200e40c1040720001d50304042002d0420300e03030101c80d0840400a010f4100341d0968480075019080602030380e050101b42003c00000000411000d8210303036984402c11002c6154000300701c0d0317017401840020780480c2004202d00030f0b424144401d40d65a0381c0021001c0400b1500c2885402c220b9400207200e0549003840c06116981062650140c002c2c90668905203056030080c00d40f2803280100708010b412116520285c80b00c1000c41d400280c0c201001c14024609413504a0281c4028001c2c0001070180c0c0c40400d03203041c001ea0108000541c011308200256940141079010748413071000c01010440c40200c0808819424000c03880601f00a92012540310b0420741070006403080044a012000c1c681402c10341800c0c00841c02d42d402c80c9092800b51409500d0b111200900d01c0c00304801e140d002000106916980120204a403c490640400c03181c60350710001ca1008130390111040800030b400400030348000208100003040c5404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350608318 1250 350607068 350607083
    0x1d0a030e03010f0c11070807150c0206070804030f1401061215060e070801031703130204050703090b0a0b0924012003190806120c101b0f150204030c0b07 67
    0x8000d403c160040d501c401c0c8080c4081204a086020b00420904c4080003808a250060060070b14100f10b844020809407840b000700180411000c045680e4002103480c840d400424072500c407526818029200100b2001c2111005491801d05101d6a81070081c1d01c22a21481804c03001c842040c5c80c1c8500c0b4145507400c841c1441c1da51240800c081d203050f407099003e0b8481c0e5603441202d40c10b42c6070000000e5005400c0710303e10441071003045081c841038120104155410348001c00d05848400301a0007a001422004260541d008204007406002c2d81c011a441e00d41100d0b0102103440b49811400c0e60840c4960ba0381c414048500c107200300394000e50701d0f00f0b281c0e10310140c2d90500c0c0d0310a041260031500910030f603210b00040c50083e1503229a00105803070f004842240c84044080e40c14094a13614030351502498003c491107024218014000c030321695601c014551051000000c52504852048034103d04a0b100a4040800e0440104a20036201030301d9210340c40050542c00c1c50b600e0030702500f0007c030444100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350609568 1250 350608318 350608331
    0x190b060d021b0d0c11060a02010e010e1c0c0807020609011e03020912030310060807021e06010f0e0f0c070204090807050c1c17130314101d0a030e0301 66
    0x19458401442c122415003030100455500c41492420142c40d14000c3d42009040544140403921000107202500401c0b142e40369074040f07240b4160301500310000514225441d1021061614002054024120316003881c0c940d240c448a15040c0c41a400e504005421650240000c00c01418158000c2111820504004031b403428461007040b1084030754000080081c5d0045080030351418854003c2c2245804440a0750071494840d10f007440b104142d01c60078040000010100c0d9469009211815502c1000e20740060503c0400d6100b642c0c0703801c2842034a1002d1021310000841c4950f01f0306a41c081d120150754001c0d0780d220241230b04001c0c1c001e00c0080c0d03071113562111000000740c4400b004240c4203114402801075200ca0004001e0514010402c1c0e441406100501400040c030010010813180c100b118417640702e00c42500d6490745800f07941c000410b1010f80c225500202c40000641c11a2028032480901200310884c003880500e4500a030b54910551201143c0e0001030b028901c1112010405400040c58 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350610818 1250 350609568 350609587
    0x60c16020a06051309020f0711120a03020102030f0f040c06270e0f0c2104050c04060b030109050105040c050712140a030e060f0702120c1f0b03010b0108190b06 70
    0x14180725031004000c50f07000101c4095004040030010300074403021204505001652000e02502e100390000101800b1083d40d20403c0b0f80d0302c000301d400c40394252302c00319030369186c0038500a4003d600903610001c0d0b03040040005440341e03840310410745c401c0d9805030303040c036002d0701d0490141d0780200200081c4455885049507024040362683c0600001c4c070040e0a91906420140b001c0210003102501c48a6030380320400440040708080c2c480300d901020284081183d40d596070402e24200064204140d5002d8146180080c0c0603540c48080c5050310500c400400069980704100001c44211154400c0812814003181f0b01040080c00284c6101c4514204008020200000c20480e03a0024640c8404241d6441c04c261506000b002071076807207486d11034940303401d040044000e07550301180503485460b00c5000407500402141806000e019041c0c0c0405110160380741c81240c8085c2601c0e070301a9010f98641308811641e98890f0703180501481c50b000e405070b2103415a2844102614a81500300d0304503c0c01c0001414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350612068 1250 350610818 350610829
    0x60d032c031002040915050109050f0f0d0308100b0c071401050c070f06030c1704060b010c140a0b0703020a080105011115190501050907140913090f140f060c1602 71
    0x100c02c070a80180e035030781080300c40001c44011440311101e09500c0c41050046036084a02d400503a0000c40341c05c8048405003001a121120a00d10107810a01088000c0c0800d508031110314040c0710711080c650180c0da00e61814801d14050700c1500d030b500d40c1c0001e40030400c01528091203259050185402e9181444490ba03503440c20382c2030b9106840b4441440c804205640c0c3c5441110354a603a6840d0140000b00d18801808030210702920250100e96034100604407a805100144c040c158000300725207519560507180382e203a1600301003d60380c4294100020b24101c3c4a40f081f12901100c07501c5012070f0780d00741401103d45107e0105109901c2c41410520700c0f400d5152000a44501c1110121003610a0a60180c3c015140c06901c402d0003140c0782402d0001d6250424070f9094003090b4042c41d9074a0f101c60783d000840b220014841c1408003460000440140000070701c02c21003003802140001c22600b50300402d5aa104400e490101c40d0340c11107008034046c146001c0040c80340d080031a2809203145041e4000a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350613318 1250 350612068 350612083
    0x70606120b0a1b050d0209010903240c0503061c02010908010e0f1e03030c0f0d0203040f05011508070512071a0406090f0311040f0e03031608060d032c03 67
    0x40e041907a80080040ba446940604100411511940c18614820240280040c040e0104014400d42c0120b0710380c0341c50740f03d140703180015500b24a00495050345000c25032428800914441c00e560b0811078801d20ba58010302c2202c2c0109000341920b03060021650a40c004078030f80d04800c031304100c0b140703070b000030319140c24003441a140c079115001c5c200e0b0901d40b20045143c14182c00d8007040958401401140480f004400d0340d81c080c8098144a0340c0c2d0000d50004009803040502e07010340325102000344001d001d0400900784146200d03500800003101040750f00b08051016201d02021580b054070184814144840349507030350001b03801107030b0704107071240c1150070350b05e142c0213142e1102100480c08002c099480100d1000410700d15486600f110f056031070303001c1400c0c0e605098034010b5451b0300d48152030020320381c0446007500c40e5900303686d20b03820010800c000c80007034401518002a0781c0e030040364452401d610903524003a80758840c0303070542a0700e034540764803003aa001c0d480985003c226404404c5d628280b209a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350614568 1250 350613318 350613323
    0xc060a03020904060f05010206070f1412091005010506090d0609060218090f09060610020a1202010c0e0603100e040c120c032001120209030a08071a090d0c020607060612 74
    0x507840700b8050302804100da0040e8821030790641300e04400c01503030341c0214400782c000849180980d0801c0100100350b0390152000500a4a840002a15000d9a2b030082c00c560050000c0010740342580254045141681c07020b0046070b6001f0410000e4240c20719040820098151081c80c01007800d144a8994000301e070040d403880460302d1440b0f2044030031445d0168040e540640da40403120403604164100c0c0355195801800607004406e8043c520103501e0081149041c40c652044c03501c1540306550340d00034003a254255010340850544200c8130449d01c0c1c601c0c16a8440c00a210314031a4440c90700501c41000f04020b04181c0d0852443c074000310b06600c15100c4850068083d41101c518070740341d840e040c0704008011204001c40031a1b14503a41c100d80c1c5c00756010f211007551905c0940c41c1c0380b03190002820011f10550003480031a00041c0d6904000030140d1001101042c207210502039560100042e84548042607900c0c0000d4940282400515100001d810203c1c018100010101c0e250441300ba141440356400307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350615818 1250 350614568 350614571
    0x105090a050a300b130804090c320d0f0b060c1b0d0209160519030b030d02010c0801180212010314061501090302220204060522030309090e0c060a03 65
    0x42c4054014070b14038034200d0708440f1070300b40c0380c94070140c65620980034050309025030f450040e145441071001381c1d020b4902400d1140b07810001d41000180c05401e540c4100c001c08440c03071440060703514810501c1ca5448030403200b030140c11315010341001540300410208468549084c0d030b55880100c01e80312140038200000e0007000400c140f0104010b030040100213102518402c02f1144550340c016240c0d0385140c0c0c2c225890389420580f500f541002622a4041c03201719030b2060040f45201d00e00070380d141d0000001c000c0203400313649074000d49000c100e00340c0e20304140c1c904c00700c2e10ba00e004008030720580c0b03050882e080c401d10380141081c0f006075260106840c2a4819a011801e240501c4144e01003400111307007001c030344100028520440c000283c40720030725100191090003044421883d59441c0c0c20005810200345200310369071500d41e1006031a40d0402d0041c104003259441544c0e00f403004000319101680c0d05070f290120f103203240088240207400450441070460041d45111819522000f0181c00400030b47d4a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350617068 1250 350615818 350615849
    0x6030c0f0906050f010305060102010b040c090513050405070608040507090501030b0f0f061507020307030524010b12160e030a03032004181d030a02030301140603150105090a050a 78
    0x14100388845908041002407a00100304160b030f80304040300300125403e00700419540e81e0440141c0c01407000160780d0b40c12500300540312172801d900481b0441502c40485011a4101300f41150204455084900134a25445604140400f5000c3d449140e48a031007582200c40342600e501c0d40d0810f0b00e07401c0c0c0c4112131900d5204144030310b944c90128500d520204d20000a6914641480001c1c0302c062002c403140042040000d000e0150748042c040c24002e0741d0007a0031100c054120362451482c5919a01042444000a000101d5201761a500321140542c045103c0c40040e00e48071a180400ca00303c52402d0280000121410301c9520700340042c0da60300d8040d45002500780c1c1841c0e003400342d03101501c0030b050310341008100c2449417503842e0b42150b80341c009804001528003180381107080da11742d8010007880f00c6e20021a0001406500100841c1a2901506003180741a480300c24401c10b404250340c04003014900c0025100b070744d44070381e004d000240f900900b035005040d620f40104101810a800208a10020340c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350618318 1250 350617068 350617079
    0x307050d030506120109020f3003030103021c0b070e210106030311030a05030c090312040b0c16060f030e1903110d0f1205041104020c01020714070503100e010f06030c 73
    0x24072201342c0303d403070000340542401079000406c1480d410070641c1c031400028040706952003041d606417040c0301400c0341c0c4164001c0e100c042c075603480d0030034030003248681c2c0f030f2091034a5044040781d035414410f0781c0603544034150740b6840410380b0030401041400b50010001e64001148041c010f1074610103918550000071580e095090042c10b0040711810100303d0f6104002e60504660b00c1000c07280d101c601c2c1205c0b5903daa110400113405d190321801c4041c1500808500880d01c0c03407260008100030a01300c0126a9900702103031a1980081e8a845502d000c12544403110f00494002c0e0000300b0302840ba0800e5806044010070136410040030b0010030f0b07002071550030040400f10380c10030445415101e80c2c1016681384845400051154441403455000030343c9a1000c24200421031030211a076104c018010b544804c04010300170b00030b42040d03c050320035005a821102000e2804550762060300c074040c000d4160013075029141c0c03014040300034000425641c1d440641805090ad48643c2000e940320301c10940c002417409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350619568 1250 350618318 350618329
    0xf071e03020f030a0f030f020706050906150d122627030f04050d0501060308031e10080c120a0f0f030f050a02150705090a0306051806090304090e0307050d030506 71
    0xc01c50b2240603403040010320302c0f581e00402c00500001852402280b45190540640042e01845400a04560902060201003100464280c0c4500340412205400e090307074008200ca002030441f400341c480380000c140031000303070b04c9900001d8004006840000132145504040300c0304c034904650045d00000307242d00b40c1060240044417032504950440c020343c1082c029065800c494400c074465140304100c81d94810041060a4000400940c4c201c070380a6100d10f0010000540c4079901200800a10394010028800d20109a2004252090300008210440d8213030284800c0307013803040d61019607109940c40000010220011514007a100e214414000c04042c03030017a11100c1d440e6680c505100062100c03511840e0300251581b4080300034800581640c946400c155403a100e29600f9170740019a407203001c400d00c00300f600010f0190401c103020000e1903141c540e600d5103034401512021600d400810042188034000e4112000c0c00000e1000d503480c2c0300b9036507100c2d850841d01d041d00c6000729460b0f408200581c03408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350620818 1250 350619568 350619583
    0xd0b0403050a260c1b0f0606010e031603060e07231809060c0a030e0d0e09090d05040b0307090b031806010f0803071704090f05010510180603020f071e0302 68
    0x111034120540404903010755503c0d01c4001e240b40003008000c600000c501041045d100714510000007511039100e00380000d41e445102c203e9110340454812440c540d0103041c006012015902e04141c11301040f403c41d40c8034070190402c4002028148211035010a2500c000c0058480311b039250079804c520740c05c41005000684146054518000b0355090411200100220b0319580c00560345950581d03881c3da402003580100300442d4030030118400c038144d444041d07800031440341002070221081000ca0b42c1740c141c0140d8801061000200080060108115000d44d00740911b401003007034284055010740310101c1d18030300c0e041200d2060034007205800c0d04003102000d1080754050004040c440c2d080506200f1043d40d68442d01d0b20003003d2540303040032807407004000c81c03e550140208801c20b1009c0d80c002130340e06001e02000c0c003c03584103490b08190341000342c0c02100308881440b03001c040516040d240c04410380081d04143d00d544072003d01040100300103403c1c01445a5071210180c80f01a01500c00e0070002c1c0342102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350622068 1250 350620818 350620847
    0x19030b130504020d2405010e0402012a0201140d183503060103090506090706031406010e09090a06060f14030d0905040b03150103080a0f0e01080103020f0d0b0403050a 73
    0x9008240300140c0c0b034486184c601c45400100305440360186940022900c07182e8016a1040b0745064004180c0035404480c0c00e02a41c000d0b60b0740780f8055840f52050501d0407000e000c003191a1292402d42c801540200150b1031000b405002d610f04107240204003406584d003420040340c2c0c1e00002c2202c28200142e07480d1217012036020010a681d10300700c0e58210301410304802203d0800754008070016500c0d80c840d40254013100d90000944007141880403803c2c0d070740c0030940908404641400c01a400110700c407800c441c41200305945201030181c00720b040c450010f1014205c0b5146024010441e0080b0b100c07405180300904000c540f80e00001d14049041c2528081514020b110303400c24810782e1907080c0c0c00003565007503840898001a1440f0014006032030725440c80c0143c2d14003007841d000001030100d0301c0040c0525640c192604144401c0241040b2010702c081f841c800d000c5071042c801031000d0f04020400351006d50015000c0050084c0c91f0720703400c000d00000c440440010741d0001d80070442650244919100c1c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350623318 1250 350622068 350622071
    0x121a0901020a021002040b2502030a050f07050f0904020415080109050a0c060305060d060f06090e01020415020a080307210e06042009130314040611070509090607030e0319030b13 78
    0x1f42001c41e5000c4a00c52081d0784108034504100d40403200c0007444000c3e0b02541e0081c00ca40120259141154a070000034030320340030a00800400242c01e0500f14440040c0e100c00800042141d907d0b5030800c4000e090140c14440707165102040401da140c000d204152441e80113000a09000320f03185499a09001a0342060b0105400d240c1030101c1526240d0230700000310390111012807081429155035004044036403040c0e2200c1e040c5440c0d00d160520642c000c01c250399a071280d0a007554980802680c0d03a0301c40d04001050307882c1c100300040409101c3c0c00084060805211103d002145030b0046074150750030802e102c070250304000107001c20000c0341e440b5070342105030a01e02007100500440020340b28010050000d20441c40200044003014418ac28884565013010b00c1d03d0b886a0326000b004058904c15042081d06204205c0c021400340303460305a042c4601d40b00710040455a941e207404402900c520340c150342003403009000c001490110504081c0c8204d140c1d55000940095200c100304540c00c4104104807840d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350624568 1250 350623318 350623327
    0x41d040209070e060d0b04150605130603090215090d0f0615150504090510030c080a0c470408010c26010b0a0c0f1104050a050f01121a0901020a021002 66
    0x10b4513003a040e9004010b01c000001040158003000c24050445081525840c0b04010004140aa00000981002c50300c090000d88042d88902e02501101e480c90703400f0313500c84241840c0c03400301d2805000030444800d0181003020383d00345a41d9408181c4803102e41c1160459107944100100390720300a8520700620018494031014500c1d50340c050042d204030f005440c00c00c3e0302c490000d015114180d030180d009617031180d8440e40c2c1680e907a8885072a0354603118100c2d0403858654001440340c079240440c04500d81960500c50254034100c0a101644901000250002a0f2a01c0c1591001070b21000751004000c0d01e0004200c0c0345a078800280b4055018104004803605480300043d01da00000aaa041d1020301c02099590b45040c2010342c0c0c2024800c0d0010020b03c0e80020303210820100850f5004040401d41d018445922014001d2043d514101c40302c25407905e14030010000b030261601e4141d000c0e0b00540e5407807503030803418801c3c60131403608880b140102e80d0001500c0310b61030340c1044a240c44080a42d03085042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350625818 1250 350624568 350624597
    0xe1f030f0303090521030c0c0705090103060902090c0a090e060f030105190c02240702070810020d0b010e09040215070f050d020c15030c03040201031107030819060609050405040305041d04020907 85
    0x5034000506030040464000c241c8d015800c104020740406450001c1c0f1001e49580c0d00e250580c041c01e0000000c0b8002c42030302020603224480e1a044d6208500c00351202ca06a40c1080e44c2c04902203c014650759101460116190302c0b91020300c01d01d40141001c2c244146014020300c100d1041e65034102c00c000c11580207032001c1c110030410071a24031514a00c010003800381d49409804928020b0b2a80007501580a183da03503d1590080ea40100150b105562090018201d594010344035091460034183e001065103002400605d020302c0d50301414003040a00c10b04006158544803107060901e40200c400c1d5120503840c05070130790108490511054210b0340703c50000481c1e407040105010190011002c2c00021004c9011a03010350440001000c03403000c1d0b56100e240b50b040090480b8410340f03d60010304e01c4030b402013210b24105c0c0540b83c2a46d0060b00c8100740540b03414140402000000d20075030821009000104004e01c8c0242a08c281d02d881d0641c03a161400d2134010046180d41c06004d480500015400c44c004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350627068 1250 350625818 350625883
    0x307030803040803040c050630010b0a111e07260d081b030910060503071505071704150206070201051311030109120203070c0509010e1f030f03030905 66
    0x7070043c1d00c20300c016180c0d11140703848603612296030082d80e8460300c04519000b64000c140030161760081c180310b640b52078501004003108148c9017030042c03002c0e0820802007544500e0191960900c81804c42080342c020b40d41c03c40705c0002240002c2c001c202c5c640c004900800100000e400c41100203248031201d160607904920185a5074035005082d582405500d0000a41c40f074040e0402c2e40740c004103890075580d6441c189010782d494090f507411101e0f41c249810b40205060030001030314000e5032000c0310300d00b000c101d0b000b0007998240c0203100100c883c40380d09420600c4005142d0080d1008003000302c00902c4070002c0080190800b6002001c01c411681b400080141400d03041281301101904601c0c0385d20001100000301c3e02410301c1c1c03180135004c81c040b441001811940007004007105800b4112600364640c0b10001c00c240c401e428451051a0a60750f4003007645100c01d84070400e0301640200f4128a066600d564151781c02d00c0c07024041d40882e9540d01e0120034400248543c0008003a1003140f402402c000d60a000d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350628318 1250 350627068 350627071
    0xb0a090501120b040f0f06091202150a021c0e0604020108130c03030e040f061410030509031e0c060901050a1802100f020c09010b04060f050c030414010c020d110f0307030803 76
    0x3803e510b0031002140502c0842e0080c507041c990844030703141d220701440c1800005896242d000b21102d0120f1101c4620151010420507070464500c000c01200f9160180504069084021088005820707621070b1000c00c46140f26007007100c240d600207001e0915007030001502101e401440340e08001e28554900e0000390000c2411400e481e03142c00e1502c07841c0b001d84081401070910301400c120040c54004082000f9034011036462550008607040e803c1c0e0b410031541201615015110001581d109200401800e81e540c100d81c0381c4111003041d69810f000e00d14a0961a00c5030640d680307901c596558080c000300200c0c0c0d0246c06144074080080b42000f1281d9400f040e0340504410010f020855000110ba003000e1003031041e1010003c1c001e00c00c460550f1251038a1003158030a114250101c2d80f09001d41c4202c2d805941074401d400f90220103142098640640980c3c2071f070022100c9410007441070701446c0169195042007074194003901c941113000c4808028050b030044814a0180309500c0341d10104009103403d412203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350629568 1250 350628318 350628323
    0x1217040f12230a0e04091a180304032003031207030c14070605100902120915011203111002030c0306190f05060c0f060108031314010c06021b010f0b0a09050112 70
    0x90b80e441c05020400c451140f802c40080b0b43c09401e0000c44003e00011007004001f86054031754066154880c154003441c07640804241d2034090f0014001000461041c3d0b00b400204070504440014080213000040d0959111161207030941102030280322039140d0501c91042c239030342c15040c108405203580c04043c146003d47c00c001441152980000360ba01951000034000800441c4825521002c1203051101075490031a01c841892291940c210514200300990a040310211541c1c04000c604c1d40d282101d03030f48001d071840d01452140849000540d40e442c802144038003889141c250326810100200444008078454440c50302c003084400703000e030b40c55003565002203410488045942d06110850581410180005070340640900c1000080c12080407004000e4005509050f05080c0c0d00d84540200304008aa4040c3c00100c0040c0d030540014071f1907005102411200c0034031030300e42090002c210309403140c00c0e440741070503900c1d909a0120707801c2c94144000603010f8580b0600044d0f04040d15401c0840e00340303902 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350630818 1250 350629568 350629637
    0x506011e051806030708010f090303050a05220602070f11010f020a050d0309061d0a0309170606090a09020a080706030e120f160b0a02180603131217040f12 68
    0x483c5941d601000707500010b15841c0001c0c07041c0d806c903071744100052040c0d084c1500441c3c101400225212040c0c400c1c1e070f2240d8111a9100380c10502416a40310400340c0343c8046400716401c001c050045100c8201d40c030782c5944100c0400d050521b01c1c200060030443e004000405561241c1c404600040340072030a64a4030f0020b180019400d040360420b4800780011800640c0015021681c03003035140404110580498001e03220050296564400d18081000400ca019035039003180300424550b1608240711a0411401d80011a15030301c581c00141401c0c02607071100d0411b6015071403c01c82d680c2c00d4003510441200c0301002c7d04d1444148501d14100340305440c0d42a001200000d01858841041d210354a81c058000c22400344510344043d422000354000c8142400030325803504022094038040044034403604044800034400c00c150360b100902040040261000e02103004031118500c00034995070f61059001d00031210000c0740f2814100f011841d03c409500810000044650b07101c0091003d2000b0009440d0b030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350632068 1250 350630818 350630821
    0x50a0207110d0c062a060203010e060a08030403021909050a050f061e090a2a0201151d0c0d11090f01170c0307020312011701060b0a17040218040506011e0518 69
    0x41810349168481410b005000d07620031009103c140d0b1f002e94141e81d01e08000c4980d030340f40d003c20090222410311540c07007541d008000c14001403e10003490802e0213040c0c20b03401099900c0d80d1000c0705551044504a071481e59480410505112460360203400c45419100100e030050440800b0084007044410280500072180c04903650300f04036449074a41032035040f5491000c4503c1e9802240001d510024a001507003007208502e4100d42008003002250030040c410602091100709440e441718006007079584041c3c080c009008006824029071030349402e54072003280e41d008003c04101f200b40e4610245410046222620100361288244a40e040f20703000e00c102e0f071a40c0c0c4285049145124840c00700f16107414140c0005a50702015801c074146a05600080c40841d80340d240b80e1000740100c01c0107000242c00d4801d200203581c0d080b50615040741c0081e080c3c07100002404040c01808205840131903a90f8810340041080021446018114040501d5181e003110701c1d010000e131000e4503002c081c40b581c081e10740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350633318 1250 350632068 350632097
    0x1c05210901110c03010c0903111e1306030b150406080c0303040b1b0a12080a050c030c131509180203130204050a150602060a1104030c12020d06050a0207110d0c06 71
    0x4103510600f080200240300b415800300e4020198059032204444404185503400c4961801080d02c481da0130119104400c41c2900701c0c00c1000c007100841d03000c01c00c030b56903100c0030002c100e10f10340951050440700510303d59a54900d05020440c1c00c0f82d40440781540005040f9a040d036000f1040324112809417001d1525200240b256080316910202420803c1c429a410403040111500140310f0f1080d690322228040e50301c184490f0705561003103481803500c039010400588915900b0000e00071500407611500c0c074068542d01e802e880d400c0c2080364840800c01408041000481c84100f940140200240a6045041608a8031550a00e8890092241d501c0d05d00044601f2820740c132180c5800b040e0040503800340c5c2e45210103174440f48255492108a81401018211411808201c0d0100c0354440301d18809189048403030714050882940490740b1038903403402c0c240071541d54005c2600440d40d40c00d0040c1d4810140c60564506031a50310708a00880440955a020843c2004d511044a85604126462003a00d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350634568 1250 350633318 350633323
    0x7080306090c130e0105040f050601020618010e1911030a0f260a0f03060f030206091002031603020c0301050a090803060d0602210604050609010b0d0b01020c1c0521090111 75
    0x4a480f421a10440d410000e845000702d40d0b15412030f9010348080058400403215503095401c2241c00c24050703400040414601104d002d807500a20340000000103542031042102400d0582540c00e01404425014040040c483e1001080c40c03050f43c210004c0414031600c0c1d4404a42c03c200280c0a803250111500131540720428140d5029803540c1c028039103a039401910701c09800019000200707400603103010404264a03183c1400710082e43d4000b082541089016400c00c0060403002c2d114204601050000d1041c1848880c0e080c0c444034800e4000d1b2461142442c2450300711480240624000c0d400c2c242e9442c042582a0b0807070303400403000d55044008611504200c1c029220350b4820540000c1d84400d400000840d0090705401a01c0c1103d080c440e0380c440d00f0402003091340c2806040c03d450710810111100206903800010400810b005440b144801a8009048100c01040c1d0b03400c810300c440141d50420406224503091001e0741c03406c0729120a6a029125100c1c0511010241800302c2d88021030f5012204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350635818 1250 350634568 350634577
    0x1e090d0c0201030b0603010602061509190b060405120f060a020a050a0e190909140a0812040501200a0e0103090804180f060b0c06070309081818040516090207080306090c 74
    0x1800071940c07548d40349402917640e0003c5803040b20b2003521501106032854410016030161309989245101d07108542c1d040300c005c0002201803680302c841004005010346031954401c05404000b006000041c005102c8941004001441041d041e4030420282d858560000240c84403082d980c601046001042c0010940d03108c0c0d41d0b82d00c07208180d826a00050091000c1d003010002501c516880c0240040300c040140e07076090703004e01c0102030030414000f029071803038800392007640030380142d0000c110b040e0b402e28051814000612140e102460009182c503da5420080d000140c130700130300c0c040043c07404d15102c2441c1c0d40520b00030340701c414030b00074103915900c605900609485030703420f0402c0003902e50307900e0f83d40d400da440403002c0361842c02006c0008480b540248a20308030690000030040c949a2215903840345080c584080e0b50784803042d40000c1201c0b1201d00c070315030300c02c40c4590000c12006c002c900d00c0204040c1035500c0040040c0c010003041c00000c80c4a41039a401403400c1c4e400c400a601c1d01d07480c2d03103070f14000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350637068 1250 350635818 350635841
    0x201050c011b020c010206060d0b091207050114010e09060105090903040e090a11030d08010909080708130e01141305090109150507090509040f0f0503160b1e090d0c020103 75
    0x80c004a01e103145107a203441080c0030507603002c444414044c0c03401680c0b910130448041c0d9025034644070010210f6200c0c604d440c0c0c04500f40c41a2113401c007281080c000c0b1500300c0c1e81e0917a20760390f60307005800c40444080341c907902401c00805915158509294000c0e51140c0c14050640944200d0020030503440c0100b041c1d90180c400010b2104940c0b81c415016950752a00440566010318950030003e02800d010520016075981c540d40e0184d542e007046907420150400210481e855030302000900e000c43d1018007d410100740d000e070480700252a100b56900091010b801816000c04241d0504016503261012600f040800c00705c0843e5541c0d46014603401441c3d0f406000e4034440a2200c121091a213a0703010611510300c13600c0346046a034503103040c808040d81c200d40041040c1c0d840940302002c84d074140400401184110201c0b8038000d41c1500300701c010030524404950185124080c041d64001d031007580718180900c5815009d40f440c0c401c01c0160780da64807040d107005005030f0740098000d6920a810443c2c0c9003a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350638318 1250 350637068 350637071
    0x15190c1a0402031e070f030b060a06090e04060e030405090a0e010509010c0e130615080a0c050a170406110c01021e0a090608070504030204050708090606150306040b0105070c0b0720030d0c0201050c01 87
    0x2030b940d09203101448c00c1121b01600c140c4440401041450003041d51400307864501d150902070784d403255200c80007000580b0b10500240300500c0000b9003542c41001c1c0901c50b2810364008136110808500660a607400030341142d200784d050800110040d03a2000b00c000e1404411103152a64641d0580d0748001000560850106581f559510440c2d45401ca101107002c0c1c1d1050404000c41c12000f582200c55006411500c00010380700e03032410000744040c62540381c00602845000494050b020203544840d07003e60b124140c40d94000ca45021107103507140d0440100e045240d00c00e490b001d654000180200b200740125810b1081c071001007074205218030b0a4501940c2d010707004000340d040296015001c2141140e24504504c10310300021602e00f48030b140c19540e060740440e21801d54440780100006803854411407410840203101900c08103010502240083c08640201030790b451140c1400c400c070014041c2e1158038800026522003107070302c0000b00c0c0c00307082100b8900b282400a1610048416105100320040d107507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350639568 1250 350638318 350638349
    0x30b100c02041b05091e0108010506071109041202070503010603110d1e030206040b011e090c0203090406030602090f01090803091507080c0705030c03150615190c1a0402031e07 77
    0x80c1c1c004d0010f0294100071076001c0c0020700001141414030b90040075480c0020031813001005581800b1003d40290340c41b401103d03c4513021107001c18402c0a013144c0a40b812844100304061640d0148a42406004164000d1000300d003907440e26550f0349500c80395540101415103100e401d02184001c1c1d48400385180104202030902c5080c000e50b01c800a407000c3d140006424000681604005031740140314400d44114040c007031500e007400005161543d50f18007940000c120441d895901d5204400295210300030060300c070300f6072001780030b07190301b660822130f0510408180c280f25007100003040c0c40580c90115001032505075203403000010380c0220080200100700201d5030520514010640805030741c02a0200c0d811703040d0403010180d0340d1300d040c003000b6038442001011404a04060740314910907940452001c0c03a148a656070b0147d51180800d4407000242646245d0003000000081d401d521070032015040b00c01e05068001035107854101c08050024412880b903169507000500200006001000a14002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 350640818 1250 350639568 350639621
    0x908030f01030c0e0411040e120c030705060f190c02030904110c0d1d12120304030504060f0e01080c16120e09090102030405070501050703021c050a0e01030b100c0204 73
    0xa294080c00115160070500d0b07804036404c00d607900054480ca81101855148a01800510000b010415181e1819000342d80400c412855400000c00c1e14100700d81c000d60740e4000c01d08011381005006411400450707411404e00c652000c0d00e85681415080462000078007400d280e10591a61107160240d5070045c1c10250480300e1105554090034012440380191854882038480449840c030485d002c80a41c0c0d01c0a251900d05402d0019413000c888031074108407001c62641e0303031900c0c01c1d40d00103c42c2100000c0c4002814001c8990001c0c2c4071000b014241008132101c120310001030041e5200600358640340c940800e02c942e034150400803056409410140e80700300c84d024420003e100512011200b40101d4441c030104010440503c21030784100d0b04280071b00551802c0600460b03840d4442c410690452060a4042480c0300340d4044928150f5503e480315903139640c404101820001060580c0d905040c5828814040e0b40c40b0011806d82a20091400360707903010702840050002e140302001341e0520044035440155 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 350642068 1250 350640818 350640841
    0x150324011e150f0f17150103020d182102030307050307030f1e200906030612030a030c120c0e0603190608010f0e0607090603050a020405030d0f0f05040b0304020d020301090803 77
    0x80003500c66441d0940401c0e0b00100369003000281c0400e071142c900c2d6170009140140c07207001002407040140b40c050302d41003070454020251b0b000200301150b0305000b003016070100045280c0000b40c1071017a400e1400c1804131b032940070307480703000003030446040c45000800540c441d03120307600c10301aa040e00f0004000003580c0300c2444400004640341c4002c800e203400e41c030291070f220906041c80c9020080c1c40551a080c1e9480c24071190383c0000d840c05800c140c070804d0300c0035810000e0000e0300311075036a82d40000b13900d8150f01009144081071550200d0b11813914111000e583c1c0e1103403c210f2a030300300360f60b0240d684c2c503030300034081550b1407130240111918900701e004100440103403c00300142d600000c06018414941c0f141d41e8031034000345c0d10180818071004082040d18002d0700187c1d480b4036004001414256921701207401d100c4041e02e00c40009071009000ea4180741c20621041c00000146170041c20241800ca50510034070001d840070b0f208080e490161001c540d0250003544909500218460301c030300b0410412a07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 350643318 1250 350642068 350642087
    0x20a0b0a110d1a01030209030705041a0915030105060f0d0f08130602152508060f060a031b4b050406030b01050a1704050114150324011e15 61
    0x6400f40241c400f2000f290322174001c6c1d54203d04001c010785801c0b4908800c110041074480b0900c080c45d9084a9003034030b55615881414415450a07885094208583c8201802c48000811807403246000820954494892420503408940d1000b07001d03107004824100b15445004250f04003180c035005090105603154081043d1828041004100c4c2880d10b0f038042e15604080e00205402841d80c04443e05010700d880344616139080079028021418a0030241d01048040d4000414140800d880300b15120455030b540581d801c3c1c640840c80c00c10183c840e01c1c10310ac0810030f051180d00c000031903e500484048906045180221000440c0003d00c010001c040548150007910170b075070101c2e241c0329104040394000c1d01100d0f070200c03085c0c0c0d443d0f200c448004030440420b41c0182082e91503659802d145101079034111403040c0113090b00081a0403000e003010405240c81d8400b502c003c10b81003011105110702c0c0a94510030306443c001200d0502000540b9408109649940d2250740d0008440e845041e810340c2012051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 350644568 1250 350643318 350643341
    0x90a051e0601050a0b1c020405040f0203070e09040b072607030c080c0a050a140d050a1d070b1b0313030809120c0a150e0303040906051c03020a0b0a110d 67
    0x100e84030b0780c0e200308106501e0303854461154800c004002c03007211040d1490b1603120b40d4005c2d00700142455204e4010408440d08400141c40711640081804a0f1035041070000c54200f400305d560207040d151660311034103a01b60140044050003085403200242010701c1124850348251101d0040c1a031a0110004010b4064420300401088490b0003240000c00c404003222000c001640300d8602c1e0442440044402c0d14003981503c0100b4401c1c00b0f00b10400419001e464004e914854020501e040d50303142100700d00350109010700d0305034000c0404004544a075000d9441800c0341024089005400c0780984d401c0d44a4001c0580c00c1b882c14100110401003a00054004420155a4003800c6c18000c01d0803a45c4040c03085030075901107d4003a003089409240d60041c03042032024500901803c0042010900d907400c20782000c00711640307442042c0401d08060b65407079038070301c095441c0c10500255614042d407a12001070b40500120150000038940c1c981070380044900c03401c00880113540e40400c03e029402400c100014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 350645818 1250 350644568 350644573
    0xf05070806010f0c02010f11030d0e0c03070305100f090c03140c06121504110c07170d080106080a0b0a09051806060319110316080d0f090905090a051e 66
    0x401e400e940b0800041d88800207030303150740103400c129800640d03441d180034980d2010480340740314034030848a06202800400c45095004990070f0340805440b424030f450707060758600942c059041000800d60014107600e0083c905a40004c8940545a046024040721140034281c00300c100ba0020811142230403040c08a2165029100e55482c01410008140304107a11380c1d10600500380401c9246035254031055405000910000d40749641c440c1e40c424607004402c0c60b10040c2c02a42003088503040d0045040c45c1c54000101800c00003003009805030041006001d043c08000314180007801041d600d500001901c00c0040114040d1592030100f03a001d84411600205e50825000c110000f0805c005010703401614020b000d000e802c14140c50481c024070041d4800d65000710041e800b2401c6031004d001a408a0a81400c1202d02c1c3c0c0c2080b807071501c2c040210380c90307004200d4290305001031030341c0c8101c2c0c080540341c00c0341012415407508858585806081000903145010310344e0001c0702c1e5103d801f00341e030851428506 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 350647068 1250 350645818 350645821
    0x6040905071e0b0f04030303020c0f010612021f0912084e0106120b190e011a09040c0224090f120a0e0111060a050f0f130201120f0f050708 61
    0x1035401401001e10b1320034881000c0c84103100080c017980281c6003201d80c00080b03c024814012400303003520010341c010035401321021040006c2d0f04001d50a107500d00031002d002d2040400b40b2400801200c0984200b414010201e0341003810894440101e5100f2118201c00ca03c40307545191007050b0b80030480c1486804100c0c84190501e81c090314124041c04a2001c0480c401c0c60fa29040080c0c400903c440c3c0072002c1e282d80c50719448065a07500c010080507000100510380b545041035031540c81c00c403068000f031021140c0440c00c1045020004100c40541c0c405443c0420a0307882c000007a0b00c0c009409a1800c402e4650f6581c031140c03400111180c5100703030701d064220f81440100050385503c1d8030b00240d03000b403440e80c1044801c4071140a07031440c0c203051a040c5060104c00c803a0f1400582844015101407021079103402c00d05c01c409101c038460f540c1200e400700051225080c031100740b9440c0b00703280340300030705100400e00d00b151860600c2e4819442c1c0f912485c424482d11480a5401c0b00070031080702e2110100e180c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 350648318 1250 350647068 350647079
    0x91d010902090703020a05040504060b2a060c1b0f0a030318170702190b070b01060809030319020d0c051210030f0f0602070807050a0203010b151206040905071e 70
    0x44140d03194000e04004036940752002c04402943c00200300205002041100040ca51201c1c0b1aa200a00c11059041e845a0101e810318481090501d001c2c2d610049000c070805401c0e2021803003d070802d101d503122a42d502c0e03504041d05280318048001c1c4803140180f14640c11407080205024040e81e100780ea04018444038500c1e10300d8000d182d09400b80c55400d41c1c104000501301d03014014050a80010045201c4001042010b1038403015a0000d00d021040441e1030410084e03007004560142c01141000d808078903220070155900d010040c80e840c2c10840c10700200c22402c400b641203070340499140c0801c7c0600300c404100500213910a40038802c1c000400400079030b41280c0324801e00140ca40c002a1401c03100007548540700d40801100080d603030150308110000004072007070018188140301d900540081c6050b401010300b10340350011894002c600ca968004140d220310011601c922020400c0c440d6a5160440461700809820754014014170406502040c02503203640074040e1820143c17100c411094460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 350649568 1250 350648318 350648321
    0xb03100501080304090209030102070f051f0c050d150905010b07261c020c010c1e0e010e060a02010b12060f010f080312092a010314060612070507050304091d01 70
    0x2441002d50640080c0710a1100c1a0300340c0050552160080001d0305001058484083c20001e40c030b401c40c1c03036502482030135110104070003c449203800740a000b002800303401c90000c0c1282c03040f1003080b000c590b5901000035400301a50342d81c40281200020420880d030b1a0070300102a035010030426918024080906100c55a05d681c14880200c03e190b540307401c116402d47c4204070011800d1040c00340030340a01c0300403a01d180c01d2190300889616a40c0e482c1d04001c00355080d559000092654008010208540c1140303a600140801003044056440f20303656801d192049004102d4001c103140d000741c42e034200054518001406a00400c0300703030100241a40c0c1d410744811041c84911610045030814000c0c41c2c0700c2e20003039410b694042040420760380c10000211141203400a07034098031a495603049201d0360996414402e181420303190b03514640c400c0c00d01e200059003034040c003c8056650695100051000f034032410075030b495943c0c420110398076103071180707640720180100c81d00d101d6010b140e641902d0740c0e68805 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 350650818 1250 350649568 350649571
    0x120c05120c0c032103040f12090501030e0f07032006040e1e040c03061508100609050106091d040503070819030b0f01050d0b040b0604170606010801080d0c02010c0b07030b031005 78
    0x5404c403200041180003034400d450304018000d44100d08200480710109004d4200d5841d900402c1d5103e510030b500740000074040790f2000300c06034200e03031042114404100d000115401134a8104100c402071068a000360909449010b413400e820040102c1d00240007407001c400d2030b000364980f4001c141d402031941030031003040d50103d50140084410641c2040440c21680c00441c00c2c0841881c02c441c2a9102c603600c51408140d641c118070701c165916001c1110000c28483c05000d4422841d15200441c9010002490710455107003c415008441d0b0216003080070800c21203001a52104038036444603503040d410003140100d40b5410f0042414500300384001c1c40d20f91510520010142c40786820514a24504030042c44002070182e001560350881e948a40c1d502c0002e04000d0100c00945c100c102c4407404250308006000e46903030f0600c8144c03001441901400324007400e200d41c0c01d141951a060b524001210a01c08285000c1c1c18240c41c40b040c012500d50503041100b980005030300700c1d04081000c0c02c404d03044400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 350652068 1250 350650818 350650843
    0xf47130b0c0601090c0e1e04060b1920010603150f1e020306010306050a0b1e030114100509040203100305010515060a140405040e1e0109020d120c05120c0c03 69
    0x882c00611149036a42d02407002448640b03094000302d911003021540d00e4284400c5828240740c0003c4d01c107550b280c24000c030000340c100c032000241444542b400004000303102c0d0004174188100c0045003074205081d07001020b0f61850820090044aa0368100700e4494140041021181410240c1d030081c0c4c000280141600000e00c820b0810240340700740350440003900041c0c00d00381059201c0d907000901d07030340c0d0441003809000043d5007240d80d01c045c5212071501c11011403c001200b00184010001c80c0d284d204002c03044481a64404032034480e140040741c0512800c00c0d040d62261012041c840d50015660150050780c2c0314a00030000707910ba0551440d45159100b4103264030103400c00010f070065200703403804440c52010765003107402c04d9141c9000600b030721514601030515a0100e060307a81000caa040bca54003800c001c90007044601c072150080707880c81e0090b50000e8180c02203003a440c40c100b88164120a01960080180e40e03154904c04481089075200c0c80000e0014030a803040640c40f4a00850201a41e40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 350653318 1250 350652068 350652073
    0x1b0203040e2205100203072604080f0d020d09062f09040f020c060f13050304060f1b1407092705010902060c0106060206010f47130b0c 59
    0x60301c805142d120110480c403000d1100181526820000b1002c00a522000c0c008101c0940c481c940360000600d009040034034066803444c0103c2484c2c0c500440c5c8010340d000364024104079903964440d01900e40b903203e070041c3d41d1040d0b40700007202a20f417901a440b043c01984100418442c0b10b1100040c031881f210800f102c03c0840011a01c040492640340005000308a4081c1c008691342c1590240441280c00142c64030809800c06010054418608034956030f101d40110281e80340703614140c8603955203028030700030b40003403100003a821444e02d4001c0300d600c10740e00c540c0a04d21040f403059140c07051810ba40311940305818410241c011550051501802c0683c0c494022803121a034001d160203001201031980582d455540e54880f6405612a40c0041401c0c5a842e4008960030f031030a14002c0c90002d05a1103501a01101c8070300384849102d010b20b03211041003085800105010118901990b074545290028161020a444480200701038001d40303141d00d40158180340355a239030280c2c04d01a109004803100241c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 350654568 1250 350653318 350653321
    0x60b090702390d030311130e06040203070206370e060609130201080a020f030f19090206090f010905040e010f1d0c06031e07030501030b090109171612031b0203040e 72
    0x6040801c401d4241c3d9000e450b001ca0b50040100010115034003008112580c40c0b0417560a20010241c5404150000d0003960110702e1881c081000239140c04020b400044040c3c14054000712599100c2c813071481d2030354802003c02e41d0303404400c281d800a00241c503240c101801a20005002c030303d0a0b42c40c551045070015030180c08550260300458400f040103051100c140d034280001e4106003601e002441c807408500b00070048900740042100c00f0350b50b00c00c844030760580c204840c0100503100c03041581d001e03850648070406458155801600cac20101504543d40040c5080f084582d44070b01500030843c1c00d5500380d800c10441441c124048241403020703944c0c01c0c5581c1305500340030341d034181100215031001caa0310307441160510054900c42440f800b5214038001035103500050003400082440203800051000003004025126941c803c051905030203c03511040000c40c0f8803540c8003085452100c000d0f4440c19490b00342c1454100075000301804c194114100c1d4140c54100d0b4001d0000044806440c0c0100300540103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 350655818 1250 350654568 350654683
    0x1c0c0503070809060709050d030909050106030b130209060405060702120f0c04060b04080d111002071a0a092f0a1d01062309150c0703031107061209060b090702 70
    0x2c2d08048022030800040c0d2b000040c185101d84134a6003e804940d401041841c405000c1040d0710a140d40300b0714409104001c3c01003569250402c4400302d501c2a501551078250500003c0c90441c0680c0100c2002d008e810030355164518041015050381c40c040302d00700b016984801d01c807585406180980c150030ba2114500ca4400c50041e40c094032072071410011951030410a40680043e40c10040f0202e90601c1003948403406109010f280c6580312209103010010070380c0e59180e01d02090782c4000210010074030b4640c0141c24000d40c3c4481804070300003814408501d030740c0302056a003050f008424648001c55a038004940d03544a0b41014419400003600ca8840035031420340511a41c3c41000540e51000f204c2062016080a2901502c01c401d5104060200c45180d03003809403501c020150001c6140d04011301c10b0200320b400c40384070782c0e4207035403e00000b400c0310031817400318010214a10880e5000c030139036042181040d8006002c000c100b04403d48a00e905032200c0c106a0b042400702401000c081c2c0005600c4074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 350657068 1250 350655818 350655829
    0x15100b041a03060a08030714010b09070e0915180a0b040b010207061110050408030a0e0708121303060227010318020f030703150207052404081c0c050307080906070905 73
    0x4003c40020082d5280c10f588036149450365100e002c0071110b242000d60801d01a80003841480303c110030a035030350f80980c40c00307020040a0042203442c0911804400011440344500d10040c805a4a00a0700012103c52010b4400709460350482d540030316142003110304048ea0800e0b0003030214490042e0001e201260401c10142c3d155070314000c58038900c4c800e1091403007004006000301400b440c0502c0d111992824901c3c0700c0c41c15600e00d04840d041c90b03489040200b20941c1c001410800c40503000c80c2103a213406a40310b600e4100d1101c1e50010b8412030000c50b00500c103620400a050303d041c00908980b040701801001941030f90f0f410b01003840159402514400941444c2d58140083c03413005081d0780419449556003150b5108506403000015070128002c0e0400c40304002120109180070480e100b03070503c0c1c410201611030700034401080302501044c114101c8000d65906194a00000d4084c0a00a840f26005103141c1080f206400014040307c00b1a038880404900d480c02524980d82d101021818070b404e221 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 350658318 1250 350657068 350657071
    0x10c14030702060a080a18173115030506060d09050319030b01021504080405121501030b040c140f0103020306010e0307080a03180f141215100b041a03 66
    0x1805010401a41c401652110014030b8102d8054591205c141044070b0704204480b100c50501200e2510908010081007221104442c00362841518940d80e10702e00548403102c148421602031501c80100d000307404000c100b442074094038a000300c085040a001700d0308606a85066800c2c58120804100744400101c05810140146008104492600c208103610400380c0407003075020400603a45400641141d80d0602c10880300c2c4d680740711071f03000e03a08198441d52103600c43c41c828544100809aa1001420820311040505030418441031180c2e40c0e480c141100024000c4400300c84a402c03003a00820412041c4603580100720014100a882c0c40e03403c0010f40c02948060401410f00c101012005041d0740c04010140241222001501410002c3d00d0080c26600450b409021032020100b818054401030850500032500400c1a0843d1030320000c0114440c0c441c0e0205009072801620f10b0303101100710302c44949003d00082150f5002c41a80c526603044280150700800c0041c4000e0f8408404074400e400145 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 350659568 1250 350658318 350658353
    0x12140706110909090d030606052505070803210a0c050d09020109090905010f0c170f0a06090e03070302070503010b060f0f040b2208060f13061e09170405010c 69
    0x15142c94105000500d200da03080fa0316040903440ba021180c1c44a500d400352100622450070581c0c10141e07064118452160400c402120401b004030180e01842010801d0300c0c020801d10301680d55442c0007144089140e0600713507501c041c3d1400340c2d010804152841c4a1215483c0c0c00340c0c0d48509084000d0410f0300503042000c4c090b410024140d2011545c4c0126100c2c00245038031030b43c00015003014424246055450002991060101040400308103824004117142d00c00f003221442480d03a5508030601b801400d4542202e6171692801c410107446490000003084400d0103602140d22007503807142054284d440030f00e0060f8201809000c5800c0f540001e80c086c111883c000e449081c1401d450f991003004540106d020f107480c140384407500001d8595a000030102400c1008082c094500e40455901413040b00540700200c04000105c1e10828442c4581c4028040c01c601290301c4900e01c0c541c40d00c5c0002d451803050a8900d10003035915000c0c00800c00c012501260810303141d038001c96110351501e800540c0e028909 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 350660818 1250 350659568 350659601
    0x307050d0602030a201c0203010b1c0236041a1c0212010501051305090d0806180103141e06010902090d06020403030302070c08010504020d120e0a080a12140706 70
    0x242500c201c100070300c55a17400b041003c026118030200440c0809030040143d01c840d0f070b0b4810070041c4204416802101e01010054032105458a0040030754002803092840540440d0820400d0175400c84109c1e00044910709034076001506c1c4402001004212000780e00704503034054901c2e0b00b034801d90600309503610b100c0c00da6920301080350140343c0200f54103901b5017880b260f007a507544005010768540801001c5100c000c01d0010425803804640c400d0341c030a0610301100c107214041340068096900e0280400d41e10031407034540610f550b503070320784408070810b9088254581c0c059102811280c0d00e200558030120881342000f0f00d62a46080d03038901c002c2d800360025030340203101c81034103001062260004000962203540c005a07950218104040d28500c580c004d108640d05040c14400903a9409a11880c9a90028585040c100f200c1e6416181c08800071451500030003500d03400a203501021840d03c0c901d038000c81e41841e5410007103004a4141e0700000205c242168248a8640400c64a90186281d84540c400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 350662068 1250 350660818 350660831
    0xa02010f02031e0307081b0909280c0f0309110607020303040e10090c0504051008090304051c11030105100603050702010f02030a0c1e0c0b0406020405060c06040c050307050d0602030a 80
    0x8120782c001002100540300b11400009000c101035000c0f10503584403500401828a054101f90300b101240304600c0307100e108500c82000705811080031182d8a43e020030f50502120201191100704010703051038558100424440d90844110324080d010311010310b540419204844642d500400849401181c800c0c0e130944428400800d4010310942c119004508010304900902c1c98060000169400c200d6120300b000801c2c441000152500302149001260500340410f49940e0440882e2030f40c01140e21140c2e1041160102024003d009031001100c0c50250101c200c03002c20369028542039500a503240c41080b00300701c5040000612a5000a4214040b1b10000c01c0046030103950340141d800c20381d05408800c1c0d032405160b01031074002c1040c424005080c42da13020a000c1098002e0500c107109036014002e100b80000240030172400d60704540181c00001c01c6d59403284090008070780d4503541181e0444010301c03a0700010804d0301c1c0c00035030307041150402420004810f220383e45000107500003502002000f44c40f0f06 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 350663318 1250 350662068 350662087
    0x61103160b0f061906050c0a0b07180f030b0c0c01092013110f07080904090c0302130501180e1e030a18050f010302071b0b03040b06120a02010f0203 65
    0x1a140104240224000c0001d030410030215100308001404203442414101c0f9070050a01203007034120121781d03650414036221148000c889007400d84c0d5010040840546004000b070b0b054000801e0224000840e0307035038030b0664903650031100241d6030b0300015060248200c009501c0220003401002994554000400c4500060b0390700e01c901181c981031a45c0d009629031584443d130519041da014081c001106c140060703c5515601805407040b11018660b00300001544404e0040c0e000850f804d04502034020030402860f414411030000940c00202d108218180b048075108200d0b001c1e240c1a20205180400806081400724000f07200d6003141c60f5480c002c880d802c010040031622280114140407002c0c50381c41100840083c02d084480c811641c00e0400c5020034815034944440510900e0420b09005984a049042009862190811024240301e000b48040307100e460450245020381d10a8401c810342c0c4e242c1310108090144070404078407056111041c40c801541c4030342038454011b803542c010744e03107842850b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 350664568 1250 350663318 350663347
    0xb0702130501030305030f060d0f1403070516080705060703090b030406230601080105010f091205190f02090a1e09241b0528140403030e0a1e061103 65
    0x743d1065000c01c4011007080104107404201e00d5002008072103440c003c0c0b006130b50390300f8046c0c0300c42c03009811030141c4005401d2100040003141c0700143c01c5403c5403241b0001f840e00401140980c00b07200001d008000700000c0c1403c1c000d06039442c0b1a8940c84080300c0508003000d04c40305400042003a1145510340551208040c0d0b907a180170303000320301e000d224200d40c035004001510184041e0702890400030400600102d566000e06207109492414030300d0101041d103030600905d0480c1510030021000031080e000301c100011b80b032900f29494825034450456035a0030350420100c070650351041031500040310351440180040da20a90074207100e660101001d91703014440d00006484c9201349070066072354820b20180c5480140040c00914800c0c41c10030700d0513140a0038000e19184011400c01581004141220b409004003645048456030b141c0e0b41c3d4546640b82402020b281d14040502c0c001c192289012810b8034203002c0094940c581920358100141c9403403011154403241407124641800300b07200c084000c0c440c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 350665818 1250 350664568 350664571
    0x6050a080c09181915060803120709060504050111070801051311090c070807060908071203140123030c0a140307140112180f0602040609060c05070b07021305 69
    0x30340c008000c8580c800d414010422400b40032500d0506038100a005009800103600180366880c15542c81d600005280104c009241010040c021071305264011460100c0040584a801e040c40440c0c50030780c5500e10b043d11941d450b801003100243c01000180300306d50052600441e2109400c00300c42d8520b0b543d45606084500a9800c1d10701010a1819803092148441d0282520030040b01d1010b07150400c4500d500300c92194201c01003204201141c0007003030122560060320415040410b040d55041c05161a004c5910103d05d1040480e29155404810402c840c0003103050307900d00c11b0039684110702c0c41504d41c5010b0100c500c0303075414420030700010750903107500c0e20303001c01030100012405046003c8800c140c141082030300f02040321718034032849807016a44503a001c02640500e40c80016684642490080c81211141e400340140880c1c45503803041002c84d5000f0000c17621a5035070390b205070307840e00011030b80502c9045000d0581d1f400104280100c1108800402460f8401405c0c0706001d110202d00900341d030030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 350667068 1250 350665818 350665829
    0x606120106051309050105060301030609020303070525150f08150d050c0301060b0a08060f011205070c0303051513052e030314190c06022208160b0d02030a06050a 71
    0x700416480351856140300c80c00040c00102c0c4c4184402d60403c0081020303800305100241603c2e803140768110654800b8001c68000f0b5401006540440c5191042203042d0020109240b000954030080016000f103a01101c5142e86643e94030f0004498041c041100c1da2900640260f035807040340100b0700441c0d0795001401400500c158080d143c0b03519030f84105401c40724607030b100740000d130300800200710400c0c1c0c010b00b45903001804943c4880c0c0c620b207a00048441440c04031039204c1c8985094280181503400c242420000d600c2a40d041c08959560383c421a000304001d0201d681101005a112a07400119000790342c0c0804501c11f003130000c0c400da01d40e915022443c000810382284010b0010b20606a2200e10a650400d8441e801e9192441c03c1914440e20010550003508200c1e07808603030700821070260125015804001c00780c143c101c6520709081c001c0d8589210b5003446224081c88460b103500c2401c200e03001c83d4820b001d1907082c0b16038088144003035030004244085a564440011a00e50780301d103c150080d14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 350668318 1250 350667068 350667077
    0x9040501150611010e0106080d050d140712060b0c0a1e050307030906090801050c04090e01110c030a080a1104270515040e0a0809010e04021b0616030c080c030606120106 74
    0x80000203d10308407900c1c03038420051a410b185090080c1c080000320086c3c21074a0b0700d040c03580c0d4207049100742c00910740d07104c0c40744085882c1c0d4240504242c1c44643d50044031007501041003031580da072103c0c050510500c1c1400c0e20301e03081100b0700c00100b42e4031419000b6001c5614103060b103500c0c1e5651803904507882132004030042040c000c0148455a84503014102910745000200b00600342145081d440d40101c0c4580d0f0342c003541703400c0850f44120081d04141080c4402400c040d4580b0f501454a507140e800c8890000c00043c03c180003e0b05d180400d0081c40b070140d14010056140c142051030040603811000c0f0306505603100c0513040350f243d142500c10144078910807024200911040340410080d2a4945c08542d165801031148c40c1c0403410500440300c0e040404d0914008060038940405c0103030043c0c88000c910044900c200c441c0351000800d034940308034142e02e4940070340d9100d040140c048034110300b81000014402000603506112070001141c105000800c124207019001103e0140110b0036080540040e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 350669568 1250 350668318 350668337
    0x20c1e04090813080a05120d02120a061403010203191d2d0d02100b0a0902120618090c010f0c061a010e040e03030c21090c090a02090f090405011506 65
    0x108803ca0524014001100141c254060a0b80740d0a40e6281e4140315140c11150003e40100030803070507412243e8400340142010641e180112800c001001c6c1c900c00d5500c801118010303880c6030319062017103d11545646045801c003280034005600101041115454000b20141501d032000008000441e041003103407800601c1005840c00040b00c40c8030404020901c3d600402c043c1c40d8050f0045000348140e44403040000d0014022400603110071015844200003520000d84000c032580814485482004152074441e030303407040c0400c580492282181c14011540012507480200d600c80c98452080d00b0f591303c1c15030034003002500c9200840322280d4440c0c1e8280e114101004403541c00102e9403c050b401268100a131441c04220107441e41302c02001d0f201c0c09440050b41114240400700c60340d034564400c0f24841003900e050030303540c0c0c3c4e60255503004501c40c0f40d20748005410304045000701c03401001c0141c1801e02c60000081884103e00d0054411100c5548401d82c4026810b40c921000b0010083d513681c0c0c0304030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 350670818 1250 350669568 350669587
    0x90902030c011106060405060301243006090f14030316030513030c0807080c070602010e03070c0b0a140a020a1b0e040f2603150102070303020c1e040908 67
    0xc0040c1611164180210240e00211003100450080d900c40d17800d03240440c41d540c42d880060300514101c44440000046054419010240c1101070020b03035111100100701940b802c0488200d5a441071100040e44030301405440025196810074141d0038412190140d4019443e0749504135201c114094450b598008000c02059100031000880c0b2066103040802c200d00307044410803181039907164040d00b40b0141465150800090400310b5601795040407415440700700c880f03141c0751142d4180c4550001582841c2030300103881c1004c0122a0b01c1a4444802091a4540020070980d03070415626841400414041002c60141d500014401440302da0f014040712505481c00200c807200c0d4400000302c45090034010b0104480320320b14250416009140000301060030310701a2460b014000041400c2c58454401d010841242c2d000385004034124100d40003d032645100499076605188000350040e0f110a4046004d810b14103002c007801307606048880f0410700724402050543d0031502046451541c001240442d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 350672068 1250 350670818 350670823
    0xb04060f1707120c050705010212071707052a1c1d03060a20041203141e0f0d02120a0e0a0b01090506060c0d120f060f030f020402070c09090203 63
    0x203441c0040e11050301900781020020000e9040042940a280d42c410320145464010001d440300740d58020020340d52200301d2040380401c0d040560315240480c001c505420044128041c844e07109806031382e145800c00b00c2c004030100c1c1003015500200c81c100c0000b4003000740c04e4801d00c8001d500880c4008520f85075070301e03e139004103103510600894154800888070708a01d030b13502051058000410000c00300c3c100751941828080500900084d0102000010340000c030440030300f44010f0003034003a8441040c44a060900c2025a100350f40c2e0035003501002d1202c1524001c9c40a01601da1640b010349080d00b010031120400c0300302d0340003001c80103526950740c08120f40721030b10303000e0456000b003e035002e80781c20702c02c0d83c4d60304500182c18042c0c401e4098540001407020703100e072426110404120f000700c4004007030244000c1c002d6112030440e0944941020051110304a09010b070000304d0b00c402800c4141140345823107942904620204c101c1e4450340810225001c03a80d8608a500075028000f40040c1c080c940e4130400d071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 350673318 1250 350672068 350672087
    0x1080c010c0c0b0703030212040b040605010b0a0203490c1701090c120c0507061109010207030f0206041d01060306080a020901050d06060f0b09090609060d030f090b04060f 75
    0x24100004540a140003400402c2520201c2c0c801c0c0318002e40b1041070f481d042d0b002c1e000e5408014400c840c0c0c18100814000142c03500f9010b0760084030100102e9880c0c46202905106400324100540d00400003240349012440d038a074015500759a400480045500d2044454441151b40e03a803103070007142e10301080e100c0d80d200c0c0c0005410701d0708028845035440140b0444c007681c144a144150f03030350384202801d014000c526511085410700000c0004070183c00300508640c1191505940c0c2b185840c1100209a201d401140e500301c005800420000d8910b0341c41c810045440c0100300d800100034000010707400076003540081c034488503401c00c1d10250304101c00241102c14a500030b0004e40e1004200d07001613242c990465041d0360055030452241a01c5007800e50240c1400e600013100b00041101c0094022007000241c50750000c1100e000f90162914401c1140000c2d041c0c3c0c0c0940c1c00314046000000290003403001c060441d020782010485030b640c1c1c03c9500d025811650202d00490803c2c01078201c5180e0001005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 350674568 1250 350673318 350673343
    0x1c030206061801030b0a0213030308240303030a0e030f0a02150f0c180303190806040b1e0402030907270608010c0212130305011a040b030d0509040f11030f0108 70
    0x41c0d05030540c4100b0312106906100240c0180f42040c0807030381140054041323420400320010703049401980e92038002c01502d000c641e4280100074241c496103260200704508541040c1c010005c5040da00c0f140385580080c0618155040300f1301c81008903610381013565014106100950700540408820031844101d881e00c0140707840d2040c8207040401c00a00250010b40751006060844a004904840013003803a501c14030b0140b900d49610100c080b9035540d444101c0500c10300c015a414001044e40d8000c0c00500c85c4a5a550814034101308100c582e04d00741a0f01440e0700100440841c2c3c400395480e41d1540d080c001c0340c02400c400700440c44071086804901d00850b0001c025003002000705140b0404c0082d15005401e210021980c070010b9445280000c10087e00091030700640204040c0c608009003820a840d80c1c6042e030300403810310708095664038000c40c584042c008551926842c0c21842405c00005100c105002d805060365a000c6420045040e07010718030a8000e12a183c5165040502e070525014201d20708 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 350675818 1250 350674568 350674579
    0x20f03031204330606031a010903080702010c020a060f0f05270102070815060f012f0102190201090203011a010e0d05071205070e100b070b090703021c03020606 70
    0x11541010a03200c1e45580583c226030000c810b11014008041c1c41c80036202024501c0981d9a0320790350142d1264002c004a803c03580781017210098031840c1e00c650841d41050301d4046200d0300810004035810100a0054501c14074014100421540c0007031584034043e00910009030f900081c00240c1030700300c00d22035070070380c6a8140982441d80300e043d500d1800250b804401038806041c070341c442e001d034000c0251a01604d0010140d442810f0724190f8044440c03801c45513a841045550f082c0511135000740b6594413407101055031880c400604110b94001034400304940e0100b59800c00c00803909a440001c014112a100d81c0040b80c800c0d0180105403e50b103029460700c400c000c021040081a0383c002e0f40800c812003003a250520032070060300344541084800d80c020f00d40c0003500b803450307410080d0109002060b518a486000400d07103440228140900050007003600a00c0200300c0280403800400f0065032048012048940054907940810000c41403011a010003c02801000d41019018008503501c000280c1d02e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 350677068 1250 350675818 350675827
    0x50a03081e04020420041202150c030301050108040f020414010905060919180c03080415021204030206071104060b03090d020a0b04022b030906120516030b0d02040612020f0303 77
    0x54024211010b84024441d40d03564265070004030902c012080079000c0c5405282d00d032944d5107003107081c40000d003e0880c4600811028811120243e10543c2c0107030710800020f500f5a03007400c006448140340a00700b0b84180520039003c2c40181c2e1a0b00401c03403824800340079140d455260004400c1034803800b41000348035460301c4040090603640c28040f121401d502c09000714843c0600d451080c5002091a400742414007512404024481a00000c0c011141c404001d00054110590304a864076200304003114140300070003042002d4586940984400e900689100c0550020440010101c40e00c42e80034401c030900100030450304200500650b94141c072a4006045550055a1a1803581400420081c03081d40746003003095844a10000c5c5819036104406010b0605c441800c0180a9041230b10620340001c124003000102801c19004540c00340b1510385070828a00d59146090b406088165102c64212602880c40c0000d80da076030103218010700e00305050071504003090040c80301303c4126002260080c0d00401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 350678318 1250 350677068 350677111
    0x38040f090f061104030b0f01080d020303010f050f0612090f07050409170c070b0a110c0103141911070303020c070b030402060706020904060306050406050f15100e0f0d050a0308 77
    0x1807031100003944802e002401d02c803101030900c8207000ea500701038081036082d0204074000c01c250034164140c40340d5604650007a0780e07007841280d41c1e1100f40601c21440883c0d81c000c10850410708400300c1c0346039008040d2803d20040407801c40f41980202e4103403180b54803000010403520001e111600c0502015a414001c80e80540ca60120119540025890b024800100c1011044050041101610700c0c8500f041d0b403117505000081501c00c104102d00c05030302a0711015992580641300782405880c42c8501e80d02c8540c6c84c00d60807400d403904004001c10090b1102c001c0a0340801d0000144006031103074500581b6000b2046201e0b1034503d9642217004802d100f0010701c0090f95410341924445580300c500940c3d51002c0c070010031b01070f2610b580002e0180d0b0824040c00100481504400d200b058107e4013101d803130351100d1300c8494140f07a43c0d0015800504a00d012440c0502c6860300d801c17201c101a102d402180b01600100740f00481d108010341c0c81d500045440004c00d540a0000c60304500d5440c045404c81880a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 350679568 1250 350678318 350678333
    0x1020c0c06130e010609090608061015111c081803031b0c01060909110102010911062d03180604020a270609201305010338040f09 57
    0x450100744541d0010581c603000a05002c0c011014065030703101c0440559651001405c0e030780140c000e1035082c60614101007101040014441d100750700382d2148645903450720000001079045520005c01700015107141c103074070940400986101c2040d4410701880340e034500f040100718034000b4094555440c0403108102c0603410000960f90080001e00c012140d0380c2135800748010b00d100d440c0401c03890f5420003000103140021684150300460260714107008529514004908a924041e07005010340e038082d14940a50825202034203600805040a2a00f00d80800b103040c4000840e2410070005500001003201c4054407041b60340c41000000001e09060405600144072b54071300d80a00041a521071a10704034440940ba120068078001c04010002151200740c5000544540011a0450014548240e0014030514100e07212006030009000840d0b0500d1300442c040c1c039030300d01594901d6039000c500ea51003164041c0000e61005101342358441c06011041804240c6800c5501079a4161400d4980d1002c9880c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 350680818 1250 350679568 350679583
    0xc010e010b0a0618090f09020a0504050f1b0c0303010b031006020a05031c060b0703020c09060303070215130e0c09090105010c02030319180e1005150d0911040221060301020c 76
    0x1500303000403134980100741d40b65080c05507800203000707600f0202c80488002103036012000c81070094402c109115111401c1c8415540183c80c1103043c000b804000802c00e41c5481c030150314814440910301d01d845480000c05285410a03002508402d000105000400c1c0340100d50310001c00140c00a800d1034071540e12019201e00a28050074903c041c1d426185c0502c9069611074405044810580c50302c0d0030241c10300a54405510304c3d5140213403101c0d00850110b20780042a2400c41d03a00419030b01000c64508030b03a69070b42e00400210403200407e82d00c081071211110180030301c155482030109441d030708100c04200b603d03401a4029814062104040405a1008002c0b58038207000b031140c0b41803259552100b219611102110116814401d800c0842c0c0480264540d80c041e984a041c840101e42e1200100701aa1078450108000e440302000540c51259040e04061a0507016000b01c507480f00315100894242d034003000c03100d001660120844c09014161406550700040103800844c10200c1203411035a45100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 350682068 1250 350680818 350680829
    0x403051e0a0b01031e02041103040209070206010b0706091a0c0c150c0a051303020621010504060605040611030d0f050105130903021e0309030102211605090108070c0605010b0c010e010b0a 82
    0x40c5500c1010005950300700c5101c003031b070240040060300c42ca03003681a42500107131000c80c441c054080100345d04510000304181a59040c0c0c1d07800c0d213401c55541d51000200340f00c1d4070890b10070325002281d0280000240f000ea20486080302e8850f59681c0a081250401800c81c1c201114403580c10248210b566030041552109102c5003003075aa540102d0800c1ca8440c403ca0f0300c025485503001441d600c01d210f01c6003030040149000903100a150344c0300c02c1000700b50740385400723618001403080c80200300f907520458914210110404c182e910300342d0050b180006461075440c8a501250b02c4400400c01e6050000300000d00c0e41034010104504001a980207481e4801c000580c1604407010503075551400040c81102c06c0060010000c40d40c0300303410300c0e07141100c4111a40c007444882040c0c00048181480890a04003200c0a540b4107240060340700040d41c1040c0042d101d001082900402d0100061141c8105800390440c00310302034640e811041940e0035640071055060603a41004003031411501d401850009030346 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 350683318 1250 350682068 350682083
    0x907050405090f1b0a060903050616211401090c0c0803060a0b030432030d0515040f0b04060b07050c040f020f032508070e0103051b0403051e0a0b0103 66
    0x860318240c80f4644504010b641000c0e000300d8100102181940141c0d0550281c180c1da00b48890b5a182002d4540d144c007440058116001100000e581d02d141603001c4541112506240e450310745510030f90000c01100f10211804181d4071190464020103070000760740101803c100a110441507418010040c01079450014000d01e40031000c10803a80d2941100800f034414400059100e2800b410b10f80000c4101da42c0359030612410b02121304400c9000c6506480c901c030340d42c0c01186410f000004680050000030100442e0840355005100107994602803d00040400000820080f0079034042204503003041e4000c00400c102007150704009480440c00403580c641c1120b00140101521512601a20541d0381c40041d0139000401c000782d060541c50804181c0c05140030400000e44000e0b000d540c10a82500d0b86c81c089030f1041c621403c15803194010542c00900c039500b1500111907003568990740c0e0881d410844036500450794851b81d0b044900107140344240544010003541d802a211840d070122306002c00b61041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 350684568 1250 350683318 350683321
    0x11a18010f14070c0f090e06180c0a0b0c0610050112020f041e03030215190e070503161406042d0e0a020306011215180e010f05090f060907050405 64
    0x9018240b091085100d1540441e40d580380e600e8039a90780340c11070251900481c466078020038900c599200d000c00780c401e10802001c031505d40a084041403011011041014801d0300c800e01070688400c8102d07002003041602542c0c444040c60b1802c0d0030410010300b9680c0b51058040108032a81e884020302d07080c0c0d644960b0051740c60031142003038007481c4200d4200e403540000d00b024940c490036a41da104001c0341e0290f400d41c1c6d0f68a007204e110802c1880241c038548103000c40c0c7c00b04510106003030341c840c0c0511701c0c0c404200c8402a641d80042402e10304c0c001c14000400100314402c10400c010094103d112507002ca85052506041800d40c01801000382c1c0c0000309104100710804074030321000850ba001d410303000e1801da0f144c035042070300401039801100e84a000500c0e10300905100c1e100740c003c0104415460030408005818400500105690744600300740301b41c1c03a01d01e00c502582d42889a440d42401c1030070042128500b401d440d40c0f40c0aa000307c540318075400741c4100140e201e40030850740207441c0e0850300401c07079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 350685818 1250 350684568 350684597
    0xe100507172a0f03040503071401020301240e040e011b09030c090b010c0f050705040f1401050f1c0501050108070b0f030c0a09180506010e03010c0909090606031208011a1801 76
    0x1a4081d448442c842c3c14000802d00c010310100001400341144100e0103030215440c111070803070030b034002031040ca10101d1160001003088408000c2c15041e81c5000e01d86072480a448100260566a080ea20180319940d01e4410013a00307802c0c90032100c3c8981e103038201000c04a20b959200341c1d011070148a481d8a0743d0b0350701580700f43d0340e10480d0800758541d00300c44a03440840c014102244c40e44900e1003114411454820b010050104500808a03611f0201d070b601d801a070300c1e02c4140701c810050844610703440084400600b004414130740105030b0043c081d40c000130f815810210114a01489a0400d002010052040e24401c0e2003c10449a02c1a1590305290704e40d6120a016514a0a5600140c1d6903c1c1040310800d600c454662240c1d11840c026681d0047d17400728002814205c1c0c1c0700300030690004007261024070070301e000d0390000d41c5090700c20f680000d0159600d803200403840350380c12a0f140000d6945801040348000070003030204180c2c0301e03080d80351421210303010f006024a00d046040e418014580e5074000e6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 350687068 1250 350685818 350685901
    0x60d15030c060e0f27090615150a080405070909060e060105030c03101e02180a0f23060906040e07030b010f0f082a07030201111602130e10050717 64
    0x4c0403645c6540800e02820b00858464070360038101d81c0340c1d0118580b08006803191401c1e561519000207940041c500d0099452000c0300c0e0714500038800e440e523105880000401d18610302c54011442c1c081c40d0006222100035003a58102681a4007840c0b09a109110007001543c000c900e2407141c05240d0b90015180d05030100c44000303007418211038001c03d840814820044041540070013021001200c110350380b07a4072840e603030011a000f03001d0201e0700414510010090500310040400001c0c0007854a400d00071890005512075100b034201001c82081c01d414003e049415000b1390000420034206004580611240100594810b9001804020046001c607010580c5003c120f5201d0440808101e401c600b045c0002410794800c5500314015071070a40c1c0764010001a1040c3c82401020344c0f01141c072000603800704124001d0a10181107044d94420405001e1801080000810340d40501c010071540390007403001d8006024a815409818003003030401c03206014455418042501401c0403200d4411030405805 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 350688318 1250 350687068 350687119
    0x60e090a0b040c0908160e0a0209031009060b13020f030c031806070305100b13121707050705010e1f08070c02091003050d050a081302060d15030c060e0f 67
    0x5411502e00041c0700901a0b12004050507507602e00221443c04084982d071803d00c0da2203114441900c0b44c0d031f1001c070b001c075080c0d50001d2000c0c00d401011600804181c200f10801c032881d458089075050780c1c480380f0304500c1c142104400306109032414114200390240b0007103040d5110007024440003030b10000025036800c0d0f4a03260a0000d81c0000c003100c0291070321010203401000141ca62498003403584400140b44003a1800700c03065040544242c01a840c917011001882c6010002c0c21501210701031204441020440e0182c29424015001442120702c0c020001d09070900c2402c4517401406100c24404142c6048801d50000104524094039a9a1015070455015544003002548501800305203c1f503604421800002c1d203001d8819210b41c00007858040c1c4091007614082e00c0400c0c0c0020001d0a0a4081d1b0082c031719560025040c1842e180c140c00d1070000301c4041c02904250030038580390a000b4810303901d008001410450030701c51100c40c00000096554583c42810728498000159072510301c030740403034000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 350689568 1250 350688318 350688341
    0x70f0204020d022a16030b060f030604110103180f0b10050d08041d0906040b0405150109020c0d0801120b0613020304030503040b0a06030f0201030f110a200601060e090a 74
    0x119120301005a400c56102e85601140d0468122007040648001d40414090342280c030003240c07110314506e142d8501a09030320040000744d025107181c104c611261010701c000ca105520400201a4a128010016080ba4024a40cd04000421071301139030015015075514000280c004078a00c540da9546044100120300d01d4200d1500109807881d13190400c03003038002601c1584c41032080c00003ca03003601a0002069030031540011550700140102c1d0220b10341c02980783e0028020030981d03104260503d00d00f4071008083c3e20401f0310a90010b00c00030800f009003d810305841c01440c1c03180c0307030b54940005441c45d004180c801070b040034005400302c0c81a50b1480854070840d86009405e40d06d078500742c00c016010303400840b0140e80007141040041c1c1c0c141810310680d42900c1c0e0024654805682c0750300110b0040803410100d981160303a5a0414113058170442c00b40194000b20743c0c94a0504010f490085200b02c1081d10003101c42c1c1c424401440540c3c1c0240044944070010b48001e6695902c1500410103421400c0c2d05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 350690818 1250 350689568 350689571
    0x2030a0c03120b120a021305060f120a0203071725050f010e040908070b100305070e1302090903090a141516080d1d0c03060601081b031609060207030305070f0204020d 73
    0x55400004020605505c5d01d40211042d00640458070000402d603a011648641e1003220101d40803400e1a021007000d445418207030031101c2c40b100700d6000c01d01c3c01a20340c01000403400505104850504d0401410301e14503509640c0240108403014912034800060040074460722107009900000e9101d8003080b0756002004105100d07e44203410854030980c4003040036030f2001151000a1092000c0d00d10345802c40c2d074070034003c204042c0b0300491500c2c910030182c81c5001c800400c01000c0701581d550104980110605005159500500030422a0f4800d02c1c2d07111003a0f008012a0781c1000c0e9480140c20102910301017200c9030380c1c00d800c43c804208581c1c40d040003088140c003ca00355054107002d0b4400302c3c1c924001040c0004480d5440c232505e40e940052010b43c1c1c3d156000c0000141154450080d480d0005449681000444100c24020700140c000302c8171049030308130f01d00440003003d074006050030040140b40041e220950454038000e03c1c0c0c1c8205107014121806810500c401c644460341255103909803102d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 350692068 1250 350690818 350690839
    0x30f0301090b0102060105010f0f0c020d06020d0b040b10090b07020402040b040b040f0e06030613330c140d09080f071b050118120606050306130c0602030a0c03120b 72
    0x201c103001010081c055500504c680c20000c1655401180080d25005031620b840190399a598000c90701d01c5c4003248200c1e04441910542c0000428078000743c402000e44040200303400c0300d03000600c4101c0d505070303d045210f025041c156240254102004500b41c51248102990750307541d500109000c2d10680d40100340c807a034002000110701c05484041c0c0103035520031081c1098150f50b410942c01c00740c0140c90b80340e0306130410703400b280c2e440010640a4211510810b0f148200d410340884400310705511021040070662014030100d800d034443c0c401d00030541c2003401c14034200140ca01c0216454016035041c01e8a0591700e04505050248000c15185400400201c403946d400c040e245c24404009483c140200309000c3c00401308071507004085082c4140016800c401c04240341c80c8010110403400d03e4203482d55503403004089001d84003800028803034212030200c50f000000c1c92801101041c090340c040b4085420078407508005c10381c0401414080394152031f269040c5240d1900b007000900f210500310f60301080506 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 350693318 1250 350692068 350692079
    0x7080a030f0b06090a0941160f1d1507060e0721060b0d0f030329010f110a0b27030a0305091603030206011a03040c0506030426040e0c0a090302090702030f0301 70
    0x155080b034420010780c214923165407000d03084200e02c1c0e401c1540403400c0a205c4000a03403040e10000000c0c0400501c0107da0a030f41004a1648643c140c0003e0391900001954001d00880317018616010321050001c100e81450015807111240452206085c90303207080380c51506020b91a004484003880081c41c41c9090956032600c2c00325000281d0040340402d0500c011445255142e921000a442445001ea0180700c0e0210044484001b020303006400d01844c9030703030650000020441c2c000300b41d1240c24903050034100f00726019908540b2b02d0039110300070b05082516031651000700a545504090381030200740d41d1500c03581c032414140650004030b0010b4500c0000000d05900082c054101c812526a0015440a15202416070310086501030411401c407402003015040010085500c01d0190801d01da03800034956031042002c07240d8200e12040640410140900001025083d2700410504462494040c002d200502070510710f00c0040d1140c0304090028800340e000f0320440b100c02c000d0540e8a640c0750303100c3c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 350694568 1250 350693318 350693411
    0xc1401110418020a1709010e0303150415270204051003050708060d050304050d0311030f0702010e0d0f0f081c020417060903040b09030307080a030f0b06090a09 70
    0x912601c4610740c80c2e020041d01c030080c0391007140d01e030b00c00560301d054400402c079403442240d600203071203100950b5885070800c002e102c0a002641c09014111501850703018030300100000d076181500b00125180c03000c0c408210003200110004500382035441ea401c0c9105a021220000b40210b910260304002e112803442c084036410340c03005120740901d403034000390394030b448003801140c544804000308264800c00c014444c0c0c0c03900c0415403245e0351003881d00c04144c1011075200e50554002b00c140e1040b241000c0b07140011580c000100321b44091040d140d000c0c80960503122101d00400515000d41611050302c40301040c000c0342803c5603010700035072821009050481440800944c081c4c81501c2c004014640c600d650000701082c06401000484000e5042c02d00b800d8804807568092010582d041c80101303c4180010b02d01d0010f0041071019440c0001d8050380d201030b82c0c013034540000140e80715480401c444d4000d5652116548180c461034800081c0d00720314001002e812000c44100c4100c13040300c0031404402c04011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 350695818 1250 350694568 350694577
    0xe13060903020c0901080705130e010608010e030a121b120f0204120209010b09010806060d1e0c080a27050a0f06150602030310140f090405010e120f0306010c140111 72
    0x241d8a0b8403480e130786c0700d0b0070507110007041c06480d40c084680000102641c02c260060800b0f508202c0c0001a01a0303501041400c40c0c044400c812041d40011910000c3d240d08414010b47c80007a11000f13100000d14888004040c069481c7d0a90900404ea4410503100006901004511003d0303c2c04555454a864241c00000030041c001c030320507200341c400400d075041c7d914190f601028042c0c460100940352b150811120307400c944401c264441d9108201d40c0c0365640d401034003a580c0b400c05000516954002402805060010803020b10b1070708000c9007160f410362580115403400150440354445c8070707952803c5400c0592942d00604500d00c0b510542081c400727954001c5080c01641c0014450301a075a02e0141e0300c0340403c41c0c07001030500d00000f041040001c0c03007203681080d41c00100704400c4241d64000290b0442c0c02903409490580d9101000904160100241c0d03062129006c0201d080c102035000d401d090b44001400786c2d0401038400c4410341081244a1401c101740c030000c00034800c040701002000c031242c10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 350697068 1250 350695818 350695843
    0x70c0f09060512030403080c0a08041e06210f0b12030d0c0c030806060307050706090b0a06120803160302040b0f0903060a020301030f0b060102280b0901020f040e1306090302 76
    0x1d00140080c035890000300c014485081d00d00954240303451500c0c0e4a000303400024441d14240203250400c4001381c3c0c0d62006001400320001024032150290301251424089a0000d40501019441d180719071220482c03403100d084000003000c0b4803c01c900c2c00d404003074068141403a40040701412550b000c400080080c1040303400da4081001007d0307002200302c0c2c5007505040c016021421010109080381802d030002c1da03120b29903060592404030240d4801080701c21070442601d0112080081c0030740c9030002d0184a0042642941952200070b9a44614825120141002c21a5003050542c00d0041d40641c05890003810300f0602c0c1c5485102080e001041503010b40035440c481d01032800000d01400c0980300742c0e0b060320b0b0881a90900002c0d0b5030340e81c2e14aa080640f01505601ca00c00e00f140f098007070000800907402c0001e64111503188903151804405402402d0810964010f0241c01200d0054406880460306100c01d42e10a91300c608854040801c00c1d5900a080e140c10606000141500021040c92008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 350698318 1250 350697068 350697071
    0x50c030a0504030e0d031e080c0d020c0304031709030601090506030d0302070606030c0b12060a06120c02070b0408070303020106050d050c010f17070509090702010902060d0f0f0f0b101119030203070c0f09 89
    0x1250a0300032030b540c5c08112a09c50303803640d0a02801403040071541c0036200820402e021285001c1c1c40c4c0e00c0340070030344608060015006500184030b02a5007000d1042500520528805100d1800c243d40000d03150f00d01030442004060b07004c5205410700c072098011000031500715071490703e41e035100c440c03000c1150712901ca4030240210320740c0450a24101a10fa0104070390155590b10340d61000f218515000e0094804190114881c10001007015421140144010600d00b801000c2c1d00d80380d031074040d081d600a5403009210b50807220403600410741c045039083c103101d02441c1400960040300011344050001000da8061203980310100480613410100411018a04480901040e5200d000032400e131420500020340003c001c0c0304800101880b81c1080903000d4020300b003c0750f034242c01d01d0900d04540c1a800780c442102d4840da2141d400d03040c0404510300f910801d29010382292850141c00740c0e100804140581d841c840e070403c03d01414070078000c0d511f03915401130103a0303a001d6403400030444e0035000d40600358015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 350699568 1250 350698318 350698367
    0x5030112020f0d080c0f0607020c0411130602011e090f110d0f060c0905030a0203120a02100e0105040b240609130f05060a06090e0f06030a080309010c080a050c030a0504030e0d03 78
    0x1030000030b2548c4105c90703543c010100c3c003a009043c0006480740c0306112140080034820100c080d50645040c0020b032040c0c1d07000103070324200c212509400b0f003401c40040900902e00749690002c81c0040d070203903e000f50041c0804544c6607600f00480c0345030150ba80b025200381c500c0719a038010844140c02c54040e20700160361340c0150720345500801d80c13600f211220095240d0300024034422011101d60107410090900e005852824520405900660303d01100c48242070759144d00704003c01a81c0d15685410410000b14101031441c8040401c128680001e0060311074500401d008116594100000600050a850a00914000c0150700c4050b00741514280c2c440e1800c5000403c61511914401c01102e40444007203c00da100c081d03038544c00710400b500c401e806004400040340880c00080c015400340d01c1260001400314030303d00b0010248030004e0454161a03040c00207120018140c0d80507a908011941d40002d59030300c480c541610349a071240b04180e000742c1007103d80014940c0151583e548040d00700c0140c2d485 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 350700818 1250 350699568 350699593
    0x31205040605030708100506130305010c0806060717070c1203020601080309010203070b1503070308040806060d12323007050c0f0312010513090305030112020f0d080c 73
    0xa9000d64050000056014000074100510601c0c8441e008460f0401c4440015115004115294894070203440c00e03141401c820010030400b4869a4a440042d2520a606080007000250075205440c0c014002100d001c12100d06101c22500301d030112a401704d40d103981556202075800e03413030401d260103402600800c1c00004040002200b1558030500581c051841d050071383c1c0d40c03c614002e020303001003103c0c803c500601209460800c504000786014050781c5448914044c400b91902800400e05402220a520f0002c00100e0214050307035145558200014031003a10190800400145544020411110b80001503010000002072243d40c14403840b8171840c50201e40e58240c400411040402902c00d40c40015501c944240017508600f6403407425220128a01c4000900d10b400c803110500c3d2405c5010b00402039031420003091034034400c41d40028000b00003142c0340074009003c14803403106c81f510b600703411104556540c0041d1000c044000e11a03180e001c0d450a01008903004203000b29210311910916020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 350702068 1250 350700818 350700827
    0x1902010e010314060d0f230706090612050a0b041103070210290312030109050114100e060d060503150403110a050703061a03010903080906010f1206021815040312 71
    0x90303003d54486043e402c1d450360b00c244070300d18011550a80c2c552101c1c07010800040c0c05a1110300328466101400203a1009601800b402c10740c0da03a01400500001c03400c1086100d811124140d5804d0b0038850004250391250070143c06083c0300800a6401486c1c4010801d00d502e8000146000d10303015421208006080b4195508a80028619a00c0c4000714910030400c060445800d09160300c000d0705950345042043d109410715003084e08400040c3c1e8072940140302c000800c2105042045040b203051400c0d5021034800391030860101c04090082d80001084181b010161300590001c1401404490b10385200b40414204084152805c40c0042c00d0b88882c2a0b8101000039210841d5801038080c0c218075145a403040002c0880010504107040300560742e4140b0f43c0c0a200e08001c080c041c0c0c95501c11031500c03c05990a1950580000448805044092000c2e15280d41c10340d80300741d80b20740c0050b901e2070140c040c0402030040c1602c4640c0302d41d9070b40e0001c1b01c01d00460003900849100300007061604039441c10694 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 350703318 1250 350702068 350702081
    0x3030c050711060c0a02090c030a1a10270914060103020a3006080d171003031101020408120c070501031a010e120f010b130917070606081902010e0103 66
    0xb440036688245088062414030003c00c51100640120f400720300c8540d006c1654400201e600704500c2101000300440e22600303020b201c0301102580701170400f100c400c5d030014070b213801c3c207520303040070058401c03d2641d14000203103c2140c00039001484e4101c26541c0c3c1c5c1c00e080a0017003914039003607440203c40441c1c440d50003070003681c43c8109a03440703c22095124030b00034941c00c01164003c0d104104080d03c0800c1c240000d00c1130304098490040902150f40c1303840300142030040003951210f0a48a06420080110b402d8001c0d901501e90515240c7d44220401040070b01a01a5030071001650003a40903034810100300d4402001c0814004040c0c40e1000c2c1c0e10801503049a00303000311545000b0618109c17850540c41150300b0000c403000106801920070398044803624100900c40d052481c0d039504c02210300145411140039520032448041441002e046548980c031560f841c10b01e9040c00c4001181500810007280c104d203010b03000304400c40b1580069170200c034860303982100007680420450b0200c2e0729907511038007805 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 350704568 1250 350703318 350703323
    0x201290a03060509070f051f1404030602040f14090903041206020c0f06100608090606131509020901110703080a050331020a080c09150414010e04141506010c0c050310050403030c0507 80
    0x70250814520603076200303001d01000309d09254100808000106070f0300c080c201800200002040180c101110125101a003014031407140100108122589500208580584104444282d9440345034035104010f80182c602d01c0e0f46034060881030500701c25002605074840d1034419845c92907160355540554411805554a0406811002c0000e211741408400840946491342c0c0014090341020040392401d54103800c41034800b50005905109580d2107101e034001e41e44824040d0007a5840c1d039039641c000e4411501d0700c41c140000400041e80c0908451401401e480c3d4468507007182c0d1a000e442402100380c0100100e1065403d00c1001c2480440003881e1030a040000d40800f045841d01607583c001813042c0d21040d50f01c16181c148480c58a550544041c2c020081e0740e40900326406e251802d00c680850301c0708488010350103803038000a8400c0458949030484420300b4044841c1006052485510f500307500219094450314a1038215281c0c243d10140c0700c1c0780070355030070000da0030003a004035441d104450f0f02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 350705818 1250 350704568 350704609
    0x40c14091020010b0109170a1509020a0e01081e1e030f1303060c050f0d02030405030d020705060a05061f030e01020c0118030e010201290a03060509070f05 68
    0x8188a4240007002540807441c0303040100300c0c03408503440600c03000440070041009075160b4890300d01d00d580110191010700001520100e2030305aa41100d41d880b00200800f50010445c00c00b02040f104442d8001c8015540240c130840b100c86c0c0380d0044950300711080c13080001500c01c20040001c51400007500303103180d058900143c480300703041007503007014100c0c4c105560000b40402c00c8881094420b2030001c141803855505114003032403031401c241040300e6031400024180038042045000d0080c100081320040c400c0410010703200d44850502a145006181244041601c0044c1d02000c0c0500050001c0c032801181500740940e5440506011030803201949450b0414900e114400140d4003d420a1700c8006035440010b0510105c44422802d44c1c0d500f622210000003617890790414036a00c85101c208114003800203000244640f4540301c0701a0400f00c0c070403403184011120703090503698000203100540d00840c1c180712034107102c28040d8840d6050b100f41c2081c001c840c600003030581011089c04180c01c028841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 350707068 1250 350705818 350705827
    0x10e150604060e0f100e090a0c080f280b09090d090605090d120c0b10080c040e030706050c090a09050114040c18060c15020304150b03030d02030a0209040c14 69
    0x41c1580c0700010249050352200c0b9104d024580c035107030401803410000c110f541c0c014040c0d15180c1402482140640381d0320500307041a0002203596041609141c001c1c1c01d402c40011595a080da80d111420b85240e03007151098821316200006094640240301c054070125050001500d4140741181d4400c0e0003800d0a01180180004000d040d0044c0301400c1c0f18400134000b070281c000166503851b02403020701d01c0320340401c0349440001d044c040e9145038031f40e01000340b002c030403a03060502000b81d44d01e81ca04200c2d00c1c4695101e840d00009151300380280c442032507100700e05100ca0b00380158000e5140d0803190741e45c0c1c0902c11000001800c22480d02821781200d450f90300650341000d641c070500000d402040d11100510004602004c400b40c1c1714a0060001c0030a65204d113216031007450f0802203810b50030b4903c60124018814400464504500321481d003d041da000116003a0b4400864294090031101068440c80441081400e00c0281c0003020400c8045038104200c0400420564142c5241500035a02d05418003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 350708318 1250 350707068 350707079
    0x20f04180b0112110715020c01110301030b041b0b0d090312110304111c05010b01080a0902030d0f090b0d0905120a050403120e1f140c0d0503150315010e150604 70
    0x140700890038940c9104007450249503446c0d05040c19120850395040d60780c0003d0f480b841e49004e2040310352080c540742d0b8540c40c40d4910707150030100c0e00f0084c10240074920380e04001c005180c85a9907000060000750380c400d8841d480510703051700501001c201a00429609156065074400c98420038090008280381d160a40c1c0310743d01e0301c46100c03101d00142030304418080850041b502240502c6a40e052064001140c0c1e1144000010110400600450000c60900702602c2c01690045140e24100009103081400901e1806040319807602c01d601c40740e803500000490030308524075908555165170150080b00d4142d41211609082c80c46002c0c0e20b000014800c2c002400000d50390740d0640740a206924042d4001c86940c0700290708083c0a180c1e0030035950402d541000ea40740c12220081071505031840c0380d400d204240016540741e160240b0618200b140001c000f0f1045940120800c1c0b28910103070480f29819510510209454000e008584418840c1000144c0104003401041241c1c1c001603c2c80d030600d40303400d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 350709568 1250 350708318 350708321
    0x140108014706040801020c030d0e1204050f0a05040e0c042301120c0b03072007031e0c0e0103030c0302100605060901050702031e01020a0311070203060411010909020f04180b0112 78
    0x5441e1150710440401001841403400d0000d8000c0303568003400784d0b641d0300026000e04100c070807180085080d074011a026102c903000500544080310000e840c46450030303554400113801c001094005076480361074141f55090081c0005910120707206c09840402030078403003107040c04072181007500700c040d0101d000b8014000305034a4031200c49114400c2c0440004a41c450203461060f4004030b41030f10004034007180310700c0c0b226058604258a448101c01401106055848101e1601c17890120b203202c0c410301200d11410842c140305860002d10584440e0481541c42c0d207801806140c00030000ea0051150340a4150301c45030902c928411170354011700d003074605480c81c030040d20709400c807000c01d0342d041c040c0710318001c141c0a12060100c0304230004400140d85400c10503002c2c080702d41c040c4042078a00800c0c06404c3c010307140014416040b030f8000781c0c10324a1919000040f1081e0015070003480d085400030445c80310805ea458042d000750f419048104000111503844201111034040a0310b00040144900d006c81c490107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 350710818 1250 350709568 350709701
    0x70e01031712010b030402012a11030705130b01030501051e040c110a050709051006080f090a080706090b0601141209120a0503090601060e030d0806010314010801 71
    0x6002030802c0d486045441c82c500c002d0340000180c040000c100011980c0c000c030360220300910f9001c58002d6040401070045920f0024200034030003000f0200914050b5030410545009007401001d40c00c444400403070903009003000f045e034640441e05180010400d0b02e0144480061507040d44e02c480810480c2004000140c4000160b003000d2003940054609500014042d00540320301850003082c40303c4c5461155002c88030001d1034010070004001c0305104c41c5900811180d0092054040c0380c3c85600c0b40743d0752608000903000010201741c1d000555200300100e90f0000382070a0700039a0b50070aa551906c00554400442c4111418070460420010141d41e400d00807498200d03c184003198044407200d00c6511040e4440c110302004200c011040020b03280d010441c1300d000d8111460081c01c2c10b5080320120341e41d4810800301307206101c589000152603074031035401411101d040c07031102d05075940d41d01401c5009068424481c199401c3c46829034014902c4c0902c100040000400c156451403101202d442e1281e84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 350712068 1250 350710818 350710853
    0x4050d110406030b0115020d020f0a060b0a050429061c020d0e0718060506190c2904020405071e030903110105040b010e0703110405060a180b0309010e070e0103 70
    0x1d40d620044081801e1290242c00b9048906c1006004100750002a02d032001803601041158003d04101442c144046607901000d07a1080d00455040c02c00780024815060075085503800c50314010000720000c07611521501140c3e83c2c0041020200c01c0703a02030000c1403040340c01c92001050407854045803000164010081c040b400710700080c1111820981e142084102d5003d003500d580d01400503462414244900d40050004942c00c600c1d1048203e040d0140002d00d1441c503081c8410ae9104000b440f49030200c00b52110080d4650310600c0f04054907400d600c120545050340241d140c00001b40362140160391428003100c031a40c01c080740083e024012800342c0b407041c0e0b080301005001c040301a1300840901440d800b682c4101400c060f290305003c03a1250b202002001c64003098200100b440300d01554108076026620159045681c4d01c0c50b1140a80d071200300070031001d0086a000400094061000c400b0b14002c4d4880d100074400c5104581c00c495a0304602c0c0640440e4480410040001822320300b003c903c010b6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 350713318 1250 350712068 350712071
    0x1e120d1b090302152104052d0a020105130807030501060f0605030421120509030702040b03070605040b03060409050f07050102010f06050a15020114130308010608011d0411270105040204050d1104 85
    0xc200112846017020f05039001c680d80d0b4482d5800040d658008180c1c082d100c16000c04290260320102295036441d1b0441d10301070305001000419600114207480400d02070f10107442140ca94a0741c0745456402040320748240304050040f14008240c16120364111ba000b41e80111416401e182e40c002140882882058190103001d040748030255000818040c040c0304640e54000b0356140d4549006100c1501d2005545a200c2d4004d07010600500760010180c03820350701401e1a040d100d5076408041402041d90982c0600988660300c416940318500160340020b07103400380e0080c4540c200c0e4040c4007042e01e0144c06081c0e4026400d52080c4441c0000c0030302c03922400300c00d100110f4483e100311f0310381605290554070310200d403881218840505812400c00b0340140b145161411040d03141074080c030740c4003501040c545c4488541402060034080c0ba40300088032980000c01d201800800b00b4110070b2000d142c03117141d0101c002d0704000040d60345890f1007a0382c00c03518080d1068120f4040c50b80c80c501044900d0034548c1d03005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 350714568 1250 350713318 350713357
    0xf0c16030e062a0601050f0102060f040f02060408060a110a0903140106030813060f020a1101030b01020f0f070810060803090d0c09060f081c021e120d1b09030215 71
    0xb4a500140d401612091401d0340d049a4403840158101315050300240c0c042c444026401c0f03400d9900040c9654072184c120440d41440d1500d2800040c2c6040024010f9480580401d011445007000b0a0750360003402600307030422000d54400441611402803008c503402140303190300204040351428a0003c10078001000005056840340c0c1c40d101c1c40e0300500c00462407194905400e020168003e26001d500d8645d5000502e48818242e035203105010078122068101900d03554401c0859008004551f07251202c40107482c03030004100715460743e540603071003840c8a5210b8140030301c0b1a04814803961045c1c0c0c03e100d000c1d5103001d0003c1c040c040c20795030441c021a112280058000b4490303034035101d60006016000354881724149050754041c9840c100c0c44582c6034402c04103c00b001610f4000541c5010100c0010000240c00c040000321410410520040c0c0030044001548054001c01540030100044561042c0030403154a00313800c50702c181ca40e0000139000110440344420008510000d020b452842494051a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 350715818 1250 350714568 350714587
    0xa050c0316020a090b0904140c12010203091902180711010903020102030601080a0b0d02040e0a060e07081e060c0702060702030d0206040b06060901050f070204150e0f0c16030e06 78
    0x55500c94400341c802a1246820390085180040d21070009042e040814019a0260400903c4506000d000100800f150031001054040140298040c8040c006c2241240f1003040e0b9109020f03520807a2030303884600690700321204547d1903001000001d0b4000c1c200b4803041e01040c2501079102809800e020500c520301641c0c4403803450900034a458140b103a4009612418014009060300101505000c409410b0140000702c070340b40e10000c00c3d80f2940403280460b0354000d9030300c00e60400041c12030140ca410300300700c0600a001d80014000003160f800108942034003c0304801028200300540700948aa08910080303182c00c10725030050088280000c05107480e081481c0d00103442d10240303404a0700541c01c141c08020a00c10001c1d0a00e030f01010a44400e89070004410000700f940c456080c2c100c12190012804c501551510342c0628880000280210691915406e50500c554000c440403030b50040710340009518100060103950000083c00800328180e40707030360b50075104030300d00d204c8070780d00100b0a1181c0c014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 350717068 1250 350715818 350715823
    0xf06020c010908040b070519030e0409030504050a030f0c090506030d232b0204080c2701030b04112704060f0c1101140610050f04092d0905030a050a050c 67
    0x41c01070307002180c2c6e03425003460b201307040406203100034071400e003081002d1020980140c02c82c0c1031038804031070020b2100707151b00c2c0a80d541d01854015a801107003030311002c020404202d0300b007210700c1d00580c0e020150550b1102105c0c103844084030820b80541050280e43c018a01901c17001e010744204022041e0004e0080030132a5050b08011522555100c65401d10200450070708a05001d5240d003500641ca41424200149d0b40d40c10003006c0a8080c07180300700e62481c41003800c900880b080d003400b50482c80e07a585d6400e140060a01c10f071010b0311a00b640d80112010384c40d01581c10385228006150515920320307a81802040740500620039180581c40320003040d25031305640705a41e5807407403a40b1075040142198900301e00312a403104800c0000c440c2c0105004540e924501d54100c3c8000d00d00d0110780d2456003035144109401180e20000352542012941c0c840c41032100c5501a0103d05030045562020341c1514607000d40f058641c014005400c20002a00f1441c4228000e00c0340c4003040c14024506020501a140f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 350718318 1250 350717068 350717077
    0x2111030a05040504050f01271803081b031e060609181815060f0604120507060305060603040b18030702090f060415080d1b1208090d020304030f06020c010908 69
    0x2000210002410f100929181c0300d5684c0204c03400d4101281903040100100681c450340d82044240c9007034008003441042c25405c440422903581c404515800b5140c81c1c003130140c000640781c4405c88201c6804600b80d4400d1a42901d1103414000c00407500c40580d807400c00c9404002074501030708170004000c408903a03240c10784900c3e540306517004100850b05e000161524001c150350b109012a40122000702084029912070750b4103c0701c1100e00840c240c2c0000e0000d2171900ca00d03130008500c0d2400070011000d120010403118100c503042e1f10180040c0d0303600d1041040a01c8102c8004105869050100d4018403058000c1c0c14070700d444d0812240f501d4420f80004029078021a1110b0811482d2810000c02d42050f000d1108520640c0c0b04000a45090021180c0c071400d400c0b56132400c1081c182040d00d0f5000031407032405807441e0001960075454800020003010210f0846810070f49104d4103002c480c50520010071103003101d40000300300a10f0100c5603205400396015540c1c016103036480740c0100e0003003181040180b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350719424 1106 350718318 350718337
    0x3030a0c0c050a0606150c0201020607120e01020c0304090b0a062703061b030e120a0318060501230102060106050a05030a060e0a0f050c07211103 64
    0x101c030300d06191400501a4810401220f050150340c1e8000020f5504a82c43d99580c09400300003546d501d0503074813009006a02120008000501c1041e444000c1c000c0080c3c0840c60301c4015159500b6600561191a0f039030b00009410071820b1aa48102d02440d8001e94100c5400380c07424130047d005a03410180701d40003100c000c0e40b08109600c03c40d003075006107900c03030001c00500200a1008521324082c0c0d8410b80400c1c905003049010140c0003646450304440d54000030301d01040c48000320003401700c404007411086411b020340f80002c0d9150285c0d0f4041c04041002010280d90491000880140c48001c1419500b0101c0140449a801000ca60b0711502c3c40c00d0080e681d03100c6c0d2600c030000b40525444801061800e5081c0840960150040180580c52040c2407006071166222032041e40f0980c00003d000780611003040d01c044605541c40d010700d45440c2004c07040c7d000c0940c04103040da8012a000e = true := by decide +kernel

theorem cover : BRFrame.Cov 350539568 350719424 := by
  have h0 := BRFrame.cov_init 350539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350539568 ≤ n) (h2 : n < 350719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
