-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3761
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:53.803621+00:00
-- url     : https://prove2.me/submissions/332f7a29-96fe-485c-8960-791ac443d3ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676258992 ≤ n < 676438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676260242 1250 676258992 676259029
    0x5061b1c0201140f010f03030c080409090f0c0501021f020304151e05011703040320061801030b0915130b09041202100c12090615090f06051f0c030c0f11 67
    0xa40c181000d030886c0051034000501404400400c1d1001c2240d00011900030b0146aa0140410800791501d030309071810164080b186c5a40d2040c010807503510002d20333071003108620009910140c40d5400d81c107000303502c090f2080c0c54203406036418070406011401000255041010801101c1012032100001c80b08182c01402600c0390003c0c005180c00f1001042d03038280e0350000e280000d41c5180f8541c020078140200c292581140d40440d000400c200540c0c4000c5a0620a807820310014880304c040000e00c03041111400e65506c41e440d01c6091030f08041c80038102c01c654000000030322040c2440040c003c035104a90845104002e404100c00342c6506000f210441240d091040c040002c1c2014040c00d05801c6080e41c014003655440c1c80018000d8070313001804000c2034008808000c03900c48603910054640902080d650504044000440c1c1c1003000c0c01402d0100e10b42441901c0d400146001c444101c13a0000c2942000300e404401004112401718101c806445580c007020007490380401c1c012041580c5060000c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676261492 1250 676260242 676260271
    0x6090305120c15070f031b020a11030a0f0501090c0605071104050712020c0606040e0c091603061a0304051002030103031b02030304170307140705061b1c020114 70
    0x2480014210081d000e2001d03010391604040d608140c07408a00b5000702056650000900602580040142c001c45409036002c1c0b050740100000e2880e503c1410202c040140d00c01e818407800700c0d02ca82400da1070403000a041d80c42e000d0322902e402d001300d030f0414000d8845135901d050b95410083c1c0e8444010040059050860621a584d220560f00c201092410b40c0650380305c13400190248e01c00e2225000d004d916203411501d8903170700c100d42503482d1412265a8095490400c016540c8100040c000744035040c003c1c101890b6a403984000301c2100c0104810405168680710b000c110480c04004204009100c2d070b41050316490a4180585013a0740741702c16504e0948100014800319030300041c0344008442c9500301c10740ba200b40c0d1010078a50302c529800482490304d03040c4031046041d40440140007d90140319241d400020703080085448400c039220f41503000d034040050418941e9006003600da65101c910607180720000c0e40d03005420031485800312100617551501c031068150f0b449441290018451041a02d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676262742 1250 676261492 676261499
    0x503130806040b040b130f0302010212150a090e0115060c06050f0f0610020a020a0801091a090606150909011229060105090409061b090e240607060c180609 68
    0x43c0d82d40e00241003d41901c00d00c900280d040f009070510342c51082d50007008107003010030606009000390005181c0c030b24290058404100d405200d040032a0301c1c0c03480100030f40c84491030f0075002d00050504219800350742d5255019241d5606c01c80c46440300400003912440e031036100c0352406070201c6400401a050603400c00091050031100103d10540c01103040d2020002d5034403811081e407410900c030700025482500543e010070005019080b452803648203000190747c0c1c004c0c0c2c0900d1144c103817040b182840b00e54003142c005811454030342c100851440d070381d2103a1032902d00e0034070118407001c409030000008602d541148c4820003418800d8992050a000300c100002820400001d0750000d000d03014604010010a4044d66039031a58007000c001c1c1d50055080204003c4d100789506000142046a008200d000c600040c40c0103482d400103120345203001c01c181c40c420400f40045240d40708a010035400002c14080d260006440384103007643d00c03241d40c40300303844200b4030b968080c2c007a545034001c0c0d01008100c80f004c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676263992 1250 676262742 676262753
    0xe0a090c140a0219030c0b010b040f0506030c0904090c150e310f060f03060c08070219030503040c08031b011107080405040207050f070e0a0f0504030507060504060b030a050313080604 80
    0xc0c41c0513404030b0345141c10381c510340c1401c40e91400e017200701070210010540002003120241000700221418090180755959481c02000a42e010848404942e028104203804840c90682d000f00c521740d100e220702000180c1c072000040743d0034002128000c0450080c405d40501032919446c0101404051041c0c8040381240300d042c1400354050100d21620140c44540020091550303402c00c60180c4102145242260740d2820b000f0301420b40402c00c003002c24a004045140c45201081c0400c683c0101150003011031603607941200c041e80024025100144940404506e075481440109a0782414180c40ca80c0c1490070f1000d5401c540610304c050b405c0c0e6000b04580701c005103408041d02d01b100d4040f1070050712024181052403c01d000c0c0c900302d003024002e04d0800304d11681c4110a9a00540c8001c408100e007506100420084030b00a45000e80420001d00000d800184150401d40c0c1c46440380002258508409010901e003d49103c1f080b070b05a0030128449141d00c0d00741d00c0300e100612000e030041c03074142801e4490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676265242 1250 676263992 676264003
    0xc0f0c0918100c0e0d03050415050301050603070c06090602030f19020c0d05070c030206070b0406060b040302010c020d060f151a0f0405210d050c1006030210030b010e0a090c140a02 79
    0x8100c42d140c40742c031240c079154004c00b6405011200504a40e183c0d0105190082c05a8801d000d5403204a40360400c64071807a2117001602d0580310060700301340c40d5880d841d00640340c1080c1a0b6086039481c0d2541c420314005101d60014602419400a0728000b034181aa41520011101030b0071601483c414445008201400240d0110504582c2065956844103051907284501d858001070340103080001c00304100700350b00b11518800c50142108000799a00d0340c0e040ca030144590302c006030010708044070701800351038100801c0e100395108800002d1001c410f000002c091b00c030300c000340540c50100b40d01d041003060b40d04c00d841c042c1e1017841c414051801c40c00e040d0108150040c1e001c0c55005051080081c05031030182c80c80c010742c4455640486d0750046107094000c100c1d6105030000040d03402940307204644040c3e030340601016070f64020b0002961800a010031001424090942410031040c440d4800054444010682c0540859080400c0311007042901a0aaa1500c2003a04038a94200326041025601045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676266492 1250 676265242 676265263
    0x1b01051602030f12040608010807030b0420030d080901240b1c11071401050405060403141204060b010f08040515040819030911010509150901050c0f0c0918 68
    0x2803804281400d070011a103040358a0381d450140e44680380c843d4443d5591030028004864180d99103511a0781c031104151303207517031300c92000401100128000c00d000803c1440300604652a9446881600d03600c0c0c80024500022640d410010500035024020922028000c0c1003010000580c2d030301180800344080344254580344648500c42c1c070041240340c828207000382d08604020300c0481c241b2545484800300c00c01c9502240702147c000381814103455510b007060144030700c500d8005000e00101d640790b840c182c4d03030500d000303110203450882003003010b040514004203140580d00541002484800000c00505101e000100100601c00c454003048001200051040115500e040c01d24441da2582d1400700d12034050592104510000c10020242c45503055100000c1d50303010b145022190a090001500d0920503801141c2c3c1100d0f0b9445a034140701e540c08000c02c1e0181061400300c0c43e00014140d29411701e00712034844400c94102c0d610440c402d140030540700350001c41c94041200c4440c0e18030050345c1d4400f003208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676267742 1250 676266492 676266517
    0x10e0a140c0d02090a080d080a0507050d0b0112110714010603020916051e0c07141c0809042d11030a0c0905091f08030a0507022218051b0105 62
    0x901214070b11841d8042e6030b8444005082d010007103480301c08094403041e03403036112400502400001454035540b4000d4600803120f5482d200d10340b44190a81c500517200000c8054144a400190516022080c4c401c09404401d0711026648500d0540342c4507000c0c0e0404c41c607a42051707042100038805a40d0340b1890b65000701c0f01c3c2c4108080c0d0032240c401900c09000b1215040038206180c1c0c003402d00410240c000301241140c11003600e1081d40c8520309020b15a000c4454680c114855005080150b044075983e20100e5000e001c00b1070030142c141d00000c05aa2030842c103036000b03903200380302034110b8006044210544814040148405403c41d0310713240c60f6000040000d488140c8a007074401c1454041d04c0c2c00760152030007404450709407424001020505d204110b03400c2d00350406010000ea90040401600d0301a180c1c0d40e070b030b03e14000c015000c00031700351402010044c214031740b00c00740a01c03410a0705c0fa201c0783c10f030040917149442e015824210705026a046400b4146412400c1e2441103a030700000700d07040300e10003c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676268992 1250 676267742 676267747
    0x61c060f0b121f06050a0f090609060e030f030c0a050706141e162f060306060a120903031401090b0d26070b062806030230010e0a140c 59
    0x500720320f003c5580218507901c01407561801092030b0b07611030010500c0d2101502d4948041e00e8905040b2240c080c035100d9440095030800d000d000c894480e0f100c1642460340181160082c900500d40c042c00d5505c403400b0350b10b4580c011f002040c104102400241c0052105062142515a5030715103c1c0e4544241c02121083c8425400300e03041e006a0300085da03076003504440c2030b40d00303000e91450a6110016401250080c0d640c90302c403100d0782d2400b40701d5015400c40340a009103081d0740781d190a0010582243d59100309100e06004081058107851146100841c0aa500410050b81d41020340ca91201c0c1a08000b120904000340e03040b640d2101040d100e802c2d035002140801504000f01460305446c14908102c840003070002e904028000703840750550245100310740803021a585018602e419461200891094600084007040558044d5010303000c42c0b00c40004901d034501907010320b030b00100104400721115100c040014040c18160f400c4599100740d010308208003c0a200c8820142620010110010312000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676270242 1250 676268992 676269001
    0x126060a0903140703200708070e06030c49121e1110141609120b09071e050402090607020909060106032d0e0c061c060f0b12 55
    0x8594000511030f480c2a243d0f01c0e1001840c00400c030362124404c05e1101400b80c2044021b81303d0100c1c0030011680200d008055051130440c1c42d86c000d600003880140d043c01111811040390300c4001c041e00c44182200350401400e148902199411103841c6181485d501c40c0ca032114140c84541c4a41c1916990002402c00200001c0141200d44081c02ca58580e00c2c0043c0d101c11840303264000245c41c52b9080c000d000e8807080d0304142280000c9502643c200a4003000b0100814206205416100445c803240d141000ca210f84501160240308980b15089420303c0c551420001480d90a10003400606922550340400321008020404400030f1805024441ea9000450a0341c50365210300701d445181c3d010b8000c1c01e007407a184034400d458020900c1032001090400d020910a44850005000d82400f185c5c26400caa00a1a03044801041811b04d2184107100d0b40d000411166540070207801d442ea400c40181081064002000c8203403aa60b40c4144071004110b401840481c05400c2650000015a5403241c09540d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676271492 1250 676270242 676270247
    0x50f061c061508010f0507020d1202090303280201090b19060509070203130b090d06050403020a0212060106020d050f070b0c070602214c08060126060a0903 68
    0x4084500e088880da0781d109a5140000480f15010700030850303100b2403800380f8240e6008484d10740060f080031018907042d90281040104514000c0001070415004401203407071079000314650440c4000c1042030307416620302c0c0036044400050070b10003401420b00036600e001c1034110151200c110301e261044c0c8804040360650050700241b030000c1c94004c140c1000f01c4044d440b940000480ea05240c0e600e070300486e600e0000011601240c801801d10030219002d521000c00400c005481181180161072600000da99007403c001140e0004001501c0c5552401801915100381c0c2c0c00134005000007030044182000ca400241c40d61540c001c05040100d0f9240c0c207891640c1c1c400d190300200410710101c0d006910702e002000503010400e04840040d11510781c154102e5080034108030011075030100301940c0d10310640c0c26594110490240120304c100ba03a500c80180b500c49030301e8010354100d51200f0010002e4104002c41400108100c83d1401c46e001c8044c400310b602d44e070004240c3d400322074850003804200762 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676272742 1250 676271492 676271539
    0x7031103031e340507060f0804021009090903090e01050102071406030a06030f05010f050105010503391b06010b1201121a1f05040c0207140406080f060106020d03050f06 74
    0x41103001c10300700d0743c1024918a010002c1c00c4016910b17881203c00209195005054800c00c0c101c4507224200d10307580340d40c03c01000c2c2020080c80420410f100c9400500292075008540c49148241c070703010b40c0d00c3c0c00e041c0c10b2030348170314143d02041c1150322554040004600302680d02d8064542500c2c515500d40d900508078000e4516940003d00da80e00c0d10030803500703214041d840140707111124101445166601c1c801166903000c02d45500201007010071410000310f41c2c540a880d140f546604509020340b4201071007a41c1d5030440d099075030000b03012444184080809210030760240c008542c03914145480201c060540d90b50500403010038008551901c414400c1c06e0001d40c42c030048543c00040035103405082040c41220385d074144402002040400714283ca494000c0d00e0248840d07034020b0844501d06030ba0307240c0da000083c4450b60066030b102000710311010244035a10602260300000e025552510b07000034908215200070b581050718110602444a600880d0650048003c40e11004512681041c1d440d40d42c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676273992 1250 676272742 676272787
    0x60203070302012a03180c0e0708070c08030703020307031506031e0207031b080d0c030204030210210f090203010903020106031e020f06030403121d250e071e0207031103031e 76
    0xa5800c187c0000b0103407001c045291080340c103a61410400c5d20754070400d80d00051030500042000ea810b00008503a54803a6010b154029140c2c500403544d141201c031411403440041d0000800251101211040d200c00d091800315100e5480b141113107000a42d0b20003d01c003806540e41007422184d100303001020301c01a28281e481501d15844200300d5400c103140054001e40c0a80300c2203014000c140c0303406001c10b0242403446044189940e0b09100162035840c000c00030074091901000699440900c2c20160310244100b1345064480d40000900a0450501901034a00c1110303098080300c842600703c0c0140ca440c0c25022400809650302500d0b030302c640c64181c0d108890702c1084030708280740c505a0b01d8001008503a00140201000a80d00c44841c4500e6191a045020401030b02946030700104214084104a0850344600f1900d820405d11040c00d54040d010160480010b0051307102550503c140401d00f0311030110a2002ca00842c6041060b042c401c500160348a01032196000124505c0c00c1e9250020400c4003c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676275242 1250 676273992 676274003
    0x1b0d0501050a02030115021506011803050a0803070e0604060e060d020715090b0702010b1e030a0b090f0d05070b13061d150a020304020306010e0901021201060203070302012a0318 78
    0x4a1a19240000c004d4000344103075140300a01c6810710110b5400481d40348410502062014120750724200150752800001d001d1191020004d43d0000100d41c0512400443c1b80c869040b60750390f401c0006c00184140340b400801ca00c14a000c210030464030360400300355202d1761416210991928004003800c03000b401340700405040c51441c2e8800101c14103d941c008240503100342800e12860320751403400c03401c899020641070b400c03920f524143d20042c11071310340d6003032081e400400316111007203a942c0361100124196100d0041d64841542e28007284030500405200403c01e1134298101100ba0b02d40d000d185201610040c619112170341d01800f401140e2b00082c910f00d20900741c0500c1340b002d51139001d94030300d08000d04c40414460003020804032003545c02240e00541d0001c00130441ca07404c01280c0c21502c540502410b01c55982080b100102c403102c040d18034001d0100741c0186488800790b04010f825120000f44920800e044115009880554622011403039040d6180c00a45034600c0110710a0948840307001030312 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676276492 1250 676275242 676275251
    0xc040909151802010305090726010605100f0f020a020108010605131a040302010e04060b031b0c160e060a0602190218010311130b0105070807020f041b030c111b0d0501 73
    0x10b8881ea21018104580c0c400c0e0380400090b6603401015440d42d40030f01034030214100110841907054003440510081003516000011074961301c01c0044c003108015440880032441c550711208500b07402681c0548403090a0028160414a69000a0004405000c0c1c141442001701e00c40d008103808010350400340000325804082c4542d0304d03aa000315901300c0c0c80103c0c002660082d8030b0138542428014102120a60340450f402c5481c0ca46180246a0300102007505400d8103212152241c0800c01610000700c0000e501e80d0800c6040038481c3d1240c98000b030000d401032036030540420034580c0c000380e01c440510140139090913480841c80000c914541900b1a04200034410001100b807100c90010120618011100021801400c0c4101e00030746002080c1d0501181060201c0c1011950440040c08038900c024a04a144184440024111440c844807010940812401c08030015010310480e02c44400ba4201102154920342c0800d07a47c16030345201a80b003c0c290b1a460b001906c4408507442d916900c00000d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676277742 1250 676276492 676276511
    0xc030b090108071503020c0a0b041b030b0411040203060a030b071106041109070207060c170c15220b06061612030906060e0618090c060d05100e0c04090915 68
    0x1039a0304081d0050060042442000c0d01340c1500900c200c2c0d082c020340c900a0040345150b034171800b0305034074014002e580c0d0104800614540001084903000998400c8028110310300381400d01d040340310116003080c1d005e144100f05110701c07a0740707030104603080301d510186881c255500e0a00868001d2038141c0840018820380c010300c4201700d14000200320801054421022542d90384c0b0341240d69041030300c00c1c9000f003580c070329010002c6020b114620070400000181c03a45031641000a2914100341a00c0d80140240c4080a200138901e40140c44008012070840c14064070180d0f0700c4500e81240040e1805118003c00591a015916029030442c2d509811084101d07550031142000380150020110884100389030090205490340060f03000d6000d4480500312510782072134040c6c036601440c405400440c141c820705c05000c480350b0b500002061408d640d140d020459007058401c4903405020f982040522042103c01c104801008500346c03021502400400b0503440c0090420030131081358150041e211608110008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676278992 1250 676277742 676277759
    0x619021209010519120e1b0a0e19020403140109030f05030c0a0c0f06051e0f01141002010e03040801140a020304120f2f2b14190e180603060402040c030b0901 69
    0x2040310300d140e0f8079000c210541c8a0811010702360f14024100d44904c0707000469803504c00c030044030308007100b29100180350640341d403181c0d048464152510380c0183e4481811000b0140d1051075010845042e0412608506106ca02140345001d001c2c0740104101038409214140044058101200ca401400420003420003070715080340807105010500d02c80003000007249410388032115440c1210413494041e6205d01205040000c00d544401041017190349a8105512000c2c0034030042c00140a08800042c1481c40c541e1034001240c001000b40c01d155206008100100349108a10940b091251409110401140741c1c01d87d2003194043c4000002c00b820034000302902201406a40c0c006811400c550400810000c2c0014030b01d9800c03100ca0400045030000078403507005035100220880d03059801f60070100300e015008002c0201040d204009441c108080c2c08604000c5a4041e03079102c01d030b01c1140e0b0340c5000000b1980c1e802000c0c0000380100c4d50350641c50312041c1300343e21a00a00c0001042c100840d40d444a0070f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676280242 1250 676278992 676279003
    0x30804080c01020715080601080402030309030105190c170406180b0403201b190e1f240c0606031e02031c09030609030e0619021209010519120e 63
    0x20360161198280c04142d9000381000c40000c04806d0780c4030812561000011155000050310803070705480144440310b60781e5028042c2e20f1044040e0403c0c41c250740715944031207081d80d02041d0950207200d00c801410039550b004904850303226800500109210201d101e208100c0c0d8000c410142200840000380410194048036580c020801e070382c44030805841c2e458215480740d800d05c10203103d101c001c807070072861402c02440717000b0828092102c0c4003109540e4a58040c01c0b650072a0340d0900e0362540c076405521841c50001e1600079001032030f5040740740c01c1b90034a03400b002d40c058032510051003058031004081000a801460207141e0100b43c550b05031603111140305260304024401c0b84240204203030103000c1401541c2c005000413690380c81c01c81280c50350f20748100904010f141030301002040d5114206070341f03858004141c05400c0c0e00516051076000107000313090010044100b01108400c0141192603079000017030750048040d151007804541981e000682d0071118400d8540070300c074100340481f0300604020a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 676281492 1250 676280242 676280263
    0x30408030d020c06061f0e0103021c090210090b0429160308010806090705010e06070501050c030702070b031015030b03010f020c06010e22030212031023151303080408 73
    0x4613401d5403078020811014180407001030f0780e08092503400c40c0586104500c0d014043e20181801481c0030010500c20840280c01184402444d480300c2d07441c800c5040980480c0c50f80c01c900e182448850b070805011120a1145109101074840000c55104003420031481600d820a480c02150f6541c0410140092101c61140000d0707000c42c3e581c200005901102140c0e2610a401d014058030580d400c210040d91a0142100c170950802001d104000020f0001d10035980200e420090b02c0e6220318100c0c500038549552070704040d00104040c024804100302d034aa511003996206c0400c80818140110100c0050006c920640e44c19800c010b101558015194002c224002512056445580c2c850005910b429020303903a224551110340c88616000d849812695242c03482441070b00c02040711840c800146410a543c0c0c40c03007041c0310307c1c410403005406282c0540d400c40001e03100090030003101700040540c042d00c000d483d5040800600541c8801003200e400001d07660001c01c0c0c40e103071a01d0300300f515981e800325003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 676282742 1250 676281492 676281517
    0xc061207020f120a180e250504050a030f06090c23030109120c050307080415080601020a020d03080c0903010612060509151b040e090607030b06120f060102030408030d02 74
    0x4808001c03060041030440c401210303d1000c51615000100440301ca29040f941d401c550320210030007042c00084403805901801040507650105080f078002203070801071511105050020400c42044030740c442600d8201166008500c440e1243c8142c2806005020303102402400890140804100070340222021510091400700755100c1c10503450a15080354454200908201c2d03d207082070120ba441051501285441503090301c0c200540c55444103d00c2d0000d412209140800c90342421200b40c1c80b0b03405d5580030500b4802010001d10030340201c0c000c502c20042c003400700720841000562011581c41150741d5144054001c00403a6a101031540c1c0c00b8201c0101110380341d08100110b5600c400014114681c207070b01842c4d0140d03e4541c0107151030112405014059101814800003a49808021036036120712120400303403a1070320f04000014105d5a00260351031182c82c040c402800814416039500380d2020014907100101c0e12030600503842c0d0300030381c1c0c08181c01c2c0c8800125200d01003441d8002d018a0a050b9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 676283992 1250 676282742 676282753
    0xe01180e011d0601080718050c070f06020405090c19033602150a051c06180b040e030c10051b160c151205360613020a15020c06120702 59
    0x40311601d440300201d104980019500345840ba007561f07401d0740400e4000d903050300c0280c6000c40c2562040c090b20b2170000c090b15041e034080313010031441c10541100c60b40200c008208c1c901e090003041030200d00400292422040541d544181002003141002c02882e1590014000c0394840034a2130740c4c503050081400881c0102c0100c2f00d00e00c4003500c60400c4c2c2c1c102280b962039207400c2c40243d200350030010b40c0303038105e6180c010303203510002440f1003501005040341405542c011540781500d0083c842039a1501144503031960080190210f6010042000c0c201c5403509803011885031112400c0d020001c14903000601d45150002d640704204241103c0071601c244910011b800c642d40e0b52034040703c3e03603114001950100c0c0710342e40703202070300d103059841607078407820250b01c00400e040000c0b400c5440002e0780c05000c3c00c1c50300d0102031802c1d41703000b04102540b020800800c4605104590302282d40482c0f148980d040800d90f00c00b009038114024010000c00e410040e024545900728400030a96442080d9094000360042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 676285242 1250 676283992 676283999
    0x30809121f0f0c0e0d061b0c06200d1113060c0210030b01050a030903210c031404020604030b07090806151503041a0c09031c02070f0e01180e011d0601 66
    0x124054521044103644500d141c1000f0413003840581a06110210b540c41e03500c00000c444944030611210300e041490340c804100503541c2c5001004c860110700880502a08113182d00040c484650031505d810004240104145825418100303160095188a030f003444028503012503101e03030180e0900350f914000c41d01c03012143c041c43c40c282d003201d0090204500040f4104010440385000b0780082032500c0c400c3c0350420300d45202c2e0310042d04845141045400c1551249034110656925000f00056034400b0100c400003803d003a40041c05a10681c4002040307201c48000103026140948101e01c01012500305403052031070003501c04080b4002c044202c900c983c80700d2402c41c1150060409480c4260390005104100440208219412042c0201500146141000507810a8405002c3ca11811150340030381c045141c40240e0190910b00180c0124034440640d800030492202944951070440f00c81443c10304200c0040800c6c100617000511821000350300701400415990003842d00e0444d007100d1201a00d803140d07203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 676286492 1250 676285242 676285271
    0x60914060909100c1106040c050915030613110a0b070b0708090a021e100201050a0b01080402010f0c030c06020f0d0f022a0f0604051e070b04030809121f 67
    0x2e860200e002e501c048580c0d02024001da1050100c402141002500030b82003942c1240352000071102200c490342240e2042195092040405802c1075a070481d070100505088082642c4200080c40c045022440345038820600000100350b0a154a000c1c00c421241901d41d206080160301954088580d2400900095030b0107205809150140640e40081c10354044070703808010b91100c1c1044019400d485075000304907140d0382e40c00044600c1c0c0540d000030803132303142c21a4148225621403c2d81b41c1807108240c10040181e03401000c0f003080c041d190420154040540c20121004050741070b0081406100003a0743c11203408510142c21441c90703c403030070300c91a0314001c0d035a01a0b0069156850404030484e4550344104003005c44118424900b40840e022500880c40303152400301c0954064940d90480c1c0f681240c000c805d04941c0208034402c40041c0151454078200300c0d042d1013513200c00303001504041624203281e40c0301403218210040f4070f02141c64083c050700b0a2a600001031888078007442c548001d080c407440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 676287742 1250 676286492 676286509
    0x8070e010602070e070903060b0f040608010e01050901150302060f0c160302032509090f1a011505070221030712050a030f06050f010e120102030f04030e0405270106030606091406 78
    0x2441031b501d4622071451503840710050040c482e05580d12101c0030915845030707101d5220740e000074040d03000081103080394840ba007400c403140030344541560b9040a5018064a502c1002901220b6040c0c8081c0c2e9030700c20100d50500140590390302c041c1103002d0007154800ac050b158209a050300d000b20207a49602c0e81110140402031020ba41000318059841d104100140311644404174950203a4541c22007141903a440d00c04402e100d01071207524003451b40c014008018002d041d460b00305c0c018144140340902030f800090f03021140399549100310042d0030f61400400380038410340c5c047c01e0707010118850a404407000541250012801103000910f40180344d40c206405000d0341c0104c8601604103880413030640011a20312000b41c20307264000100984c2048401c0c0f00b44001d500c5070665501d1003500381018a8000c0402820f40001ca101d0b07810300b01448000c540000c00d244843d00400c1c07034079000105600855000d08100d0344007504043c6040f030006103850054010400c054403008558002d50f446000700240407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 676288992 1250 676287742 676287751
    0x115030e1507120603020a0e1503030c150406060512060405010b0105071502090402070c0b0c070605090918071206061505250201050904020301060c060516020a1b08070e010602070e 79
    0x840c0103201103402d40380600321601016002e003a011400382d0f00d035000b055100d1542e0f80503812243ca05810010307000d03010b24050103c40b4040700a1460310032201c00d00c650b503003003024002c0014506507001c80c08001c5541e001038001e01c005000319a010003c010700e60b4864400b1038003501c0950070401e00c280a50711410880d5038481d444280441812403844c00744009401501460b500702c0c0c0d00f04103000c0032401c10380d80c100083c08030604807681c0d5003c1c55403c2d4103060b5075622a0041c04000d0000c400c10b6601c254145500485803501c0c1c0c064182150b4100c0e19007005a4030224048002c00114001d0255640290042d145050f80043c0c04c0c890b800c8040707440d441003820441d03c5a075840d031014900041c4400004103a03005150050420020708001012030740282e1160740030076011082070007004554041d4590004181079130302035003001408043d445015840005001c070164100d040c4055003070704072010240c1610f50448070700070780350302c841103a9807030070701413000580316040e40040c4812600c640203103c3c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 676290242 1250 676288992 676289023
    0xb1305010b120c0909010b0d0c0806130c20161203020d0503070c060c08070e09010f0b0703120e01060519141203070f030905011202031b070302150115030e 68
    0x300005210440820040a0240c04143c14100700301c80c150f5880d401c1a40c0640031481000d59100100242c00d421110500101400d00c1814010040b4680c0c3e406250955801d0b4a007010a40c3c0c1da031010100d541744800d84241918400c0701d9501c81010400040c031164035500d5820240e840d54641880314400c00100000074010382c003490301901410320403805141c0100c2503062540d8146900c0da035a00655200b5001c0c400096032010401803925031020104140d02d90540700c0000315414220400429a00e5020741d2064020000700101054440d20b03008217800030f0707010100180410304002c140031b09800d00c103a03481401c8100004aa103141001d2040071551003082443c0c0d210f10b514240007101000500b0b81095010910000300410010707043d60620302e01c41d80d10400420304050001d80b42c01200c0b0b43c0041014414001c100340242c401c001c09016001b403a06150b141c49481c90304902c2c100d4052010760040c02c258000140f01c41c41031709112884041c80d182803011029050345680d43e07a440d01015200b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 676291492 1250 676290242 676290247
    0x60f06130b1e011110091e02030a02010503060102030904090b040c080d121814160f0b12060d140303090c010e1c0c09020c0a021201020c03070b0a09060509010b1305010b 74
    0xc2d5064a10880e8140042c1030106a04d103c10404d0782c102640d00720341c440c000d5151000c03e41044030f0028030101e40b1a0010900c1c6060186c0d4020907603603c480790009042c0132001000c42c103103a00810035654841001401413090710300d00d142090f400c940c2624100d0704c01441e4500840d01e6140414101031a03440d651700e10003020103000d00d20000c0c0a00e0340f034820f65000f107040e0400c0824080c40c05c050300042628020f0642d244200f10715500c070080b643c40502100401042488152034950031125212a0b408600c0b0043d142e000016040101c070810080c1041c234000c0704c16510b02d902001640c8202841010785907030501c520019500c3c0c9900725911984003807034400c024190b070708030031500304003900035903106407015102c400c10004c90340721000001044e40305c034860504601d440500300b5030509100000754240408104529a0381c0034000005141940070000100b4040003540015902ca40110091140e8209040039a00902d031040340701d80904455881090b900c01c4034014203040b1051520183d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 676292742 1250 676291492 676291519
    0x306060708070606090203160e010509130f0609020408060103050c010804020904060f0b12150c28020c09010303030b0103050f011a0f1908190e061314060f06130b 71
    0x190315030003060102d80f410758a5201040f00c280500c040c6200e81800045041c101d522100081c100090303494105041040411055649803507150200034a03000000c80802c000f000d440c011b0dc0035204c02d401c402c070480c0c0f011400244800d400520305040ba0b004106440d040b403440c400440700000200c60180d009a0b00c4008540012007680c00210116216000083c1c5481c00d800051804c401c0030600b440e041d80311080c8803081110001002d50010280c5120b68544140030000c480e10a000ca50b45056103035003d01c6440d03c0c079000b40914064148000d041c40303803940c1c5030714019004050440d16035002030310b440006015038002541c7e503810781d4260303a4a0081c600005200b03d0180e4821094103140350020302111403200581c0e1440c014040454603050300900c0d1058028500700e11750292514818104400c0080c501d80224486400241c0902c416400354800c0c1019a03095a0010011b060341c440c503070030040400f125010160050b40102d40e03034251010819016000d40308513840c2d00d64414441d51800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 676293992 1250 676292742 676292753
    0x30c032703040b0d0207060f0608280b040201050d060308042d03020f060706060b0405120712120c140a150608060f04061b081023010f0e03030f0405040b0603060607 72
    0x14940440100d038050701d001b2141c1d580009580303800a40d407980720f4440d00184880e5205202c08035601d21800145c0a03201074400724440f800c1c0c01c12902414020200000c80c0559100e0001c4a010030620f40c0c044c0691365403442c044070075034014030030307200d4110041d903e8032180c0c0541584100f4100d4a895000c440a0850f000c1101c902c8452180070ba0107401000024009111402100020440301c600700343c40701d160906110f140d00c0f601c28003141c5a0452107040c0404450004808500ca03001003995180164100c01a01c1c0302c1083c1d04003030001031210034900c5048200007100d11185108005d80f50180c50030030040c0c42900c005000306061500700e040080c04003c101d2580c5548580903130f802080300c40c0c10300c2065040b6200b040082c000070713010708100500e6040100a0701c0052040e003203501c100c0140c0d48008a9514022242c860400c41c19030300b00c100c240d10480b00c040c00c81400409603035681c07180b22103000480d481032040c07900035824088084207918205064030301c2000058801442e000305030382c49 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 676295242 1250 676293992 676293997
    0x21f0c06050601030b130e0d05091c0203191b061812050a08070506040b1317180411120c0f0702011115040609021305010612150506030c032703040b 65
    0xc0d20b040560316010281203664804103a2000c0c0181c206c00503015101e0250b6a05298104041c03505000e010409a0344948034001d840c03024607a402944503072070140380b0009003070405519a20006100c4c1750038050500186220071103610450680103d20183e484e0310664107e031038a0106411100101010006001d181c55044003492150702030750040740c1941e1303e14846401049042d01e055105004100800068034516500061280c41000004038903a481151182c05070001e44c04842021500054a4030f4020ce406041c030b43c000c1c01809408226020203020742c000075102c10070054160086006616800101e91050030b90100d1249004526001513401c050789900185291040801c00880050104c440703600031482000003240342c85881c010004500c0c1c0e40502040010711b03140040000301d030080d02d205040c0000c800c011a001e44c51842c3d130004a10703c0d80c01150400800410000d1042e503000085105105e4000040300000401540355044503900011000e03070741c4200024404041c42501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 676296492 1250 676295242 676295251
    0x519080706020307053c070f02042a0305060a0b070201050706060f030317060108071b02030a06022d0a050d021c0b010e04020a140904060b0313021f0c0605 68
    0x4000e151040300e03a00d4800b00c0e4000c49180e00002d0010500380300400b00d40e0a8100c100c0710240c00011096085000c40e582c511100c0480060108001010000c202c1e540318110800c6400900070446821664844400e810040304900e51000056940d0300c42a0301912603503004a0000e8102c0450300e08021900c2902e0f48045403d906000060100d4000201603000b910094420340d804030704a249980b0b00a40320840d50046015840080340030414503076404030702c0780ea1045080c5055824410406900e6a0ba00c14104001c0d40601803402c01c00f0601c4032a0f0020181c0a8076400b02c18100e804941c401c10510105e82c07031720355148a003000003c0c0964403c101504003454007910041c54590088140084042c240221031512134407845450002e613006908044041c0080e0360640c03800c4404a001800c0f030303a200010050030304011031445138a0300d6550002001d032641c02c03000e55503814585500e20030b034101240d00700d200b041c0b80d40c01490a000040c0500c0a4500e06440300003142001707903134005c0074100040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 676297742 1250 676296492 676296503
    0x603053702041523010c031d0103020d182a030b1e1806181e0106030206041d010b07110f03010b0603010b0703020c030610030213061206020c1005040519 67
    0x200410800d0003c03003680080180500f003408203c4440c81500344020b091001a041c44000203010010a400c1f58070015003a80c2c00e25000c0e8101e40c801c0040c0c0080c05266a40781c0307220702d0703c07003200d8411480e030340004085806804010780ca008014540030341d00c0c0345000801295108401c04000103418440b013130390400f140203161156000c000056450610045850f403a49074580d001070320301ea0000b4403649821100c0b241c090b508402c1c4261030b45aa80941080200c801e80c185428140c20110030f501840c069540100a1a5159900c07115854803002d01401107000b050544000120540e6150441d14500d5001141c039003c01070b04410001c1c954220426280c0654070f40b6151201d076034400c001140038003500544280c85104a0030002d15054174656414001c0c0c1c055402e1043c9104104250411260304944580d0002030b009000030180444d944964920b85024a54808110740c0d9000352803416000d900b22860110700540c0b020941d00107540c0039009800020708800621001d800040402e405031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 676298992 1250 676297742 676297751
    0x30a05130509040b190504030f1803050102030a15061107090b0f0907110c01080118091511070618031403070c080c0c0901050a0b0a1818060305370204 66
    0x1680400ca2664040350115110307284c450404c4540c91039101c1c10f03003400204400401c8149010b81e0040c6c082c4480c07150721020300c4440d603070301101d04210390f03501c00145038098005d5440e0b080100c1590f025100c010808000c5100b10000480d400e8404c4404804a0780a1402050401d01c4c0050300d00c000d211038a0340320f80003d11940440e03100d40722070000318060800703507480044400c0c00c1408241000c00c0c0c0490341d410844120010090301c80f90000019010100070740005a20340d0924110441c500403002c1c003a41d090821024907034690807500507040703407400f4180070b01403840c854000740400f81c0302c8403005000c10509080c04584c0480740e0051503000341d43e4185201422515103440e003668100c0000382a09500107109a5964109100c0140c0100700c25070310101980e0414a54006a000d045070031400c00040ba000300c5070900d04410350400910740c0c2101040c100760440303890000350501c1c1c04203554a02c20003c0c0d101c0030465001c6802070545070b0b0a01030300305a181000d505241d4a034100166072141e1503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 676300242 1250 676298992 676298999
    0xc0e06090115023a2c0a091508060c040510031407030b130f020d0b120d1211030702010e071e06180b0309151b04033f090506040602030a0513 62
    0x2e262030030b499074034071751242c20012214400740c000c00d00000d181c21020710000b00c044041521165440303029079070101808150004082492951459075520200d1548124024044401c2000740107000f500d105991024010b4540c210903003d8840003010041120820703000a03d040b4865809888114030050030300d8a00260281c200302030b54240c80d050039420b80d00050504440b5401c0c8900b03402d52506075034000c1c0d10b241c8040c606444106802160080c401c1c038100d5901c100041d0b41c03207101000d03007603030000c0c3d181e003061075009000f04050103504181d4414802d0100d00480c61007114103c104500d04070300c0e051b5040c50001c4511405c804030071050004040000b00d0700c41c0014001e0741c031503001d036002044100d0b81941d04041140d0b0240c482c800381425007041d52494501082181c041e00d400c2006400c4000300100e84000d00c0e02500c070141000c60142240c0d50010145a2800015000300d40c0ca2074a01521001001007034812442f51602681c0304001740398040740a1030181022040e03a0701c074109042e55 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 676301492 1250 676300242 676300333
    0x1b1106070903122f030d0e0a030f1101060b0406110f12030c0a03060e042a0302090a02180409200f03070905070909140703060605160803130c0e0609011502 68
    0x20311107840c4c02580001c0345d442c1140c0418828092540200c20081107058095100275104030507085040c000c00a90010b085a0a8400d402100062410a00030f50382c1e43c4c2d960f40028002078544400000c140181e170f540e00d89101e00000e03006011440800000e1964455030a8090b07590b000c40c11003c01e040c1c4a200000d660300c070740905184140d0042400518040c2c0c044940000c4c098050301031901c1c1c100c6c03200d080c000b58076030368076159201d151040010381c1d0f00510a5198210f00c02000702980c0b2904240700d40b020405544484141d402182607103442100b143c01c2017100b03465207101c07010b4040e03019290030400308041c3e0700616041581e6060203c1501e4450402c0000d54140c040d002044c110032005020f20709605201e0280148418600141010121025012041c00c105009059601d0100120300c41610800c40c0741c64081e48294914601503480c14440c2c0c2c03d2500300e400c244511003200c000215000c410480a090b003146038040c02e88415208080055110080c8110070240250f0800000741c03003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 676302742 1250 676301492 676301567
    0xb010207120f02030607081603021308100e010f020a0c0f0f0c0f1806030305070327030506041103030910030c21020903010f0b130b041b110607090312 66
    0x14091401e0110551060044c145030001c0504000c0811003298200030350002c0b1810035101d40300e054500503955004840b002001000b0b1604080d100d030140050160700403c403580309100c540c4d9100000c1c8607503100380f00d1035404c0340035400c40c0201080e44070300e40000140c90120700e0540b092083c001807810303103401c0c0c0b18545920341c2a040900c102d003030344a081c40300e450807030002d04c140c82062106200e140d0840e50024114000c403100182402040040e07003220a000e0305052030043c0c400911004050f03034a0525540c0e84070f041d1019035103030051f40680e0b040e82c1408812940a010041d205000100c140c2d0b40403030003444905c1d4108100503808846c025210400c5400a405a44949e005a1112850700403d82124100002c08800340c0c80d00541007401d072a02c401c800611140c510000402840d004045400b41510076001500150324085001c0d0180d0024a2040340240300c01c02c48255690300c0c5c606850082c6903000280c40b50350000c01050307555104038504c809190702c43c5101c0d400356045100e104801c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 676303992 1250 676302742 676302779
    0x1509061516110904021804030e030102031003020a0510210e190302010e0a05120d020c070b0a0f05040e01150e130c141201050d050708060c090f0d02130b010207 70
    0x8058a008034024005202c8860085040440d00c81040741403a034001410701e5180c4149400845109000805260140b20780d5074103244060004c0d0750b24900700c0c44050044100f40000c030b21910501c1d8000c181400c003e00002c0c50103403540c072283c895004c01c0e0401942080e907241110001174856100c810380840500001145000c0b190295000910324035000e0b00351741d524001d83e1810b50189460700701284000980701c84500280c40700513036410410001c00c01038468070741008541e02c124040050320410030802041e80f50600e075100d0583d05000340f81160a88070340d01c146400c4a13021801413000c40001010410140c6407424400080b01d80302700811141d90311007220244569075041405d205680119003800302c6d8841024052502080005c040f00788041806247c0c0100345c155034003020070004005a00141011030101c0d50b451070400e1510129034401241d13540211080002c1c0d0441d410414560060a513009044506e041002014000104215410181184504a400034045210f00103142c1d41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 676305242 1250 676303992 676304017
    0x40810050105040b060703080f10050307030c09050f070207031b051807123b0f07050109050109080d080403090b160b060d020d0b0a02040f080606010201060e15090615 73
    0xd5890b00b800c1100b15400d1411140c0a082e00701b040e240000d81c00380075194025070480201c0c0300c075140d03112081104281038210036014801c103140407043c443c03138882800c112809500c0070310680e0307240010349404103001e940540260344482410f10024000004540640700400a441d0352590b035500000d8602e0100031882a203040c469040c0002d1a501c150100c115000c2c083c018400700e54030507045610102c120741030f1400801c04100d07003001c2030f0200c0180351101c1005000c4139075403214a62000e4540d200d0744100b501203900e00100154035409801c18008850400c0090110084c543e54140c0f0040c00c010022020002105070105418201901130b1510f0f508440d4002001c802900d0b100d0030b1001c024103a14031400c4103600420041c0e0720048543c4925034090504e039520b485904280000e4000c40c0c0188072030740c2c0310b524041010000041e030148500d03c268000c1c01290b582e142c109821046c10b82d43d50845d8492028030f0440c03401c02d1602544c0180c4041e0100a4019a19500319110303003242158040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 676306492 1250 676305242 676305251
    0x3020304110a0b03070c21030e010c2a050c04150618061e181d010515160609050102040e0601120608030d020a0512040615170c010e041410090e03030c04050f06040810 73
    0x4550346c9c02d1003540055416170030302c404210344038801c451240d02035441c4c0c0c440c4070718440381510070404203101d0610390303080c0070348140700a8403040003a007844803090040d03000190101001031840c050704682c00044444a40701c40301c01c0008203010840362100f02c40e2110600901114000f0100108410f89004181e8800c20280d07116544440965404040c2e0010380704403001e64000f031800110a08441d1820300d40d03000706484011501d80386020300310402018100e5480420009543d100031400e8030300c1820300343c2e900101095000447c808481c0c0318040d400c883c1e070051146e0307900c240055004001ea0b001c03d0070a2820701c601440050180f05003118225200c03611143d020004e602400400c0024101849800083ca50541e561a5a404201c485181005070362503c0d0005620381d64001c184222156034840214542401c440ca000340d854410010005d20700004090940404001e0301d0107542e412036954505032400003080711585c01c014469a00c540100800a001c0b00c0420821551340c03100d003408a07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 676307742 1250 676306492 676306511
    0x90d02120d1206210203072d0510020705100e0405090d030c020a050606090c0d090f12050403021c141c17042a0801060603020304110a0b03070c2103 65
    0x28100030115480714001802c0c0181030014400780e20b410040c06503800d00d4036201314030900010b0729011943d0b00c6103000d0341140385106540030b800100802d190716000d00c41c0031002d41d600c090003650b800e8503162400503007105c2e8082c0514a0000948500840a880d184250380c03268000101150300541e0104013a0340000c0891a0551301809001100d040a0014092480042d103401c1e499401c028200d41c810040d450001c1c0060110704107544210078130400400844005250a40ca01d4801c00d030b055929405040d500000903110300100c07015283d002d008024414602c0010b4503800c4540042150b28070001d807944441c0c00020031034403001c180b0320a0440c043d1004900060104008004a58444c1e49490108808144800091900c00c5075091003900301185410b0a00c0e05402190410b200c25400c0903c00110746a0640156018034000c1681c600001c0086040005568051150480c44c0b5030600c0003416460140c13420b082003502502980d08619410f0207034550310602244038802003a501c0d2244d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 676308992 1250 676307742 676307747
    0x11041508010b09060114090102011d0105091e0a08031806090a120302040b040b0702030a0b0c0406030b06070b1b0c121c0b01021009060e060a02040305100917090d02120d 74
    0x42d1440c020a071014892401c0c5000000c01c1008124035114405000065104041c1d100b50300c400d01803200038408010300005045490302030502511030204910070403000380d1b480304080c00c405026040b4140149007003a00c076a59100310b0342004141c080d0307000c9000d140380388801d0240222486160008003410b501c50746480d10949030200900e0341010144148070521400f1030300c0c1c0407101074445001040d41c4410f40e610009151240e03041c4011f01000002040c80030803a40710002d8420340c0c40c1a1800d010031f40c041d00a101c101c0c0104c08000c0c210280710000f2a003544070035130b000415100741c1501e481c44e00a13503c441d40e02e00f5071502880c004241e03001500003d03030365100d8000000c40603852001d1280e641030000003547e0303030350403801c51766800d41e47d04840d1704000003944080c4601802000340d883ca85400c8100000940240c442035940d4010501c088000050b1803003815040f41e441001d05260700e440c2440840d40d034101c00681908180049035010169071100e920109065544000300750320300008000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 676310242 1250 676308992 676309001
    0x1c03081b0313051f020405030c060f0915070c08150a0b0904110a030b09011b0203070503070809120a0615050d020a0b030c0f0408010c030c091d041104150801 69
    0x110450394503110340c0c6060a041660449400c044030545104040949082003824030381d0f2250340b070354000f88800411515030381940181044030411400d8a1440c040241401854800d0112224094408015115191400030b82010384004280e01080c100740c0b02e983e502c3d28440b01604402d1881d8090600c411501c414044240d61003000c05106201c1003040801050b0762000c06440101646251810003c2a07251000c4803c010342d000304070061103041444035940200342440d400035805001011001c0e81a0000007124151984000150310b0705040342c640c1c1c07401d60048005240e0100e86000c048d0000c4200300315000985008101c0050241020b4040c03882020099000c42c0c006d080c2c41c034001c40584e85440b940302c02c8511107003050b503403503440002100d00c0d485600802c2c103003500d000c01c01103414901503100e4182c2c541e0302d8400b00680607000318203696801040c03046108041d9011002010451030a003031130b801611034034074030510032100e00000e42554618100c240240c0c10620080001c000700340207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 676311492 1250 676310242 676310251
    0x903060b01140703030b04020d02130e360a0209150906031b06070c050409080a02120910110c040203070e0f06030105030a0f17030c070b0a050601020d030f0b1c0308 72
    0xb4a400411010118205507003d040005420705984030b401016540380c9404903160060b140408543d03440c40c04490300646e10140c0155002c84603c540080c0043d00003203450b59520415946801c4461282c40c0c480076001c5101ca00030b1303858084d0440082c016124500400d00400c10030b9841e51074020900184444120b000f402c55220b54040d0401c023003000300c05507408403002c8040c1c80c90743c1e481290f420080c0550741e01da4030041e041440e15029000b8003601101808031101d00c3e0f803d0711580b8549512080c03e50148907146a0300842242d8061a0b0500402290030100b4807802a609140d150000003412600104c1705040403a62140040601c0d01d001d00a40c02c8007842121810308550504000c07a6542c060703094010940c0481c04035003018400c1e14a44500d2480d9691412613585c5824070448010f074001071412610020004045441e11a045c001e481c8501810390062a4134108800104e014001300d881ca00a410f0313890280d400a521011070f580c44c3c038608004c030948004841d2070b004104610050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 676312742 1250 676311492 676311497
    0xe071202040312031b0e060a1707050705150f070509030a1b080f06010e04020d0203031b031209010b130213050a03080702030c01020d052209020d0902010216050102071a0f0a0903060b01 81
    0x1740003141d00400d90000c42c440680b801912140400c100359440900b554030b258046d00d0720b204220f11640c1c00700050000c0d52140d02035482e00c86000c2010020f842068400d12101103d0000160141d407244002d020380420080498103550a203840700b481e09024035503000b984161a0740d00b8015510204460405031690400a001542c9440c07800b08410b800500028824040005803105558080050354109a200a800445004918915660307988910b804106a00503480040c00900045c41801c0300c0c02006041501c0c01140310790f689000307500140078081e070000c007120080b4003911070000d154050742c40f0b500e00741d551300f08500405140c03020b20601c46046600c00d1824092181d4004c09a40721b243c10582010a00c0852a4004840090760b42095181a201003001003044140c3d07006060500e00070707000c0d54007801040e6407403a40794a881c001d050150b48000e02c20810341a4240b0400303090046010054280741d0000754810303c070b90003c001ca8000504141013401030244078481e18082d9413090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 676313992 1250 676312742 676312781
    0x108010b0708030c0c0703290f040302100b0a15020a05010608070b0712030212150f030705030a08032e0608090c0d0204020a020c04050a0606030506030f070e07120204031203 76
    0x2079542d030b110361000508041c0003c201044204040c0020807000001d1940300e49800e0540c06a07041d01c7c0300710100b02021602c1400400007044003000c028054a010301d405901030007502000725404800381c54403440180c0c020361a00e00008a400010340d8210030301301d05038040e2818050324107005080d520702d07400120131078201c48020084c0314a00c070101c6054562205207406041b0040900f03400a0181c0510790300e021000034204650501e2860381000e06101c2160011010525403050640e54078a900480b6019888410444003051140001d903078401c01d4007059014118404c071040026400d01d440100c0400c4003424180006900400c0c1290306c00400700c02084000d080c08001841c400304000301034002e40e070001e141c142e1070f4401c0c480c4410300300c0040d2050040d800c250b00c10740e00811082c03180c00c00007883c000206219140104000f03081d040b000005216160030855100d401d0713580074100740d00303100e84410341d10780c188402e0024100540c0209000800540d220301c0180648515184041b03004005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 676315242 1250 676313992 676314007
    0x31b010b010915030608120301031e03050d0902190b09100810050d11031c020714060f0318120414030c011e03150f06090b0301081f020f180108010b 65
    0x81085030b022200c003010381c20340380b1480c2c00059000742842d420124080c002c0c00e034540c5249008800039412203108245130280320008441910041c0d058550040000c0e204001c1e0100d0480c282d0040e80885000600ea5100e80080d05040202040d05601c510801080071a480031103290450030004640b40380c0c00e08101c03a180c1307841d1042c200c1c0320314040c8030700c24a04100c41c80c1c148401a020364120640280440301e20f19035003441704100034801c560703100040c456488049142034121076043d10560005d0180b40c00c0280700c03e0594419000200004070444038517100d0064444100404800c1c4c0b90702141c03030340d500c42c20b0034946030a48200d000c042d8001e40c045e050010700d60b40e02401200810001a460100e030000b01141200580303000340d1b88040180468001085441c280c4036480c1c1190903d850380c04004e0f076943c240300c01c5400309115410064000d407610304d240310000c0160a40046c660307070f001890090694821480d0390403010005040c00148501c0240c156002145640034004691186003003404c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 676316492 1250 676315242 676315247
    0xe040b1801030c0509010b0403021027050328020402090d020d0b0a06090c0e040b0f0d081206090c0f0a0203070b04050a021212091504051503220b010501030216050f031b010b01 77
    0x3503110080c010050528245c142c9403080e1189040400433569211040c0e21980341107801135131074028140310780202444807840e942283d004003016018041e4040c1001d0513502000000e4005581568210103903a00d0280160782e076003030011009105501c58500c40c1072002442e4110f548a4100000c2d241ca404000041150400d01400745803500702c0d40440d5071500c443c0459100c41c180d005c1140c10035010300c50001080003c0004d0400091000110880d65030340c2c0c01045140d00c0152180600c4070b00400c0a0141401c1100003407180c1c1c040d42c01200d141a03001d6450705054801150141c842c5d400c9420520110f140010315003040c41a0b02d0001c040090107510b6035122403140440580c428018801c901c01c190803048166802010001c06c3c4280b2100070718076000d500d13842294004180580d00c001b031b06a450382d1b00b1055280719040841c2c070b442d0ba800c240c0198020360004155100c0c0075650b000c4100080d10030410900c0320020740c0081c6483e00e40d2605008608012201400301c40d904252810001ea617 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 676317742 1250 676316492 676316497
    0x1c0908030c0c15090d0e0301060303090b0d0b19091b052a0f06010303020d020303090307080f070f050f160509070305180d0807140a0f0e040b1801030c0509010b 70
    0x80c0c100394607942d50034021800e03500e04501c0200f84032203441202c0070481000b0f03002c00c0b08800301c40c00e03840ba5040c692004c4105400c88085000042c081020300c40144500690301010341001c0074a20b00c00030360f103054500041c1c0103200302440860581c012520500a40d0014058103600c11540e004402a0b2902d4401c094a40d029072403103402190303107030044000e268103000e1403010203200ca038090f50f044c0c1050240d00d40c1c491000b400103070090321a5420349070340f06100000300ca10808105000d0350030b04401e030f925507000b80c0c44000e8108080c6028040c40010a521a01c101034103442100104001c14481808030709110102c0c41458120801c810100001c1c0ca0302c803200c0d94461003600e00001c40350746404000041424025808440e44608202c1d0038200b60440170702c0d40104120780345d0f664008480200d0a54900c80c41a1610018002c1d003040c059a501408440301c0c40400184003181c0301000740007242c0c81ca2200c2d200100c03245022401001030200701c01c12900904001d41d1908130541c10242251500e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 676318992 1250 676317742 676317751
    0xc121501050f190e06121507301e060303090b07053d020c1b0319030512100501080f0c090d11010e06040f12080c01111c090803 56
    0x401501066210715503c40c003c0980c2c0182e804691000103840d2100041c926000b110b40030b0103441103403010024220000341520003c010780c111b00105030344400003265005806581c43c281c9410785400b116a445200780e420440701d6040300c0001c2d241c44641e202c0360490405040c0401c01c07610f820801d1000c2640b1013404415034102000c0c3c2d0b40c0c1c995035450303c1c81c0761002602410403141401d04031404102c1e00500c3da80505009071082c0440b68041c80002412072280c40d59911036035001620154440142040303140c080354001701030383c030705142d41d040c01c08071000d0503c0304070300050000845500000507102c030b042d085003254011080e800d0400002814150010700041281c01401e000180110204003c586010002800071445860a840c20200c0490341c8065280443c0c0207841d0000703076081c0b032815901116040c105101440349002c00d040f440c1904a201610104030400032035031180f5007401100d1008020017803590b0744482105940509080c221701d00140c25080001ca9004140c0000036203412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 676320242 1250 676318992 676318999
    0x50403020402071509080d0f02130e1902030c0c01051003050a0314090607030905010e150405120c030312060307080610060e0d02090c03060103140c030a02030907030605090c12150105 80
    0x750441da0601c2c00020200f01100d051007401c14211100300917456020781008547c204052000030420a45407069010f0140c828100074220041000440207a0ba1030940100142d404d640521001c410038009a0b40f0890f69440030324400a001d9600350070034895582d00c201039561080e0a1425540c4144e1992b0842c1c1000d01082030341094002025400700880d50300c4038000302070a954201500e000340030000c05102d140d005c50792040c28503905061211035481ca11342c1410a4070304c0d00d030074802000600035000903d01400d00c0786030b5901340c40c4c0d20f00b0030041451242c080c0d61007560b07103810b80806260074606e0704181d00d190082c005100000340201114000d8400314107190b8011101e42c0301083c2c0000101102035800185002400703c0d2448660040d4040c000030f90b814443c2d510313006411640f50314161040e40c10440708000145060f0140c0d4050364100d4284010f46007007d58030f480c1d480c103840c801e9a40025980010f200c0003000e151141055900c0c0d080c0380e01400401c17440c0c0328079108030030051056500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 676321492 1250 676320242 676320247
    0x804151d060a1404081c03020a0e1c06091a180a020d170307030e060105151801030608060a0204090b01030b10081812070c0b09060a1412011202010f0f050403020402 72
    0x300c103402582030311403c114040d100303512180d03102c00d005e544481851005400448503600406001d200e07008070369102a05456000c20b490128090000d080c481480b84010101c424030305e00c1c0028068060320021a0054040388040070300c02c2400d200310701c40a800944508504148040c003800045016508542c0458a031004c09502d4207142900b0482101c100c83c50110003c01c010300103801d40d21540407070301c0303500482c0c4241e030721007040c80508160012812110a010311a0102d186d016008417540081d040c900455215655902c8078900301c41910755064803600454184000340040c4240385a0100903e014480b180c40311001c81d401006a0707a102d000c0001c5600040c0c112490620900101c0003044201c40c80e202c07003080500e10b280c00c1000201d03440710030203d00013050a05581030340e00c1114010421403800c8151507054076a00c0c99600010030044041c00421b01d5400b210340c1c10717802000054103810f54403d140c400144142c0c40940307442c0501c400000320b203040c541e000c000d4900fa241d042c0e4005a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 676322742 1250 676321492 676321507
    0x27041103072309120d0207140a0e0a090611220506070f030e03070f031502030705030711070b0d02120f04110f0109081e07231018030804151d06 63
    0x14401d00c103c070801c68201c100060003011800d800510895500000d9003520240354540c140105201201d41a0a9201d01001e070140b040c0d460501d00513070082440c510004511040c0d42e01c500c252103045110108c209000301d038003500c000840c40015031004440340c2041a09080c28009030715030040003400b400e10500c601504007014007410f50070600c940010b0403507131802e50320005440301c0315603070100312100b000a60030701800100d00d00aa03400b5900d207454080c11951250350071940d0511400364901548100c0c0710008440124070014030145507280c0740541e0b10010b46030b030200f10f0711001d00300c0c0c0c1207018410100030208440c11000150035000b00e403a000000c0c4040012610074101d5002072800307001d0701a13218405010454509e111003d540c05039122903941d10104a18001c5602e9000450074500010905500d007117564003a051410341816007540c0c6154242c2100d003015500100c2d203400d070001d0103001000084030900105401c40c0303852521002003110048074212102d0301039008a0300401c441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 676323992 1250 676322742 676322807
    0xf2b0c050c0904060e010f0b06030f0403090e0a0501050405220312140108010b04110309060f07141303020310020702060912122b0c020c12032704110307 67
    0x107010301000800744071090034942446401414140501641d6620b0030496152000c024081c0c4075040074020800d5085a8078580e40101010000300101d0030024441800b061802d802011240603d0700b018001480e9030500051100300c401c09451072800d2100c80c0030640c0c0080c04090a507015039490718040c503a501c07105000c01d001c0c11210244154501000c000403032060b030154001025400c040740d05000c0c500300c1100344181844140c486d40301c00d801081c0002c40d0440c2200d20f080d0806001d1625024941040c1c0000034503802c0007080c01e2040398810070800035480d08005580508401060841c6481d0803540028400e10401d601e003030003942d0505500d10486018000d5080c1407000c0401c031a40c0e07c8061580c0d00a0150300c924012402468482110004610740718181e14a0441d400428400302e51504101c5c81d000b0084070404184800c2000200c4111540d0704045400c0401c14441c44548060302000180c5041e81c6d10788410410900070800307410751084500d0f50b00e607050b0a11080c41000413118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 676325242 1250 676323992 676324003
    0x40c1a0d0c0315031110050702090a0207030e09011d01060f02030904091a0429060906210d0c051e03070f080409020a05071101030b03030f0a02070312020f2b0c05 71
    0x900d0950710303c0c200009002805070000020401140d40301c2c14481e0090381640d15010344040a504800b5038000901b03504500d50080c503600d402070400c5103005c001e020000d2590340342600711a080041005988031a09040b85105000d044107061907415a00d0011000303580b4003030610210700c110b40300d0800320280004c03031000d41440c15000d0001c440c1d40c50582802442148a20300004102d9525880b43d08801302c01a1142d01030700000b06a500151100e90030442000d90300380729007200700b82a680980e542501002074050008032a221100494101c3c248a4106140d10362070220410780350141403529040032080b10790103039200440d84000495130070a20894000c41d0090040e8a100045558210750080d002e40081c2e0700c60700082d4412581200110180c1e50303404e429942541c024800094010288c402401c40000320748120b80342031b5900d0319115042138190300c130500580c1142030b440c59405d005008400c442c003851a07800b5042c0f4031079014a8034084586888104200300000c0c1a41003000501c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 676326492 1250 676325242 676325261
    0x120306011b060e0c0127140609181b04030215033d0801090209150420090a170d031a0402031509070201060e010b0c01180506040c1a0d0c03 61
    0x50811002d949220b60f15615005106040d000c20a00c6140c4500c0c51401d41102d2100415080b460210901e000b2080d0203c000e60312401e580b18506010404031607d501000940b08481014000304d9030400151003600c00000d007600001c80e0398200800d00c0561034007510000241804000d50f1764079940c03901e210310f44d0b00c10201c044990b01c907074540c4544100c0120391120410341080d1160070502e0b64a0fa269822200440c0303000350440ca214002941003084640304802034580a403001c40d08e001040400320006040c0c2007000507011012844410b9800c004e900c41c40a0b01e14056000008100c4890669480c0b801c0303180e075820951110300701d640f40621078440d41c45448002e482907441c0e003410012000403080c0c1d060200d00481030321000032000c41c41401a035040f10040940300e210399080506254466102c4043e50074103649803d02c2d003030a1812002400c03c0240114043c0c20242800d00d04400c1c00c0c00d003030f4082040d050308041521048142c41c000c0f00e03020044100001100310610000b82c1c09028250f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 676327742 1250 676326492 676326503
    0x604121b05011e141501030204080d08240102031801230a030c05131202040204211b03200d1202161211130209060d090212120306011b 59
    0xd2652041280c150010220321110303e4003118210208000802260800000803c50000b20800305002e000741c0c40840a00000c18034000d85030a4071041c00c0e0f031401c030b140100d1100040301c460070402c0301a4080c400204c117811301c0402d80d01a101c0400000d540340a0f10801c54001040c520a4840c0c0d80c0c0100940065032812414042a9201c0030000c00001c4d00103038216800f00741099001c1d4503007842503045030150452600f10a00041c281102c142000c00004004c0741c1141d030800001ca901c0e55060340c601002102015801c3c251891817502c1a001041640700e000c541003800341c01d01c0010030444580d0ba03404002004095615240d00006481001d1007002402d00c1c0c3c0500b182c141400d501180600764030303551483c81640c0c2603841246a048102103000500340b10005c8102040c240307054044440390b071501c0300005d41400074110001d401e6521940d80301d402e00783d40b03062040071820300c007c039404000030540240c0480649400c08440a205c001d2005d4100300e1290741c1c00c240d22010915140c0d80b1a0001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 676328992 1250 676327742 676327787
    0x4090308040b06010908060115030f240f05010212160f05030306040c0c050a030c0503130803190206040c090c020102040305011401140d030f14091314010603020c060412 74
    0x1414050210801501d0070341d1100e07408030005503035500414660085810f020020405a8a0054011605059240c003d01015207030a0484a42c1d9498080c910106514150303100420382200c0341098513100c02d41c028111403843c541d040050780c0c1c010903a41920046605d8143c0d036080c0c410302074100d80c225900000c0034410303000e01001c18048000080c501c2250256010802d4081c03851003a140c1c010f90000c02003031940f14081860000780300c1d070008149035200d00126801d040f0040400030008080e9084070307507960b20200748000c0d6990041e4400002c2c01050000e045282042d45852030859400c0c040d195a407511504210050b0340700b541120002c0d1740040007040181032010301424501020312940484408403800788183e0320b88041d0005180743c4c152030700c08100c5d40182c400c1c0c4903c2e040c0010009410428400282036032210f04030300d640304425440005003da1000d144215681040c2c001e581007503c14030500712203200004802d9006030b0400e4582c100c02416580c202e50101c0c11081112596101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 676330242 1250 676328992 676329011
    0x909070c06090525030503071b0e011205010c0e030607030917040b03150307050904110d080a020d020f28050a02060c030706050c0f2a01050711160e01031203090204 72
    0x200320070100d14904e00000c07030b08150840c4880f0a1010502028150307400411031500090503040c02030341811309481103208200e035905016070703091030240c0c00741c000303d00c141100d10100002807080100700380c60360506441000d10072020135907c01c0300620703035018581d0b500403100600c02d00c161008202020709003940d0391141c842c520641d46800030340d55004c80e200c1d10350b0340000c03038a00850500e09641c00a0404806580c0d140c440310180030300304540a400c581c1401e5035801113503540e80201400300c2c0d6a0014824141c241000a24150219108200b107400c59030400e03803413000100303184c01503000310b000080608040e400c01509090780724400035070040f03000411403100000030010f000b80c140102e8040005030754003038141809109500780440d90300c0e800c000484090030030203802895040080d528101c2d414551011900310303602540d02130b012502d050381e00c803030b440410030034118030222800003130301040c0c500300b0002d210b240c041c000148480401d403a014140b5210744d1081030b81c5600180207205c2d40c0003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 676331492 1250 676330242 676330253
    0x30b0103260a02071a030f1b07050303180d0807090b1b0a05280309050d080c1b042a0807050c0a030e01081f0314030c03030108070e0610050909070c0609 67
    0x4280b092850011421142111417010002542d10528070003c070180301c1d03920b1095400d01d40f90248920407240b80180909404540c041000d1407040202001000317004d400b400050740741100d030030414000c03c4040c10800018942c04070030741040360494400e50781c0350403074a400010403002a0b0a03c074010b1084007041014014001801c5054083c00c0744003200310b403018241226448070f0020082e01088079410104030505144880340640760050002d03600b0180c060400ca0308108400e8171172400b17100d00031030303584080c0341510549034440e00017050310740202070900c1d0304640040402c015609002c08d00001514250180d01100c03503140b04c1c907003980c00403030303070b034a00a800030203561480c0380020807240c0002c07880b091480036034101c0b001c2907212504080c615980ca800032109491700c524540400d01c0302c281406810800b5501070b00c074038805000d40c103060a17401c14201c94002c2400740710310301c40722024840c1c540000c00c030383c1010400e072003203d83c0d80c0c0c50a0b01990040104840100b0701840c0504181c00e010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 676332742 1250 676331492 676331503
    0x141b0705010f08010f05011b1a06040b0a0513020d0e03070c26100504030e0612010512030a2307151e0605010921020913031206030b0103260a02 63
    0x150300b6210030804608895003156050b07004d00640410060200c4144220741c0191102031244102c0300800ea10540f09640b1480c0500c41082c040c001d61a603c000d001540c9024000d003e03842e0000d480807104945000b0000b80380c00000003410b008140d00040c88481e80d1240d0f0030403070309100c01e50100d0741d80301e4491074610700040040c801e020098550310024514030750b40b54052600c00350501c006003100b4001040f0b03000100b50103002201841191038101c20141c40380c00c06030080300d1200310182c0b030662400e024044100300704c0d444032500ba0801c1109200e81030300404d5108151406005100110019112600741440f9071030f0090681515072035188140394080c0c211507424014101d12440c40902d826850060300c096001e01404a01c41400a0050700c80d40d28800182c031101c0428006003404580109030101000c1e40c60114528010500c101030640010cc082e000000d0480c0070805d80d4995140e0607828034060100800350313030034102c220402081a50054500154083e100c0340e40b8118082d02a660701c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 676333992 1250 676332742 676332749
    0x11040b0a12090206040605030a1d0d0e03010603210c0f06020d140103081b01061a22030507090513060c1110090b010506130305030a09140d0c0303141b07 67
    0x285125102640940e800c1c041c2041c0302d90302400c403078201070400030140c980e80c1004040300052039031a82c40c81a00089201d100c4409258540507248580c4a00e000500301e039510ba04041c060ba0504004000051083c20801340000068200780c0180307180d01c0c01180d10351a01c40d00603115200850030201413150590042c9440c2e10560010401c045140d078608242d13000900c80a003411109100c0290b80301203114107040f010040e04000a0200d49825800f01c00c51801c00c01c281c080c1d07102091304c0181001880441c100c20f0340030381080092a18554406a0700c0115010703d040d1240c0b114042450b1003568810401c4c41d42d44440148080c955030b00004040c10041c0c040304034140314100d51190560100d105280e0500d401c051501c11981c201424807a8a51001080103101041e0420000c0030030384c01d10151450110a0340d404101030b14182903042c9908103803007540e101c2e100300302190f800544410307606d1040360b42c9818600844071088019030001c3c0101000701080c82041c00c1d60b01004040403d1400a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 676335242 1250 676333992 676333997
    0x80310090c0c020117150303131a071101050d18061a01050901080a0c1701150207150804150204051e040c050406020d0806150f030403110d0905011211040b0a 69
    0x1008040000311036403840210b010b40031620681c03136007003001c042031640e0341e100c4800310001c80c1c8110030b000400d00c0c40d4803516265a10500c1e0010921015625450926200d10300c0040923040203015201c400700301c081c00c040b8074188079000071a90a00a4660084502a5400c1240ca01416200e04100c0b019142c0900c2104d10f860310074001194079801802503e01404060b0358000441c0d84485210000b089103114070814001403010404080151000c1c00b40a0943c16a02a001c20091580a0b03d84941c2e6000130072251000004800469803050b4600e0703121341c11108550440c50740f010403400910a84d080b05800c1541c5080b040d600c101465080c00843ca003d42d410040b28084480442e028041e0340070311401a0800700c0401d180c54440c642440c1c000c0c0e001032911460783d245e4207548140d81e11400c2c101d001704001108100a040d004a030759015581d41030060304540c181074a00500a0340340d402518140405403071b0b0200c42c0000e0f68880741d20306003104c1e0300302c0c0c0d5152036107540d1403103401802c00b2000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 676336492 1250 676335242 676335251
    0x50c010f050106050702060f0d0c09080d05040b070b130501021803060f1308030703020f2b110d020c070f060c020a08030c030306150d090b0a0f0209030a06021608031009 74
    0x6400c0351a20550741280d1031035580d00d003044002d0313003003240561013660040d03904403007070040f412058258420900340b07022a07142c0c004664640580382e402c0c03101c03004110342071013070511040005004890840740001e6221b1005142a601c03c2e201410742c516194026003298408039080c1131010341040041c1c4880b400b1001c503065a943e413071a2000310802150a143c0d010812003050300028141c0e005950040c1e40d5090140c1420390540c2d0003031b8a40c004824280600c590030314141d00710600c10040e07200112142c6018002514000c0365286d01d8418141d2031310318190f00041541d0880e00034403204c00684440c8801103c00c5554050043c80180342ca0026441501c10715000100407000104442c1801d4103e805181540d840d001004849010350007400035031001040103050b20038140c41181440d5102d0034000541341848601d4a04032202d041c003141c804d6104112180c0e443d0b034006010807a140d0f2040001d40d540f002c038090940c002d110700030003c0c101c00b8048244000300c051501c2c000c0554207400300810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 676337742 1250 676336492 676336511
    0x40312030923010c1128230303011a030f1b07050f0102030f22021504031a090f0a03080103151d0d031a1011070807121506080619060902030403050c01 66
    0x761110900500300b06e80c0e03140c1e49026426110300074640c00c0d00a00601c0036000c0c41540c09043d41911325a95880110350b000000140a04c2e030008000c403610380300701e054060940c0307031410f5840c0409801800310001d964842c840b803030b21012020101c6900c0c5501c50305503484d010000421a0217500b007665500e102c2e49180c0c0004444c1c201c00003054054a5500c10540e209041e03076002c1c0224684a190503101e207007020040400451001c040d81480250f008801c0c401038503102d0490f50405403425050f188076000f041d407240c080b9910030300c01c505594105600045489001195a000b07103220f0045020000c01c40d0204070300c0d1140415200c0c14609603840030b0100041080d001660000d5500805502603c4090300702000c607c9003d0108075011420112894180c503845036914201d501e0384400c0203100484c03c40300030052a1900d01c8000e803c0300d2000d02c40c180c1880491525043c00400842a03140d0720a50541c124050760008002001003040c1190307241810f007801066944045298036056003441c034043e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 676338992 1250 676337742 676337777
    0x1103040221061501023a09120201030b0d0b1008070914010b030a090b0a0c090f1d091501061e0221070524041502040312030923010c 58
    0xe4560341c820009809159529010820302841c8140706134114801d180105500006405040044943c070880003080b440d6030003040d00c90300c101162101c040100c0c490003080580084418103410a509007800708014000e200410940c0e0450700010307103802c0e401014450340c200304040c5c1c0070603149140d0680c0c61080d101e04220080e201e604182d01c58000c0c03500010415103003480d003d190420286840459009040e4840c00c022520598131221929501c9544c408a04e400500d520b008001003035203401c91a203000070881c0080300c030780006a418495480003030240c0070144611303003074080340d03803450009540c4448000b003522903da0401c2a1020f44000d05c807004500000d52000000840d074a5805114100799801240742c00481084480d48942d465003d103454880003c03003c400d102c076030480818503003420004a003400c0300c45030744a0b13144108018808220000c0160a003c5e8040c1008542c4200c0c52400440040c0d00c0c05006042000165800c00740c0481900141d010007460f40c2c0309030307440107240e83e43e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 676340242 1250 676338992 676339039
    0x6112401062304050d03020a1a0619050d02010804080408010f050a0507020114180f07142b020d210f020705010e03060f04060209060403030c0c09020a051b070911030402 74
    0xb88491200a0004018510b01400700700c9029120b40b0548025040c0f964400a0305012401d07111078041201c8200540c904241549040750303c0c6000036184018a842c01040f501d8180e114081d04116001000406004000040701d0003040748400800c24800b1405040000b01015a10306015500309804a8200d62050084941100800c0c580c02040d81320344002154043c000807880310320b401010150303031605030140322480040002310b40c0002c180c1031180c100b01c1c56410700103951031001100d0202c9500c80c00c1030036200c3c5140d075068480c0d041c068802d080c02a403881c1c10444060082001f103660f00d000a07448640d1441c04000c03502151107a80d122801513421328051014540c00d5072010000900203c28a1052504035015000c018a88030807a030202c1c001d540a41c1068002c60a060080800c1001004901d030080c0200703902103082050502c0018018420500084507034002801c114141e1982400311000804040360204400854443c044003250001c0360141e100b07000402000a10700c410112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 676341492 1250 676340242 676340297
    0x6070807030239040f02120f06010203031015020a0b090a1703070c02060f21102106150e270d0509060d200c0d03090302070611240106 59
    0x4a02c001c1c0300151043d02560351160010603809501c0f0300c011080308038144000d01d4401c1c41c120100c055454020151181410080c042a0442d8010401c11021510ad5445a025181c404a1489400260f158128502500d41201070303e4030f05403800707001c9090000141401c0c040c1c4242840e4070b2081c1458042000c60108880e500040f8481904210052808000030181d040300c005681e07040507050740303290719600410b206d4040c00149410501021a03000404d440042c154008141903111014504400040303441d0f000130811601d91200c80c811982865071900900b07001c1d401101ca40c50140749083c28600e441190402c40c0c404911800031303801000ca0080e100c0320803526554500510101804855808840005115030782d40d41540d4a40304118000948110003210440c0c0700c00d00c06041da801c0c020040040001c0c1881d00d0001000642c000c9040021502c2500306a07841c00240003100b1705002e50203180f0441c4003101c1d060640d005252030f02c800d068400540d103090080c9040400b00d2500085000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 676342742 1250 676341492 676341553
    0xe0c0c010b010e1c0305040f0902092b0305090301020c011506030b010203070503180d12080a0513050c0402030709050306090102130b120f0c0c0f011a1005030a020c01020405060708070302 82
    0x11040c0783c0720304e01c64501000c50300c01e240140c0b4040c2d03903001c00303040f1074070541140800a0b00011108400d20b8040802001845032035207010080414030005400850810402820321002184918041c0c3e401e5050718440f10b4104000d000903c4c1c20b1007242ea01d81150300030b5802281c0741c40c041017225440041514120381c1d00c071005501d011a841800321202a1928a06900500725000b940002e21804405078200d46a900d40c00e00071b081a80801c4141e51008003406400705004107080c002c1003000440308000001990016500d4a6034407048507980d4030f85c1c0023030f80c046c03140300d0038025030101c158001d00e1540303c2000d262400d00d0700e80c21103d0701840307040040b4000c410100d01042d42c54031490619508444845411807501275002c0480e410b18418244034034841e5520200100d00055850307203091240000c8800c068a070440010241c454000603209100b07141d80401e449403802c9007541150064034009000e2038030740d003141c9807007404c0d07030b010000440050142510400b5041d0001054441d00031a08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 676343992 1250 676342742 676342759
    0xd0c0206011505070b0a0f060803070b01061d0108070c0503160c0905010b030c0403030f030204051e0a080c030a0b060a0302060403051f060303090504050601200f010b0d0c0e0705040e0c0c010b010e 86
    0x406c4075028203204554185851741e00c00e07000840c2d44003007008005103031240c04c000e001985403041c09002d00403412200301d6910644d2440d007075540e07400306525911980c17504000c981080715080092031400340c030085a012552415840c020702281165010496070001828461a80c0340e00100e02c56001c261001d01c43c406040c0000c0c00001d00803a140b80c0c1039040b40c40d005041070307601c0700010030503582d002c0c012203140644180b107641e0b070030300c0c800c090301500c0040020039090310003c02013a91851915000b0b4040e42c0101c020502c26621014114011030b0001d09064450b0740300d081864841ca1101c2d01d40c04480304050001d50300d26402d001300c0045a0305501c5403e20070f898a0144400740a00508042c100010414040c094000305c0f5418810a03884074010207200d0121030401d803c464013000c1e641c2c892030490f50641e00161a0b11105010b03903036541d03415601030703d845505444e64019600440b1840310200704110b00030518801502c081507452000b404851540001503940710741000d850b64005004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 676345242 1250 676343992 676344001
    0x30109050c100201091b03031805010906120e01050106050c060907030b070804030516030e0102150609010504090f060c0305040b13050604082d04080c15040e04080d0c0206011505070b 80
    0x402c10403602149500002c00d40d126590b07160a4210031146c2004d4500700111401d205141d4818030030041501202d8407506070604000010b48211441c1c4503c104100002c00714180c40310720b03900491444030701030300240302c2542c68040141003600107200e0003030075100d000c001a01d213a10000d6210704a07908000411002e40b1600e404843c2c0e560000d0054050145c10844a0400c0390310072020000c043c060b43da800c0c45162500002400c2401d42e10105140314103100c10b029442d92800901411102d040320001214041480d0480301e8011600002c4d201d985003e82c496115900354120b140304600c211107002d8a6905c249142005c9614031344090002c1e40800e000074001842c580050147c1c8140101e00c0003000300507850100c040d9500c04007010448804601001441410001915031507800c489041c03114a4a031385811440c091407080320b043d2480705000c5800e10803500c0845802c0a84403009001043e540e04019590780c02c20301c00c0d915100c48421a1a034224440d03800c0d00d44469000c5c0510780f580c0c84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 676346492 1250 676345242 676345249
    0x301050426030f0112141b130b01082202090114040507030207080d0e0f0706030207150203041e02060f180f0301050c070615090c09081606090e04030e031b0f030109050c 74
    0x81700e0b0300322084040c2400300c080c0c510040050b00c041003011000c502c0e402404506000305210360a4521030418180b6000c510325a07003104440e0f81c4403801c4504018051032a00a80700e90020b42d410117500013113013a0000c00c440c0544016002400010b0302c0506c5261600e075003c904034425003002403d00314080c0311007c1c410350507410546845100b00c044403441940b40d2049400c09400758000c001084c7d0010302c5c4020045185108001d103001680210700310b1600c0e80b00d210355101000d5a110b052a00070070074000319912a802e8801e004280444661503401c8443d00d01c006210030000c01d4418403c524000a00349014000c9500c9525801282c2d8245011035491b88054181c4c0c0c041d00e03080084100c40400c081c140e61003901c010009558511155a24102d04c0c80c0c00c0240f902e60158118040c2070090003002e420100d014102c0c1c008841032103a0363758504048454040700c030040d03981400b07011b043c2c0c403c1101325581c43c81c0c88103044641c45c0c814070f030f5881010b00321440154000c0543e04000c095010310316 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 676347742 1250 676346492 676346519
    0x170d09090e120c1e0a05030307180b03180609161424031605160816210306060c120819061e08061b180301050426030f01 53
    0x4407000499401c05180005054241c00c03025040005070302410b40c011180c0400b014030040c81d080034015020b0b601003503c030503440b807100604d800c0501030159424071780130040540300001400025181a01d80c100400e04a09080d140c4018002034407858001c10f20340305007c5030200d078941401c0060a2118030306001003030740f040c0c201a0640d111b0b03c4641c001510301e01d4210003088421080c000c2583d6031400098030083c100728652401c007000400e0002d5000d00010341e0320b5440c6507401000c0b550f141c4190340110300c0a0040040010700c01a12003a04035444200752408140c464540d4605001c81504c6880c2241c0352a004040645503a00360715a002090740100c0003250004e030740744034422100d40e01950040c00d682c0c03d540140721030301140c3d615074500040c160103c03003d03100b80c4020304060b013000b8920322031070381040070034565504000413004c81710003042d41076049510000d80244400d1030141481d407200da0480400020500840280c0248000940e0441e031084100b495003004690034071a0349019203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 676348992 1250 676347742 676347761
    0x409090f03080c191b05101b02120d200d0905010606030b030c0f040605060c070501030b0906010c11060d150806060a030807060c05090d060b011713080304081e0301170d0909 76
    0x810f001440718011803014011087c0c0000078030340c0031603071138004440e80702c0b802c0d06141e00c0c00854000c005101c41c00a0100229040191000c00106505514501101c0310042050f40d4211960b0005071031414141d803600312004441c001c0002300549035a820341074054501582c2c0c0694036030058000d1a44a140000c00c2018625028200040395074030b480200c5c1440d4060800611158040142000f41c0d40c0c8c140a2501121825610364241c5c3c188100041d2000000c04001041d040520b0700074030040d00d074101614070242400c002030040d6040040070300e4843e0014000c004441c020030740068101d041c0103e80c0300440c0d502003846407500e55281c68010003061440e040b001001802c00070300c0b18998854080d840070900400000910344140400175040f00501c0103226030800b41c01c001c0000036100b120780346d462284c03c078003926529500d915054525105020160b42070200034103102e00210a0380b00030798142c4a125625200203084411015500d400090101000403090344061203401c03010782280000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 676350242 1250 676348992 676349027
    0xf15090904110306040f0c091406060c0a020621010506030408072a1401030b0103050118020717030112050d141801110a0305090a2301080c0409090f03080c19 69
    0x25000442e002034109403003650152000182c0c02055030900c2050f000c43e0000305801c0030b0800c0001411040c4480d14440205940d200c2c620210301903a07680030500a413010300341c1c024034942e910350030504041c21040709021030000e04d007581c00020540303051843c04c90740540e4019401d0707800d02e0440e0f500c5942e29542e1908991007910034040c1110019010502c01000d440d000300d20103801000b071000141220000c241c400d04040c104001001140102a840c00d1400d010f2003000d603a66049050000c1303c003074602010843c01e080000000f400c0740005c2210709009106000341c5025804e070440442e00d080841c2078619440d182007185543d2100343c62808250004181845440c1c0060200c0680c10a1440f0000ba4003040380007400740401c1c60422030b040007500744002008520417207200c000c208842d2880a1506005070a00810107400c100700541780104046c600500c0400c01b245882ca400804005c02240071a660030003203100030444805030307030882c080c030040c80303c0303011500100f02c0d1006d80c9140702d0242c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 676351492 1250 676350242 676350263
    0xf02131a07020f180a090b1609062f01140717070807110f0106080f0f060a0209010504080f030705060a0504110108040309080d0201022104030f0e0307090603060b0f15090904 76
    0x40e402d101c40c0003449000701d45000260404941803407d15158020030040d116a9015605005150071201c000705452061400703000c0c0c80515121880e58000000c0c2c407000003070640f0302c8016080340540001c1c1c0780861801814405854500303003034a1300c0d0401480c58222911140c005070f45203201c0e03803115a2110310352420503501c0c0c60710380c0d8241c100100e014404d1102d9440b1304052004000070040109140024001820341c982d105c40000c3e25400060404020309400180c1c241071680f140d0280d6014002d90340540d0985000f0036100d0399603610100b0211103500418000505400d111711405119a80002c440052084031800444400704000c2040742840711118000c40c80580401000c41a5070481e0001695204521440e03c05081800d002e0b42d4204100020840020b501c80c03403241700300103607042c1080040700181c006801d00d605070300311401c0d140c03500c0000000d104103a00015402d003400d03100705200c81d40000500143d040d0100c0d40311000141041001190f050070070b0381e158407034040c55403040d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 676352742 1250 676351492 676351519
    0xb0a090602041203020f010b03030406050d0506150a020a03020d051207050d0908130512060c04151b1217040506150f0a0e090f0d0c030507050c03010f02131a07020f 72
    0x92082800b88800d5006a11084a030004c070706d02485041c1d5a150110015400c291400c40000e0103440303504a0711050585034404100142c5500302c8280f10724101250b21515802d45286c025612030340058160014450528031032038160151045813002c1889440c07203281a59030301015225075001418588610342c0d2540f0b40e07008901c0040c041c0480c04009000503c0440c5494104801d1100c0c5c40d14400054000314280110700c004001210211042c02c001300c0111060340d031060754400c110792002102c1c09500841c1104205482202c01513a640f151100e19040b05903460380007080c4000c40c0c000b0240d03071001e0040740a1241c100c3c2801e82c0c045000345100310016414022036800c00460384904a102d8880c014418501d03000e0100c00300e03440400000b40f50b4050320804c000c043c00c242c40005070510400040e074809100307043c0700c0c0c41110302d40034000380f140588418031140254001c142180c032460580e0000700d00141261a5240d001c1611000b203401e0040c15001c11240e840e84403041548540c0740d48110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 676353992 1250 676352742 676352759
    0x709060905010203121f03060209030c0303030910110d0c09060306090b090615131202180405190602040306022803021c0b040b100f03050609010803070b070918060816030b0a09060204 80
    0x8201a51103814094ac42c0d81000f03003410f2800680000380d85c403e401c2031040010110000585035641c501d4003c0108076490768601e03212040c41520f01c0c507560281030002860700b03150000014821551155405c00c14075030740d140300300704441100750841d80c4006083c001c600700c0d15049204014461041008030f00d070202004085601403200c6c0d000501420343c2c18402000e600e8001190b10303104c00001c00e1546145010740d13500340c4078242030200d42c0384058820001d03414400305a042d10003565201c1801c5503240407040f4804816403485d05910418481d4402d40e50781940f080c001c0c0d55220517020540b110f1074101c022003102812480c03c0d4150895070714400840c0030394901c00b110f044a01c03652144d22203110260801801d90701c00403d16401752524138010440310b48000104c1381800d40000d40d0810340d0719441012038900c5410351161466001c007031610b85070ba182c550322000448400004407601c151135041000c03103180030340c031010b0a019a410001840c0c80c8054000c02c0d2110b10620005240c03036100c0a09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 676355242 1250 676353992 676354051
    0x1f050a0608010801110c100e1f09110406080c06091305010608040b0a020405010519020109061b17090705120a060f0e060f0606031602010902090103050303070906090501020312 77
    0x8400010440c1c0c004020200007032160001703440d80c01c0a030a207050780040c2e0079680c8004081074600d90a644d024814549181031103902100e000d00ca401322202000ca00d0300d4809010103800c10b60340c7d88007c0641d2541c528140c880c0208954810028019170842407040000c00c0c3c0111480d10b0b080741c880119010180d040707115060203081680c44403401400c190401c0c20f8160001440822403500c10401440207a80103010f0b10407404101540400d4605004400c074054491910000c10340c500304110904009039018003100d03541540c2d0746007144503042d0030300101140026101c111042e0041107090000d410421588800d1f4142d0408440c00d560362a40c0305800c0b42e866200303510f690f0340d90300300802c803a25090008942119140c448035005040078000100e44c0e11014041d0440c951005500801250007901700d240c06540090900f40c0d1913a6900305191280d004681d10800078203001000304050307000d40c203004203950040e80110300b004055442c074140030f0000307001000e8003a01c542c003401e440e6544031507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 676356492 1250 676355242 676355249
    0xc04020a050a0909090c351b06031e1b1201140613060503062d0102011d0d030908042c0603031602040c17130314070201081f050a 57
    0x26480d40e0340b00e1019004140002c0c5410100c9444c0c2055030013404601c082c0c00260a0760b002c0c603108038102d4a0003140c40b40b240c41624107001a00b8040c4580d040320072000c00e0340c0e030040c040d40d02c00c00d41c1000e04d44200007192001710380c144550b41140300c4040c4140300041c0019403000300c0d035004003001460302d404854250421040815441007080050003425400903409207502d5080d034056080020003c00704032240380501400b0100403002c000207106a0700d001c5058000c01103081103c6240c0c405050a488502c0000019405076080c41012032400c1c0103071121194211040010304401e860880048015024181e410f07a00c0c55818080455920617030b2604030402e005099200d82a03040d4040000002d00b002481c081c42500b00b0721106205400300549810440d5041b01e000490b0381c0000c0c0b080d40c04000c9015500c010a104804102403460350310750505e8114080d44817216101c202c40922035251140e158000d00044602010410040801a01c195242960a06081815240c0010450075903540c0d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 676357742 1250 676356492 676356497
    0xc03030c30250203090d051f02071a091b01170f0a0e06010609050103020f0c0d0c1106030412030902040917121f0317040515040602011416030c020c04020a 68
    0xc00b4081e01c85021005010510030011500240965034040079489020f80344039580252410308582080103800d0141c00000d020001801c100d0079002070100009400581d01118100340d18051a240070500c4c0024030301c1400c1d0400100b00d0082401011088056041e00032810302c6800d10764181c540d061041c0c09031007107072040e038685618a0416203400595206090740c00f41500040010b1280c940d100c001c07039050365020300f0b0250b030360308802c503c04880784108a0010b080d401a05000303106190b1008560010300d0180c0b42d141c48007400e0324100f100c54482074038000d2000c07600c1010000c01600a4008802080c00100700140021064441c207804513101c03420340c01c2c642d500190300c0c800c0700580300c0041d4010501d204440122004020700440b122040e00020300000030000032018a603d03800100d0300501405422100024206800c040a0742c002c3c0c003c00000d5420a81440c2d200c141c0e04070030900c1040c0c0e1a0009141c031000d42c0d0160002c1070810564021401906400400340c1c0300c0e03000501c800340b05036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 676358992 1250 676357742 676357837
    0x30201051c110913060521030c0d021608060f010911120106050306120610050d051905010204170a021818060c190f021c0903050a030c11060c03030c 65
    0x16800c112221113601c4c88280103c0c64404180501c0c0c42d145101ca40c000896500b04c01030a0520310050b2550007109904c01641c0f003500004901980e0209902000550002c0341c2c039041616148541d8071001d0440703c4211480c01d010040041c0c038600c1d00030314142c3d03921040380c0d4900980101d8505400340240c010030040b40c4000b0501085040c410900a0f02c2003042000d0b150714105140c00c81e040c0100d508c41c0d1445000d81c0340c400020301804ac00b004500c1206020561591050341c900503020b50403502c1010b404600302d0f540c02c8078003000454540c410a41c000c01c5040c2d0b0090325a585401c1e510040d0840d0900881a1041030740000200200c50080b1450340d010358403804840341d030004161042c551101045480802e040069400280030783d60501000780d603100c517080d441d01c101c8052080303510240c414455141040180368000ba4083c0351140110407119007c524602031040c41d124080041e84203600030000104241041d50240610003130727081c9141c010042e03011948403601014040350703000c6480ea = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676360242 1250 676358992 676359007
    0x7030906140916120b011211030a0506010f0b2503180308070b07032018090a05071103091507021305010315062102040b0109050301050109020c07080a02030601030201051c11 76
    0x201454000200420340498800c40c0080c1c0d05c5d03450002c010700c40c4400000d0840b1080b020041c1c01c100c00080d0035805030031038003404410706040c0d540720800c0c0300b55a002041a100440d89441d4038080740e40001c401b08440401d0000200c0703039000392210650076000c00c01e00d00110342c101c4000e14002c0000314016140c0f540c440800c3d00300341c4d100c6003002e423048080c50b2908045440080d044404000c4450241043d035807114009981070041503121540c16030f20904605c204150109035500a034055165a82c414034189504811184e80384a80040194089441010004810400002008154400f0748404c4104401da084001174440a800444d600c100c150b400c08a0320f01d05125200050400580d00000b07082044454203a010341c0d190041d0096440b2058820303584d0007603814030024680600200301d69030352003902d00000d400c000310703481e103501031250f0000d4028800503002c0c0d8025001030141090b64a07580c0159016401480790343e00c2c10100a0680da0f0122451043c1110f00f202c40741c0c9940e41c1c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676361492 1250 676360242 676360273
    0x702040615080112080705060403030509060702061005060a021006060309031805090412031e020d141006030c020a0611030433020c01180c0e0f0f070309061409 70
    0x140c000c0700201e841c400003440400e9025001a0444043c0d840c4140c0c000700b01c0c1094201407060040242040c410f600c240410927a041d0701207441044000c0c1a14425100d110080780c80c0c02041d00c0001c2d08808001c0184407928144c0e0041801d0b00250040b01d01c5810400d000340d080d200584e006802185e07580100d4402d2540141d86c1001e110171483e05031008909100c00542c140d00c000d00b001e0001c551000e840d00420340a0303030080d8520710020203410320640c0f0b4003604030081d500102c5128185800c00e40c8020010103100382003405804008800346074141000d00450017009180c00080031446000c9030712000c2841e5105030522403620119841d031341d1601d401c1a513038404180704580000300f440000c40f62601c0800450609200075801c02598403031203002a0b50140c80354694049505040c8415001042200314000d030458401840303841a950b1862014005440100d42045102c1c0c000070010742000d129a0082038528400c60700013500406070500d6140724a0f080f180d00c4820351210721200c40b03010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676362742 1250 676361492 676361501
    0xc0703050c0a1e0603090204420b030a020904330f230627090f070c0b1e0705030f010807050d0305030a2003010312020106060c080a0c1403070204 64
    0x240a411581d2000406241ca0014003100c1c840e4008055071a0600803c56840750803600303c00c1003c10152034015401500f07001110200c61a1241d8006000045000727458212001c0e800c0b100d2054015056030f40340280074019621060056a026a9484111040e0401070b400900103520403805011740d096001e0243d40052990f80104000c03480e075034001c008600e14854101050b590040d002e03000d0343d103003001190300c9000e6408200c0c00c80c030300004683d00545a00d28103001e07184003114542d005071a807030b25850065078241c0d1114005200700d40400e010801405001d90003e10018403ca02c405028403c07441c1010240e07100000640c00001b4020b02c0c4104c2d040c003901400c5824080c001a900e400700241c1d6620310a600181844004000540c400794281d02282044c103254007407598490030300d14182c060794401d000c202e0f078002290801b00f640501c140300b0f55083e130740c003034440f814955800e484a01c881e42000300040b080044041101001071000903141c908410301c6801182c981c0c2c0c5074810401600c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676363992 1250 676362742 676362749
    0x402041d06030c0d3c0b060a0b161a04060914060906180f0d02070302130e060403080a02270a090207081204030c1e060b0f0f060d020c0703050c0a 64
    0x1d6100c3c5046011a035202015015031683c0700001d035026880322080f404032400800b00d01c414840d1140c080c4440414414184140d040c4280782094482d036440042042d11030803030090f0105ca048c288244044101da07041e030003494a010344040da001c414030920745802410304440c201c0c5c805849085210030450815110090620004040c20742483e00001c400d40d07070000142103600f84204401072050f400e10038030058000f42d4071841951001e000c00d000c0650b440405100480c050088180803080d900c40c076111381c0800031103540180c40703c1c1c0c0344d9480441d405200580000410703a4208800340b10400b00100d001e100502e0805000e1040ba003200c1000014502c2d40c2c8031000c018010031520001500040880c0d04806100106012a855900342181d202c085280000c05509070034241e51006101e2100714a5141c0c411390040c00b000803400213001c200a50024029002a98907401d0303a5a89001409049030040c240c00050030912008030041c980031943d40140e0b2550400c80a081e1542013008428019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676365242 1250 676363992 676363999
    0x30301060c0b280209011404170610080309190e04050106060320030f090c030a24060608390301180905060c030c04093305010c020d0f020402041d06 65
    0x707401c42e210100b007507180f01e01090b0341d5035400118110a07a000700000c0c00c40e8164050401d86507501e8017400008800c24401304001f40c40341c4000034807d40c00b4003591400740ca0b0b10300003540c1000d0b007071014001402c01a1105c0030200d141810080f0740070302000d880911807402140045842840e001c1c020301102c8500496004030021150025400e11600b03080300c0d00b11001d440741803002d44d14501400e0500c1d60030b032600d6505010790350701c1c04284081004411005400940190f8071403003a0180003048404c180715a5010600e2000040c1c03031490160200d05001c1700304504407000300b612540d02c0010342400700f202400341d07402100500c11030400b20000340c03140490800c1000440c400c0d07118541da524005016050103000000001c2c20000500d05480040c480500c05101d02407040c80c9040803082c564024030048044225145136054480b00510100c48040c0c54040340000c0580038030132900e4405c04103a642d9004106640016142d0380f0040006050b4040244400d00324096007000303110307019018621 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676366492 1250 676365242 676365271
    0xc0609050a0509040602040506070f0c05030a120e030a05030d141509060607030e0a060c29070311120c0304021c03080c180a06020304081006151808030301060c0b 71
    0xe40301c10221105551003211800c4803a6241c2c901440a84142c1d006075400c0b00c0d0100d0350008100d0131888034010340744a00e0040c420f2980381e405040e92460b1140d8090301100444040c4e5054034003c40d130141800c03c019040d01c000704c1241c0c607000e2035a400035040303a505581d944410401142080e81c929003000074002151940110b40b4002490410040d110038481c4400003103d4003003500034041d403900c45a02800f8020f40310760350000948dc1e1640c100060311903460329401d07942c00c0e40e80c1894146460040b05031046075030f1550101280140381c41610481524010088240b50b469141e40240c414050b141c0b603d681e901c5c251040c800d0813900c651958801d8202c1c0070404000a030003040b0303150b010f680c50407204d850750501105240d0b00b00303506850682000441c0004528180c0c00b000800075509000104c46000300c0d140002400c0b554a44115000c4454001040100503c00c02a0012500d020134840a42070b8951207018107503031083e030000011400c90104da20030012950a0980d11042c44cd12548 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676367742 1250 676366492 676366499
    0x3151e270c06120c040315090204230126070f082401060c030e0603040b0f240f01030608060c0d0c111902060408070303021b040b0a060521040f0c0609 66
    0x1d503140594040f041c3c0c06082240060300ca01c00130415103008641150104010f0b92007452900d0080c5051001607002d0380c10000c00750018140303040b8041c045e00003262401e0f142e80c42c04400c00c94080810401e030304655400054030807220002c10a1402030050304100004140c50840c4680c50b000028014240100520200325003818081401c3c9044803c10b00781400084c50380d24003140c6d600c070030707803003081e4400f5002c4207200611902102c03903441403025031425541d5444401100900380ca100024203420f450200c44941207003040140d52702044018100801c2d0700b03485091443c14a082210704d42020440420304141c405540e0003500d42d04d00300703401c05010203c17521040645030f050840704280981c1c159181d039000c6481d00d104990044c020181501c00035501ea00d0000d4481c0c4d89420781200100940441c070304149010b20a8817508600113080c01382007468050309035500e402000c0801d0340d40d07007208101c6c00c0e048071180c0c0c00c910481c030407500c41a41c03a4081c41c0200c000111034000ea010403d490310b060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676368992 1250 676367742 676367749
    0xf0e0a05030a12060b07052401053304080f102307021509070f1a0a0807030609090b16030e031c0f0c051b01090203151e270c 55
    0x4030200501031600248200382030b403500c3c0180010f58803603040008001602d1042c0080800c6410040d03a4902c040d40e800050f0880303000840c4000c0c01600d621004030340300317200b66944200c1048206c940c0c03404103c504422844800c106500940d02814413504034120308030145405100740440a6001d0100304450145503241d000345092980d810100440d0000225903414000c0040205511951907041c400380790102a01c0d4035946c07940701c1c003e032111700d800c008501a1413a0011011140d501c081d0681048414441141c5410300a0710002c10f140d0f07100004240e60758640116420540108100130060510210b007011420043e508442010324001100140d04004401c072110708001742e0000c44150005004c190003006120100141c00d481c000500d01d120303402c000030b070503601c1940c204000e00c0003240c040c40c2d090380c0c24040001d626401100c00071543c00408000f00ea0030013040181d00100072044000500140001e580e800751410600c03100c100f80315518021051486a420b029044052004011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676370242 1250 676368992 676368997
    0xd0e03012a12051e18011b0e0102030711040203040c0f080109021005090f010807050d0509160f0b0922020d0e07081216081201030c05090c09060702090c16060f0e0a0503 74
    0x680702c0000c0030001c81c030128100c14085e403090009000070003c03410200a0001020700040d00540490300d5003401d01034560000c410390f8136054001c02070040714101a42000000e500c001c1045524001406010654400e180b407407001800c140340c0001213150307030341c010058203100f0100c41c081040020072a42c085900c1e80c0f034880020380000c0c00c0c4207100d0740780d1400541d000d00074200c403507240310700d0b000401040303000000b0b5002e00c80e62071080740d03507120340c4681501444c0c5401f4003d900c0f02034001c0040025078100003844008440c0d0424542e07406c25910421036040c1ea02c4051010303a202d480e40e030445c240641c28081d0310300416094008049038142d050000700b0601580d641e842e00140c103198418240501c1c4003c44400080540082481d03603180d00e02181d015510740100c074020001440040d074042a40c8003210b9001400400349400d142e46542003101c0441c00610600c9122028040011011149130383e200d045442500c0104083c0c3c880c2c08000c0450368031418540a85c1c4c081c2800c01c000c554007008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676371492 1250 676370242 676370281
    0x90501031212180b0117121801091805070809010b0d030e0d020312120c040e400b090105060603040f0c0302031603051e0d0e03012a1205 60
    0x10040401001e00c02d44900034001c10742c00a009020482880041002d0840d00794160345030049003001c1000301c0e40302103548407070b100c2010070717510f50400c29a8800d0b00e18025241c00700070f0514050244036116842200340406c003011000100c0e480c0d605010705c2d15000021aa40310300c0000c000c2148040b8200000c01d1102c400101400340000b07841c0300281030300c80441101c901a005022650f051285004603070150784100140c04c12041c108000c601c0098a0204440c01c80b03409058200080c0c40e080c030303120100000a41c803035018080f2750f44010703100d0b034800c0784c0d940301c2c488110b00c48217200c03000d801c00c000c441c40010401c3d501a4944410817845540314000c1d00c0c0c010b03802403400c04046003103290096521880390006036161040101d0503680000c498403800940e441641030380d107808210306c000402070071503100a40c0a03402204100d40400d11a43c4511410325004001080103490103d81e002c0311035210710a8010350700a80014400282c00000c0034101607400705080203240b8202030404145600902c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676372742 1250 676371492 676371497
    0xd05150a050d02040204030c030b011e050f100c2117040507120c21120c0515100f080102040801050702060403140a090305030d0b01111912051603050309070905010312 73
    0xc21890564480c1c5e81070714055644409000342c025100d04040320303815400d103e580e00a6075410f00c00148014031300a520107c94024225501c8c0d0300390802000310625010031100c0410100102440104905500305100c0240116681008944441c00180b00b80c40219110030a2000d4805101c0082c81c005540350446103045412902140146800c03c480c282e564815104403100d4409421800007030000306140303612921303208001000300401982c42c0007844c28040c0060b0040e4001503100300b070b02510150301a4283c08010505503c82101c00d0200d145a0404a8142c0d40030034140140c4500340300302034010009000420391484c00342d4004050b860140f6078501340b00400300345407000324040c40c40300e000f8650002c01d42e1748400745484420001c208107070740180010703160090b80c491500049003200f4200180e14060001e002142c892a548901d40642d050070001d00f0020b01800d08001608100c22510a07550942d0f00d09010016501d401040c1c0c00c20104d027880c0c84010800294006c401d404400c4460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676373992 1250 676372742 676372759
    0x60e01050f0316020307053c06040209101d1611120d060b0a0c02030706050a1407050c030601061101060503070b0702090709091b021c02060f090f120d05150a05 70
    0x44105d096010b8158002c1507403047c134802d5007850b0079298000031404041c000811b01901030101800920024070881c0c103030f0740c2084c00460701505004200b160300c08030441417407002c5656244208800075807001012151a00c00302809807402c1189000b0f4010705080c50704550000700846130685030041c1400b1240c0d01c41e00011290f90360015504418014260600c1c6942c450000001c050002e5a00c03050480c1b003030080490105606010380c00381e0327902601c980e680b44114a4001d18080e05030b4458a004d40746485940c00d004955038003044801c0c041c1c004e594814000c0d2046042c00350940f403c81c2c01040c401e0f00038480c144036200f450000d50f1011a0100d920796080c5d01d86030000e40c1e00103026080500c2042c20644013126501c1705541c0c140c0700f490365a0071115503490107141c0c0040780c1c0010740080016040309d40841c034071540d0200c0098200113a901640c006000305c802c2c8a207441b81940d10542c420300082000d85085e4000c1c03003402e901c01800180e8110620003000001c80005481c06000c0c0300300f420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676375242 1250 676373992 676374031
    0x10f05040b130c0306050106050307031401060e01030218211606080f1807032312071112030a0336060e01023001120c051003090807030306060e01050f03 67
    0x540381020003113401005c1003010356141c841c010055401201d42c8000300e0300b030a09100d02000200740281c1241c2207640c0f2031f10821170440c0114040c0d4080c0f006680181080c0701071030050b075120090403864040d5080708007050b00b10b4020060401103000515001c0f143d600c201003108642099009500c01101003020285030303640b0301d04c410f680c003481d881c05200d4800e0b1600407041141441041c2c81d071007402c207868448641c100811a60b42d150100141c400424280428000550300002c030004008000788a1040444880842407558111800300c41c0000d452b01e140084950128140544030718604264100c0100016814282e001c0c0c0410010200c1d40e6130000d01221140a5050b1090407900c40c45c1e612244081f0041c20340e550403141000c1e50880c1000c000010300500d01d003c1900103582c012041c2c11050701d81000c00c44800d42c1c4100503014180c99255202c00540050002c0694901ca520006507450a10794002c060310321035030006043c030008001841c4940c0210b815030b644901495a00100d81d000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676376492 1250 676375242 676375253
    0x717030c030f190c0903021e0a0314071a120c04030305031801200c06060306070c0611090603130606090e031e0c1f050c0f09060d1506020d02010f05040b13 68
    0x80520b410210604d400305512040b0381c00316204040380d000302c424400e2207540d10041d1462200d0220003640c0250340c440c0410008100e400700e8214605014243d8118545d181e6010002c50144410308920f65000140c40314183c100402094001012109981c01c09056a8016140b44800b914a140c10746260784c1c5040c280e0400d402c40103003010940b041c5000081170742800c1d1401d0b040089000e45a02580c2c0000b00e0a00300014032903c16401c940e941c00d0404e05648030387c0000d11020541c102c19030402c0010040580b40c64000350301aa1f004103013880749108608202d011201d40703800000b5001c0c18a00e200305500000402c0c7e075561150003003003050881c0c40c081400490f1186042640c6540980c80c4021002148035014100c5402c01281c1801a039413408400103041c4241e0310714a00d040e8003070102c144242422409050410100700001910403507403060035140c10071951100006038400056034000035030a000701000385c40c07128414805800c0c02da0350384c080d0400042c820301801505102e45418841c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676377742 1250 676376492 676376521
    0x60512040b090c040617011d0303070c030302250501140f01050f0d0b040809030d0c0213020307020c040e071401090510030b030a0f1a090d170721020717030c030f 71
    0x100f004008114055881c0b100710f10601600c00c01d69100d500e444d800d03a40080341222002c00180394200518550340d58030300282c0704440d09000075000c041e402d01c031311a02510001c600c00d214441f00700304000801b51502e051401d65042128141126034000c007070007480642441901d0642d40222403011000d9015004190074440414000d07107100003107401d00050011902c01898054000d40590f01c1e017001280e410b841041c0c56402c000e410024240203081d0201440c4e003d15007011552059072801d001d000009000c2e40c2d42c2c1200b031030941d0050002006030380d4107981018402c0000382000e45c03c1d00d2a200025080318014041201490f456030b00620207039805101e204030940e801034500c00011158100580c01da051840324000700070544010401813000043c0d03040c900c180e207646a4010003225242c0c100078100c05009001444844403000c1620040d81e40001d40b402c840110044c0c94600500304800091406840500c100500f00244030900c1084002c407540400741c8005030116450381801026001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676378992 1250 676377742 676377763
    0x2060913060b07050c03030f090d02010309050d11010605010e010e040c0c020909060f0c030610110c0a29070b0a1e020d0c030e0d0e1507080f0c07060512040b09 70
    0x103140400c0418120b4568010304401c50059040b644511400301c00d05070750748144440c50100040904c0142118a40000300b0307210b091040c50081144465650755500e8003106000040110703900303041d42020804d092040c3c20050809181603101c0d0744050002030000d0f14503104060080e0f44030441c0000c40790183c07150342e448960180070719402d4030b480e03a105900e03100c3c1a583da02301d580c0f207080410703418111001500e0060000030410f0f0704003c0b00103011755291041400041190164884101c150768030443c1c600010496030801d810380d140103d541c03c8000c03620b07600b1203803510800d202c07100206a1250103980d106202c841c0000713003000080082c0170785003881d03000003501c1d0340001400c009204054101145a1015403814050a900d81c0c04154840954200c1c040000d030070582a4400c034606a1482e01c40307554402102d5242203991303110400158007081516010004c00600a085403808102600040c07426240047c103003a0500013445c0305c1400a400504000c80103004240400380612004004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676380242 1250 676378992 676379029
    0x1031506172a0705010b04090b01050d11030f0f060c0a0f080a11040306090308060f360109050106021603050c01030903120606081515030a0213030f0804171504020609 73
    0x100309a40289030543c45100110b825508200369691141400d028a0792940d0303001c0d42c2186268207180c140020a6212401030f100014560f5130503540e43c40903c940b02110040e900503040080c00511303000c0c900440a416502d40c0c80f02004420f00ca65840102c0c2220408a8600158aa03c40640c624054603d400688122400001780041044215070125000c2c600c01d46404000d5656081040000401e0020f4141c02c490000c0b82401d0b094000544250f20100240c034a07020300270070440074020700314240c00c0360082503500d90050008940402103044c43e8804440082042d41c11a907916445a01d101102814903884d000d2150800d070080038194625800e50343e003001103568400e0010503035402a00c826202c80030b082285503d03801d00201c104c0351300d05071000c03141c6940c5808180100035481030081c003620510010002c40082c1000080c000b41c14054900141c550f410302c0105015070407140f86040720343d40301c4c0c025000001e1906100320740c0035404990749a00d403031221000c581e08060780041d0f45039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676381492 1250 676380242 676380301
    0x804081b12210f041a090709060807050427170712030f05060d0c03080706090503040f1505030403020d11101503050c0a050310051b03040308060103150617 68
    0x450504800b0b5461900d0441c1d5200c46881d440942149814159000780c4140c05408643c0c25599030810f00c0c9070498403078000c4550007903688012008955664200d80700039003040b48104028a05030240d854080a09460466680071503140c1c20200b03142c1ca940200300d5000a1031801c900200302c42914a80d60b0801560001a101803c0007001004107420804a180c41c0c1341c0860a58140791584a00342036120502d40201c40c01c54803840da01d42c202405c2243c03010b894245410000d00180082c000810111841d103052908140d8120030300310041c103814013008070600410000c00e030b000801c0c034800419810140030f00405441c10074280000f140c2d800f540107060443c80d10b0403c006a181c1002c40340204260740c60003001008000b4080030a124155060344985001000c698251f03004541140d041414188007400800d142001354000700d4082e0042a005010000503507014024220a07141d041103048000307080034405011070022403000401540d01800182074480b807600155420700e082c031100da4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676382742 1250 676381492 676381507
    0x912091d0402031e1e1603030e1c0f0b0a05150405190c0905030c030a0809090702160605040e0609040305160f0f0b180303101203020c04060b0315010804081b12 70
    0x245d41c3c8514110513140340343e0b6403140401c40500810402e50307810130400d40c503410501d940c45c1140c0071240c4480c4241d0040022660000c0d25070880c2c00000101d00c43c071210702d54100c6d141894882484010302503030016043c1402c01901b80202c2c02580030300c440403600050b40b074071941043c00c1046130140c641074a6030301c0e00107031640c00c542084126003160000c030201d840e800e50300d2084c180c84103041072006004200a00440e02240741100340035512038146e10441e280b0107c503480b202c90390485a480840803074030014040c040e282420560f0baa00c01c3c025288071075241040e0307400030401c0c4500002d2040c07030fa0014603d038042000105210350b403140c100c1251200a041d42c2840d1445032415541c0c0c0c104502040300307500d013521010003078911510826040070259858603400e429621102d90049003140070b1045441126641c52007008007901710840350700d4903858251404040c1d10201302c44103050001400401000507106001c59001810042807139016030300c1d940c046c502d0803401a4000911f0305001c84c414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676383992 1250 676382742 676382803
    0x2011509050105030c04180201030c020a06020a0807090603020a020715110709020a1e0c0201050f0d020a0c050c0d0506040809120d080f0106030e060609190f0912091d040203 76
    0x40c1038507812000d842c0e49039003240401c03040f100d05400007980d00c047c8691450156010341e000c041a00b00c170740150b0b40f000c11199103400880e4409114540482d1809003406110703130340804010b000c0c0c030542c10210f180c00ca100c100070356141c4aa125a41c40003820320802400c252040e05031a4949907010101c510054460342100040c2d0015085940000c8003c3d1a000c8070703407580c4048052550840e100e121941e481900116501e50102d46046440034003000881710304202440103100c4096180e4494102104a140141c1400500b0504070f2180c0c0000c0440c00c04100c4c04190150010390000c2c000d0358551440e0003050200c010122441061b000f601c0303000c002030781c00c2042c0c10300c0340d24895403052041ea2107940940403140300b684100f416600110000d0a01e00380008032070707040f0051420f032150b00341d1248440000e0311040c4514a8250f5196904442048100a040d185280840c00d112000070b00b003001d601c1d504041020070181c44500107012400f952130030303c03651502601a03641c03000482d4011a94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676385242 1250 676383992 676384001
    0x30e030a0c12080610110a02090f1605190810050607050d030510060504030303020a0e09090703140d0c240507110c10120e1203040f030207080f1c02011509 68
    0x10b0350001180245003560900c1510314138401c3c84001c04040300d0780d07940340c000c603603d000810344011140304205000300981d445c000f0443c46044210140240c0749040045080c5030b0f40074074400d0041c481e040c0304008900c11080c605c01c0000340d20f46400c000b0703a81c0b02500102d52108030f42c000b07900510001411001c1c044081440025183c2540b014440d5071944046090444400d200c0d020002d0b5040c841800043d103c2c1c1c008200c4403109207021208290303120700241940d101030714030421550010b1400c0082000c01c000f41d81210381b45030040c00310114090000b81140740c8d80c100c000d100040c440f90078203411459074502c10813030312000800c020b1440d003500301405400c40282e05901c3c3c0d204400300300c089450402c1d06840500c0c4a50384910118210b15801d40c00b0b41042c00d6041c0b042c0c021105810340806098001d17510480c00307180005c4d4081c000c3d08010703062000039003002032a0340000801c080b2284000030070b1082c0100410022111040c0168101d00411402c9240d2040104c00c0c400000c101c18603401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676386492 1250 676385242 676385267
    0x190303090807060f020604022205010609050102010f140103030f140c010903090b1c0f0605060708180a1413060e100f14090c2d03040605160816030e030a 67
    0x11207541c55150f180c1528034111074800c0301d00680c04400050014202041440500c08800c50b503100d0002405101c00c1c01d4640c260405c40000b540680204015a0309000307017949071012550401501e403040c8844e41d000320050201400b40700c91001800b40461140002095106405840e2500c030003400303000d0b602a042800081d00000c94509000c500e0b8007032001114100c08003860800702d0f240070400032074054038051030b940c2e54043e81c4402c001095210b2070300030b0207040e02c20310050790364200c2050000350036014610020300480411005221504c201c209200035240220341101c420003504441e50003410745074202c45007510804003840010b0541c1c030710030000d55000c400c0e008134203901c8030800b000d0920b01d0002c0d140d0000d420004260a049904010315210030107401401c82e0315510100012046d040c4002001c40742000004c000c2030021a00c101034020740c1240c5152042e4002c2c01c402030044101824080c4148404810307840c607503010382d00c00c030b0116030303050141d1b6118891201c2c0070340b03505038002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676387742 1250 676386492 676386509
    0x2d200c0f070e06180106080a0e030d0608030d0501090b011b020406090608060a0c1b0807260c16030b0a23092b020d0809103204030905040b19030309 65
    0x43c102418003404c0401c0d81030320f400780d82d070480c07075a01c0404007030190014000300442408104001c407070030611402100054006080110307968041c1c450302004a0308164000c120003031070030700c0390202030f81d008502c01809200c158516140e00f40034000140100016031042c1a080d1030000c0010f48010003203141c80c81841c00d40c80030404030101030425600d81e0f14801c0e0141030340998401940009401c880074118150140204004071540e4640c00031031034450180d003002044d008070311b1440003441007100310255041d9480c1101920724680c0d582204400c050040018503031102c50020b0a24000e902282c0c001e090a0145079403420312042ca540c03100500c9110f0144003000107990418141d10080500c56000310340c1c0140740310348c0c070b10608860a039000707070518241d4090b5440381c80720400203000d0085001d12109811008c000e01034161150812499006251419004200804a0303080070100c001ca032420345021881c25000d10020704500040b000301e402c04c01c11010b001c82415402001c42c020746031040f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676388992 1250 676387742 676387759
    0x19180b07020d08060d0503120906160906080402010c0503120a051509061c0320072d140102121305040501050105070f080d020d2d200c0f070e06 63
    0x350200e841d400601545400319456001007490f0b414403010b1410000d0051080e00d06100311043c244841120655450b0407030f5100c101801a903815070215511001258200010011f1400c81d014060100051000e418040c03500002414440c0a004640209800b580f41d4505490400441d000606080c2e86000406045101d9011241130400d070460103404010865440301c028010b01440881d0360800403420001c040480c0b42d220702c2d070085a01d41c0c200000000d13100d840d08140b13600c180c000da03070172200c040c500c0da030509003482518051000c1c040d240b5600040e00402d019000503858a8183d071009204044005011038511107100ca03410103594040301d061140d40da07180011501802103050182c860038600700c41c03d002402d003500404402241c2c40d00541004560b07508002208c0c0c80c02850307010b000c01540c4c0b2301ca1000c09040503030807699403c02d08010074045420010a05455000b18030800031001500862074003040005c0652010004101e403141500d130003000700d40480585059000b0201f8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676390242 1250 676388992 676389001
    0x402041e0e16120b04090c03080d050c190309030504120317010f080303070e04060513050a0506040e03120c04030807050a05010f09030509091801020c0c09010f05030a0b19180b 77
    0x3039190b00080595074500788141d140500c44020100c10304410340c020f41d20008100095030300000d0000a5000e69a010b4840501c0103d100a442e0001c05060704004208440301d01e50141d112020011180ca20300003916101c2c52030181c80340d100c0d9401c42000c250010802c90105540001101d10500010042c400350340d90360750303400e40e0701030590140c0d030840c0c0c0007030000507a51b0b48580032100c0c004100405c003040160ba15408a030081000d44108001c5030386500401080c208075025541c0c010300d06460800507403004100b0a500c9018401e003642c0b00c0c21821002c03c440008500c107442c007541c4c000d40e010b907032250940341490340e4000e070341402c0b40c0035424000002001c200a00ca001403003034040c0c0342c0382e1070b01c0e00320400c0001d60000202140512510003903410550a03091024061440000c13005004600c4210100f02800074141d2014103948115201403000e40c4000c1541000075510082d0203101d40c840a840c01501b041140f009007489180c51440d50703055007001680c0068074042c503205820341c0c48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676391492 1250 676390242 676390261
    0x32f06011412060105150f0d0c03020901030c021506011d0312042d03060b0d140706112a0604120605150616030e0d08030907080601051002060708060402041e0e 70
    0xc00d120b03040d0701c44849540c0707006c5132605400800e4142080500e561414510010100c00c0752840d4500d100000e0340842d41011702c1d6010300c1582c2e000200e40c00103051419035902040d50040b13000b44207a0411064900b07014082c940c000001007440c20007410364900c03c0c8601c00140290300144640c030412034002241c07900d603900c0c0c154412030a10102110200450658807250060152106040e03004000d00d4800d0020543d035511403190001e910f8080c1504a25051008001c0303000c21100c0d9107143c00c0381d0b180c04005050151240602550039219078828443d407800509a401294070040400500c001000d00700803290b170141d03103d10740422040b40440d04002c00e00089000717507134402c8051603d045508000c0b07401100d40e01c00c54580100b0a0406120035914088141c005135080c030304c25400500d003808400c00c24440350380940020b43e0312001003415070000941c0c1e60005841ca00074480714030b010580035111601100c0c00740005401503e043c849200e03140002860341c2c42014101514200400c51000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676392742 1250 676391492 676391503
    0xd0504080604170c060f01050f030d08130321020705070b091c26120708060307090b030a0606060509040507210b0402042402120304032f06011412 64
    0x300503400421031603465070b031040f042d41910a4800c220850602000840f820108256445410f500203c0c1da540d5241c40c1c18440a03082c0310038014030941048901000c06680085166400415030910004510083c05c090303c100114100c50400c1040d540f51301c404d501d030507400910780d841c442d00455010595a8419258038014420000d900020380c00c6a201e1788655070322a0320130903003c0c054880c2e003440005500d00b40090282d81090f480301001c10142d00140082c450180d0140507405d20301c41925010780041d84a64490145070103844e03030b41403030f00d607140c50403c0004501c42c0d001c1ca04201c480c0d01d60b00098001c1c0c1000c1c40485c030513402c000010340344034807030081803c1c0401d0041d40c442c040800803107020301500c404004e403034000b6800d1000244a208950080c810302042d44426074402003803000007810100b06400ba01540c039010418880080c1e80501025514031000d00101d00007043c00c00b00d40044440c8650282180c8240c000201e4441c04601b4001c40c041804c94007401c4804400400ca44c60b035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676393992 1250 676392742 676392749
    0x50915090706090b0a0908070909030806040b0919022205041803120b04090f1113020403050718090203070905063d050f1305040f1506030c020304081e0d0504 69
    0x705401c0b0200013100c481d801074881001c081c00d280070250b46035040c103458440203034400503c1607110340070354051540111a094005c1020b03102480403400f05400305540701c8001c0c0810240407480000c09041c3d203030b2941030380e000b80d00052602207250024030107048503e6660103814841c52521124550703031012081c0c4100b03440d41c1034660000d04d00803580d4801c000c00703418040e00c2d009a122101741c0d00260015900e400c400d8400d41a4800081c840c106204504503500b0030f00e8040d601c100424008500700040d040c084031402440f42c0a640d190310355a0004c0e01c810000290140b00d40180420301030718a8020f144102000d0341d01201d06094404103901100e20480c0500b410b84c1070880c54010b0803a00e80c040c1c0301080d202c3c14000c2c030f048842d40c0140199031107000c485509406401081c041407409014040341c0b608251011b0101c02e610300036046008000384aa00c0903d42e591007071f40d94850084c030541340180114015101690843c02c0c010020400c4044000200d00075916030090722801802520242c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676395242 1250 676393992 676393997
    0x302090a0203131101180b0c06011208040b0d0f02070b07110c010e04091a0114031c0e09060f0a0305010204050f0301051608090715020d020d0504210f0204050915090706 74
    0x2102081d20764448a1240191480c100280d1b18148140328148001d050300401000e501d0035507500440604500b4094103030007641400d10b0224410010400e1007003a5000d0b50309480002c4c0d40c503100c80040300005e00e03039808074050305030003c1102001c1c0300b0b1a4070040d11071b0a854699a004c000c0a0381496256415010340c28041051f440c016240c5003419401b50301114882c94010b006140e940d92046c0390280264881401001061107500303203410b003401040c0c240d450112404203401e506a002400036202d4650490050803040c0c006040c070380e14248894002c1d04081c0c045110030340c8a0400300c1c042d40c007c4c000d86014140000d022281c0b418140b00e9075100303683d51031038014080710410702200c0e40000540318144a103d95540030400151200c0c540360707044925001442c40b50540f55000e07040031840c3c1d60f04004d001051208018a04403001e803011802c04010850020001600c1d14809c00004104013079007040c90a13080098280002840c01003458000882e01001d075600f860036541d070021030081800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676396492 1250 676395242 676395271
    0x90510050f0706060321021c0f031e180b010f0e0606071103152e050d030309050a030c1a0103080706020f1216110f030a051b0a0605010302090a0203 65
    0x1010038004002e06281c2c0d00c22107000c030750503a40391117502040242100003d00034944c01081196180c04212158000390301e011020000c080c11200581f00c8a401002541416103030f440308a040c0d100c1c210103c0081c494043c042041c0c4c0340321001d0000c01c00803000111a41810100081030120030040c2000454107641905952603403614103014080e080f4950803180c1d41e0f0104030342e20780c03658288aa051121200d44401042d440c151480c25250780c000b5441902003210041992003c14400e8900400c4e500143d074211510856407034220028012002d0180c81d0f4013984500004040d44001800c0b0340b40c1c003c0d2840c4541e00340b61506084025428400140b040c03000f003014000180194001e410941d000070301d02410140060003150078074074110740b1001c0e80a072170701119441c1c640101d0401295000c0320700503c3c511240c4d0f06465924405c412b0b0250500030049034008060341640d144c1441e0140a43c280c41d5210064030340b84000d404280012440381c594880014842c152510030769116401800100c03c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676397742 1250 676396492 676396507
    0x1002030c0702190f1e050d0302060a0b0a03060207080310150e19030506040303050603010f0e0c120f0d02060601030f05040b040b0603071208030f090a05250f060302070309051005 78
    0x4241e066268000c04030004103000161080683e20b20b00014950111702601c4588080d05121401a03607400843c400c070340440c80c074408241d00088071540302c81d4204001402207225000a0300c10001da43c0001d010b0b40c0006540001c02a0b50400781d4000c50080607406103103a10b441a04ea04441954501d0b40060344a56903010359281c48050051040c000101900300c2c0f544a440302410280120340542c00b0940340c4052010a0909118503182c5000c440300030000340c6001d22116443d006004e8000d0b00c00d845203801500309031802d01120021400d000210365a218007800b0182d1201e40848416011a2800700c84041680280c090284280e5000403404402c0d942c542c2e9600081d44050615509441a100c012801c0682000e0747e5090b6402030062a80741c0c41c1c00c8400c200c1a4100404050072074014404c65400070b0790004074812503038281d003c6107518000288032480130000c507600a1030041c6072400002900d58065000384071042c080c1c0c0c1ca0a01c59a00c4906111030001340074200c50010703e04002c00e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676398992 1250 676397742 676397749
    0x606130b01030204181b030b100305180d170c13050d060609050702160f0f03080c0309040903050d15050a060c020d02060a050949021207081002030c0702 67
    0xc4001a0505006003000d8031202c0d12035040650311450440240d0790013041c1d00c0d02c4011086031076005801c0c80c0500400d4a40000716003c00c031050340410034961184040b9581c1461a0100488400c00300116400312070a0000102030340000c28600400700c101e8000701d513000315208201c0c0c5411000214411302580380c0700c14403d03440d030100020354030940d07210400700b4010254000d85000e020103a0040076815503110140d800003040b0303840301040001d0003100b007114800202c80b8400f2a600482c04a4541a13490f084500754800d462209500900d08a584800c040d0001c01804c0c21124450041007900d0303c080f248000a051800349591048001101b001018420000c8000d010720281c0814508000369010650303903045400351802181d804140d407000ea04100d41c6d2100c018855000c9001c0312810300f000308010001c1030700c0c0d01c0c0150120b10704000211806400800b80720358060500350141644c850401d884481d10f01032800640240301d0f61240c060414000c5d40d002e18420380c0007514018065080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676400242 1250 676398992 676399001
    0x80c1611010c0507030b01051302130b0a050f040602070608060d020d150e16051503010f030f1110120f0c08060409111c0209010b160b060a09020705031b060613 70
    0x1481d0420450040b00070000b54103100c0c3d00002c621480100b030507541450200309100d00441e00c030782a440d20502030501a0021303403040310102d405209980b951360010140864061003a070085120540002a000648030b9000504c101100c00c181d6130308546446880070040c0c0c1d02c810010181d4403500c10840f020110b040c0c049041110381181c1c070300040609044030310714205031045041d40d50f0f18810102c10022420005541d4038400c0e030785c030b2542d49550f041c40c08600c0c900700b050002400c006034001d9041c0400084040614124000512051503a210316100400200411100600490401110340200465802084500c15541c0c6600003259a40401d01000b09481042502c40c079041e00d8031b885094441c80040d03210b1040d03000c011204503c160051240d603070380c1170784010b202950030084083c01035281c4800042059000d032304031b0025100c003400205840034580141801b10f01c00100d0038100b0000200410485503d1000c0c01c4120880001c6103031151002c40700260405403100b2409401641e07a4007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676401492 1250 676400242 676400273
    0x2708060411210c0910061706040b1c0c090b0a0e0a0f063201080105060903071509080105010f080a021c08040b030a0e010e0c1e0909010507080c16 64
    0x40410b0001550400500c80e074240c84240a05400020f0000c40c2070a10029880d840707080d41807042922881e188000b04042a1091010108204007001c40c4203580c807500050083c030f4000303040e290400c1404120543e401c3c02c0800864581881140005902c61107000e03042d19204001c03d04c9000034035190240301c3c0180010600b040d203036a43c40140c001c0300e0b00b620032880900501084808140140072003500e60389a941500c0414031000c0380040056a80128a1419100140c80b00342d00c90409a02207072501e00135801030800ea904810001141640c02649401200c40110080c0403599030b64030103000e06c4e41c160042d0310b002d8000c1c451005c0035050016441b080140c8041c0411240d0103a9103c1c0007460700150411031174801c1c00424009840c07514013031084004002c5000b0021181c54a100035078551240303213054081c002c20810440b10030503954100400c0c9502400051342840d103400700a00034041241c985002c0b421010226901e4a004c200b83c80c442d4085212442c034950f025164008803a06e00790 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676402742 1250 676401492 676401499
    0x80a030213150201091703010e070c021f030506010e06031b0f13031a06120a1401020c030c0307031b150908070516060206011a0301090b0102010213062708060411 71
    0x40e00081e000b44180140312201403035070000a802540d4501040c440c070300d021400f80450300610051011060803501c00d500000e0300e013040c4094500741c0c1702040c6204000c072030050401c000180c81d0411076826401640c80340d0400d0b41c800e280c80c0c100504006240c0400e0b540c200a1081c0c035041e0a016501490040c49610310192069042015031100751032400c40c2500300708ca0607440201514280d0035175104403030b00000111240004e108010480d150784501c040c80160605540b2030704e80084803c02c2d4100d074020144441500d03a100d01c2c03520840e03600d6010140440000f50040c0744580d44424000c07005101a078483d07501c00c0f008130b02c130203050050888400c003511626800c2046900041c0200094110500d42c8107460004618102d80a810300310160f0001c215244202002000381c01c80c601120306440d5981000107607881c0e4140103e0082c028409400219001b100f000b06000b5040010460040028030b80c46002d10b0140d04808409541e502c078540403a48440e0108000901045035031000c5007026 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676403992 1250 676402742 676402777
    0x180714060a0306081020030103050a02041a0a030b01051306081002130b0a08040b160e010309061103011211040c2a0819171005190b0d0c0807020703080a0302 69
    0xc1c3c104600b0070145400301d40721143d9560703a0f0046c034910300fa010800350840c4c41089055624540700e01d9126203114100030711441c1c0e036000181585140000b1071117405000740c410308001d6100e240400c4415028000c4500c100c1e1040c01c5000c4045885c050407058be1400301c06808080381c48001c85019421407844202d444404010104500003180003a103450070b219660706406042c40c0c204800c10503006041407202d04401c4100340309042d00080121b80d03542003880d0008082c46503040103002025240724010f6840303c000000988014440b03419450580104908101c40c0c2500040100f183d805500300404100c407110203015407030041560483e070400e05441c0b1401d004056980c0c8040da4480560041d0084144034052591b070b5100100c013145030f48050807100582410000040486083d1003104c0c07140b085010369007032807c60071090f84010b180b14103c040e12007008810a8016200d540f03440c0380001c1d03501c0c0024146520000789c0104483d04040440d141c282c03c5002100650f00400324107000d00d0b00c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676405242 1250 676403992 676403999
    0x5070f080a080114010f0e0f0604120b0916030b01030818041e11070803060f060415021b0f0a03030305100503120c011404211214180714060a0306 64
    0x40c00c00a00700d6102955039003400c1d40c18032a5000b901d107812280c480c100241030708017101c0c03982c00c03034070507010b0040491380c6001c00d010f8903000400d40c3c482c0f50000d001d1f05c0041703500c1c1c50420100307040090050420781d0a41e07444100284801c415401284405404402600c0041002c00c0500b002400141f419560b001d0b143d003e440040340c151100c61404800924071720030807074030049540c42400c0303da0101d0207075a440d2000e1929201c0e881d002c05482140b00d05904841f50501342e80c0c500844000b09480da0900829202003117029450f0304a9022520132115610704407241843c1207043e800711140020103103c01c2c5804c64a04800800000f002c182040c05010030210301d5a81c104020709004041140712a503074410179003641c0c00e558100684000a03200da80920000500130a0b0000050600082100461203249801c840068480e95105200f40c500002e040c7d03101092441d0744c1c0f05400c0900e011307030800c01021406075101c106100d00346060700c07442c7c0d452143e8a08040100580d50641c03801041d0f5a48 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676406492 1250 676405242 676405253
    0x80f03031824191a010206010803090d02060d06030f060204030c0501050a1706010333060f0c0b070203091e0306061f0c021305010807080105090c130b010309080412060b0604031205070f 81
    0x8446401030800e0b4108184c00303043d6031304105007409818142c01a605004032000884c00c20f11043c00028440c4001003042170384206113910002c0190f40090020030000c80c541460310080d80700e4001a5403410001e840802ea650144080350f0002032189d560300490b11b2910f10a03074010102512241c10035486120201c04074140d60400488040d05a443c0c8480c207100405180c1c0f07250b0360364482170600c0611010820801e400240208105820105294040c4e0f51100100e0951149148940c0d2001d000445001000709d0507403e444c0d00300e0260129030661701d540c41000010340c508078500c410380304800800d002c22803154207202d110f10303c042c010130700da03211080101040d140c0c241c000100c1c6500038030b010043d040d024001d0f150031494000182c5040100c1402141e014845001810745941d2900803072501a4405c0e405540003942140345681c4075511540308034000807401c1419911141000128403a500d408422501201e600200210b1408028181035510390000c060542c1c22400d609206008601c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676407742 1250 676406492 676406501
    0x30509070504020307050c07150f051c020f25080414040f0f020306100507031403071803110a06050f070f1a040501090b010617070509030304080f0303182419 69
    0x248544415840b161710071f214514200440e401150140c1c0020018000190400c00070010220913240c2036503540311600c12071041c401482d03d41d0202ca88001150342005180b040582440142e00011410003a140c500315884420f108030080c040220800003004180042c0c0940c040c0040054030229100200300f02c03540031901600c60080b4190b40020400500346810007009080803c42d04081d401c104840c6c0300200b20012041c854a0f44110020106030001e001da00180003410380c0020ba039070060f0701d07490000d9600c4007408440340540722890000c504240104256070600c40b4030403906003441c40035113561031004200e50742134a49002e020031100b84214001c9c801440b950080001061980e45450140c2e503800d4145d00610400081c0d090060603c265150520740101c02450300c00c0c1c031030303d10350b0010b03045110399440802c10f4801c2c5001000380950102c003035449805005d00400e207031107140f406562a01c0c901c214101c140942c81d0503001150222a010680000224100c184c10b0740c14000404100e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676408992 1250 676407742 676407751
    0x20414091209180109091a010617040204110a030603030f020307030e0607030c0209010b1c18111518040b1903030302031b0a050c160f0302091f1e0b0304030905010305090705040203 79
    0x9529007071003400707216440d415070192030300c4240307c1c2c860341d03250040090800c2801c1c0c0c180046040ca0a0205081d5540c1d5040341c0381104000d00c41030340d40d651102000c0c008180c20b200481c0402c03840410f5048807070000c8141c82103a50152205128102c0c240300304020755002c200120280180c010305000940c0b501c0326114081c12600b440c5a5403001e144d0481848a54055840e9101a0810306440345e0502c0c281280c02e41c15031302c4520900d180d15000d0004040006003940d02c684a031010521044111440291040c550402d850400a40700880240604c0b54108802c8254a8501c0c080420009100b0744c01541d108002c101c0b81c0c245801d074030346068100c0d03100072003840000b480810a66000380c002d01c4182200345211082900722071070b1140b04a034070700b0780348006445000b10600040e200b5248074a4031940c2d00040810051880d01c8040603019201884810505010f2804010550b40e07151070441e805540c050300d440c4920351070b000045003c3e0800810000f090f0007503040005a076180c0d1b00195000707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676410242 1250 676408992 676409009
    0x5070c0308060301060f05120a060c0e0424031e0c06033309020705011407020a050607080c030c0d020913050105010e0a230303040f0609030204140912091801 69
    0x14288942401440d054016084030311a03407402004010701180207440384111042504e1000641480c0c0c0b41c0c00742041341d09000503100608040d5a02c102d140d10200311941c0050440d0304116603d1007d100c0c581d040000a5039484031000c1c0300d400d10108526441c100305100d078840c0b003050845a2581d0301503a500c1654000008281c03104080050001d00d000500c0c00300b450a01600801c2280d84602140c40209114071909558005032580600200b0b400407210100a14492400e5040c04e05c0b00a644010380007098940d8000c5502043c0b0b00c0344281c98042c00f42d86058038a900f0340d2200c01d008601d65008200e0f6200312582084a00e0340c82d2140c0c0c04000c8011000720001500b0740c50034001410310184040094454107075013400340700d100002d924040c4002250039000d440b008640021031715500c9550456141c2c0600b14500080e2142d02c0340c860011359200799001d11004403181e40090300748074140d130280d0171a040100f05410401d500c1014082410b0002d00e40384c4aaa4620604030010100780c208110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676411492 1250 676410242 676410257
    0xb040f1e0602030f011401020d110c0607110a06021203060f010c021809010f06030503070605042906030c06040302091620030903010606080105060d020c010b060c011b030c050901140d0507 82
    0x41580d9040c0c4d5050040044081641c0d0a0f41c1b0400003e40b1030a5042803d002d00004055500d42c0000c20495000f20003005040b05a56455038103081110303a22804106109903c60b0602190a604c007142c0d514907200b59000003801c1d0740303809003042511000080e4003410081c3e008100da015950701d10b002d0f481e01c8080c001900007401c0940e200303420740f60503040a8004e681085000c20000700008111603160b6001076000481d07072154641242080c184203054032900d007040844082400002d40c0c1e032801401c084040303a00054240046c0700749401a84006035001040d40005480c50240000c5926946a03070300d01000c11030f850300f000c401d2108500a90070025480403ea59007581001d109110141085080c00300c1c031580344c100040e0507449111003201000740c02240006003240b094104820740e283c001c00b200d842d040d02c8609140200007841c10610030800404595890354040d12403c0007c4a40d955003516241c0700c0f00c0155004104282c80004151040041844a4901f8401c42c0d00440051307840cae01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676412742 1250 676411492 676411501
    0x12040b0106110d0516080c06090c090609010e04030c02100201060503070f030503091504030b01060c06180803060d0809101e030b0307140102030c060a05011706040b040f1e060203 78
    0x22050580010381804a600160440d06800252031640340e1124030700207aa5030080c0180e40b089502040009000e450041912440c8400204540c1d1144402030704a4168405203010440a54800d640c0c55401c000301d803005100b81a80781d0b07803140d4494020b0800c1c81303420326103501090040600100c5840180d6503000c00340500c1c0b50a000d5000103250a0030310410b00390131901c403180c8070b10076110352034440c0d900303035440d0544070105800351001190001241d0880350707500c00c40a04072001c4106c0c12904c15140c00d40455001381300c0900c003025260441c01950441c1c0e01d250034000e40c81d400300310a890500091003c81610f070340d1009802e00503000daa840450000058440d00e034032018450b2242c0c01c0c5400c0c6071420406440014442c021100c000861440d08a10900140d080d440303881c1030141e482c000c15040160030800c581000381240c1d007001d0040000450021210748640c416900100b081c0128004900030905907581c2108490003841c0d0340001010201010500c103108400c2180c54540100410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676413992 1250 676412742 676412753
    0x8010c0e0607020307060f0903080309150705070f0b070302040801050a0c0305090a0f0201080c070803090703031220030916090f200a11120a030f050901091a0403030f021204 76
    0x14003030400a07a0301908000e0350b9030000b41c4543c1030b401070340204035022054080c9544521001c100854009048540d40d0600c1c0d4007103511084114100501200c6100101d24490311440c00c54010607040300c0d041c0441c2c50b055031240701c1800302814040801d5003c0c80007003000003007803048034000c0010f80000100041e071040e025040e1280248203601640142442c1ca000c01c0a644401c41a681e09103040340380d13070740c600710003000a008154010b01500000f0040205c00703030000170342100b038070701946075080b103803204071011402d407904000c00c0d0104c0c1c0c010040c0340780b60b0780e41e1a01458011080c0070a9401410860035401c0740c01c1050751002400175224030b25000701029a100d403014100d1703074002043d620044289500d00d03900c00d117128001000f2441e81c60f80c40e0b489050154240a181c100160703951350348010401005440c41c2d00400c00d00c0d524160110b40003500500c54150000c0d0f000710710948450030003080c6898403900501c107605240e1035555074507866040d40700818509030300b1010000d06003000e040a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676415242 1250 676413992 676414007
    0x109050c010c12120207350f0d0207020d050a230a080301050d020406150c050114070e0d1703070518040c122301030f051606050711011808010c 63
    0x2107418000403800328000b00350041d902030b80c1203c0350f00380245030f607000401d01c0c0002d124130311028010f91003800c450b40715401e1901c0c00313003c02d50b407440d03040400c140406005c890390300c00d400310840f03499020000804031440a070080e202090004004614000c0c2ca40c40d05411700c031a04404403211401e6040f003490103031307040b48080d49032200d410040a030049640e4400c60184010b025aa21404c10350140c501155296040340c00503105e10709107a03e110350080c80141a2043d114802c0303405509101102204c0b600000c034081c4184019a601020611450107105008481c1c80c0c05644880c0c4040c03000c540c819803440118001c40066484d03035503842072001501c4003440d044071560f208500b00f8101d0803055070310110030b603c041180c0e0130014410b068108805104610110a05201520080000b0620440c080d04c05070150051041e01c41402220742c540032090003c2c0250350224000744060707004074100001d914040341060504c448111862801c106840d49140e000c00c050303030344900101244983c8400c1707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676416492 1250 676415242 676415263
    0x51512150a0f08030901030207110d06020307260114030a05010e2a09150621060306011e032d120f021917041206020c060c2b0204090e010905 62
    0x6150b07100e642405681c0f41c50344074420032141010340111380e000921940216030300071341030001c2103218445498501503010390401c54406021980210003a100545030781c1c40320b40031042c3c0316800e82880e0700f081484404080d08081080d0180b007031101c05000990300344901c080342032284009204540544444100c400380d02200012201e40d0030000a085d0b881b408580c54000c507209801d910b03000300200204040d405018040c44544600b01d03000c0c5917405856800c10b000720000d406581c0d4583c0c90784c0050040e0b154080ca105034035807403441d040000c100f80e00c40c55202100d440c0300003103907030070340d035060303208000e80203e09451420041c0c407001041500082e12182e00c00701c50000d00f60310030510344800c40c08040c010010703085502c040d00d2100c4000b411400c84020748100c25858070000000c1c280200290400869510a803088201081c1400808070a40c0ca500c2c2d950380754002024492400043c0301e07444003401d50819502884085480c203014040c0081e2303a01035200010b8088200c0c14580d140c9440501d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676417742 1250 676416492 676416509
    0x6021603180909200127050406080c090411011806110d030c09030f0213020307120b0406150f0306050a0909030e0f060703050f090a030b0114090c04051512150a 70
    0x8541c01c000303801c0b00300c400361043c9025140003040c8005030040e00ca0b1b07801401c0402c6510381c000700030306910603880c00c02400c0e03910503102082010384400300980d171491440c2c2481e500000001c0002c00155811651600515040c5040c010004008440c203503402040d400207400701c5c0e0700c0150714401c00e00402560680146518040c40300b404243d0020b0a168140d0201900c2e001418846030195181c00c0300c080c42141d020f11046580f85010207006047c0c0d13500c016401c420030306001c08092189040c2c01404107031511101d5000458881c800150360280f1202d038908181070b109c54001501350384440d2a0340040200c510003054120052800038040c00d80d0050702c034030440300201b403c102d0b13232200781c280e5075010f41c1410104c0d034a001401c1c20003503034014a0202507011406200c08000c02c4644034009040391170880390260070013045000c202d0001411200d9070020b1405000811043c078020f0050510181065400d503d000b542219142c000e8004031901e00420200311881d00345810550321000090a404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676418992 1250 676417742 676417751
    0x507030810030c14030a1b2c010909050a0512090f090408040902030712020f120f13080904110d0209090609040312111b011b210504060216031809 64
    0x15562540d18480300d000340010340060300b240304c010f0307201044001e0445400c10404015044000800b00400f9994051010500400019150b60343c418a04504450702c40c4141e440c6240e0800c46490004d0900c11000e54291086800f504007003803003032200c081003140c042035055803090484144148038512a0308280a0084903082002203540b003c29141644c1d0720440c00751780d0b0745540404491145d00c0c44c0443c11100c0c030000b01049501643c2d0700a02d19442d09031050681a5611a00000d501008480301c0c0340850900700e61200044002c00109240750300240000b61218a205070312059402c40c3c1c200d80201d503800512080940303000640039070f1180c011900807140d4903041e600140151959665061619101c1503000403028101d000d5071800c00b1403224050b68580350f0709010f070181640c0700402e88400302070500c80070f000d0b10600d40044210040080070399044400a00d42d4002c0c400108140c80c11503080c82001000c03040c0307051160f1f200b4001d07600c51325848031003c0c0200e12140143d015000e0390380780 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676420242 1250 676418992 676418999
    0xe10120b0a1802010507060b010306081c12060b0d0b0613030308102c131703070311090d0b0411040908030717040308010302012709060611210304080f07030507030810 73
    0x102207400440d0307c08004504001c40304c005030003602850b00000d00b40d00809071040d69400c3d80c08004044000c280d694000d400300250244400c441e0030f40140c0f000e0107000c011171038403082542c020310080078000c3d004a01e03080c28040c520511174400c0d00b045000030a148140027030780b8808003203640604000100b81c01a0108010201e8982d0b202d020040d1140e0b01240c0020f400d0000d4900d14810560400c1d280c080180c103101280c44290b0084a2000c0401c0c03400c114180013400050503901c240401030b00c40d00c007101c0e043d00c070760310600c200420450302040c2104412020b905e5500504050b07a12494010341c0341c2c102101d0103090b8200c0012800407401859082101090f8400080e504694085c2401d44002103540c10124625020300c0c1c40702c004412002d000a8800c0207a442902120306035a62060181883c1104070b40360720080c0d41c046440c11011207201103450042000f56002440b0700000c92911045912404113034004110950201d80041500c00c103045d0403c41c8160701c43d02c0400d100958608 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676421492 1250 676420242 676420247
    0x30f09040e1c0c05070e130203190b1f081204030c08060c043b0109110301030506160c050f0a062a03020f0f0304060903090b030708010e10120b0a180201 67
    0x2c1092201d042061079880c0700107010090140038054141c0300b2a02982c0e213856000c1c1c05900035a04002ca02900c03983c20035500020803201e8184500d517015018083d661500c191404903204000a0011180340f104030026a081040000f540560081d0100e1502c0f1807840c10040e02e0590745500c0b48515030003400070842504803030341c200c600303550310f03184c00d80b042ca00d0b100e8118a0310b80c51101c281c01d405070040e000c1034105004500e29412191001c006005c0d088040c004403106002c28800140980e2204010600917002c070360700c08103c49010302d458218000365032500d038601800304202c80100d40081285c14288800b0f40602041c10a5001401c01000c80320752040761082c4101c55004105076011030841c00743d203981c50444520f008140001d41d100d041a00b0003000401c800795040b40030a0300f5220001c0c044c482141540c0c4190070545400040780e1030624200301c0b00c1c00040070b441c441052444e01141c501d10480c509101240560b00e0b52103c1e240030000d032400c80c2c3e1130120001041107140750080041c2c0e07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676422742 1250 676421492 676421533
    0x30327080a02121204051c02041406040b03010b010e130e060f04051603020303090111031e04091b0207032d060f060611032a06190c1b110a08030f09040e 67
    0x4030b003a101d131f0041031002c02c1e01c4c449500c50803100075441810048040c50842e801400da1340140e07802c880070480d40c20b8103c2003508aa14403080a40031800d449015020782ca040c1d0903d2499000c010740225540e221908401c5c1000000c0303a4040079814828284418000104002100c5800000c20a04041c3c259000607940340650003045040007009050758004480c21302c140e801c0104038242449517028410141d80c8950094000d208a081c074022510b101000149002028481c13a030300036240040c1151a5020949803a0840815126401170848018800a031800381c100780030340170009500e565010340d0026104164002e20030001e0411404a02c7c080c00f03c11281c104000c18414403407805000c0e5548034a03c2e5520b50040140110010002e4852006100710346152141c6000c001c4104000c0040e5160380403050b050f14441283d181c0c43c0c0c00a441441802d44024004181001040e6107040003465680000c8440c01c0d0094040344021041c141401074120301407a20b006070511140640031441c0300b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676423992 1250 676422742 676422749
    0x1060f0807181e1e050915090f0c0405090a0204030b092109030c0307030c0515070f0f02040b0d03030c020c0301140a020f070c0801061703030907030327080a02121204 73
    0x8a402903d0100c18825a012100090900c00c64890444600b024880341442e07440c0b08442c000d070021000150810b181c80b5900b10b0080c0000d1115429481e800b2480541c15001082aa0444800c020100c0c10756280d5401c12f04c01c0e580e007100581d8580c21441c048240f403201030b00ea114030764849000c503a0700c80701d5648207061072020051700035140e180714030000b45407400d4900c0c07540d0580550070303010040c48011404902900d5003503c601c010060071407a080814890349102418500009441000280c0000c0d04542c400340010804101c1208010014041301032031507084010035600d046000c40716030103000718551401c04030020020106011101c40c52040700500290101d90b0005031021861000401d4034005074100300800012903d80000354001d1265002d682c94010401e84201b85582c4004112442142d249015246c61032965a00b9128a00300c801004145603103840500c002c01c5070104a0340041000900501406925006000c5000b141c40070800140c0c00050081d2502c407000012107045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676425242 1250 676423992 676424009
    0x1518400206090418060504051507051213140a060f020f12130503070c062a03030b04060911032508130302120309060907060905030705040207050a080301060f080718 72
    0x584044800003801804000c00c10060100074136025800d001c1503900caa44070314481d401301e4008114012880e00b0ba00c00c01c4400d0380c0011000c1069001042c101c240403500702c1c4c40c1e0600c1c01041d000b0b80c0d8403052080d80d0850300300c066070710400601050140501601a080c50380c1a02103142c441400b00b55440e500c90b03841c40c900d402c07401c01e01180001018542408a03140c0140641e51114218030704906400342c00d208020004501182d000440020000c2d4540440d070510801c200d080176a030360540192404019032584150b40c2d04002422903650b00450303c08011030040d8940c0c0c1d1070079510043d00c0d1100902c0c104c0250600d8808d03200c0f0346800c4a14141c0000c0802d1103443d1398013040c07400b2460240364000804002c00c011080c094440000551240900025015618880d2b100d1070101c03107041d9544100d903419440603800304090304280d030041420500600568040d00d070181c40f1803049070f000785d02c41d40014807907201e0050742d40e03403000f441e94000681c0c1c50003800e0400c00b4604031000c5400d0307000300002c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676426492 1250 676425242 676425247
    0x603020a20070302100815060306011d042a02010f060b0901080a020c010c0e010e03010903080a09030e0a0e1b090307050906040e0d0e010210060e1518400206 69
    0x1c861a041024500441d40107110b40d4030344844220080181d6410f03101c544091096001c11140341c5051000d0b24424001a5141032150345100c00380d040080102c1a4150407070340c0c842c8070702c01d030008a41141c201d40d4400c60511901e0b901c08100203007124a6441c00811907031810707005100311078070701c411a0030a100034a04281161183c07a00d4078020302c074402d9140c1d419841d080d0980d110507000340b050a819031003602c42c01100403550f030502d401c6e14014003000380000c4220703001540484a40c1c0c80282107a01a1030072040480801020403800d43c040d41219818800c408100a000d400e00d0b01920700d2400c000b54030754100040400426034801c0030303028035840346c030031140019001d03181d070361100080c541040110780c0c40154a12000d0318042030400124018050321120303c008000f18010340085841e450030726841503492106240240348004c0c8115400b43c0301585494182c050460b00c14010400b1032000000303224286203105500d10444100c00a107403c040119601c41d040800100c000394040d1000359 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676427742 1250 676426492 676426547
    0x1150b041503020304170313060c1e0f0e030a0c1715040204090206220e060102030705071a0c0f0d031811040e010e0114040204050a090b0c07110411090a0603020a 71
    0x4050200d0f41143d2241a90202c1008000d00886241c4022240a0751080001e1300d0070900441e94bc50000d0186010310743c65101d0f012006100b5540e15084104c01c0c642420f07241000c800090410240040c266050481c0b120103010780d0716404041c1800010307810003003d0002001c81c0764600700c000100040e03c0345a45a560105540b1102c048881c180403090711803000358064000e0400d051401e0083c80c46110622000488075400081106c4c600390b0098001e0a01528002100034411f03000292007a038100c0901c0f22404000080142c51088200400a049000c4000c01d0086c1101c03c24010b52a1648541090300041204440260010b00d41520003250b001001c46134103024110144103400158a440342c7d248811042d8050140110310803541413107240c444c0d42111042c0d64003d280541980000c0303011500c400414001000150f01c1400e10090001a50000408454072400c5208550030001040150b80c135101c07800c4c40c044c0106003011070410520382c400818588020000d03c203849041010344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676428992 1250 676427742 676427753
    0xb0402070606051f14090f0d060f0c1803170c010623060f040603090f08030c09040629071515060323060f06040f17060c0703021005071e0201150b041503020304 70
    0x10300136000c014043c1214400c8c00c0c900700780200000e014072040c1500d010032840d2203d10441061601c94080c40300540901d055440b040804a865010349510700420420321038898000e0140c1d9005056882c2101c148602010b0303e8205040100c003500c1c0310b10350800a00d00342c900c680e000d441c10f03120fa5240c006a242c1c0140b4028a020300c11201c040c01168001c02007040543c1103400804440c03000303031020f010360b9590740001c4900c820000c01804a229480c00f1005000050ba4007078034083c5c0c007070b110301034403200d0a070420011076841001f02c0380178401c0d04501340003e0350580240e441c07408401e060090980700c8180070b18242c1d138010303120301d100749410703c29486039685002c00d4a000d0007003130568154080c2d54800003294446c2c080b00714565401003400042c40300c2840404c1c3c4603560b415070040c1003825803d40044000301401410b4109010100c40c8940300c400c1452011004990207400000f4600e041d0071140d003001250f80d10800c9030a000300410722140551881010310140b0305c2c2000b58480d102c502c3c0c00e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676430242 1250 676428992 676429009
    0xc120c03030c0807052e0e070e1f0b071e03020d1b0b010803030106030b1f0311070b0f2a0706020c1f061a2109010b0402070606051f1409 60
    0x81c00d5841b85e05554400d1000032000303c050400480d28610100002d4415030064500040d501d940340d0308844800c002e038841090b640350388202071006050102951500b00ca2080c40319801c16401e000f00404c400040040d10b6680102845110481051207103481c1e8000356584e5a209200c0204450620071031603140048140d101110b51201080c5215a100d00600c4ea40350400d1161038002410b150140c129401d00740d0b9040c6070698071055a40b171603040120290090000c80c050b40800c5141000000086500b0003402405940750503500c44180c24078a001001d800d80141c0306510240c2824000011270000d2021100c10a40c4150056120201c0c82c2003181088182e165803503144800c0c044410803890151300600c2984e10290802450043c2c80800c041d044c00ba86030380d210707038009020302c0e0301e4481032041c40c0e164400b00400010071150420800300b026a00041da04948071074803850248900d1600080d40d0710304215807140d0036003a05400078000d00600c82c808000d015070500180c5000580c550220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676431492 1250 676430242 676430257
    0x804081b120c010905070e010b03070f0210020d02071406060d0f020a0f1206060801050630031c06080d020312070e0a0b030f091f02090f1503040c120c03030c08 70
    0x24507544035040d00012034003030000345200300c03103500801c0380102d212071385002258182c40c13040708000e056940300b40040d9203145e031a6191400398815020072544041030381c0001c00300103041e02005030302d4214a10340350543c03070303a81d403400d002f00d4120100704000c4c0c0c1c66098100c16695040144151102d4583c008100c002c5002c0e0886180344080143c08908101e090462400c2140726050401901ba0307183e0880703003210b505075840d50f032045030308038848a299081055221145080482084500400c000342845d5600c10102c00072101c0c007000801001d00040e115000060003403a0151206001d103850007910f80c03181c40000c0b00041c40550108490a00c0343c401d01d00f8107040a445d12a40c1d90312003292034030b02e80044401e00389051302030700010b907211000305100300130210008140705040c1e49144214060741025419503002007000301140419038411600d42001d15040c09810395034241400c00e44880041900002c82c407201100c0c200c0001008001010202ca0701890854082c5c0305d0703440d012000c1e01c00d610 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676432742 1250 676431492 676431523
    0xe060d0c050910020d0f0804020a0b0702130e061609050d0f0c080f010510150210020d11071109090601060c020f010302070f0c05010e0a2d050a06031406010804081b 72
    0x2080c9031120713030001440c00c54034403241c4401e20920703541d9008a1b4000340c01c40d00250040c98000e400c002060503800a00344481c4001e042d842c07070402484524049815000401c200c55008c40c1c03d104a600104401c42403411103858407294060504c3d001c81c5040c10182e80080055004124101c00e000359088090080c1c030366a400d40720b104a028101d0713806803000340c0b000c141c21070740004006045400314085a0358003030b0907006450722961401030000203410880d150391805484202c907001e8159075000801050388900b0b0000000c8a4120520004d220020301062050f40071342c0c0180700c070940103010380c020fa030b50480b8211342140c03c4100480213070050380d10040241b08010902c17400c01a104030fa04007900c8081ea12410849068802c2100c1d50003e03104071039110320050300996891120348140c0b80c0101030b44001d0440e0541e07a001141280900d0340c4813100095a51006441c180032074568942c000703a0910b0074203d94202900c2d1003000340300c0c410b88800030503880c06000386241c500384000095101e004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676433992 1250 676432742 676432759
    0x6041104031104061d040209071b051e063115020c01050f0c090f030a020d03090e010920030a0929131211190606090b010e060d0c0509 59
    0x900d40082c101e00c801d4001ca11550401c5004240402015000545415100d0b0300c0ca44c0b42e02c0381d400380322034450003034080001c0100c0c041c1c4000c00010401c03080c0112501c0b03100180125103407020513032102c200d803180d01603e6030030480a010f140c488162005007002812106014000040101c100d0320f10745c901300080c1a98503007504841d02c0c8400b5406081c00914040c002d0246d80d41312a5046a04c1c90304807160580c0700c000380500c5005044c0100302c85210300001c1d048030b076490050f0700024a0000c800d035080380054200b000a00044d4036486c03049004200c50306d4240914411200a0090000c010009640740840800001c0b0508039a03008441c035240c1000b40c10315003010382c2c1d000c4010a12407942ca0f489852011002c42c18600407049500344040d04031000711484208441c044501d40591203103e000c0c0c0c80b80e0f411000e24680c035501440030161088070000f5000e86421504000e03a08040210740c140301c5600050a115150401103800001d0010720000d600c1080c483e0a403041d00855901c203070040280c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676435242 1250 676433992 676433999
    0xe011502030c1507020c0103141302040209060c0a0c0f030f0803090309150a02010606091a0f07120e0406050102030702150d0f02070803040209100f05012d03060312090e0f06041104 79
    0xb2528180c010035680d400d0322400361b021001901941ca042c1251942d012196000812000415160303a1007035100401c05460540a4400a11150005009042160400a00f52042101280f00000206980d500c0c0c5500d0a113580c8888889050222024200c01c0d00000041d070480d03424001c075007180000800c050040c140c01c01da000d0050b001017514034050740c60118003003640c50013241e04504031030800d0760501e0710480300b0540c1c0d40d0b00d800a0002c19500b0005102401c00075510030245900003d140d6610301c20300f200082003106952240e4040360564000300001005625100748900c1da4800388510541d0351259808640020030311030600e210001d201003402400c00183d0030082d80034038000c885910840d100d000745800304020328850041d1480203403404205131350188003010075200e6121502490b131010010a52405060424a200001da90b04401e00c100142c000c61240c0c90001442c04600d070074240741c1c25000207035000e48402414860400010000c0c0c0c2c8541040b0a03100003101159252030380d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676436492 1250 676435242 676435273
    0x210c0307050f3a0204080c0609150f09040c030605010512040507080a08030f0105031212070302130e0709091e09050c04140f0106050f0a030902121605120105010e011502030c 76
    0x210100c1200800601d00c9910340d550b51030300944068640c02c001901704c8540b1f502c20001103911038030b000c6411940d00080070140c0100031019240010f01e101c1c1680d0b03201c8208c030030441101c05185010007032614010b03041c01140da103c5c05075110f80a500302c51806a898a080046c44d00065520074a04c3c0e00c03480c0c1c00c5a04011420000c5d601800c0c4804800b10076907201c0080580b949a8203580c41194003060142e003201c100820741141d000319040c02c005250818601400d4841b442039000104030000e01c1c42070005096000214000070001600e04200043c21110801480000c900490313110740c0e19043c211041c403201780007810503110000c10070013164807903405d04940d51034201c43c1c0645a181c0c1000000c1d0041c02030040310540a02298064a492001c00090b001003000038002e0f80c10000c002040c910200c3c0030414161034021035200d010b5aa840e0604001208426801e14500350341040d004100301070b20700c182c0d241540e66442e00c0440c0303810303040f504a00c0d6000c3c0240d00d00c594855120404000107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676437742 1250 676436492 676436557
    0x7060309110a030f0f081e040302091e0a0c0203041d06010f080108071a070c0e150f03030403030e180a0902091303080a0c09030c0308210c0307050f 65
    0x24401c00e10450070540000401040444501c405404680f0113052040011030201a13020715502c00c40c80182400b4454001010046145840703a11a8400050500962030030100e03140d48050b6200c80f00c5414101440040c01c010000b40c01c480d5a0398848400317424180c0280262406424180c0c050110703940f09030381050f038102c0d003a03030000e0118821a140480c0c0d00e1003044a07505980081000340881d41ca4072056a1790212140078038042003c0134407240d0700003416064003000800140341c2004803400c11402441151048480542c07042c030f00c0e10001401500d002c4143e170220703601800c04102c000c40f200c0220b0002000881070503844c802c014200011004554030080d00300303000342c515444c107668109040504c003502c81d00140116440d0800071712020100d410070080c0e0244c1d482c2c0300303034515a20381c2d480d8841401342e003080b18031102c0800d00d03801c504040e01c5100c03404445141c1000c601d0a150003100b155201c05403d65040200000d000421400c05070216004403560341004052150320400004a10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676438848 1106 676437742 676437761
    0xd0f0c0c030803090a0b0a0209010215070201090209090a05010b1e2101060902041404061203080c09060301060e013504170313110109030f03030e010608070603 70
    0x1400b0001850003500c0e0103008000480003031a28220580c0d0091400315010310601200c1160b07a800181c203c07001d02030b820420000d496550049001d407203490406074204e40024140540440002851007059014400030403a03106820b042080102c401c003000d1f220484003100d490350364a810010b000000b440d407943d150b0a09031030442035003500d11a6100702411580840c0170824086003620311450410101c4081200304c1c00c0009030240ca680030b02c405010030808500141c02201041c08070385a60400a010395125030399640007d0106c564041c807580000d000c50048070520300a800700d9810401a0002008104640810b00e016100000c0c0203035025807600f440010300030314030001107008450824141c4185582d45c00c0030503820520f04030990402030311100403c045110920a1650580d140c50049464030189180038054203d40d080b012842c050001c00041041d0103a01203c0354 = true := by decide +kernel

theorem cover : BRFrame.Cov 676258992 676438848 := by
  have h0 := BRFrame.cov_init 676258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676258992 ≤ n) (h2 : n < 676438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
