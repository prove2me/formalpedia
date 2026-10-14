-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:33:04.64624+00:00
-- url     : https://prove2.me/submissions/3ce9bd27-5cbf-4ed9-8982-193206c4b34d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369604316 ≤ n < 369784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369605566 1250 369604316 369604331
    0xd2a0509210c040504030206060109140105040501260711060703140112020409140718090b130503042c06010206010623090316061101020a09031202150f01060306050607021003 77
    0xc104100304142550b00500521540c505454000c1d01c4020507980e4078041090741d0700c08101d00f0250180d05841d11410780d95241171600d00801140c14842a548100b4500f40d1402c1d03c002500e1002c50030b5103c0c040f180c6a0114404a0900c90340c0303420002446a02018500340c1c00313184ea00031420702c01d07045070031b00d6009001054650001030018009010300400c01c4440704401d44000d000455080d040354180408441c56000014854040e0b03007072200e0050038003510301c00180c4400c00341c0024945090244084a0806031200d81140220f40790803021407400b80d407400c03541507c50514054550014082c07029281c0b65142c420090203d13500e64640540078030003185022000302d004403d0302c40e45080101110480b1400c0d840c00240000b69005803400030341403c1c16100355800500840f06116666907480c1c810340e1441c1c81d42e081b5243c0001003401103000703440104d2a002c801c00d42050080e144d500305200c1c01c0d49018405812211298403a0340900410312103000580d49862003021004294180400d662 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369606816 1250 369605566 369605629
    0x12010b09010e011404140105041503060c0804140f060601050a1b080408060c0c0a080f09180604060501030608030d0b030111070b07170c18060d2a0509 66
    0x1004008101034000c00e1490000a40300d0010980b5030484003000d0f143c20100052038240815a059100500d00c02d0448000401c480e0070590310520858111300041c170030070741d165591320055409141450000407210001d06c0705101c203041040b448050040c0003450800d80900c0c4503901c41038001c0030f26051144c00324090190600504100b0319240d01800100110f25141c545172519401c1401740c40d41910400b00042c0402d06070204032402c0803840e40040520722081e0713540da1042c0d1300108030384c10011020321400d01c8946a0b50480781881d8a15512034205151032070a00048507900d42c0090704150808504010116002c4125200721220400224102a0b68000303e4050003802452003501400000c141c403d00c00508207040c001c0c5000e950f43c02c00038450030070403460309205694142407590700700009200d6160020b40c205090501801081c04e040302c0510324011501e0039051a0880c0c025040c1c4003041c1e12000e0308211a00007a800c02074105403100303000c03465040314074803c0c40080000a0501100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369608066 1250 369606816 369606821
    0x1a030c10180602010e16060c3c020f01090b0d180b0c0d05090d051b0c0915010816050702090a06050d060e0d082404230106091706061201 60
    0xa000c000c640c540c1c00076a560350001c0c0201480c2d40b81258501400c00c074031001a00c514004802c03210240c0d5400161001c9488800090758410108a030180d4003025807404030b1611000202c040c80c1c000c08050181e012401849240802000360a0400c24045001c0c05010140c0081d1045401a610001180707040050140d40050480c00003400100c06030b400c008208507103100a1a00c000300600902003915190a403075680e04840034880080390050240344441d0600382c542c442c28405460441d80280010400f04411070410340f45601c1a9840500f0301c2c0c0c0550704550b5458101055025400e00208a024024100d0113807000081c4281c49100100b56401e4a94004d80080c1900404060241005140510003000c056130190001d0190b0a003000c0142e000d44c02a40c42a0425800d1614a0b03001049034020100c90022040d406952547d4490003038031511f07134a4500301d070030284418003941400000b401c2c0e071141c2e41c0800c0300909660040310030740303001081c450713007180007503070000b90b05003102c03452601 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369609316 1250 369608066 369608087
    0x50a0c080d0209131509270803060a0602031201211a0a1b080c0306180103081b16060507030c02061206040509030903191a010305060a1a030c10 63
    0x10308000314084200d100726074010090058102e40d0031000c20001040b01090355409030b082c040000b03810104001448040d00701c0111a013402c80044082548072540c5c030102095000c040d42c071a0000720400c012070410310b6100000d06424002181441c2d40d4103001420404140592480465072140c65410441c007190070721015507221402050041000e5801500c80c141141c692103410f05001d12011020340020110103854242e6542001698605000d40010340c0701404050b00170710001e84001080002c40b600d14041d600c5102a81d0707a0b02c0c020014441c42c509121103c504035041007180364401c541810b002d008a510500700f031600c6000d24107007610b04400c0020060b4001c44c000450000016041c4890752050310101e40420254451254180e6a0300412501c5a0580e02030284c048002c480720186100e070900c00c001d45080f059030209640c500900070b9204a405901010501604503e01d0280c05074220400c05503030800d10b52000041d503500e0701c13001725a004c1c52685007011800c92080b0350001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369610566 1250 369609316 369609323
    0x11060903070f060c03031a090402090c0f0406031d0610030b04150612050106060906050d05060f040905072409140316080d030b1c021c0f11031c050406050a0c 69
    0x11401d5503243c401805552014504074006071070500c881400c200400212100150007801c2200c840d0746503400d0040d001c402501030300a44005004184a20304818001c10203401d890b43e000c18520b041070882c603402c0c0000203441c4140c2d0402020060310007030780444402203030b8100420712800d489504001c0c0740d4420321039085080f50f003401000300b5903a1603c907290031001d121f10001c000e116907882003281e40305400c2c02034100140b4104820201000503800140c0c02c10130040200c0e0500002c1c100260440f00010300c11541d94000f00401c00440c22102c8000c12103205107031401c009940c0d09030300108081c1441c010f040740740781130305202c155179101000301503201100000d6034103180d62600301036652240051070ba0300000e4202008078490f07003014103428032460307000d00c013181800c80c0c075600700468469400c42501d80021800582c0000c5081550a8403869001c0c0300300c82c0c043c964210034107041c5283c0341030b40580c021500c50590a22540901101c2c100c3d012441d1241c0c079182003070011100c098480d440503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369611816 1250 369610566 369610589
    0x3060609062d0a110c01050307050904060830040302011205070c05060703060f06020304050618060f070c0e180d0305070e030a15050106020a15090809030a0c0303030b010203071106090307 82
    0x41c1030704420007040703040484e84a804484007100916540c0740300c19001d09000034014000704031414094005810000401000420b20f240c951128504d407038150041d404c944451104101c50344030500c925080820700100b10580b070541140c001900c41e452840345085032945e2140002c038401d11030f42000c044d165110f0152845400d01c2c000060180c8440c0c041c41c00701c1e0082000004001c1c0c0000f08440481c0d00280240e030030003035250200c0110714076480b04c80e50441e0003001284d0103865030b00018400280700e0301c10510087e0402120401400e0b006140c100303442e00340061041c1001d40010b92034041c0e1074900d404112070703413a02401c0325421010781c08160503200703144a4500304400e030400b101500c50303012803c01c1036a030b030341d5400c9070703500c154080c0640740c1030340d0300391003541102d16801c445c2e2014040c0d01e0042c03030609104046441c01040b01416a50005214814410183d240c015841d5001091006504001c20b0b500c1c2c1e0a140c010402010f4030440e00003440703d00e0340e00d0609c06034004000802d400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369613066 1250 369611816 369611887
    0x723060402011b0b1e06030c090a090507080d0201060f0e040b060d03300c1419021609020304110910090f110705060129120406151d0901020306060906 66
    0xc100080c2d0480c4020480034100081140c11700050445003080b0041039410143c40d80c6094100034441803003303440c01d0180d584049040407041013a0505036005600000b15213103020b500c0d10083c5a180c1260007120b0b03200b014000403035500c0103615005203044501d501441814a02503c06900000841d0f902c0b04026400706110031485c42030054249509000340322100d04940211009501e8240f0b0280d40c0609200d424003402c60f1a802c00f10344602401155420980d0814080107610700358030118505070000b007040304005040491003442802900d07060078030300b0008448600c03402c081c020703541440d070b0320304607a40c210803590001e0000c031183e910b42e00d80d00c01705400c10b43c1d224002402104184c440710702c06a4808603c4011200024030060703006410300c0c0c5030f800314840d4054042c2040c1c032810f40b60300e42100d074040244042c1005103240020725480121030b40114042010051007040140d00c10300c100401d94482204803483d101049400039540c025503107403021140324131418200116000c401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369614316 1250 369613066 369613081
    0x5100e1e070f08070e040b130e0c100c12091e1d0103151e0f060503061609050906210f010e030f1e0d050a020304061406010c0212120c030723060402011b0b 68
    0x1049841d9428070040e28ac400c000c2030b042c03004003040046100001840f101c481030100700720f0701e52145040e00d54501902c3c0a581e80090b0780408139075a0b2940d950b5000400104546140c800c51203c00c5011284401043c1d0700d141c90b010304042240241400c40e039251862482c1070403025250110180307400204216907010b0803072010003070045010707140c068072600c03010030710080c5641c01742c6035044178139903c1090b01810b0205002c100000a0281600528080d40382c90a291507441010a40003400c0010300d0341980d00c0c4211802e4450b801020202c0e034204010260840082e0411030b00c0010300086210200548460301c210b60b4400d00041c04d51280c0341c40207001400b505900298080c03400381390140301400341003009180f819401e446460100b10384044c41001824000d1f40b01016420030800e6586131212100c4100c3c0f0369000302404c032241d4100040384803c000041d080d100c3c4d481402405054030f446031184860340d5407005030010381170000c0040810100d202040e04024042c1d8000d048a006040092 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369615566 1250 369614316 369614321
    0xa12031104081b0a27020901030216061401050d080d0e0309130213050103180f03052205120307170d090f0f0c0806060a0905100e1e070f08070e040b13 66
    0x2001140314000401c00040c030700410851001c070b40c000c0d10817041c000f01c900b100718500950216900074145034080c450300581c1950110300c44842d81c00303078201149400320301680d00282d6038143c2149100b1000c641d00c900c00300f4070709000d640c005800b078080040c01c10800012249503004120703400364840348071032500c80750300c9180d00507007005503000b02c1d40c807006500c0710010340954486104072440c11140c18401c8012510701a840450319009081441c500700700c201c08141444501c0140c003102599148041040b81404001c055510050002450400b034155440b00046161020354010103000820140d0a4132400d500514015910003070902c10340d420782c40c1000c0c0c0342d076502c0c07000d841c40e00084900040c4244081100b0b442440001c000d403161074184150320000f440c0c084c0c2580b00d090340b2201c020a544803600e6105004031907000c00035440280d40c1840c050400d900904000400c4601c8100c036101030b82004c01c40d90440c0307aa040810f240e010000114000340700030703018207a021410034004c416010859 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369616816 1250 369615566 369615613
    0x4060f27060b061909080d0f1b1b03050c0904051e160f0503101109270108030309060c0a02060103030c0f150b040f0b060906091c05010b04060501020a1203110408 71
    0xc0e01d80e4100d161b6a29201a154182c20340040c3c003040825060015251251050f00301440f0290b6541074400d4260711010440d0b540191104581c2d41401014002c0c00400c1120b0b4110309004c0300d07902c0040c601542d480303031141e241c0b40300c060301c0ca4904140007a1040c000c0c088a09402407600b03000034502c1c1c1d0f0b400c100340600094800d66001c0d00501c0019021030718980503000c0404d280054141c07030440c0c8201804141c003102d02441c800d0b10840003080c0700245455050f42e00904a0030300954503414141c04c0203040150103042024034400401038014407a80110384241140d4041c102400f07101b40c0d03424400c00c600c1400c3c60050814070007142101c1d048510394809000d444050350100440c0f0441c1100302d0488110300c2102d6486481441011040e2030100000e001c940001707001a40340003040c600c110a00340760399000b15400d944030781455032141010321070070f4010403091004088601c0706482d0f00c2e0022540d414017008158803601c901c282c2d0002d00e402c4800501d0322008813203d003401180301200883d406d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369618066 1250 369616816 369616867
    0x302060a050106050a0207060f0903230105061e060904020d1409060606040f050f1203030109050130030807030b1c060f0203190b13060b0304060f27060b06 68
    0x500c400850464403407815a13817014080c0c1c00401c034440c2485000d8904c0a0203880d1201005003a0304044006661f0000100704010501c20212000491055103400d582000b0071381800f801401c03420003400c907aa000c20900103402039400d5982c41c1e541e08080341c003074481e54807441441d0f800c08040c040700c03540303854900b032044d000d00040c0c6a11703854080c200b0aa511461182c4440c020092000b48000d10703007144d8804021800411050245e44c46400a50964000b60302040455540b0780c0108028083c4410300d000c4003100f03030114000c642c2d0360b44605400e040014005010442c107100010070aa00076408400441d20040400440703880c0261202440c551004084622a0809010016094490003a213016030720704c941c10b4182c1d88204007038400400710504110340c000b40065040904441030311072140130341000c5079015501d1420703041c4042a00c00304011090014035000c44010008a00046c201045501d800d102031100403030f0801101070108544060350240740014485054000b64074401448100e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369619316 1250 369618066 369618071
    0x613060e04140d020c1c050a032001020a050307030b040e060a0c030b04051605071b060c0303290f060403080a02010203160806030a0b040317010602030405030705090c30040302060a 79
    0x1851040030b52261007140c40c450240e807052007040d071645050303140a105480304481c410b10040d41364640308e02d4403411050a41c0031031000d20000325211590404e07000c5105011000394940706143d400180382c3d220041c88801003580d07481c0c54240e655901c0d0425045c002501c0111100f50030803240c101c00a08a542480012074a8650740207480d007006d00035140306808828031300307807580810b50b07003600c0991091504480e01200c01c1005101e502070049010003404240c0e417508404084c07460017404907a4140344503113240315500c807041c20050003824441100d071030581d2000480603861010074424012900000c09560001c41d0314903001e40d05601440c410000e82c0c0440300c0388031010b28151201d220070b0754002d400d50803200100001c0303002d9440d4160400e01c01d1400000b5a0903410707034546586002c3c1c1007000141c100080401691a003003150078040d0104860300912402e01040040c6030f80310301580c400800c0c24207040d4160240305002901c02c0d074001215840c40c2850180703030007900c84100b120340d04a040e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369620566 1250 369619316 369619343
    0xa140f01090c061b080412080f0c0a110d05120d0f051302011b031704030c0b331e03070b040b040f0f05060909041b03050a17070f0602030613060e04 65
    0x7072011354801d080d04405100d14140c1444445107220142401c25a04080d0801071031403643c210034002c011001d29580074001c04002860008200195a00400d1003003a04031400004a9004200228404841003020b655914603030364880181c8000d605410b1040e02e484108580580c1d440c42d0601c042d4401d81c0c0350314070f5060105612400c2040d08401800045a580641e0801810f0f220802d801c680281849500031000c0c2c5d485680c5004100d800c82076003001c0c100d01c17003080c01895600d0b001002a64907140c0b215049800405d81180c060801d156403c0f0010307009155949092040710090015240c03207943c2c890700d503100031245501c14030540301404280c1c1713000a48008030107250016180018a01c80c0b85c0300c0340d0404c0001e10480540103540750400342d41c6d0004100703401c028090045110340003400030300c0118203101c00c507940c1104140765510000c0100c10b00103904039070280c100e10351004005031a42c85a00c0030480100e6a140c002e41d02d20b18141001c82e441c400c0c4510184140c0c880c01c20440f010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369621816 1250 369620566 369620597
    0xb030c060408071e050909100b1c0b040807060c08100503030301060c06020913050a0902010306050a050f121204060c1b03030509060a260702070807080a140f01090c06 73
    0x910403442203400681003003c050000d50070b800707034818410622601520242c1c2e03c1d400000c000d0354090380c3d00011980246100b4400d020b0500610400702c2007221040d4080c2480c0285035800381c68040024016240140010304111070170f4160340219800ca8020000341d044808080c1c0300342803d1303460a40d5aa41401c5c001040d00d00003040741c3c140d601580e1181101c6080d5030f6104040e41064034100e034040c44225046151590300c2c45080e01c103803580c6002284080b0180009811510160821030040038480f205002c1b40e2520001c0d210251410340e011500d615540b805e0303a081842c0c6406d4555440e01c00100000c0e103c1c0c2c032240740004540501da032440c0101100810000d070040b00d1100401107003082c08444850324140028000300c24660070401e500c000d0108405034024000400320040b00491010302c11510340c100844005403140400500590b42484496951032080c030b44002c0015600c1855488900d000703100d00b6281007d5070340240002c842514101161044600a20000824140c04c64105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369623066 1250 369621816 369621829
    0x20d1107030309050d02041806020a1418190e01060905010305010e090c040e0a050102030f010f05010815060721120b2b05150c1c0b1e0f030109060b030c 67
    0x1c032a415124528224540401e011181d4000c24050740c0c440e995461080c14003520082c20004584118401660350514202c06081c0a0700d12000030f00000f0309000f46503508504c14080043c03004104c4000c8580300480185a40c0c1800d241c0041416894600001929a400820400a940d0241c07414049a80c07900e110f882c103141d04941e07240e926441310881303a000d03003040d9001038a0030f000f0b0701c151460f6a456441c0c480c20b9900583d000f03001d41d50600010440c6074000d011410140409113007509840c106031280106640201700d407039104080000d40d610821075070101c03080e00305800300012820201070340070103448031342c200c0300a0507200c0c20040308480c0f902c3c3c9080c9031042804201d944542c4200c0400d03100088031040ca004075507900c90910f05201e01078990b00c08910130700c19040b005603a000e02c92a00e24014804166102c90f080c200741602215560360b9261500102c0b80007416045000444d001410301000a90115095481c000046040c03080355081b00e01e040500303808071140d519000060220 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369624316 1250 369623066 369623069
    0x130605180607050606101e08090c0102010207080a1202090406122010030e010f1514030a080910020703060509250302150f071502030610080103050706230a020d1107 72
    0x629000780c40090b1413443e01c851100303a03444581c901071202c284940d40c54200035900707c6803035001ca0b00e080c1c10003018040810000540203800c0c03009600305a0140c0c0d40b1400b41c0102c04601092041600034460304500d2a41a00d802c50001001400752596508001c485140d040600740d071601400340050542c007690807100488440007030140d405014030b03848110010460806020801d540700c001c0036880aa450145905110b40c640e114181980351840303124208500c1031010307020750170000800300880c1102c0140d034908401545c1407816200d00400880c1407144a40000344000e10b81000d105408000049840702c0e40304e03c514084c0d40c2040507c028846004910001f50300030741c0c088009002d43c40c0700002e49480c001c141c003c10308020840e6145803041c0c182c241800000c0e41e01104100c82490403500c0c4150851060130044003039410340d1100780d200c20701030181100b40316900f54600003a010252a5022030900400e669480e003500d000c000351180004d03a40036001558016558100300c0010a6840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369625566 1250 369624316 369624323
    0x4051e13080a030c03021e04080d080115110f0604030801140603040209060d050f06010303050d060929060d0608100e16140d02090f06030709020a081308130605180607 73
    0x14144000c2c02c0b022006840c580407507004264003440301c1c001d4103c0b4905042c8180210900603070f00e0b02c0c20840c81c103140c230040d201000b0810107464010490807260780322003c0500c000b49011012240ad1000c05460500c45a40d210034600c141c1080200b4141c0c440d41c0141628100350000c103c401c00c403030400943c0d01050f41d02035445152070f03021405c18608221180b41891240e825180342c0c3c401c00000b64107046c42644181c000c83c80c00203842a5501d01c610501c4042d0a070744c1400c001c8a00342c50480c960320071802c0340d0409508449070507030302c107a42c1d41e605a0791001c801c00300501c03040c1c0c3c1303e20070540c0300c0c4940e01890150506214902280410100710049001107001c0240c1104d850098908081030783d0700045500b05000c10f200c000980c8980d10030074800d42d1690a210840e09000e03003072624121896005c10442c62040c0020007645521080c0075400c408201c891140e1004242000d9035284a03502c842068807001800008081e80c01c074029001402d03c5010b50b0039000210003d0280034424100c005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369626816 1250 369625566 369625583
    0xe0a0b010509151c030f080c0921030426010c2106030602030f0f090706050a1d060424091a0c01090b01121b0b0306100e04051e13 57
    0x140300360b060648031558400c2481052010814103000810101c0da510191181c00000c448120310a142e00000e0b07426035082149000500d034648507405440501440040728410503001c2c075480c040c2000243d2800c2011030180c141c0b90385036030f51600300d03143c0e09141781524400d290000c2440341c1d00170184a8250250745a84a014000301001485146d0000c0d0900c0031443c555074003404000b240161002d1807003640d82c03020040c42da0034503030103210300585d0041c410501c3ea03110507401d06c840c40c2e0103c10340308121443c0c100208c10408241400c0b80f030040102d441a044040414001002108a01c41000032104188030000312820654100e0b19282c140c041c40e01c40380062081c5085010100c0700403d0401d02c0b22000181c0031080d03586007002c2e100203900811045030040d04040c1484000c0c20180d8038100f943e4100740c442031411a00d8222400000c0c03240d03110300f110521b803401c0c050180610400c0302c00001e004010740d00d4420540403410305411540380356881c850300000d40c159840c00301c925103a0b0b0440300301e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369628066 1250 369626816 369626819
    0xf1d060a02030609040305161a06030f0706050a0315081c1112040b030c0d0504050c0f010216090e0a06050702030315030109031d040609021803060c0711090c2b0e0a0b01 74
    0x43c7c590b07621130003a1418154940c1605000301d200170300e440e1124462805004550f0800303a003014605040d050186005802c0b9900c1000140d4010045886c0c00e22141400701d1100c0c0c0700c1c40d00305c464002d258041c0c0c034580241c0740c42942004074215505149206a210382c1c1150a041c440b40d96540f00140f00d066600d0803c02091080c0c9404078048c43d0b20040e000c02d0302c0d14010b0242c241100703841059038101c1d0700c2d81c81220814090300e000091020801001e100800c103510741c050040c101002207201c0c2c50039103a030754001c1c07040c2c4400520840300081e8001c0d00138015801c210000030354a0740111200c1080c800725424030b800c0c519040c0035101010380c15540e04446201c24180002c80c82c5019449542d025a0350035000692085034000f0b0582c082290342c40f08076240004050504018001380284901c00d001c0242000207980384003038010f001e00960361100d075030345d42c130708160501e10400a540c4144000d10b8040c01c10741c0403801c0c103410380e14124002441007050f040441991250b8042d802481d400c0c49800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369629316 1250 369628066 369628073
    0x4140d0512100503030a1206120b0604020327210a1205090c030f07080d0503040507030f020f0d060e0c030d09142107060306050a0e010603020901030f1d060a0203060904 74
    0x10480c0e0003060b00d40d140c031856039403034000070718584c4034064a17004504c0d480c40e003400b5440b040c0324800080045440b215207d40da01d0b03886104c0c140004210328401c6074048040707100711403440c210f02903140c01a00340780306410707607503e40c16901d2103401c000c540080c0c1c0d198041c01c0011030a906940c81921980c45030809030030100d04a1000d8207000700640458800d0b940c43c500030380e5042180034050075074240600011424414040d003000740320062001844020002d000c001031000400c001280e4100b0141e0782c0031292480080c500907018000c02d80c0c84002e03c00c4210034007440343d202c01c1c400c0c1400c01c02c440480c600c5078107064454040e000c0c00f4022401e41c5e0000c01c104103034030280c40b510b510010a240301e00309810480c0c00d4440c0c002820a480390748142c1c1c092013030070f40510981c070250808a403050445031502c8845132030030405001e04001c040d00460941c5843e4080d4003c000311902924050120125038202e1400205100480e210140b1450010448028591007100e00585c400391840c0401d039100d46 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369630566 1250 369629316 369629347
    0x1707030905010b280e040f02010f02101407031b05031506070803070206010f0803040b0f0d02070204090506061009051c0515010905040c060813020f060403060e030304140d05 76
    0x6031150354881202c40402da480301e03940c01210b80e407443c161400ca402e050313840c080021550003148503100c1220900001c1146002490700f81c031b9092134440558031b01620100d04002420800146140c104100e00c40c950314403501c807903c11080c070b035810040e44079000110f403000f15500d00c810b400305000308041084c030b4140304441502c02c58050182460624180c0d02e08245a02c1103c1d144010b81000c0b0061110900040040d80201000d80040d82400d00f011410302c47d5124035901600704843c00600444080003a8055592031a00100300b04140c100a0600a44490f822a42c0314401c04401e4000a03000340139840580954001400000c1d50006440c0000343d031450700d100a40d041c1c8221402107406c001425046400703401c01100200307032030030585029400310507550082c0b0700740140e11042085850401d4400b003030268040b03400882040140b0003007080d510441d0805440c40e802d00e401c404820800000950180b40302d40b102c070aa940380410314940350300039209598006001041308143c0c1c245644c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369631816 1250 369630566 369630581
    0x2010f1b06110c0604110102011808042105010e100510030c0e062107051503040312050c160c030b0c04030201020715031803180806090309060d18080408010507170703 73
    0xc0d8021854586010810f615018007241c1c1103a1401200355094615682801540d494081500c61103c621140d41c1e11103032240500d00401e00e00020a41414461302803905c240c1d46460b4000d0001c20080040c40045621140900c221508070380c141408900f044040508103011070f80c000a03560007603401c2612000000d4000390103507500c0300c0045424480b60b015403050305400307044c000083c040f0a14180501a04070825541818803500600800010a401180041d80e1848202c0002000d81c0d039580401024040d641d1525080f1a03000700306001c00c0400c284140a4900580c0440082c0d0380f401007160f12071249010085c0103801070700d0308029102e04800d03010300035446818081807084c50208580d00b001c0791840190009100c4101d00e540c000800400e01c00a080500701911061802224856a0703205400c070440c080c02000034800d01e000d8155021001220184066000f41c00315410a2032854100380141c01c0123529000108480350300030b000da11043c201d0010410351030380d9550301c03c2d4001c2c03401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369633066 1250 369631816 369631841
    0x12170105150c280c051e092703040905090a020d020d0807061811011e0507051606020a020307080303150f1201140703141504200a090302010f1b06 64
    0x50040f0035518101c80c404028140e94581c1d196003a6444504242048021a5014501a001c2881c241e50400b80b00403400104000903110b4a0194039081000703a003410b035a0346103941c4007410840c941c10070301000c0020300484100d0641882031f61507120345952103840305003009502c8100c0c1314501c0010b06010f036030302102c00d0280300700b40c0c245509a180c92003680c0f036401401595840e01c200e00010407910714031340300d0003c00030718240d01906200ba008854842c68000f101c000e104000c201041000010415807880d16422922483c15a1340d4003400b950b141090302007240309024040001c15008800410b0300e1050307485484800030005030b4818403503103125100301c581d000061380301e002013805024020141c0b44002c0741c90300720079861701c10401002c8406800f0a816201559418841044c04051a91041c00021100010303001c030038540007868070518030001445108080399003d80d147e0000000380469000f0380f6505050b40303501d4012148000c000d000b4a80300c0b001041d008001c981f0359440034070071010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369634316 1250 369633066 369633073
    0x50a0e0a0b030a060c0507021005070506010303081305010609140726070e0303180f0a060504030803100f06050406140301050108130507050d0c0914010e3112170105150c 74
    0x1801d40300e584c00e4070b858002100205e5000a40c2c0421800c0020540011483c5480c000381040f040c2c1e51b82c640c032400c06110190410407050045001403c190b2000e42080d0761010081120581c2d03041500090014403814800c070413201c00010b0156401800752600c1c03e03074071000d10a10701034030340003641000001600480030007038440208403c41c0c40800083c04068415a20034034242000d02c1040a65401592294041d41c050b46c1c0030490070341c2040c1540c0c10780e030303000c0e00a0352269500101c503210007481c4e17886000b9548c2c100c10009901c5401c00d0050082d11166074404682031000d400351240780c403082c859035002900403c00203060300108425028454400c5055070107080d60b034400140e060904038403d42c1e041008450070882c032510340c4203074034440403552240c503007940c54248244200d400003003044221400a04498444d0344409086c10030100c0002d80c1e1140030307151070400012a00c9014018404610808602d40c00120781108141c100c0700014501000380e048001c0650382504224001d191610 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369635566 1250 369634316 369634333
    0x14010504092f040e030c06070216050607110a0e010617060a2733030b060d050a050706080708100e01050103090809060d020c0d18090b01111015050a0e0a0b03 69
    0x1600c81c000c41c05401004c0f002076445022844405040034400f60214042d54485558000001000340c9034004a980403680e0a88038a0320782400410311004e800456413000f09013102090440701c43d403001d4180c4081e50346150003801c0002c08000ca103c82900c480780e110350380003001c000c00703820044580082007010400030508030355400c6490a03541040b0300c10040c5101d2080101004950310094410420715490051a852840d1114801604098400c0b4040c03650a035010b824005d08000354044150f0140490700d4590360380714010584813044d2032013070003c2c0d0500041070503140b00c882c56030b0588240304c50701070703859290100640c000c00d42c0341c90440780390100707000548042d51505e018040e10188643c0c0983c0c1d6072000c407070f068100b82044540070240500908002c00b810301622040007030314400400003500ca440c6000694520400d104080401d00c290444c1c001c2044080d00940298a080820110016260700402c0815129800f42c41540444e180c002508103040741c102c1c1d00a590042e06031070020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369636816 1250 369635566 369635569
    0x30b01092904150305010501140301090b0a0c170c0706050f0906150d050a12090e10031101141b120c0a120c02060c0609060a090807031206090f14010504092f 69
    0x5640c0245c074103035503440040000002a8802c8805450220000c2000d5141d996030862069030141c90160b005135240c80300324259000e0f8031a10740600404042c00041c1c908020000301c076a104c10412107049040c00701081500303c604032210f0040c0307101000b400c80356450340107075403202c460208200d0b030108040e20f400d008030ba402e0100702400350281c4645240d5609488025040364030551058007549003100810124410210f2494150380e441a1540004569080100c1c1c0011940501c040000350010321800c1404003540f1039140024800161a03004400601a41c90350040c0e8032001020341202c0d0b02c04000890007500c0703c02941481c1098107000110741c001c14450740248940009640c00718050015940c0104102c0b50b00160b010018026129540d891401f40e01500d40f0090030b10109204124214406402c410090405001c040040c0144061101e000d0240010500c0f5200b101c203001098500b014000d958100d5005054550f841441c40d2072445100c01e04030004802e2800d4481e090400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369638066 1250 369636816 369636851
    0x160207060c0b062214090f06060d03081b0c01090210080c09040203060310060b2718070311180a091802060304060f09030801031b0e180a0f0804030b01092904 69
    0x45440306566170764107140200266241060600c000441d640c0042e0812203d641c402c0040c110081d414a0100c1150b05da4042c0c030008030b245580c031241341c81340210b414a20940c0560155180760300899010241c20411042034030081801d0f110714040c0311081144629606203600151b400c450040c08880e1070040d400800e404590950300710f032085040009076107400710600064518082e80312a0080b075804145400280000000320740c903001d5040e542c2c0042d111a00039032150702900d00b807500b00750791801864612144000c82c01a801e225145001c00441c0780c0748244900e0440001c00400114030030010780030400c0c6a0001401100c443d81c817049001440000e031b000e113241980c4a44c0b08d00449504528015208100f01070343c640002d2002d03101007200000300100310b5003004000580300040400803005900f010900140030f07001040c00107101c800c21051000800c112400707040b00082503600e5003c008140c84502e5030030351610107054040852120010400c8801e0303d40200b000405400c041140881d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369639316 1250 369638066 369638081
    0x181415150f060705070f0f090507352e0e01050103091b14040b04020a0f0516050a050a05060c040b070204020901090905100801050711060a05090c0603160207060c0b0622 74
    0x3618031030307010104a4050385204403400740c40868070030310040c0742c07494004205062160000742011303d2411501c40d1000a03056643d102f40f91801d1503007944c80c011848090220850b9090b02215000a03042810f0303000b103400c20f80940300e007048100c005902e48001100603150380c12050300d00d0401d00403081c0005500d44011402807c0007140c403040390003804104400c40d01840c2d07446003d280100f141d015815030103c44051220003600340f4a0702d03000c80720103400c4540c100400090051180c00b1510003400000500b4001e000d1091045a050740d40355005821140510f100b0b284a40e4424007a40c00146000d4010740303441c200624210a40981d074162000540b030040d54006c00b11064510140700c01c40080c00740341d83c0800d01e41080d041c81c0140980b0030381e0701c020007409001d105645034045201020180140c60f03124100900050302c9040507202e0150307146039100b0302005031050400014043c0d00805031005103581003126144655511014440004000c0510308082c61900d80c40b0802603007107120303248 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 369640566 1250 369639316 369639329
    0x30221091615170103020315090f0f010b0f0f0603010306020705030913020a020f06100320091618030818010309140309010e060415050d181415150f06070507 69
    0x403401c1c8180400b5041400b050f40400e810002c0780700620140c0c0340022074031109211200c6484160307647c03501c654280794011a083e803d9005000031024100e005400441846004541c00c005141c2080100b2440244694826402080901c010400b08445034050807440b409102501d19010404d4001020000341980081601e030780498a044856810014018441c0e4004010103180c2403844d86a07010b40c0342c51000406901c424052524101d0506410580708400644004914201007429002c0911480c1d04032001138581c04850038104840d00d0741204598200691900d041c509240070b08100c00c111003240d0500da100c5c54210001200c28140040c3e080c4440301558507042c0705400100340503004100940301d103009000501400c41040ca554111700d8241c01c0030f41e520814600303001c0c05804a0f41d00c420144010194031018007401c0b1035109181001c0c402500c182c20703111074441c03203200700545281c10002e04800e043c4000e810404000c14486400500d03030380c00c3c04c81c107a495a150492170340041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 369641816 1250 369640566 369640589
    0x30c18090f0b041b230103020f0706020c3c1f050907060302040506180307031b0e240906030703080319050705040b0306060f0903010f06150302210916 66
    0x40184411207013030341c480c12440c04180354607074585003002c1c01034016058000f428840b00702211030540e01941c1200d13919542c03544250b40b02d40c140c0c02d111000f9001245070540724010002c900306264032408180c20010954604000b01011203d46650700d40580c4c4a1110740d032088211740c1c035084034800300d802402c0024250210b10f41c0f90003203150f820009940c0c00403060500502040c46166290741c151000f81421003000c803003051130a000240340559070362000c4c00c1d00000364034400110110850040940c3c5040001c0b504907220500d042c0e918030000520082180d1030980c030741d44980740641081d500564010100c4a03e19226220ba20780f81d4010342d0000c3c00024030071162180d03200140500d0703074005002c2c14014203040c5071018090092000505051043e90006928980100100b013510b420345c030064020055000000c0008000f46914001e180d040c1283c2c400c4902820b100f80216000240f08000c0303c2184030f840d1038100c7e903810300a400c00002d801408808000c40d1407071140e0000030a00318849 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 369643066 1250 369641816 369641821
    0x13091d100c020709090b010510020c0907030221070c02090406060518151206040803091e03070b0f010b090603190212010e01090501060f0f0c0c12060e07030c18090f0b 73
    0x2e46404440c0d03202c8100542003208403070104411841e0786046076800d684a40b2660b404103400c0b0706110b2010344185e8424609014091040d07031507406030440718000c401201d500d40b10585000548841103882d10001140a42c244006044c500b45864200b40b00c1d01e00805d02a4503030000440c910b94900e8192841e4084034104110500c003038504d91007160090310701040c1c1309a0044013580301d000051014200075000030200307449101c02c200d0300385071400303800242442450b2070b44000d40b070390300000003038039030b01400c2010684249203502042d0407584001c0e0707881c0c43c045031401849020341004211071100c2c00c00460b1180c0e00740b1f6a000400182032034400807001581041e514074000141138000f824510324002c0184500b5400c000b030002c410903242042c81c01ea02c044501102c103000c040e0740060518041c1c203c005100c0c80d81503e1304500310310545003071103254807046400c2c0e90b4008600c00540170f000a51800c000d204030051312ba032a50441580086201001394031454040c2c80050000c50301090140308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 369644316 1250 369643066 369643091
    0x1404090b0a0b09330a1d0f0303190c0f05014508070615170109051009080403050f0a0b06091003030509040e0610061413091d10 56
    0x280700014016184485041041c8080403075103100c00000142005a54100f1904a80c4c21015032136030240507004100d556050003140041403011819022034001203010500c42541ca4040c2501c182124041d00460814100d0452a145075001200c48410b200d01c41c4c0c82ca0020a400c205001241c60080c8004103401507091500b09101e0111110340e03464214520b0324400e800c14404500101040c2401103c3c04c8840b1424040094400e0003030040c0103078581000100d5000102c10300d1004c440800041c804500780c080c00ca2400d80d05400d1004045400445001007101c030654812645c050207480b000c1e0505440e076484ca45448606440c4403801e80c041d90303805080040041040e98030603020f845146040c01c182c03601580d84076580c00000c09000001c0b404284903101c1e03030301c9001055204412280f80303040004500d15150424000d0b040090f51800d150403903442540304503251008405802904903161044a8000f400e901d070244030000d003410000c9816410800502550340c82d01000041c0c0c0000c0b982 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 369645566 1250 369644316 369644329
    0x5160f090909381f05100201060609050102030c0604080a0201060312020f0601060e0916050f04031406060406030b0a05060402041a0d050a0e0703030e030106050a0b030403020609060f010909031404090b 88
    0x300c1071840c214101c0c3c82c1120780b050030504107400ca502660074100c41c52081c00501c0d15059540c000c2c81c1c00c82c0d80350004602065054102d0303011244651540603200d80ca49004a80303903c070b00c1480c2d0b58541d101c0d5000c03074002200c440040200d4a02c6100000d400f54032640d52840c0100200c0c2d4000050f4001811502070f010140001030050526091031780f21b076060000428107044008010f900301c0c03160800140000d5002e070003200c02d640140030810b66103546a2820036492048030784110728078444d540005a0ba418284280015240c0001c06503110780e0324452444098140200400e0300030350240000280e0403054001000f095580103045070302c4181c000c1ca00d00899800814404015041c101c11a920030300214280041d680c061603c144070304e0111001c00d000d40303440d5001c5504800140382c0001c1d00000e0a014500a074820307802c2d00c8943d00e0b1480c0c0c03e40d45503801e4850344421030080d8010400300c41964030022100d4880c1c107200c4010550702c0364058658000d5401007050340e4581c0c00c060384514209 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 369646816 1250 369645566 369645623
    0x30c150105030d14070f24050a05061f020f01020a1116180b04060f12050d0f0f0e011701180609021e09060403060204081b030105160f090909 62
    0xc2e070081c00d25201c00d40c0300500306148544290164800010948144005005091078003a0071141d030360206118041c01c0f001080000401c61481031403c4046040307200c250080e1740c000c2d5030042c968000760b8001c000c201101006a07400324154440c1002d0344e2044c000a0003e000403806544854104c4e5840000301030401d124015541038094205005100110241100880b20700c41c050700019010308000210b4000c02194100c2480d042d40b0b004002034400b00580c40e03084c82403082c020380e5040d20203050144d4094165000c840d010480154110749000e200780c4845011580c14501220580e00c1c11181c42c0d410142a040741001d001003002906079100b403806044002d16045404501e0220440c0e60728410360000c0d60905000400041d02c43c002c0d80c0d1ba441607402654109108554440d5104c0742e1503550100c0c1803100e14090780c00c07044d5105901c0c040c07003064491108449176a01341203980034116003041a94040600b0300642900c0491040458800c03800450b10030f1500d26981400398483c1e10750305000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 369648066 1250 369646816 369646819
    0x20a030905010f120b0d02061801020d170703050a0207060509150c070519020f15030403180302060d09080c0d020a0c1401020a030c02040f050a0b040501050603270a05030c150105 78
    0x2900f12104002e610940d408020540118001002001100010880d8203d4040658419800325005d165000400002225443c0903000c0700d51442c00c08a0a07921001d0707441180c114625aa00010000c9000e0782015900c203d0107200186400c261f0707030f101e4088440503160b8040aa01c0840c12021068500010a03040300302c3c4440c003803d0256507075446a880300c10002030007040b01c1010a103401c54807045a030101d040801409501301c0c0c0713a850101021500201c80c03c0c1d0020711800800b0554240f401c08040644ea00a4411460b00003d030901d0806050b598204a5060b00200318044100000740040c19140025034082c0c8100c401e541000c403148480b68212818145c0101c0341c2c0d9400c1e0ba0009007160520b581810700c2010662503000080c0140116180b103040c0034100420800000510f40c02a0741e81942101c081000741d07264000c4c8080b90000310340082c00e81c0111380c05809000c0d082d500d80c08032000c0c207401b1102080300036991141507400c00c440002065200a00c0f00c44502c12425255003d041c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 369649316 1250 369648066 369648077
    0xb0a03061a04020c100e070801050f070f1404350c01020f010605011e05070c14010f110d0309110319150b0604230904080a110304050f210a03020a03090501 68
    0x130004040d54954030080c0b403d0244c1d554400303240007420310900c440300081038030b50b00800041c0381038001d190490030b00f212000001008a2800b03000350307000303040090b00c0d070720000030785810203041c0b000c10482000c01c0154590004111212903000e4141100710a011220250240007c210780300006481c00b04e9a41320928240d0404200340400d99024145110380c5e0410010362418460100003620b441c032549c3e070064541c00c0c18074804504484100c00e0944843e00a90b111192131609090031150034120091a0750560401d440e110041480380d0850700001c1d000b07080050341c0b22181c0000901c0d220b02400e20302c1c040c015904801c001c0c0000840642d00d00f0001042c00d0151600b0000010b1032442a03000700e00e40340d801c8280c115a4200350521a00c4800e4014082e004c050406061408041e08403440788400140c803d0380d06682c440f00441500e0485a000c2c1038011103c507030300c00304000810400e40b48982c10803607070920791aa010400008007424080c0d006006081d1341070400415024940e00010305000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 369650566 1250 369649316 369649327
    0x1f0c0f050c06070305060105070503180f0405071d01030212191b1718061003051b0f12010209030304030317130506070e010e0324010e07170402040b0a03061a0402 71
    0xc1d40815400c2d03000071030f441d002506945003001684c0da4010450060314610000c2807114858a014a0311004110100c68a01c04204240200001d40780c0440b50b15000414030141403400c0d018121158442000c14100542014245d481020900340101c6a4017100002c0c420100303040c41091150500000000c0844500c1c40d5248001529000b016049203284411050025841107030010390b803010081c82ca41903a49909080741201070800250205840d240034141c421001c14000c90401c6808490281042d43c1d07103d040420003000c0c400201b8000c2c40d40d5001c00a03064555014002000918800d84074440e001006038401c0c400c6240081825401c9000140c00704080340c00000e84031fa211030b85140004100c510080100c0c0d910520052036500f500c40d000300b4810744000e800380e800004d42c2d100f460702400d0b0390311740c034155a1786001d43d41040402c0d40618200f030500c0b90821160340c41400944040354800c500400326140c108640c1c03054450750759541d0441064060f030084009101421a425401e19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 369651816 1250 369650566 369650587
    0x5131b0c030507080904060b03090c010210020423040e06090f0c190e040f061a01020c0a0b03060904060e070f060f0f0504120213020c03070c080a0b01171f0c0f05 71
    0x1403055040213801e840e408500c0d45090b40c3d0300c5d0445805002c0d035550954a83c181407010030303611260400e200d4054002d000d00000c1314041342c0300f99411280401c0030900c00e05c80348003d40c282804400c042340e400c5600d0b044580854602003001d44d000d01900300c0201008081070082070704004218808a115030100014100c0d001c500c6103044080c1e412900840b040c03a01c4a250860000062010007402d42c0c1c10300501c00a003081020f66008900800e800351107140e06840c040080f2034507140070741c00704600c4c2400465510f01b0025041540140b0561000502400400c005468041e1a5004400c4103009a20034042550300104841c2990001e040140003071808841c01b60841c01140240c1101c64034882588041d5940e40c1d6600b02520356424085694520003030040d520390307000b02c00c01ea850b0007840100040344c0700002201c045064000300380424a900b809044d5649000610b8100d51a2080c0c24013000760210540c803004ca40092a18009210101040094841e4828842440921000b4801440c1a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 369653066 1250 369651816 369651827
    0xa0206010821120601050c151905040f080306060c01060b0901110c012a06020310050306061512070c120306030c080706091206020f030c030402030601121208040c05131b0c03 76
    0x1c9907240c203c00049560f0040106e90500034800081218032a00c0441640c5e62054494280520701c2c0e40c421210b03c860382c100d4401920000da84c002c004c20704d000e424201090140c80a9600301d00010f00d51403800c4440b4000720300356000ca0b040040e809100046211441d030308403002d2284c080351080a002c03045151070001e0024500002c0ca035800300b070310781c880f4694411030b120300c040c92580c040811074480c103111900600401460103100d0213485402c0105420385805001d10b000500c024590516007120111114034000c0054000301c10300801454083c002071480a07948038601072a030f40080c010349141406040e510107a8802c0400381c2051000f881843c1e842001c03a82607880406a03510824510715000300203110390892011500004401d202003515542c00641c0598022811540c00c0d903200c001200300c007000174900910090709500c1d40e41c940b07801040313080e07071042c0658007145140e965140801d40128401d001d002c1d240307507206103041e139041d43d00d00f0080c800c99891070201115903003954081c29 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 369654316 1250 369653066 369653077
    0x3030f06040b011e02070b0a0203032e1e03020603040f120f050a080c0c16080f15060f010e04020a0f08010b0c0a14010b040c030204080c0f030601060507030c02060a0206010821 77
    0x13949241c2c5040040080c000c10210b001000309000960780d405401030000d40300d0f0029545500e8401040c07003001d8000c0356251090800820008014a1582ca080f2100301c40c1b080c0b0113038480e0864501d010020160360380c100a903100e0307400361041141c00c441502e80f81254004a9041d60188585180d404c50002c0d8071106542c41c140d90360074815a581c0303a09070100001d019042b0400a90304c83c81e0030003002424040818011240e28000b161700601d030074080c641d1a441d030500c40c0341805200700c00141d0305140100941e4400c40c1e060504464104ca06004541603900194462002c540100c2c84078650301d0740103e2840c0100100c80e078240c20403900c003200b01d46929101030054440380c0f00100d402c9401000b0b40c0109800d4500810801080890140103000303900103101e0801c1e0341c01040d11040c61401c002c5002d45024000802404981c0c0c2011030239200b0b604416010b60800c0b09458407540140c5509009081c042096002000170b5890211503d262084003074910b803100c0402d04918400c0f1900e4000d031035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 369655566 1250 369654316 369654347
    0x10031115040504150f1710050705090d0f0b15030709050405030304230a05100b10020715140c071401110c1005070b0f1006020115090b2103030f06040b01 67
    0x280b05850038410782484e07a00360884003a11448407400203040030300c00c4110702c200000400750341856940200c0002121401c55844001c2841001004081c2c40c0211031003403044c0c4508500000d00f032a98941842c094001c44001d40000300c80030303500e400c525082244034000c201c207030800c0c070103464203071340b1141c5030300001e00b005100103540e40100c280319402e0318070308181e44008000c44d12000181e0501c182c2d20140901c8045200703192007260b00940c20411581040240310b50020310226181102142e0003d0454808500300000b070141c040143c1c020720014018020028010584a414200c200c420091030b4441c2c4c1c1d05002048440056013103012a0700700e9050011101060b5461410100b9075240c410380e50010244005e070350400c02065500f1403d01d018032441c202ca01105034860506030300702c1c6d1480e400c02043e41d07005042003000001581100044d482c1c0a0108a22429954040c580300542032211204a410100400180c55071204015901010440d024002004600000781000225034500c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 369656816 1250 369655566 369655571
    0x1803071509021c030e2e080903090a06120605100909020702130507032009011d040b06040e070221040905071106270106031707060e0610031115040504 66
    0x1e0159918810207403070b50f080101c0301100d451501e01c1d000b0400800700380024810403001d100000920201500020040481e00241403112607591082c1c070414001031408a083c0700c00c02003c086a1124032501004190988850342084c0300100254203852a0f0b0700014001c0c80e0b51240e40c0b9995501480880890f0b04100c0c5c0103030f4400303850000c9046007618880b1074120070b040c82d0a004000d5450b0b4003e0040d10200200e03000c80104080328103486109400699000800341d481c0c0c85010080518125040300307001b4000102c061300640891400c0e0071680c0004030803285041040135480c1c05201e400f807024000c1c900d4603030905200344034120324040c130700031501c4207a43c980004914900543e06644242c642e0300848940b4034101303007c8800010504049115030362281c44c560031010050146405590780110104600e501a41c030301c8065410011054070b0050301d0354002aa80103080c40524000d0343d080905007a03036415410005990004680494040c1c044185604c95000e01d210a807030030381c3d5045901 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 369658066 1250 369656816 369656831
    0x230a0b0a140d06091104080f0111091207050d03081b0301050d08030405030d050405010c020120030f0c1c060609140d03030c030b031005010306140106090324020a0818030715 76
    0x41400038001c5401410583d40385c101480c40c64038154016108655010003142c1001c2e0204400a00380c41509901019882e000d01a45070300c0c0c6030031000140003030302044c01c4600955440d0300040880c5000070301503000c21110b10610074415406802c1c0c4840081e02e9a801e451945010702060101501d500003510036100440403404200041c0101c44c583c101503601400941458100701c0d000f00600d12100d8095071a204040c0b000c00d0060080280d00c141018943e410f665940500018802d8001d0500c0d10640c030070006640c041c2040c4052034200c04070000700082c054240200500540c106800c0b420301e00e0b4445e02c2c0c481c450f60b01d13204c1c85455143d05107404504c0f51450a41980035103808090075605001da907400d0082c80905900c40da0490f4044c44007071100c103c40a6412030070300c03028000c00340080d12408060002c6903800d550500d507055955031102c032100045841d0801c036003186001a0005959400b0301001e0000c0c81c00100c0b8880c3c41c1d901940c980f0900c3e03501c1e0000d0f441c009014203207540c3c68016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 369659316 1250 369658066 369658087
    0x10501021615200f07050a05150c01090f060b240304030e01020c0402040605091306030c03080304300e0109301212051b0a0513230a0b0a14 61
    0x3d8039510009400440948603000440d602d0300ea86040000083e240b00340c14000a441c03030a850000304882c5c0281901d9100707010282d0711b801075403150340846510340d00c5094150000d4400c0340c2c03004286018007000181d07640220200070204c02240747d1524680303080d84e581015949614102c83c1c005500d410206c0c1c1511020380143e0070864000d419550080c4085800100b0303d401c000103041074041181c003c1105e246140014045402c217020141c020002d1240c18400034594000442c0c100d8000c030124210707a500c242510304030981c1c1c0051a030040c0908a0641c48064014505500e841d03801d00744588528180380070303450700c03203403014010f42d400c00d108003040a4015002a43e020344d5030042d408034100c550140d0060840900d06400042c0289410002686030000034803949003d0303c0700000d549843c4001008403000e4210441110310002110000141a0301c50613a000c0c1da440c640d000c005088203400100080005030741d1100d034144000700040411260302001118941c039604151030b40316104d00e0b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 369660566 1250 369659316 369659327
    0x5070e030d12060b0403030c0b190515040b0306190902011101020c060601020d0c030c170c070f17010501080a0b0912031906150917030706110909010501021615 70
    0x814554040c01403881c80340c015a440b40baa108103152219040c01081e584007111816440360744030240005000c8030031500002c0e8480d039101c1e08010585021141c2d03107002d0164004440041d0f4607d04100c0004e46108841c1c00d060040c810130480803005000030345400c141e80742107000b40740c0d0107441940e0b44032000300841e8082c221003900c0032500c0c40210344940385006659a940310542c0c0c100c0c05031145440703c501c911321556192503410f5050341c03240c0405040c0e80d601001e44941e0700804410642c140641c41071840c0c10881003004010030b00900305000c2c03614104001d02d1440030300381085070b410040180f0020301d0003d16541a56400380a01c0284d9492504650600c6c04541c811213814000000340a1510410981208001040e00017000f83e540e8441d0409080200c0062440200e141c40f03400b0072840204040e00c2c0c26911520b0180c81c03402025030f40e048201d40c20000702c4c14400070301040040302810034401440c090b000030b000820b1100c0742c0b4611203031048890700c507a00c0046c402103051095130b407280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 369661816 1250 369660566 369660587
    0x4030c0204020c0f060f0a141303050d0e01020c0706080c0f12070201020c030c01061a030f0612010f09080715021e0322030809010c030506011b02060910050d060b040510030507 77
    0xc0680f500c2d4180f51b0000a201038054070f110094900300880b20300400c81c1140194010302142d424080b071042c2544d41941c00b074000c20102d00c0480e0b5143c00c80c0e6081c041c280024000654083c001c2d0160364109000900302e0040940003445085080c021302c0b01d803840150884d228082168001d204035030f01c0000807400b9120720480d1502602000c00d50081143c01504178906540e200c010f400d4a18210041101c0c00d4001168603030303800039416000c11400d040004c1000011048040049100b00d0509401019503503540800c4a01d0100004c0350402e010080f411071940784031944042d45040310f0000502c140c10b840c284250701000000002c0744000b01a00f00703081c281640c650708080a41c41c03a08010b4084c1100b1602c000752942006040071030a8420703c00c603403142d103050311606a840090000c3e02c1031000c2004040740c00003010001604582e40d070328001d11400046980380b60b5100f412560103001d03600a40e1003917400040030b01040c8941e6490b6002e06800c1c580c80d14000400355907254048400402e075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 369663066 1250 369661816 369661843
    0x70807140a09020408151609150e12100f0902010e01140412030302030109051005090c071a0903090a0801061211040f09141509030a0c0305041707090506030604030c0204020c 76
    0x103400030301170030040341d0242c8415520420783d9044e0780f10544240e00011403003204c000641550010b1120520001e11083c0d01c2a076894180d0045800030041514411070041031101c5d030784400510402c02084e40950a02810086024441200c9680c00070780401100e807042c905110548051941c200c2c03d801c291801071000c510710088460890902a000354401c0c00ba803071500d810440011510b8038000c0c0c00b0307403c580b0068002c82e042e13951800340301015001448100d4046408040e003502420b0039054a6000e41c5c0c50304c0180d03a07079104031010005980c00030303400070380301b41d040140030890035200001102000d60414041140c10429400140040c0340b200351150f04545000010f00901a440c00c0c050001c4600004031040203007061400046000c08480d1004d89600411a62006a1081c03003050f00030f610905081c3c0c20709807101d4a0714403004003000700c201c442d4080c0c41c003080041c02c0c501903180c000300150041d140d9402d044d28001e214280051010f80240e40002d016107800c001045041d15210a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 369664316 1250 369663066 369663071
    0x1d03040303030207061103090723060403060b0102060609390a03060f21150b0315040b07110303130503160f05010b0612041509080f0a11070807140a09 66
    0x4480c80c002d0020b421130082540c3c2a443d040c1d0107004005144103ca0013201980b00070320526140030040101c19980540e1300c139010b801c400d81c510301502ca00028002551040c1c4d80843d190b05280f00080c80d1840c003e040700d102e10565802e004682241803200741305000001c2c0c00c0b1245494001001202181c1c00200c03a002c0940010f0a004040c3e15901000644005d01e052005060703039074107030f5000358241c509401c03800c0c442c100fa8040011b02c50350307075000848040b40001c00c0e2003194200090400d0036030070591200b0346c0700c1e908102c100620101010390100305170a2009041540c01b07a0190360740001002041403418083e20f00c401c2c0a8100140c40c00000140350b0010302d00c49510341000a05003410045407070f03600f00110080d40740b800c40c082d16402041700705030320080e5a90340c441d060380301000c00d805050540d0754171040002c03944504c018851005014005a83e0f4407200000501c00c000980b0000d491f070b00001428800c2503800304d440c41c00c0b0391243d58096a8540300b0400182101420340c40501d9552 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 369665566 1250 369664316 369664319
    0x303030c19021204080d0e06040602030a030203040f0501060b04031106041a0915030c1c0606050a320306011d090a0e010e010c03060806091f020c03091305010f060c050a061d0304 78
    0x40025410486c0c1000d940301c0c04139524050501203a40950f000f00c00141e08144640e2a0710b0384039502030f507070050080c60102540a240e45030203084858a403c2103500900014050040c049a1048600300b1041554070910b410302d40f188000307000c66140100c41070140c002aa52120365204102d02880c842022034441d664108212904425400240c03240d16403041c04a9130601042e55216160031a5007544406140007011034088072043c00305031004000c02c0c079410560401040380000c0000f04e184070b400040c6e03281409800034203184a180003aa1320750000c40c03076803882034413003d441c20342000c00d224000ca20300940070b640d42d024099408050203030350b18040020106540c9600004c0840c1c40c0c16040d03450300d444042400751604400141a0450490900c41c0343c00f40910350f0081c60301e0111312084e241804410800156444514554000c82c02d488070014880402c16249520081c049820640300c00e0300c096581ca5218000e6540203000320b56516000100d000c41202c00f1114406c14406495695 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 369666816 1250 369665566 369665579
    0x305100e01090b09011524180803030a0b0a12050a15020702031219080f070e040609150e09150c09011b0503130e060f0f010e040e07050f0303030c19021204 68
    0x20280740c0c1c0c40d0402c401c46c811002403016900800c1c0307661401e1f00b00d08801e80310380030901502c013440965a1208003034012280007450040901c041c60182012250102e41c95024078200720f5440c545401401540c0c5017015040c0005200044030102254414000405948183c0e580f038000e0242c020080d4040c06400c55501494103444010f103c900110840c5660000c0c00701400c540040044404c5c0e00c414180e000460105802481c520752100700090010540380d4850708000140c0d407405103c00b00700e9221308401d20503200120700443c0d000400500400042c5070f5428a800880405065503116440026090206034801c03001144444805041420107210510700540d030fa03405401303060811800084003145511240140a01400009101c06009029103040007810500000303500d0521101c0e0b5420a01d94507503005201d210562100548180c501c0c2c5028005404000e802c002c0c480d170020001c0207007040c030304c405441e595418080403469040717807990140c0c075008082c46880c2601c0030208001402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 369668066 1250 369666816 369666821
    0x30a1511070b0f310f2103060e090a1106040e0c030a05100513051f080307030206150114070f06090606080c011107091e090f0218010305100e01090b0901 67
    0x41e030f5441c10020380540d612900b841c40440c101c86090b502c44140c0c07008000d030700780740a0a82e40c02401605030003008921075603a0102200203030385160795548a056a1a4015054800c000c010311884001208619001050948071082c6030401444080c0522140205807614010340300034201c0b241505149042c42c0e010488aa0800c0b03420190301402c040000d4280003581d410740003107840113007400c10607111800440003e0b000050085400304a8800000100c1200c103000e0340050005c0340c0a1552090f403810021300304000104143c40e042c0c207144019003182d0b4042c81806010251071310541d21840030307141050261004180c042c0020303044c2550201031255540c44a002c0300d4010033203504c4c0c1200c410041d204d54006c4080c1d0081b07038202d044100f100c080e01e40c00c0a401080864407000c00b424050b0704100480d14400029282c0f00c3d03c51541904600301414000000d81d4120303500a07040d85560b132103990b604802c0441080068559494000156094021058441c1d100401000c03620345030651600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 369669316 1250 369668066 369668071
    0x180f0207081e09030c01030c0c0f03050c010c05090d020d051002040e010504060501020d08180c1801080c03190f0303020f070609030e04110301090506190b0c0c060405030a1511070b 79
    0x4400b0102d8082d10520700040d4120741c0e00160180c040d00c80000c8800040d002000c0174034206051007114151000041c86440a07424220312a4480c1c0341c640420f00d00040c06c40380d11040300740901004100d89078555230340340c030000105681182d131a001886103291941c2032420029440ca1401d00200c1c000c1512608014014180c4200f82c4e810040d032541c88004a0307895024000c1c410100701d0800110300c00d03080c0c4402092460302c2c0d0404844542c2013080c0880d6110440d02406d1072140e40d904014843c00900f440f8980e420001100104403c402c0c1440d9600340c5a03a8010080180f0070300250902054020340590703480300f030b86400350b5449100720308101020380ba001c0b0084000130302e91382240c203003840c1c90312035004901a680202800e503030034140d00e90014540074000c070754020302d24031155071038501c642183d00240c80598415600e840ca4850001c0c506a01c01c0d80360381c4035034804d000c20301036500d00190000c05a500680d8450029008001a400802c0e4282920751345082c00a0701d0300601c00b0200242c0d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 369670566 1250 369669316 369669337
    0x402040b0604050d03031a15071401091a1b1b07050a1a03100909080403060b090408070602090a030503040f0503190b060904210c0b070c0507180f020708 67
    0x200d24101801040301c02e00c501e02545520440c1c0a544d400480c1c442e900c000d8020441a142c940c82854001c000303800d442c481244c8491035080011800c040010381c4540342010b0210301c0007484648a10350b00d29001c004004004080c81c410b1800151074001050686c0b003200c8031107643c0c03503034030700c4665003070781010f155030032b030b4903258410418005110308044001d2421600c5500014103110210381c590100e980c0050a1724003060b0041c4404560078815220300070140e445246002e43c0c807460352034500150350000400034407441c200320030040458845000c60703003142e03800140140d079112002c001441d50a16504090424400820003080c045d00b400c62100986801700c04540000001c60b1414024169003080144050840c0022401c0c90902130220b5070807a2284215000311150300c02c0748c4480002540c06000001d5080360100305208032020234582100b50f07868448141e8410351509036690744244104a05c0c0c100c10b01203044902503507030041ca9000d11188040d51746910f5070604080c07580080080d40f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 369671816 1250 369670566 369670571
    0x40e100305061609060509191d01060e030d0302070303180303150b07020a0303050715090506040c0501080403020c01271401030522030e12030715050a0606021216050d0503040204 78
    0x1e0316070250300103543c501c048240c0e1105030260503c135080b0340340c1d08844825900404004019004004264001400340600103465200311901c047c03560a003000603405030b414400751911889075600c001c2201d0311071a0762404c3c0036a45813590316044000300b26029601d400030124000d10700030582c1c550008407030804461540080d20791600c08224641c41002c80081d44010803840810010f4011780c06011654010707124007140281501c072650a4071544401125a900860b0400081200703032006900034040030f02e0013801d1803038250f034043d5981401010b41414440410710701a150746c680e071310f40c20049814a80c005511503450070030300280c1e040102007030b012a0901002843c101960202103d0180c2d0b195541d240c00d11440d1419038040c2c0c2400742c0c541d00024290000000e1903000c100900c1228400d86140c182da4240c0e40321002140d0020788810740c41410514100182e990000d0740c2c1080240310000d855507165460080d07090540700c0301e0020400d000b400300c003d21664020b4003a40c0b0550094038103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 369673066 1250 369671816 369671821
    0x61d0105100b0403020d03031d0a120503010b120a0e030703090f0503030909041202030f07111810060e060c150403090f0303210608030d020d0e1203011a040e10030506 73
    0x14445010340703406110031031041800108098501400344110250080c1000a03042c00420302038016142c011080c020b10394014040c800c100503003c018003586018500e440c60035035042140e038030458410044446d0714a40c404000c140d0008440d40542c41141c0031408403a99000107160161030141184500258544201310000d03c81c100801200c004040051000105da40d0300e9482004000e607450245003144424030442e096044090010401c15000e0001c01d298104118100403000110300c0107251200310080034400104040520079050387e026051541461f0303114004101540921429480b0034070074030f40c0038001006c4091001e4003c0c0d0080d0303541280c1d15101c1a42d1a030003880c40c80010002070160000110310343c03c62030184040425650017203007140e40e0318451841c41e08003030040401d9650000d4a14403100c001e128180002d407040001d000c045c3c9103411182401d02052003017400b2000745070120002c503000802118080c3c1011200e0360b1042c00c007960301040072035072404100d4840c41000e01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 369674316 1250 369673066 369673081
    0xa09060e16020c09091507030e0c03010e07050609030a0b0a0209090c090102031e070c090c02100b0901090507050c1009121e0e0a0801050a0e010606050a1713061d0105 73
    0x2103a44188030142c004101c1c80007080240504844000c00640c40c5000e80d20f140c50521880842d4940961255607010403da09154042d90501d107448400c81d110761314000440d200d8800c003080050880b0310448402e5110b080140100781000e1840200402c0341002008020b840341059001d000d03004000d5030f0180181d41c461440700e20758450448414056071041c0040c1001001600300902024000f68800e8148610750303032049111050307900440c0d410b640306c10b2107200e00c590410400b0000003800c18180a880d201401040719060103010305182c568443e80042c08150082c0c1c115111365100c002254030f41c1800d0310452004000c03000301250320915100da0249142d108403180010800d43c03036100301d40054070140035a40308203a8030940b41c200c0b120f608002140c0a081c0b007a24468015683e0104445c0016142942119202e40103041031060a004c000c1045600c0003400c11000c452440d40069a1a2600d10341c003181c0c0c02d400001e06a80c2000182c1d0b000031074282e07c2c035440b500790400900c01603c41a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 369675566 1250 369674316 369674341
    0xa030612150504060f2307091d060118030308060102210d0b03011107031d01020105070f0c050c0904081305090105030c060d14010b0c060c130b0d06050a09060e 70
    0x14050040032207100000c507845182d5000e00c1d00f080c419103000807200c040100c01001e80382d000d640003510880f01500810b1107404c42e8240b0b41c2c044041d1900c3c00240e814a40d0705d048500341c0360f006150450080002074020b0b4000c01b82c0c240400c100c4001c41980300c0d680c2c070f0000c02080c01210144c1c011b00406013007901d41e01d44181c1464640800c010050b0070300c21400c00f140001c1204036481a131564903804a0490111040000c2090318065601d25034650b50230f0b44091849007200031442d046a14100801c1b5075650f0100d01034003400860b107800890f200003401d03c00d160031400054564015240310074401000410001864a91042c2064240607030740c1e03008201006000b440303815010707001a00c003980c081c0362840003080110300500300054080c0405090b0750ed1a4800d8200a03c031200000e00296400742c1008603d9101501c0c20000e07180000000001500c0042031040329000300012507a0b034201043c82d001500a0400a0b0101b03040648d2034440304082d144c0ea01c105843c3c0d0501c0c0000c0b821118104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 369676816 1250 369675566 369675599
    0xd0507020f060901090f090b09010b070209010e13060501060917010c0504152d120c020a020d0201030f050a02090a090b0307030201050906070605091e060907061d13020a0306 76
    0x828800d4811038407414414140d1000360034a04000c000c140108844070704440c0307180030349404240003900040c40414891165010b8108092217002449000b0040c0c1d00c0c51606410b40314680c2c3d208203551960583c00c02d00f501918802020317a81018004500300c3e6111404402b00c503a00da00c0e101006020240ca542218103602ca20b40004004000c180401c0e9100600e803d050141c0c0d2a10040c001100e40448910100c24941d078201e00192640350b20101d03510026000d03d0032582e0004100c00740351107034041e5440c0012400280038000784903031030003035a004c0d601500d00342d42c0d002020302880c50b020306030707500071340c00b101c4028400ca400c0c20000c00c55582c3c0b071081e05840d803400760081a80500303680054a03190864400241e000a04000003000108a801102d0099404000800182419540084035504034100391764641e8031600400110000004100d81150120706185007886c0b10f441d40c03520309000c8030813107d0f0000003404c841d41020401d42e00906900000c0c2d6030800040c0d40b203518048040001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 369678066 1250 369676816 369676819
    0x15061605280f0825050114011a2502030a0c0611070e0f0604110703030f1b051803160609080d110307030e01170703020705010c0306080a030c02180412020d050702 71
    0x30010000000d043c1100800300200c400b4808116050305040c600312a42004204a400765118403180b64400342100b4002d001d40120b501e43e05038903040060100d9980140c8001500940c0303402070403101400c440c09901c0f42c0c02e0b00134096400d604400d003800c0215800d03c0c4143d10010380819081e4007140c401048040550b00284800c0d04240c592840345e010704000074100d01e03885030365128081142510200104105d0f03100c0d0f24003103042050603441c2012a60f14000c10007101d01c00a8403450904d6200c811540e0000780b441c6504461080b13800403d180403400c40500c00796050510010604980082d02c3d841140d50400c100c4034199010541141c1d68244000c6e10b140a50080c4054000640500788000d1950010b14101900e904a5100b480302e00005807004000f080d4001030360400d002c000e00403074401c0c910504040c00107519050249680301e0340a540907082008031a0040c0031940d909803c100e800b125003940c42d00ca41410f04045203090095806400548140100603025601681c182c4044640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 369679316 1250 369678066 369678083
    0x10305061c020a080303040308010e06040209060708160204020a0504080606030f0a0b09010212010906060e180a1a100f0909050c0406080411030601060f1805091506160528 75
    0x4001d48144403116504a0740300c03552110201d009036081000d107100b94000c3d61501d0741d079450705c1a4240340000182695000e5401008808129200c4c0c0c4100c03170380c0580c0200341d6a91144190b81c092000032031a00020750040c0000350a01c02641e01c000a40291030a140070b85000d40c030303a0001c050740e032407540d4005801c43e0040410314000c140d45107031480d4464442800907140011078100292040000d8010b40b85042e40c0301402d210032030f40001c04030900d45040d50018109039030b02500000c2e02e079009007079000e2607448009420084818a03401101407802400103010041900c03000741610381040c1a01780050103800000034041189c2c012207020340c40041804d803500d420002c2c100c0b215403009100b980d0110350182144101c1e107003004010300074038182c2c2c0d0f0110b2030007058074028012008000100001041000c081c01556940c800194012801c2d644520034014202c0120301a400313182074080c0d06050041403941405004102a40442c1600150300c103522880f240e8504ca0b8442c021000d0136000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 369680566 1250 369679316 369679339
    0x1110c010305040503120a0519020a021515090a090b1003080f07110d0308010302040c020c030601052112040509130b0f0636250e060d050901020a080601030506 70
    0x14001c2c0d100d40e800c03601400c00e581ca40f0b428a018540d19000554400302400c0e904d504100310b40000d110100300c2c10705000c5c402d500c2c190128200950f0750b50400244c0c554800c005021803050349a01c0b0901d9107030340028214038100c0c03420141c000300400e03081c030094440145840009441c0c2540d0710300c45050f6548a1000d034148901c50784501e10036008000c04607545620b4103401400c3c9c2e902c508140c2c13140c43c0700e03a032460071740d44c1144144400d03105000c1c058020b40d800303400f015a540d540454600e064400684d4064034031041c0748070f0501910b0442042044034081d0807288003154484200034800d41d6402d40b0f58101503100c84404155290184002400c1ba24111010411502519800a0f0842c3c0000d0403012810003001280c1d0403c594a0303ca240d840c0381107000050b444070359081c01540403890045065034030320031988545207401508280d0342000f2144c410700c00c06a0b20001035030100d2108120800c081d10f810ba906074000d611651002010540380c00005c1e485603c80d004243c42103402a00a07130041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 369681816 1250 369680566 369680569
    0x160e06030c0d150b2214011401080a02130b040303031812031a030601080d021e0316051005041a16140a050f03130201080106090501080135011a01110c 66
    0x14540c3c8491110115120610542e0a6540c0b07414454440c00b200780d411496a0900f6079041100c1011213080301d039403038020042068400d10f00e03038084c1c094402c0c2012030a03640ea0444140c028490400300201c80c07544020041224152880640b050705e20030388040012395100ca98109450050034030080c0340b46111242d409006120390418200c0c04201094100e11544860010313042100981000c43eaaa010711aa2041d00e43d04200840c0d40c01502180c01d200884441216030700e038401c1c0500c01c200660485c280b102040010002c0d03421142524004004c0c80c01e00e443e01c801041c200e1000c0c46a003111510114102d05458031804030100c0701911105107182005d076400c2c105811901d000c405200050080c40c0508010748011031046d10300040b8248420755030300c0003521041e01a0007030740410124041c1804242d8124841034190b030b0458010114801104614032030b0003584c03220005448410711f8080c810404150840c1958107169400002c1e101c010b4401110780c007a40009041c01ca9200e18442c1015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 369683066 1250 369681816 369681833
    0x5041101052b1a090105091b070b091c051305040c09270608030f070f1118101205030d0c0c021e24090f0a0503160e06030c0d 55
    0x1c46034040d007024071840103040c00920541d240b910004141d80707520b0340c0c190048100032000c00c1c1d0082214038000550403c40400d0650000403e803020310f80c941043c3c1043d024044003a59180c907070081f001e810030326281412640b9100c0040111485400c100700401c80c19024405079410805a60540d01159103440208006030041e48400d1051010070f1102161504105040e00740d420700141244205030821460041103941c0c5a000781d055400a100d03032440b008640341250b12035900a4020b50b0410007030b09000740300e4442c101841c2d500400017074040c0c00000070403103585d10036400440310394200303982c60b9003012000416603002050742d00200050400e960055101d032070300419601e03040210302c429034003040d02d51403142c0c0e0040e000380c0e520841c40c100f40b41c600e100710541e03581c007020010030300f420140800c054010f91102d030b072046100c1113000c6525140d003408280101001812120101c21001c00311200d94014002c1444141160000944e00d085c0058101c801d2403018061448256085d2280ca20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 369684316 1250 369683066 369683077
    0xe04060e13020a0b16052b050706020d02030403020609061f05010507060f110705161a1602030303130606050a06080c030703020426010b0103090b06040e2b11010504110105 75
    0x1d00a89144000c60700d8985480600045418103681074180d42c0c080c10440d1030020700d400b1005d0441c4c846940c1c0e40c07c503c1401c410b5185098582803032901e41c3c08a1500350041e00500d5503034100284040b0801c400c2c140d00013515806107481b4002d50300c0644a0341c08090310300c43c03240c90980805620a07403c00c40d552040c0020010349000b84c10003d81d240c896010b010541d640e1004502d24a00c0200d5858148a0140944450103100c10441c41d00b81c2e140210740841d139080c40f803201f542c0c141b02080312006c58208440640045030b009050b640e50380341c15103c12800081c850300585d80f1915250700800c05041c4005600140c6090340c0b91240565503840101c50264001040c0c074080540130301c070001c0c4500410040c40c013510442000c01c402c521150803400d0840b00041030140c10141842950400310385010039054100006540201d0450600350700a4600382d42c4002e20244102c181050441180f00d90038061800001c95603241c0411113400902d600341c49085d01c014018080441550005602400040c175 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 369685566 1250 369684316 369684319
    0x3280c1b11030a0803010602060106110606040b01050712090807050f090c0c0a080f030f060910050103020f040314030408061806060d1707030305190c090e0703090b070f0e04060e1302 80
    0x1002040000c030303081c0702c4083c00c101d40031440800180001034041c00207901400480ca080d203006140030004541e1003030080e00050069075200070030b61301079200e03508441c0c420390443c00104e5503c6034038000901c805494815000345000d82000424203213000311482e62070080043c03001042c0e13181d4804404045d8440342618405106824910000803880006001e801c5011015a9144e14107030360030103020071004080600c030718801010002d5020444c142002641d10038030740142c54240c4d41c1f410314075910813a00301500680c502c280240c2880c3c2c002008205a034410410750303006d070300c0d0480c0840d00c00607100703070b01041504040d000850504242d10030032081130252003942c0c00f404000d00c080c4419402120147d0000b5110b60800c250703c0d001d03030b10000010100410401c65810164402050072a103030150004000c04000071038075580c820741006181036003100019116044c9004040c204498203030074013005c1805070300c420f20b451401c1c2c410b2000325811880448410382e01d00d51003101410b0156400c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 369686816 1250 369685566 369685583
    0x2004090c0308031603060803030a0e010b13020d270f060219050702010914030a06021321030f0923041b020106050909061e07030f0203280c1b 62
    0x1080400c140c91800390003107000b8620035640b4100000c2d81d002c01400398207070000740740c1403050422070700a0002c01c0b280e1040c1c2c43c1200040c0061404603450150441c0803046501152042034841012945e900070400d40004001c104001c044580811602d000c0000b200600c003651486084045051088001400d6201d01c0005261051000d0384144800c4000349500003c1c0340480c0180031541c0001220000c0d08241d0300c0c00c80390514140c000b0b551000c030560020181d60700814160391b541c0354981140b0280c27603000603080450a480380c3c00010000306402c1940052003104034004600d028524100907110151040d0041540d14606441450000700841e80c00c2030340c03000c4030301d0706000303202c0041d000d400d103680081103c070b242500300b1070400800343c01c0811941103e0144003200750300100340034070740511084002c2c00d45c0e41d1100c29070007031640c80000741209000008004444001810500e031180e103044812581ca03079410342d103a044854141850020411414000b245156041c11581c1010300c2188079 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 369688066 1250 369686816 369686831
    0x3314060a0504080a030e09090a08030c13150305090607081006080727080f030f0417070e010605120a090b0109270501020406020f030c120714190201090902072004 71
    0x244c1c9003c0d1148425000100341c030702c0c12011440d00401c41074005007500010b0207107411035195071754207110182910300b4000000481010003050900b9540080000c0c5d400f0190031280030102401519040318503030f402d400b5a50001e0010350240ca00c16004180020042682900300001590501c8001e09400180441a100c281c206501403030311030000c1400c811030b44605c621349459545070002c5c20100c2507641c1c000b03105004641c0c05120903241102c11560030103011340c03080780c441760401019800158000c150310001080e01600080100445039640d11101080d60701d0101d540700f00c5d150140700a041d400c0080040100c203601d500700a4540c1107149150110101703103001508491102802140c0316500814104107070380d0180900c081421400b030155141104500e03001d52603030340000c002c2110031030100300070060050640d1101c1d9401c1104c001c65116032410305540240401c1d508003240060060301c00406d56403014001e48250584c80441e5811604808498004040548540c0b9400c503584881 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 369689316 1250 369688066 369688079
    0x51c08010521010c0903031101020901051227010c080610020d030c02030c0114010f0506090603012904090b031e100911090c0409050912030408070f063314060a0504 72
    0x644c04451884e40c4030110301e036146d4030300a00a440d02980401003070740306008004061760017900711110301a00903050010303a51200d2490b0702c1283c6000303039181080e07901e10b44100e220005501000d0004d0468881096a6071080204070a2003070200300200140c11100d00c1d045c1c1140039400c10301c04115540150303414a030322a0101421141c030422460310316243c00e00100300664000c0340c520003815040d80d24500d8500d10001003003d42c401031080b40c4c230907201881e418030300a1032509010204010461959070390380e42c1d100c000d00900307054465070380710b80101c8818008035101c2228401d4100c070200007810702c1c0ca48180c09100240320b00b104c04d9074401c07148a0b4842c05035551444503842044260704203602d86041103c2c90007150b50080045c50154000d1a800c0d140e0303090079069990261b440f56400d56250020b04e0054410285810004c004900340380c45040d4002d41c40c8a0103282c01c3c2c602120084103c0f41446203980c00e2220710030f440002c00140001441400d10303500601d030f01041030801c24982aa40c2e017 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 369690566 1250 369689316 369689321
    0x1030c090b2109010219050c15010b03010510031a1504050405070f08070c0f020d06180c0510020303040f030e0109151e02031c050a06170604051c0801052101 69
    0x50329504109034041c1224032207900305640680103d480d2008505021944082850800d14501c0c8402401001b1840c1c3d50311010030480c02942e0385400317407558200c0d40d42d200f1041c0f6a810078000e0700e00c00c02c050003059120030700c2403191500002c2c181c00005030150341c00b020b01c40406030500c0d150112074020000480e0540341c1b4000eaa010344002d96464070b800d103034480002c06203440030b80804d0802c45900c0c215404562281d49000041e034041710003042809451404600400c291002049001c928203403000a00c00b030300c01803004551040c0da8005c04a04407101c01c0362644000c4178000e108801c071440c0c01d4007081c03090780744400000040c141380d6001621041c00040050f100000c180008546180c100c50360040f2250105005069000540c10404254050f002e081c03060f9482c03a12159864000a000e82a103401070801403640c40c000d880c080f000901225203406007250305132000e22520f00c3e005d41d002170550031642003d01076074a20800b40d08100801802c0d242c132003d294604014020040c402ca202803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 369691816 1250 369690566 369690577
    0x914060d15150507051c0c14010c320903010207020a080a0203150f060907091802041d09070e09100c05090306070807050d09020402070f08030a0b0a05060901030c090b 73
    0x4600c0082007403526905203036000e19056918100002405640001200054034506d09020f14800201c01007001c0f40c1240c2070441e000c400b40610200c444540c041000650203150035802d02d994002250300001c4140940c691401e20b48051185511884800e4220180181c07290802c02800985000b14940001c0c2c01e2200d280c0005400b5041aa503e90031840d04100700729004031408101d545501d00554078121105004144502600c8014009400f1034402c0d11300c0303c040c04181d001100304003000702c00034000303412902800d54a503ca0020702500b43c002c440b80c05105054460050107844d05241010300d0103000501b01040c1c91080c04ec1d007039040d078094020741c8241511591855103039109001003618002026010205210300c08080c4480280c1c818203c03480c0681e200400308010341a440410000c1c40740c400c1c09400000c40507400750411448a004600403030040405200300e10605040209418143c0300d21544043d08110f503103950350194019051130071150078110070142d41d0f000070a4a59120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 369693066 1250 369691816 369691841
    0x1e070509041208011d01050d26090a2102060d0608030a0f0e0901030c05010f020a05010c08240a0603240b130f0b041a22030618030914060d 61
    0x188000110f602030025070040070305012038000100c1540607a00541018011940113a22039a611024005451702e60280a11214070f015840e041580c454284c0350840041188194080080064910300c24101c1c100014115404500c2c00010b82d03003004050341c03142c0500820b1a84684000501a00034006403000800c00e440300c035103150700804c0080c864168404618440c0100c3d8006001041d01c2c6414681944c1c000c2c20f03e914112a8280c09900d4000d01c0c00c4010520740c20603019022540c0e01c42507003030144008240c41c42251303003841028281d54454050031a04115414020000c2c14820b810040f15601c506102440302441000013040380c2c05103401032207140c100002d0f0012400c540c034616000500c281500c00d41c43c5401c00420b03c0c0148181d1003020f03065071038a5003402c1884400d00440b901030b000700141040f11007820034019108aca403407000b902c242c0c0c500040d1030039800325403084880866241c4e45408016080c030b01c0c44040071340380124150f00000103102900300114944619034502c0e40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 369694316 1250 369693066 369693083
    0x10503100b0123130501032a0e12072606150409021806120304050a0306020c1533060904110c10090c0f1d0403020a020901090f0c02010209031e07050904 67
    0xd800d82080711601315540194101440c0852440d66400070346004030b280500d08185820417000c2d4081101d03101c0030244150381c040d1a07034001101001c800260314041700c1072280d00e0312921013003016181310a61178079030003aa00d420650001d0a0b200f003038122a03045083c01800020031000b2500072607d20700c0f44409210b40b0120203011300016103010310500031020015802140303054100404540020583e00c80141056004280304000403018032118031081c55031065032480746062403542030280b007406200e28042d19016001d81c407130400e8400000f2007220140c4030034074020f02082440010403003140904a0040180000e0015107414031080070f2002c2c8024000ca0f105c0030b2030410100403216a4400000b14a075800200079014220018241101700507100f540c0075550f43c1000e0f0300344480c40f00004c0d4010001c900108400c5125448444154202042044035503511a4107908034400e84650729459031003c0580c4a1800e40e0100c0140a2600c0d05d0035078003103950b030760302180340c00f41c003920121032600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 369695566 1250 369694316 369694327
    0x15050415122c2a0f040e0318011707081807080705030f0106030209040b09010e0724090501051905090d0501061a03010501142b0c0e0108010503100b0123 67
    0x11000029511049045006003010b008004100503415684001e10001c80b84038202218440e5902e0000b60444c400c00b0740284020000700f0400b1383c41364040b10005501c804050b0f00c075034055109040255074540450100190394594407004d542ca0200240740b0b2154803a1644034507020070b014001c507001844da40c0000c10f01b9900b401d01f050b0410003a14003010301685800c10800c0543e4411004a40060701b144050703000d5106d88680c1e901600c0c10621401e1184664000003841d000502416140b40a0110340c0740040700e100350086801030414400d250000c1c500740300112a0121010403803041503014102240340039021008100483c810365015038a99548510030481c0000b101000484048810180761856040a00103850f040c2e4001c40415a6800400c10300400c10340c1108212201841800c110342910016401c400600105110040000c1d102d10291206500503803c03281618001809810280216074901000308641d041450402114581c00040b189080c0b400900c41e95440d10b042d60b440703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 369696816 1250 369695566 369695621
    0x60c070f1d09070e07140406020d0905040c0c0303021b0a0809030f030c0d0309080d02070c031716080d110403050601031e0305070f11040e0a0204061505041512 70
    0x450030003604074840070748420441d00e5000850b101c0d003698502010300d14540c07110361040710441410440c9490a10000030041105900045e006800030304d41e5507085a4240c5400a22041e00c61040300400401c0b01c000c0b001f0300290094014090340800704120411025190101510f4950b000205441c0c076503002070700c500302e0f00742800300c0c2d82c00352540402146044001982b080d91003a626003910b04240c0c4e80c0c1030000c10405d81408035064460301048c15515240541403440c208896440b0860380181d00c000600010344201042c2c541029860614005d1500756031603540440d407180d5592621141e444e214108800c1540024002a6004400501d050741c1945060f0030360302200d40884203540550681000065481400c03034200c150f001c04500e1003034003180340118021400705034807944241014060400e005000034003407103c1c0e0003190280242076440508c01420b05c8422018000540300300808d0218012141d200105d1000c10300d8940d0940c1000c8180e03008847c1d0b401e82c03220301040021881c8540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 369698066 1250 369696816 369696839
    0x4050d020105010e011203140307020c030106050f030d260126071212020f010203130c0506071e110907050a02150108101a0d0503030702070b03010311010509060c070f 73
    0x94445400208080d5040c112405071a1005124003440810340c540c800d4205403250200030141c41e0b04002490310b9041088029403a04c45904c44207000b903103003540010340780c0741101c41c1c0c0e1021030300030700900515104401c013180d024003c0d10f08100154244100c1c2890550820400d6000300340d0f0f0300381d100250044040310005071001e100c00c241c1c15800200203001c011040c17140031100652002d48015030850078601642804d00039841515254808000c11841d00d640c00349621103036100d0102c101245803100c040040a01036035001415a906440b6812600903a440240b00c140f40100000c0141e48240c80000c0d0b000c0c0300480780b5000180010a13a03a8601c0e80400280c1118162184055003641c145a0303401d03070303468210281070a0140c841e00081844e0503000f6000c1400c0101030400103520707601e0b0504a42d20340c82a9500c000610550790000303440449181560f040e00d40c030440071a06c6a0154004483c541c20016515a00110410a00c039582108104640041070303075a0300c283e4034a1410901102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 369699316 1250 369698066 369698083
    0x7080c090109021201050915030106060f11120708090a09020307030209040501151d01170405010204030b0601090b090607170c010b031908070605070507080c0705040f060b0313110d0b0405 82
    0x1282c40c0180090402c601d1200d20040c151882522002c0095564404d001c0c600720407450135941552070b0003004550554000194224140a6110350040c440c41124140e0b49003860080c1d6030009009111340d00004c2c03402d81c0107266035000205040e50700c0383c94401e40c600320b90054400c1c0000c65400a41040c050620740a1a80180f0f80c11401c243e048508031405018114041160300301406400400c98860303004650415000344400b4202506160914149000f58018081664060010800a45190b11030150081a55081513071035090442c0902031010365008a00204c407001941007d4101c1400d0200181505c1c202000001c5a2601944281420007180e41d1340240c00302599100800460b00810858440c80e40c0040009495640c49008036024001e45800400044000034040381c1e4000020745902543d40807242046014040800071044824030b01c03590310221380030b200065003801c218503e2040d207401184407502c210444000152000314070b500480d607403503981c0140424800c0c00c00c006034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 369700566 1250 369699316 369699329
    0x170a091b060e0d0f02042703030b0a08010501050a06050c0304050d03020d03060801020a0c150b04050f040b06090615130801020f0706140402030a0f031205040605040b06101d01030e07080c0901 84
    0x90419225100c00250180021303000e070180c3c0d124001e280702c103800d4549030003191a81074400098500e5070b01d8010081c00b913120015114035512640490b480b00103128160407201e004240441a0b0301c1c006007660960800b21000a82e030105000000303541e1510544030310f0301886076000e0b041c0f0050104c000b5049a40360b41000d08583e01c1489540344054002c0c00840d400c0c0d8018130410780220b42ea070803e001801c0750602c0d5607000f41c148020301992416040e9198000e6105d025030f0714056030303408140080458115071440d8041001c0320040140c00b0124001d00308451158800420b540e12681c02c203007680d00982070340c507040700001884810300405214a81180c0c5c2d40d249110360034101600000c0d522255564042d0402d030890040c00704250059850701c28000b40698180058079107810545c005080480d829904210150000f411034a030890010907071071403584448000c2084500f07001803100020b159281030540d01c0400c56400b28040200c400280b41e940000d200d001003000a11510500c180e0080c1d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 369701816 1250 369700566 369700579
    0x70806030610053a0303140a0c05030c0703111615020703050c0103020a0203130807090e0c090403080702070909200a0602071a070b0f0106081006170a091b060e 70
    0x3e11040c0c0e9107065284100d09140042e08a485400003082c20a003003891143e131200311a10003000030142c254001c400d09107800807142800e55242600c01044e282044d0180001650401c0020205542c4801030b1130094020b00c6e0049210700d107062070516190301d5802d140005000d600381040b2076800050500b1a50a0910240044502e1a51394541c0d40003031403409814142c022580644581c4204107844404071034403071140285a03100c00c00ca4035291140281e000507410080151840c01c0000f4920404000181441c0c1e150750f52030301c003111546005041c3d0300450289442c00200c502c40c5004210507240641c0940900e4420720f044401d0350b0301070003030701f074011900d00408000013a00400c5120881d41c0d842c03509041121000300040042c0309085004104150034420f00651100d102d0125058420907100c0f03012a4650201000c07040009204500018004600d0741c003264a120840c00e812a0040c000843e80003da9070781e10701d2a40450254001c0440c5100e002c0040035802030540500c044141c07120b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 369703066 1250 369701816 369701819
    0xd031d0c010503040b04080f0403080d0b042f090d030503060f0901050625080c100525051b01020a02060403020d030912031e020406030b0f1512040f0506070806030610 73
    0x107442e5000041001d42103160700400581802800401c641c400000d04440f1903071a84c992800c14a40d03003040c00807070300241c80d110300703050241810b01c28004c1039409406007603682401c0c040d1140014401c11910140008140b00c0035000340c40b00307501d0401861003610303015141d280c000300303001d800000489202d01c9844110010040c4c0e45601003100c1070000c076011511b0405800d1005010007403c0400c0040c520140002e03091014100400c41c0e14041c0410f10007401140c03658060501400500000f45015035802c5402c1c04845004400170030000c603401c1891811914441452422a0400210300c000340c1c000e001008105a030602c0004558040f074102000240501d80342c000004010340c3c02541890341d20150700d07070003070300b43c50b00c400a1020321881955541d4a4840017800360040064a6018810081540d6010714005000485150000005c507007420203540c0c00400c024405001035505050800c01c51010070780c1489010710a04550311410761900b007001c1858a0418010305008108882200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 369704316 1250 369703066 369703069
    0x180e010b090f0907030b0a02042102060a0c0204061e030b0906190b060c0d090918021305040c0f0e06100f0e06030603010f0f0e0d0801060906120b030d031d0c 69
    0x20069004620342c8110407040c2e4508820918016642c1c0015051980d110100a150780c0e058004200351406413a052021030200c84607017500000028000390711030020f11000326103e115041d00301e06940004d00c04114035603580b039880e0314505000850000d0281e011014014070540c41607060b00040e841c00100302d180350002e21213070740b4070610304c1101e1016250203c5041c5950761600303607002d9080403001e0710450200c940d00605802e03401e104840141c1d041110140d644200352120b050790340d4000c0c008096540419514400030700c40248111090240d0300c00104403402201014405400415444181400d01ca0200440b0012801e0b502007080b96212031074440f07503404120828400d905403400354981c4c95810001c2e01400703d0030034401c0c1352450010105031140c1d142c4c10507004c149a4a00342c400000742200c3c00c0ba40d201090080c0382c003203100a4010070200703200c1d170017030506161840300c000745542e0480002401c1c54445009400004e445100e003c071301405500140c0065842c0400500031200381c0d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 369705566 1250 369704316 369704329
    0x7050f0d09060512190c02010516020c061b0f2e05130609020120011e050f130303020403080f03060112051902071511190206070c0f0219180e010b 64
    0x2151070089503e51010485d8201d0000d03000341e002c08064001d002003c000d010082c001c0031f040340c40c05110007056540011850000c120403a0b40c0b01c025107035519040348417120942c84041040c0d90080c510a41d5103c03840705805001c6040071351848410b0151146015844404d0742d40b80ba010740801e140ba10050104092081441124090380035001041c020482e000589141a004060000413984a505030041a006520001131601000f020703051840104040904a0380101d44c24581c11006a0125a60408105c05900e07194820714015242c03c0d102e650301145600045201000d0000c04428421150307003000e07624050030501c8004012500d05040e00c1c1d5000040085100000c80e0300090b44410b01c85504030015000700d00120520611103640e405480039880908042d4829900160b0031110900c08901c0f41d018400302e546240114059413240508120307002d100701c2c2d00c00040804801c04400c0e9100c80c0000305030380034444c1c010224800c1c441c0c043d602c1c0f8504081c0181d142c0f811074025569142c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 369706816 1250 369705566 369705577
    0x30705060603070f0963201f120905060705070206071e120306121e06111305030a050307080c07080f0102070c061806030c030b0607050f0d090605 64
    0x1400803580030a620790b4614142c07542601d80c0d4030140280c980c0720b07480b40c4112241c500c0400b080381e40607031141d603003103e40d6401c0c0038000c003400303a0700c0e8a10540c404030303462801d061f003000700300c1c80a03484a410040001700305000c00102508140703424144150700d5900003003116440340e460601444482c43d250764250300c0b08402000002400350110f0b07004295110841030382c803031903030041e002c0c04590400b00c01c0520b4407041c02e20865280309154290303103080c0c0c440c4c05804115071050301d05850000d00f640d5200007503d0113401403401100f4103104c2201180c1c080c018101c07180c0507010a02e40e2003044490046040c40c0503000580640c1c06800103000203500003085802458000c01c0d82600e8080420916060280079440b1143c548141d9120581191043d8020a00b45101d0005d025810f595a0b00c1a00c034004456150180484422030400000f80681c0100d800345106290004000300c41d400014003a0300001c00036241039000302d028800000d010000070b41e007032040c0e080c81c03515a45002002003d62007074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 369708066 1250 369706816 369706829
    0x115030b01170a14010e070902130506070b010315020f0a030902030d0302040b030a09051e010605130c051602013c140d0207060204032901091b0e0f0d0302030705060603070f 76
    0x103400c0000d600744c400303600210304188420161020560359000f00c0b03000e134003e00c41c02c281c0e408029400040700d24122040b111583d6111100000d42d03840c541b545041ccc60f00740b81800300040d8080200080749804000140918607254500044122603030050510303086407124250309041c41040705005110401c1c1c1541d81c05032001401003444545454020f0403d82d09a0994241d40707846030100c403541d901074108ca005e80d901a034114032000081c400060694000d1024903021600421005a07415100d002d00c0c0d007020b0060500c8500c2249001303070380c0100010704c880d055a100780c50750380c5012248903c0070f0441c40031451801c1000d0f2040c00c40d55201a00c02d0011090742c1580c001025420004140c058500443d08440650342c11051589103c441c070515072401c104140b05031002056064541c410300c10440028007080c580e0440040065400482090540380e00840c00d5100d0f601a03036440300900340040c400ea002d1501d8032143c0ca0614500300d4081c0455101e900a0281072003942d4074030300808103d949 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 369709316 1250 369708066 369708083
    0x60b0a11060603210c010203090304080c0a0b070209040204141e0c030402010f08041505010b090316030305090d0602040902181e030c060304061803090609062f07080115030b01170a 79
    0xc04c00c2c1c40c0344502c10040e410b400c0d940003104124074a400031000e001140c0300c00c0c00303540000000790104846408940103048445001340800e40150a12a0540e82d000c1d201800006840441c07464540354210100d0300030b408801511240c03028009000c8055800c440c1201110b41941080c2c2d00280c400325105500c1d0080200d40b40c001801e014142c0086060904000420089540c640d1a490141d0340203528880c0284030b04115018500d10b148603000c2100c2e0150b4405040800540400074076140300942956002d400f88000314020740d103880285070300720341400ca0a0100d0390240c01e10280060b10101e07035001c01800e540f44401610302007140d200c410b80403140241c0c0d9503260318000004101078103c8860110440c98041e0415400c000c0c0d403410b81c0e000342c4410602507a0f400048800507201d541c207000041d181c0d0f945c031900c910b1016080c070b0100001d0003071700e50498848a21030708540f84100410740c962a84201042880801e01e04076025080303010300124a07117090800d140c3c2c1c860707007018002c00580 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 369710566 1250 369709316 369709363
    0x6120603380901090c051e010311070501020c030310120312021323030105090313140307030215030f0a0605010c110f061b010c0f0f03051009060b0a11060603 69
    0xa0000da03078980c00601c00850015424115480350003080891000c840c4c4840013000480d080c500441608900540615200e031a468107030b00440c05171500d1030041c10f44503820301c840360014100f8000f070010000314070b00541c0c803450f245203818030120f026030129070030b02510f1004401084d4040100d100391595000c1c09a82c0d90036911007a42184800c0c0c0c00728541045090300b80824854a00350314248170f0f0110000d1005482c1c4200751a101d20584031444014561300c001081400c5444564126400c40241690520740e580d40206407845160f1000006444000007040b40240b40e01d10803030340113000080c0400c134041c1840e002030030586038104081c028804204102138160354123200301400c404003820350764481074242c0040d181e52099145801740d0b5402e0508000219100d01356641c494503059442d00c448100710700301038008080140110091402440001c1140c2c403540c0918001020320720b050301ea40d20031054004003924a0441d260420350000350a20180d0f0744c1c0011008d040c01002400c140c03242 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 369711816 1250 369710566 369710633
    0x9090a090c050a0e1801061401110f01180c1d060418060f020d0f091109190507050a0e0a06050d0e0a021002010903021b0105040608070513030c06120603 67
    0x90301a9802140d0046070f200d00030510340780c64140c190181303074494019804100054000c50a0314040d0107854444c10b411000142c0e95032050300508580f82c800800c0e1040d2883e620103640c2599078010b50307008403000d43c0d40c11400700102c0b048480010102e81042d421280e2a4007540d503100900542250300c41ea464050705020a03045089030400036611600c00c100a00c01440310360046e41048030f403000c5003854190b9041c011100c07401404006a40301184100203511300c8200106280081c4c042000880810b05074150700d061486554007808690711004c0c3c480401400003031102d90125104d90003001c0300a42000306940110030307103034907100790000440c0c1c1c841c1e0303803640310301d03001c5824800fa51060000162000761074065009050b15400303542511030700c402c4000e95140e042c0c0708491180c00036000b0007080048612841d0029088138840c507040d450f250b40070030100c0e110145078200b618202c04100d07003000703d42e81200c0340c82c4501401c02c0b011f02c0150b01c0c60701e504500d101d4208010030391880450520045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 369713066 1250 369711816 369711833
    0x1a0904050601110a050d120e0d0804050717070e150906120c130209030106230f0f09270f0a08181305060a0902030c03061e03010e030c0c0609090a09 65
    0x40014443c00c48202c01c0c03080c10b100750748449074031560f000300300388290009450120703005254a0042c07400003001c3c25072001c00100c07900400140151424040e44070301044c400018001840c942d0700c000010900305041c05060104920060310038000c1000d850701e043d0640d0bc4056105e41d00042c11a41010521b00c81c1c1d8519041580400203998802d2196440805007256680138101490b41078008101241c0c82d20000c0140300102c0c841032034200c080d40e2038030305507242000840880c000701a000c2080644164007117001500d05440210340c03000382d0795080107607050320007042810003050b030000e01880e51000d414a48610741803101a0001d0800a584500c440c80c4070f1005110010151440c0300101030296190001c0c401620301030702c6044046000144204203009490140e42501045490b640307811041102e020741d850f00060301e00c0641c1c010300f51155801c0c4245405481c261000d15507505a04107401d0419900003c103074400c0700140107841d11620780d9107034603a010700000030008450a40d424202c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 369714316 1250 369713066 369713087
    0x605042a0e060d0f05041209030203100f0b0a1202090919141203040813080105070e130f1503060b03030708250c150e0a080606040221040c0f1a0904050601 68
    0x118280b650942c410790703007544175a218074054003440103001d03003610049403031840902c00650f26910059407400020070b00d50205a0028a190001940012210200f001040a540421400344601c4500c80541c00c052940580c8014440c010b04600111959a9006038150f010090406a0b100da581d8451000801020383c80c441c0d80424544c480c41c2c00e10b455501c0707078441c0c0020490203403c850300141041d4140030f1240a00801d48410749298501c3c0c05104110780c02e002a540015140c45650366071503502c0c811a14010101ca100d01d240b2411400d2904c150344c03030b03030040d103019600c1084003c0c0498499001d455010881c0188503071800c003c0c401501188411510142100384581c1e4002031440020103e844485820b0325042e00075940c500401031b003018984203116481d0030600004001c0d00d030550043c03202c0e1094010084000075603440b00070010341e007240c0c200d4034030500176000c1c010940017440d07480007010044081c1042d81820f0f94a1a21401500e043c240120748442c08180340303a021b101000c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 369715566 1250 369714316 369714337
    0x31a091c0215010b0418020a080a0b040207020901140f06030402101808071203090506030601020c01030506031005100e24010e060903030c011b11060c13050603040302010605042a0e06 80
    0x51280d41c4a0146a503140e1046c8660900012059852144d50320f41e4001c5d519a0f140548403400240e803440c000d880603203068200e030343d4010790810042005a46107c079a03406000c4400344031512016120a0040c18104455114840d620501c02c00c40140e550000003604043c26280541c1c036550f822024641c130704107542085889004840011850250101d092070714070b4060742c0d40510869507001071158500c000d50788140181c0182c0003110055001e5003006822a002078100c0b040d40d1803200318282140c8081c0c07107484031002007190030440c0085c407050f5160402052203103400c1100310740f24030983d041c0c543d01195052041080040f10070b50781b031703100391002d144024041da41d80e9404010541e00078007610b00a58803200c403117800840d040b441400e1140381d414498000304103580f00d0082c80501500300b0707080207101a04442011501d51900b0000d14011846078001080381230a040c10041625440e1380a817041c4400d02c3c0d202a03552443c50903500c1400c8141c1000320080303020703c01080e040e101d003d060300d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 369716816 1250 369715566 369715603
    0x8030403180609050102030910051b03040e090d08150d080a0302030402030601060905030d1407020604030b0108190b040807050f070617010e040b011a0c1501031a091c02 74
    0x145078000d10041c00e009040341d10001c081ea11000c00b6290002c0c540241401030b4400e0251861500b42155440c101059609065040200802c0408140c038150314415096406c08201045441c0380310110355000f0010a0141c0821b0f0800708005080b050014607480124040461091043d102c4844091103184c005442039522440c641015000e54130584017240a031140030000a1b503a0b00c07440c00da800f43c64000300645006070b4804021100e6003120001005068010403800303006907203210050005600ca90a01807041d1300d402a80e601b004041d02130050707a44541c4034079500080341d15410b1607100754059103084d00c5081d581015407400040300da0600c0f00f0301c00c00c100819070b142c118002c40b102280c1601d000000c0e03030700c803454840110829103009041e42d525000610207800b00f0558081e000080c0f10607182003007a103c4400d450103113010361101c03105072040018028055200001260703070310454010110750800e480704580d43c60380c54001ca2100074504c6015100c0510034088000c110311b00c0c1c0c2d41d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 369718066 1250 369716816 369716821
    0x2016020a090b0f01021c051b19051b061905272107030b071701030318120b06060307030204030f050102092e08060a170601080d0c0c0b0d090803 63
    0x7010020480412001d1180038901030f4422a03603c00a8120011040c0c4500480d0801211100707841641080c0d00f00d60020301c81d0030341907001a40410140680108045101c614032501d420110300301502a111102d00755004082d60f08641c9644044440728111040f6040009042c0c80003100d540c054081000042220100b501240c00c69914084d405440105d61072200100c42c5111758102e040c1c2d03030007440352a404c462410000f00f50645400d603400039042c02c152012030301544e000e9800000907001180400c506140c1141040d404208080240160000c02034070103071203440b00000c0360f00041c0f0540c8540b00c00400628030a10070740540c1c00540c0d200c3d03020810b103201442c12034040d40260014900810000140000c2d8200d030040795004610b103030010751140301110100304e882660040c80f45400c40709800c4006048546c0c10928100013500d903026041c15410000c015080400001c0c0300c2c81000104000400814114980e240484501490865440490448010103407195410241421101004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 369719316 1250 369718066 369718079
    0x6091005090702160506090a0b0304080f070f0c0f12060e010617010b040506151902011b0f0e030318040e0a021002060106080912030103080c0114010b1b012016020a 72
    0x144043c8019a00d1000c5501585840900c1b01c640903810700594441d000c48020003258500c4402150418081e1605038a80031004545101a80c8a810b080311000003e04050092203129030b100d402400c40b01401c8203e80e03161000003a091000601d028080c3e50307582501600d049000d60040c4018070100720065000380701c0100700c6009290590031240181e00700320014600345001070703c0075030700c05900008070b00303201c1041d61552626000030200415903507201c1c84181501011611921440c0c1e203540c2e5225006003944004003130500d00709a56000750b100303000110310188403070200c83c0840b0b000c0d200040e12001104105103001004c003000b0f5000054000e1403640641e004c00d256041c0c52a0362190603050b04d500340700b140e441d41e5901000180b008248010f10005101d200100040401c4100100b20f584200503a41e064000aa1260a001100242c07003800b02c03480e10036034102c090044008200000070078114118224030108503c05060000030b42c4940e240c40c4964160310143c0203000050003681b19103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369720566 1250 369719316 369719323
    0x709050a15080c030103030c0f0602070213020307020f010b01053001080102220602060a0c0513060e0f060c06040b07090b03070201050703180507051e0904081b1506091005090702 78
    0x60781e03000042c02c000006848814210102c034100d9601d81d440e030ba04440e403520380f02c601d1018104115420f907020425040544c1d0307134022005280301c038000c006980e41003200e00a0b140070f400307507120401741c0d042c09444403030782c0c0c0c00070705440c03015800002000c8140c581c0d945100c001c03403000c02d40d0b0900e000485d0003c5100541540540b01003242018080816003981c50080d0707039850180b0503200141e1001e40040c6c55110341c0e4102004130b0318141041030401f1140301e5820700d200484c0e0401c000003210604c1060103480e1007401640d5410050303845c2c525041c01327007a08a8490f80001c3c40035095131031940106a4480c030035000b001c003d04503514542d8580c2081d50b00280a00700a50b9048000b90501e06030f8095801042c40c4485d03100d501400400e00940741c1414420982c5a54001214580351102d20181765144e07030207202d200d1803040c0d10b01e03070f51a002181c0340e140700c00980b0a27102c015401221407004a84c040310000f504032000700c0c0c03440c5540c2e0f21011a4284503505ea041136420441c01b4060044007038000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369721816 1250 369720566 369720599
    0xf0c030c0c041515030b04020702030a0501050405010b120705061b030313050607050c0c040c0e0604060503271009050a0204110a090e10050f030703051504050d0819050709050a 77
    0x7100c05000f8950310795080160300c103c0380900000724032002d04920316180240d001c80460b10000e4030160400c5440d4000a04010714040199580c2e5180d40c204402c01000f841000103050702160800c1c8121209900c5540e02e542e10f0107034078061500050310500703115203070f24540380040700c10003200c0d038901d4810030134101075801c4141111a407140340042140c581c0540706544503079680034010010f82500004100103061203208550a12624050341074941d1078040041018080945a036540d074100540881e440765a0300f051042900b08035900d951200c2000b04200d80500c0800c0b0001c00e2040c52410241e0400082c0c107002540245464106040315814001405240400341c40740d92000f5901c4640c040c0d021012512100103850100061029140274814242481006000c036001c80f5281d51b111883c201c0012044040100440200300801c101000901c8000d04e0925000506040620050040c0300d904424110701c9502e50000441003403140c2250702c0100300060a004850396121114141002d08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369723066 1250 369721816 369721819
    0x213081629040b1209010c0e1c08040b040f0906050105030f07050903070608150d050c121e1c03020c0d0c050f0d080a0605010201090209130c09020c0309040606020109170f0c030c0c 79
    0xe003400107400e0317041841010310302d02803a2903040b0312181030790030081d00c0060b135000113401d86c44280c0c0d0740f000300b0118800340020b031840e00314840c2e645082a0048400e0415a840500710a041c504144038036648042684d4011840c401881503d80701c204003946c072805210013107074061107802d200051140e0b104005078000d4000e0152000c442e403001050068181c40100040c2c60390707102c003040400a0a00062801440c078510f8142d07000380b000b01d19044910340b890402050b40783d003c801c030207106045908409450650b00d090440c43d000c000044940c50300c01d0070200e00180404a901842400001d201d00a1014011030544203c508800400361113000282d43c5c0e400c00718a00640420254014800c030300d40307141c004121040d241e480160740b105050281004a038100900400095100000c1c006040c504a81502031913fa1000f5411301c0b00300c03407483d4000021a8103000d0b0802c0462200c00c0000b44100c01c1c10702071035840e2440b140f00d0800d840350b2103112559210008070b8980c3c0500109181011050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369724316 1250 369723066 369723097
    0x8250b060a0b0c0a120e0904050607021204080c0607060b04050f0a0513020a0302040b0612040c0810060b09010f0918141308030a0c02011e0213081629040b 68
    0x2140d0b941d041080c010312000300c80d55400a15030801154610b40310098a400c0c1d4604840c074550400301141483c0001d56003158564809414000030640501c8080e0380c1c82080605c10b407c2624000140344d80f0702940c211503004440003e0b60301d0034801741d0341190a030340102400502c454140309009400360b90742140c00030136052030080801d2038424648100f44225400a0102c0b4540f4215020007005280100e9007a80c0448200300b1980310000d28200c1900c114010302d80302c07810510f40102d0324145406103240022261418a0034400041800e060b07482d20403081ca04121801140d00c8299003104a0780c21080602400c0c901c003402c0c981554101640042c0c9007551100030761a280d003a040d40200140004207044400d00c002410701520fa408107030361000601c0040341d4110700c0b400084145141610721250141c0024413944104420703880900200b000030000d008030543c5010010000c0e8007030080030300b1078034041c14105172105911262981080c001c00391a40d1580e4038001d030b89455203c2c0b04032119010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369725566 1250 369724316 369724319
    0x50d0c2003090a06030b0a0905010b0a030c020d14091813020f0306060105031315020307030203060925030c030f051003120203070b0402060a0507050a050607020106050d0c0308250b060a 81
    0x3140441075502c8201c02401c0f0301007031410500160041c04040c95510b4004002040000341501e042c000c0d9402019200111552841e1080c0001d09594032001200c0965000003102358405034880c0c43c0360a5103420003001a00c500c9100c00142e144008001c0d203010000280c01401641007800740fa021819100300c41e46045c002c8658140750f2603031002c4079000e001c58401d20005500d900c8000c0c140303001d14401c0291100010704551180100e0b00203482030381c0026400b008001c00ca0611200194000d1500c20a10803003980c042c002550060b94103c2071400c040e19000e00c0c85942c0d000383c002d0810700503180005d01480c6084801e00b802c400300342c80143c3e512074003a20074a22180c00442180c01c0d041d00020324526982c0ea036028401d042e442500403904000d8100f105c4d0000c200b09010504206200c0d401604041c00c01382c200238207554443c1c01051050780d45000440001d088191004c0480c3d42c0b00030790383d407107585240070b02d010440701524510728450140064000c200c000803045129030402c9070740c5c04015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369726816 1250 369725566 369725627
    0x8010b0a120c06081b031608060f0d1509050a0803270606101106070e030607140d0b01030b091905010b070323090a0806090601050102161401050d0c 65
    0x1ca04003802030078450109405100700c52003480e4050744580440841d20108030001103880e00340d801100d91817440c2100b40d0080210075403140d0030f00e40014040703500c3c1c238010b1318820016440c911242030003480540f666003908900415500035072640c503042800d4460045141c245202c1c15402207070030400b001902c1d03180d2914052407aa082c903400c0d805000404080d1741d04001d101154070003012030400d05c180a00c0e0141c038070b03200b005000c0c0306580680c0c1e04645e00d40500181807508030007921460510030010040c0290380039031015aa4400101c800215082c50b4031001079008002c80404103402018400070840a04441c0d078130700b1350307200d000802044244e076a81c02081c0c00e4040c910000300025046150091707015000400707001d200b00041d80007450500c40d0340c002000380203554001c120319007000042001030312082c441d0034010002070028109855a6080c03c2e070500c0c0d0a8082c0d41c80c0d40b01c420002941c903034415410b4900105040c5010400103a803100c3c0a840c0c401c0d02c022048640d01d0a10034040740 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369728066 1250 369726816 369726839
    0x2f010509010b0303130311061b0f0d050c0307030806060c0607020d082202060c070504020301080c0411042601060e0a1b0903120e03030706090309150507080f0f070c08010b0a 76
    0x100c03280e541560521b41507503541041015140d11481e1b00050078001040340d0051070480c408035551020040c0300c05000c07085014203090240d4018424441d050000d200581c00200031260078371303494070b0020065030350200007070280d00540c1405080c61041d4410800001e400050256044001e038076010007a1b980c01e890820402600b0302e0014110008205640044c100080504203100070901503d01d900c1d02d410208049030001da01c6000507901185035124141403c0c41015590003019007030502c1d25040c9201e03402c100300649802109489a031108800048080d4414000b61204880a20960801c0102640544074000020110f0702d8505946a40c160141358820202ca87c8514100440640e510080d00d090001c440415014082080203400190543c8542600f107442500e40e240c0f4203041c52100148942c5200c240024003204000000100307413188241e030401d442c00030015503600f40c044aa003100e4025181c009001600c404404200a80107400140700340100b501e400c0e00c200c0c0c0e60703994080d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369729316 1250 369728066 369728077
    0x80c031005010c0201050706050421020615060715150302180601021f090b2401050309030409020d090602180f06090f09061f0503090c01050a020d2f010509010b0303 72
    0x1001080401c100d41d5003c2c02030685118014185141042e40b40d0321101c0554000b203904840341094040400100103254103000c00b6017180d4801400c0c1f9203816000103003800d20302e298152083c40c001c0380c20010030516145503a45030310900c100b40202c0a400c1c6981c10303100c115000492050051041c1414a5041800b50300c0c0b1078103050740140219601c4901420485d103420a0a01c032094551031140702203400d07800503a001c4ca80c2003014004080e04401190150250031080740e04109040090010324100081500c00303582e1341e40c0c0c006a4562103040d000c001025407040040210b40045007231640150b540428a2020f40140c03550360450321b00f20f04200300340c400e5000c030fa54840507114003003c00d07040590030340390f01c10400b9264140c0c0d480c50002039030404000103001e00014600004100d0790407000d1103036004182d02820142d0510b40002006515118103100701c038100f0902951791451130000641004188420344a07d80c4c1c480242e10015010344412031303e41d58150308100c00c0392804d0030000101c90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369730566 1250 369729316 369729331
    0x4231615080906040f0501111b1603081b010f0e010e0606032103040c03020904120f090f150207090c020705030705060910050f0f030112120c0309120204060e0c0a080c03 74
    0x1c0d640c1d07140c0d542c542002d50121821b4640390350f9402c084840e001600014030003c2c2d680307a802402c0d05552130055262503903640000d02c580058000400009482509a41c141480c8070b000301094148410f41c14010028061000700d158204215002e8800041d031040c0c0040b8541026120107076160014956111040c0c104e80c81004030a81034600c0d0100e0b104061031300300d4418090308200b140d8076000a2a41301040d902680c0a41c606074480c1d20450704003400c2ca000040a04024450618200c07810039011070302d1085445614280003c0c06549100307000c11f20281024030010448003245040003540e6600f2409054000e1041c0d030008210761410806603401d0420041212814048065044500340c000c8c4d400e03070036080e0741449100400641d40d0b0140d4042c0c560150602c501d0b0308a4140ba51103084c010b801141031003030403c0e040001c26030064010060741d544885016048a480c80460014249a40b100315000c00c0f80051200030400480140300302d00e02e56541c0310f442d840d1851200700c5c030310082d00c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369731816 1250 369730566 369730573
    0x1503030807021f180203010f021b0c06090d060b0a0f06020f013606181e0b07030b0303040f080106050f011d010e040204150c050d0903020306042316150809 68
    0x1000384420360000300107040410444d5040350000d9021a081d00c0d4a0340c003400046402050180036905042d4244080d0350f54840100a514640c1000c50640d1280c50610703800340ca22a04010180111a007181c80c602c2000b40901d1b508541e1020340814041140c01040c0050007203030704458070f40f8414001c19480e04042d0a980300341407280381d2040d0021303a130492280900460800e0401c046021842074010600030507500c01180145807412668080d00780c0443c10a040c1d1070306d41c10300400e400c8000d56a0080c80c6080006982c42c2180c006032071802150f00130001a051340501080360034064021004503141030b50701e9032004034484010748803000f5607180303896110400d4a0b2602e5035842a05044c07400b00002d00300520f0030380c9410181c0949002e040c400e001040c0510300740320810404201d4a40d111450307142020640b0700b10b5000076214040900301500b4031150520300e0419601c040540380e00e040c40d1608440f052050804040065101482941a02110701c81c0b0032107424040d407041489000101c02070f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369733066 1250 369731816 369731863
    0x905032710050405211903020d0504060806042a050702100207030f06051306060314060105060301150302031b07030c0c051503010608150a0906051c030e060a05090301150303080702 79
    0x40c401440000004800c1d039105c07500101c036107034609104030003005035903080032182e44100381006480c0c24400c003450740030408100020081e0076070050740c3c1ca070007030801c942c0442c1100e4082003241007698000782c828403400b00c40304200856504140101412407090b1441c2410400c5010180e80300d443d10302c4050003d1002900d01d178000b9259600050744080300007400012002070741c4800c01100c6041e0811101d040c0c400301c00c0c5c41c1e17000b400c1100c0c0e4014401158080e1031581001c200070000521071501405060300803001c5030845152074131481c40032800d41c4209848010ba0300f4003c01c00c01e660030007580d1030741040c0b0010645091003101e9540180d85040c000340703143d10f0007004859120004203444c0e401000d00c00521304d555641600c510040c45d041300003040141c100741c02c01c114a030242d40c000020388081c07607417100080d40140e041110704500b1a00c1c5502d4440010040e43c240c480c68220a604d5440c103007800e085a40200c8202054a00079503424540d5924414241d0f40c07078a0040074802d111215011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369734316 1250 369733066 369733069
    0x152309030f0d060e01090e060f0601020c060a0905190e011d07200f0105100602010207020f0910080706020d030c0309051c030212010f09110421060905032710050405 72
    0x621402c030481400042c95581d0381e56030840440282c11021290340c0364012014508000c00c6110303002a81103100602c14284200081c1d40c41c482c0815880c01090b0202e510018580503000e04001088044c2c03401100102610002e2402c0380760740038840310005404008141030205e08405041f041801c0c940103070079101e1034000d440d800e00210704202c0c2104010240500020107001c56030031250768100201d11070038100c14207611030041390460b008681c4140001c2e0f015a0702c03c820030f440f04000755419010768458180491004581d03420201c0140714240c0300181680e40010301132051061541c08200c5191208004c601345d030300a540282665102e4040301420860808034050718418034180146040b561441c40300110100768010a11707164505001c00c051043c034010320403080c04407040d85140a0615404086c0141c00c00c9800300110410064a810403031036610800f8820f070494200c80c2c4801111000511000d00c00d068500801502030308541281400901074040d5280764480b80e0501c1e0a040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369735566 1250 369734316 369734347
    0x80a0f081e07050c010932010201021603020303040201230a11100e0114010e071211040f03051b090601050d0e1903050a08090d1e02010915230903 64
    0xc90803900692600e25044007005040282550b510860240c8800121500090038910f42c59100d59520100048156440111503240161031110a5424500c0c44136500040b8024002c04c400e20136400000c2d4064410b15800001441c840c43c403d0b65109404421040022a042505550803105450602c07003084824001d2603544656684081124500d09110550406480445c000411941d564034080c0101005500c105800b40c601d41c0e082c12000d0610010080150080701c14941d940740e07941d4100d8070b100d01d801003150010003c600f084140aa00ca080041e00e0303922100f03000c2220226208903004504005800b544604016101c85080c1501612500302810042402001c0c0c1e0240aaa031150815904a10010304d030080e52510346801c4401001b4110201c094210503950344088a00d1060700d5101d0180d031207000d142e4031424420303045800141e003d0045041c00030070b6041103202591048000350320000c04648913101041915142810b05034041d80203886003103058008006000d041c032600d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369736816 1250 369735566 369735577
    0x10c0204090317100e090a051e070323061e0105100c060c0e10020303011a0a050d06060f030b06040b0706091b0602010902091e01050907090f0f050109080a0f08 70
    0x81c2820500c0998a11603000e1101c3d00316100e80d450340003140240564244003c4030780d440b4204200400c585005511020382d03074251000142514001c0c1c0707034100d42880b0140301002c01542e104040a43c00d001c0042c0c102c21325103000350350140a114280004e44200c400411594601010400d50030085c0d00b0041485413581c001c4000600341308682c03481d04000f80c0644280501410590b442c4080c641d014410407004c001140d01d01c03811940b0178030042c40305203a10888807105c101d11b101c1043d5120b03800720b400d496602500f1704031f40c1c0040c0380c01c0000507040d400c020342005500c010b42d0104040200c6604020041c0202e00039a0f000304018070030311001031855031080000368001c0d22044451710301344001243d0340701543c1150006035118094002141003003081d10750000507110064540100c0c0100c00c0115201c148078103403146602d0004141007502801e0078902502c00c0c80d40b0081e4054031041d150550b05484e12a203400540f5800d40040d0aa50200e050401603902a003101038401e89525954410f0b04070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369738066 1250 369736816 369736823
    0x312091908130315060e070801210f020409050106030c060504061d0105091003141e06010806040612030206040512040806161b060506040e0609030904090c0506030907090b040b010c020409 82
    0xa002c404a0301024241d001d000e001c1c0e0011405074141b5810000c03224014011405020300c120042c0140c0107848200c04036009410490180040c10341094040d060940c040030790810b00e880b071100c0a206041d00201d040d24010411031000ba6030312101290280318a10800001540700d911124003a003a8001039528080c0524010341411044400605495094002500881d50360000c0c269066259940381c5c3c0d1201920381011a041c11000e4016441d60f0018800e604102466002a80a6072164020006090482d082e180314154a00d40655035440588041d6040c1c8a0105c00503041c0301413104442c03c0e078951502510080e00c82c0d928440c04030340e04044c1d5500340716026a00316045000142080333440d40c0034030404103c90a0041c2403000700c811001c404807035070304040100603180000008944034281d0655000407a00068104002c01e20281d070001a4002c50000620540100014a0f84280c0e42310300002c1020014010820045034032000b4000d0226016105d101c015182a070f001052417400f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369739316 1250 369738066 369738097
    0xa0b030c012f01111222030315080105090a050f0606010905131407050414032d0f01020f03040b070906390303060801110403020a0302090c12090312091908 68
    0x30300740402070a4419041d500b003501c841c041601030002280c0440e0642201036010000b0310601c000402006d0070500001c080c0900d40c64908000c080100303104900d0007480d410008008606101051940715030800d00141ca030780c42110700d81c3c0007214001c507041d800786105850f41c0003504d181c24244400e0403d109682d0801c10780d00c40142c83d07801d80b5031015038410b130b043c0d666050b5103a04010b825100d842c50440c200b0b01036480444c0d03000040a01100d0b80703102581e04460304404d03035030b0031486d00e1820300c000c00a611030f94008508200305e04810000380d4003951154090070815038522004035405030b050b00c0350100290640005410800c8501102180b45260440c013400081820350300c02400d02c074003642100002d54943c020081054281302d00c80b18840f030091464035007851078000444034030340c030b001c0a8443c0c118400404d020503543c0c802c6521522500c04001040e140c240095a00da1b0031914000001002000006601e1540070504050700380b140040244082031603281d15580b6000702200560024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369740566 1250 369739316 369739397
    0x610080603060609131a0708090109031211040f030c0f050616030e01120e150c0412060c110604031101060e040b1f080709020403060614030d0305070201090f0b0a0b030c01 75
    0x8809040d401032160341c2e2504c0c0560780c1041f060080186200502c02c1040b64904842880029800a00002c4a1005000205a007804502914046e10036540403020350401841c0000c204400c81e05888100e407001702134012504d90301d40500065100315440c040c190190322a80c1070019000d003c50071080807061500030046502e6503c0d4a044450341240c15816510403103001078034440800101e42c2c40400c0e00125428903281c0001c3c000c2c150b8604100038049625500040d096602c155054000d080c0300004544407400d050030090104800602079000c29420654081105114546094059507000c140d85041f9076070001c00c10003944c805015030b40e24010000740050035240810900018010701e1800584d19403851034164125183c0360703c40c4515001c80e401c05140d9580100c1d0240035203483c0e00300440e0315070310034000303d00400d81048000d000354072040b0b920060142d04a80d080c0304414406082058091090415a41c1c0048440c0c15000440c0c40c142002d417420b05000408884601c00c00480204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369741816 1250 369740566 369740573
    0x10110a0801030b0c042102040b030d0c080d0207060204171b0109030305090409081c05100303090e0a060b0d240f050f0f1008040c060f02070306111b0303061008060306060913 76
    0xd070343c101a04da00d195495406c80341036152a102d03a08030860100c2c000d100f0a1003e200181075a00101800b0b0007016000c01e04040000c5981c04988500f64840b0301155110b807180d5407604154082c6001c0e1540c1e100b80b8800c0400030700c14445942c100382d814ac403100350b5289903a40440c0c01d0303400a0344d07040d001030700d445d0540001212440503000003002050240e0140c6107000906c0300301d400c000d0941402d01c1c40810104042034019150320f041c0c170b840d504000000d84d102d030740400c0a40b8590b03019042096000030090300c9036040303900c1224492824040086101402c11480321140c43d24054441a00c074441805c201728075200d0f62a9586e1900500f10101d044501c00c0000c040a04124488010410400c104810003540b005008098905402c26039440800e2401c020768400e400d00000340315503954540794804610b50b60a8a030004981e81c21164140c05880c0030301c2e1a9001510703003e0017410094000303e4100c1c0140303141e6100b0b00001e4014201990f80c141080410b140c083c01c1203d49600e202c0080021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369743066 1250 369741816 369741839
    0x40b1809040308180105040c0b07050325020103050a1a0f13020304060609060602030c0a02130905030703030603030216140603070c080408010c020601060f08060f0102070f0810110a0801030b0c04 85
    0x6030b4042d40700d84120f443e00e940b000c62002c10611205a16901d050b04100000c0d0034a8450703026541c0c052101c540700c09042ca082403070351241c54207021060f101240300c2000d445000003a1100c0398804e0340c09104945420f10070000381c640308001200320b0358003801e0907411810011090701154200900440d40326010703146010880c0c0c0b06031003c1d6006c58596005002007d990300680c0700504142c40211700e4610703884183c1d40c8a04100350b0007441a00d900d20380003000c0c0501e4120103003013074012050b01d585070054540500209032a20080b80540a58100c0b050109030001291084909000e5400d240440c041c0801020790310003420740c0b003404050190700010070010406440a410300303100008070b228540001038680f48050340b001c0d04000c15000000041a4005402600600d0075900001c9100c080d00060303042c0400c03908601c0a4030495540000e41701400641058042e0b1610010020100498041d0405100303642465010544007401003000030b80e02d0b0016071b404140550300038241174890041c1100d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369744316 1250 369743066 369743071
    0x70203191514060307050a2105070b0f12060a0501050708210103050703060f021e181003020703030608061003030807090b0706050703051510051810030c020f060c040b1809 75
    0x580b40c480b00401c0708a0a00b00056800341ca400c48902081d207240210028a500c0421510701236020441c01c0320b010040200454030241a80c0310204c1d0b1180103c0740d400240750010201c0b00341d08841030000c6003850401c05003c3c2c080c1c44060795401d240035000e48036900103901880010245400345c1e0703d42c4854006010003a07000e14461406001ca480c55410400141c038100d003900207059104120440400d001901960320300204105440e03158580d08080c0002048441c035004d8020342c0302101907511503815401003003007034840c1d201000f4041e00e5802d2103664900440740c00d00420004030062011a0050804c1540300d91140b0386411600d4540d0304406c41c6400c2024102d078843c0d02e540a00c0b80c12505406050791102550840200034140c440001d544040801c89403070911000243e5030481c540c003940c51110002000d403050b0403030741410320001c00800d440c0503c04014094a070304035040d40741c0411094000c0d01c503c045039041c503007410000350060b8048c902c80e0a80f54402c4061100640328024140e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369745566 1250 369744316 369744341
    0x2910030819021509060f0907050a05010e0f040f060f080a080a08091f05100608061e0a170604020328061805010e060906010b090102060415110d020a020c060702031915 73
    0xb4590800300d006c43d001d00742c040c0010003560002101401692124444541200d40c2440d0a104507424180410101c0e40c041480c950801e01705003d417940e801107600060101c0340d4a0a180762856610b6882d9511400420001880144104450038669118804480c0c00101d403105480b2403900b03c1e881050f507810030001e44200c0e0340d1101c04000200c0a04900400140030505000e020f51504000040d0b52005c84072100c6840c505502c09404940c5613541c1001c003030185003482c3d039280a00c40b03031905c3c1d5844003181c2c00c03480b0b80f1903014000b40c0d5410780e00842071164000500d1200d01758071543c80c0405000c020601c420810014200310340410424000c44103100b100b0b0f40039100d141024001d0700d00741745050b007092007070302e4003004060441d9900140e2994410f0708000100350102d2401d014401420132090036190020700800c800d0315201c5594018984c03840c540c1c00321450344286206001580c01614806545500280090300c11804009846404140b0603040f8040300c821103c0365004035010b50402c0e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369746816 1250 369745566 369745573
    0x4020d020f0d0f03170705030711030c10060510020c09011a0915090f030732180a15030b04060e011b20011401170a2910030819021509 59
    0x1014550840007803411024080b8940c1790504e007200c005001031202602c04810010403103c0b80f011b200051058921a203107030000d9403000640b002502d400b40000340074251003aa900703102450b0441c000148401d9a0340050503102050b80b0b0403c080710390b800303100200404501d0030041011295141020841e003901003140c03040c0c03180446e00600401c0580480600c0c000d41c0f000c882071081d24031040c1c20f280d0300c9001052208020140c3d01410310303100b10898695070012011800c40d40310b040003030302892003188000c07030420040c0e0440c400c0c0004500c00d448050300c3c00c0c030050f000c5004201c0d25082600b00030801000031a00c440201c000d017000c0104034403a00005010502101c0055410080034407000c0d075203030024000001005aa24084401807080c1d10b4000d48038a4603607910b0b00e080c440c2990064010700034403034880d00c0d00e80c4c503103102d1900307241280b01d200e12100041d502d40901800105903604070290a0801030503400d00c803403043c51543c1c0d00302584513400d0000c0d0800301a9551910841504029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369748066 1250 369746816 369746843
    0xc090b0a0c05010203012c0705091908070f060f020a150c05070c0e01060201060602010519090f0510020915180402090109050301110a17041e020d1e030f02031204020d020f0d 76
    0x4015603a1f1200032490b040e02c008005000581d584141519030300402101c07200c40f500e84240c400000c03c01ca43c6e009100c01d0044640000c0d1492100f500202107a0f0700b070300c3e800101041c080d0100d840381c048010003007402d1600400712100c01440c1c3d100846060f61810240d10308142c0d038071550b42c1c0c0c240c2da520600104000e500180701c1d0b2035082c082c035001400c10340028400b5051070310100c1c88030501c014500008542d114060020312482c05107250516400c1419100600c4079510214080e5128004d428041c001c40626140c180e480d14003114070300d1904114507602c1722107410402000e54003880c0341d41d041221210000c2281c0e5004c0c46010850740500041c4d5a41c0c03010150003900040c560b041ca55821121881000003280a000400040c1c81d410040b8081070009440003038010100003030050a650380642682180180350100454000e001c2d84400e200481114001ca80d40d1140301e443c80810135404021500504008601121041c40103000b4108200c0e00f030080384140001101c20f81c0c1c640300e00d003003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369749316 1250 369748066 369748109
    0x90c050c101d07030c050607111203041505031612060504020a02070302031b060307080604020d180209061509060c0118030203040e0609070903030e0a030b1e0a0c090b0a0c0501020301 80
    0x26980d00c074582d5000603200702851500c3e510841d02c1148152402103c00041460400101d102c0741c110702003000344800400d82c0d005070210750760b42250040e400c11500596040d030819000c1c0c0162071141d44522080c070103200d0a00801c69200b00696841c0d4905925100045041d6a90307001800b45440c2c250300600e45036245004240ca40001080b0b0790081c0c4083c0c070810400c0e80c40303a0048a0303101609003040c255607194800494000c2c81000d9544038910b00e006120603202182180440f08540200d801102c01c2cac4034002000020000c2c031603410481c410410400d81306003490780190417603030084000000d8207110082d540c05620503808040300140c100203402d000c900101c14541c0e0b08908149d505107158501281c0290501b106400054207001004102800a640f0a1000c00c00b450780080f450110b400c00102015000d940e0505440c0300c01181d03400038458080c01c0c45541c0010405da81c804001c00d281c46020f00d5981d01410b2050100a03151001c88041002400118000c04d0002071074180c51030100c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369750566 1250 369749316 369749351
    0xf02030d0314180d08040f0f0f05010c080c032a2a010c02060f06220f0b030604122610050a080303090a0204050618010e04110a060801090c050c10 64
    0xb010756032201e01c00111009030003030000b0480d12144d62402c040e80f240d00c4a05110303c0f06200b060009101542c0d00c0c60f49000c102d0220015040c1e5031040000744012054507400340e410280c00c0f0307450007180f40148002002d40f0350f4030603113075000701c140c59914106169160014403240c0c404030712640f1a024a43c2600480702c1c1e080d902002146488008100c81e01a100000f5162140504102032058140c00400d1440d900e01c4205644001512560282a0030071900700b0040c2030220200306410780341c000310000600300854014400d5622070102403003003690150030350b210390380d080342c0c05000303004141e40d03030500c1070110315260103452807100c10170009140c40200114145180c1110805410a10a000350010000340301081d5590454000c5610303a034090108280c4400d91022400c404107100c000100b00c502000c0c854000c600503080160320780900780c1408600c1e681751203513000103a42c01c001082601640c1d803000c6580e03002841c0003403030300301c44031030031441c050800311000c0c0b00c15a01c4149000a0a106 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369751816 1250 369750566 369750571
    0x7021501290721090b2d0309060408090109050d03081b0403050703060c05130306090203101a041e0908030a05010b04060f031a0a080c0a06080912070c0308041707050406140d0f02030d0314 82
    0x352030341c7ca0b40c42c1010300303580c0b0f812000c0d1000f4004170340403610200c0c4c0d85c00f8100e000f002d008058403460310940b090034010881a001c0d2400180303903054410a03034550016604603004c0e40d811100a00c5030300d00c0d5039986e00c0180a0340000408005041c8500c3c0c2103482c141300c05400542c02a03001003000c20343c0f4010981070541c144000c40c001c80c5461014204a5041800c10f05035800c219000103071a00c0611901c0c448090100e00101094a04071100c1d00704000c55018500650319100d0400613a80c841e005041544594000c4002003548540940c0e5035610a4208500300f01c81c000380c0c08054480e10b4082403a40c11070b034015650300d4021288800080c180030440000500c1140380c0300d40b540c10400085519116019441150350328005404000d04c000c044c410380045a1201085030f0f0303039988041f1042080c0160141d0300c014001c59000140a2400d40a070344144c1e03001a08644078a0982c1c420040d1103103e032603040700d009042828070405070354103000c80000e122650b1408213400c064031803464078030b1500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369753066 1250 369751816 369751897
    0x10e0f061201141f03090507080f030406030f09080f0304082701020f1b1309140303060109060309020f120f15070905040e0304030b07021501290721090b 67
    0x521040a29054401310002c00c01034090500169850880c01e2050130003c054201038003910400f40056266074001001b042124807983e010429a10131138900c0b4140d94a8030400b40c5090014041c0c040010b00784401103401c1403107128951b2070b01040280040040c4101d0540004060114003065461f58050200707400310901140034042d03101e00700d140c0b170209150107203109005280c0644104507131001903020080042c0c000456081e0400b207005203c0c3e0320791084074000c0c0000c0300c0740700001d003c50213401249500c42d030040c04810381e152640144101a14032001c40e41c05849040314650440710140043c0d164009115514040740c45d108070f01400d502c206600c01401145003402d040b60030000401560152684a0707c000c9250f121840200d20b080d5071802030881441c0c440c030001070301c0890400e500d0900c0601049482209030026580c05403030040395030140c0030084991071180d0310318040810200c001d17003508007405a903490350792a034029080000281380b8800e4030340408e00700c002c40075400c1201006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369754316 1250 369753066 369753079
    0x120605060f0307150507060e2503050309060708220e011a040312020a0c080606091b0d0b04110d0b040f020301061e021c0804030305070f0905010e0f06120114 69
    0x49020200c1e5803040d842c1300e0322602d0011100070b2a03003180b140e03040302e040c16005242403200384001c0108540724600700c880c1c000c2c04080c0c08910310503103400c43d111a0032a03030450051400d10407100140040c1341d10003842203a603018100683c1c4e49003201101e03c1c0300100c940c401d5410b1000c0c01c000104542c0503068204181e000090400d50f8050070340441260180d0307500001a512645039058240e00d009090000140219080d080104440d40001381c1a803195504881d03200242d150004107006207080c0403808811030008118031820030985800180e038004025000207407196a41ca000c04080c1c02059401300080d17161248000a4038190103a00c28071101204211f00d0765252002c041c14010080141d60501c000030640b20030f90034028000100000755008106106c0c0858040040040c0800c131401c4010130300d41808a00f500340300703154010540e0040c0d1220f00c100ea003400010740b82544140c1000c0d500a542d520701c420262201c0014010501c0c00f002d50030881c6d414070942250410086040c140540c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369755566 1250 369754316 369754339
    0x12190612060213030215030703111305010c230d14030c1204150f0b0310050705030606071110020a0201020f0c061614120d0606090b07082212060506 65
    0x105200002100d8503401880169140f640030764581d514880c951000c1d600481006450003610051401548200d01d07958041081d2503151480706142e00030805680002d9011072001d0166500036158000aa8003480210440e00c070094416001d41c8400c42040a0b81d400c401e03075118100d5000781420044e24001c0003c1805d52600203032000603030041010b10720400290201240c10320486440080101300e4031031082c00313140c1c603803079450002d4040101410301a04c03650410442c41c01d03061140500410781c540d03070a4a075450341800c11500d500705203026208206a00945840340d41c43d4400d881d401003554000c0c0100b04640d00002e4249007003003521800c560000902042c1c00e0b65004100c0380403240541d00c49960000500f001e01003910900c0c240f411030721510000c51401070510010740044100c060301407003050f4850804a23007040c0144039008800209002081c0051080009406004038099091507400c20741844003a00c0000c5500c1056201402010181403041d903019580c1d01c240e055810b10401c1c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369756816 1250 369755566 369755579
    0x70b0301180b010c05030c060403090503030306180901020d0e0c180f13032618010209090f062202070519020f040c1b05150105090601081f0b121906 65
    0x110540210129a15a1005440c40a030301401342425200e41202c210307510b90b43c01c007820a50380c1409450950124440b010001464500081203910400700500000c0d45a0800b420123010ba5501401d0113040d55020b05c1009a0185c82d40b003640f000780d000f000142074050040041c0b01282d4034040b202400454901c00704902000011a29038101c408031202940e414810300b82184d4030142d2000000191801c0015484049410000e2074000c0d0105030700d461095006032034207803c0380704050340b15030400c02c050001030354006030482103540321034007030962042c84003012140801461800300c9030002ca40e000c200d42007407020822a48800e0104400c80b031703c0440858000648000c031650580d407107151128020524248901c0001554032005002035034400400e1a0075511101c0111904030000c8400d03000080e0761410340e840350301441040e10f6070300d403075103034900329071441c2c84004d40b2072644000101d00080d00740d0b840d000401c1010b0710021104e2450402110302041d030007030284010406400d103001130094 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369758066 1250 369756816 369756839
    0xd0c02061b0c070e090105040309092309070909050f060702010510031214030709050117070c1e0506042102061603020c0f0d110706180927050c03070b0301 68
    0x10a035030904181c070b4584402100c1d151500e6504040100e4801c0000e11104140540006004034030a407031780345046072900005d80c12141d20707000029800c2c486100c4107003942004106542c000e21500142e48107140c9030003c41d0300307440c9044011289940000040c10010400b0700175560004d10768070003030000f41480070010780200210700010303003041054820901c05a000301643e07101c01c1c60760341078a9102e1030045000fa1401060703100780381c003041d6484222840c1e90740446c00b4a1061600d61100c480b142003035150800031200c40e100090104406c514031101191040020714407992064001c44900c0c0101c1d5040907681105e40e03196001c1d03600c501d0500c104208030a0000d4040300c241c1c0b40c01602d1f811380c906501c2c0750682c90800d425175801081000c1d6102079111854507812820042210000c1b5598681100e50b241d6041d22003c8c2803003c40c801340074810807034004562807502c200d0101041e0444287c04182000c4a035000c850a50190b10001d88034141440300340e000380b0198110509661500c000b0489 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369759316 1250 369758066 369758101
    0x112203020303031b31091509090503160c150e090c0d180f0b0c0a12090201051209100b030a0507121403030906070e0a0b090f0a1a0d0c0206 61
    0x11004c2146804014002041034510302070302900c103500c0c1c50705141c06118421081d4469801054062800403503080801c1c02215062030b40040440b807114034181307025004040a06040762140410032035007041d81c8884000754656405150760480e0075281c42c4091420801000d02c0d0818880e0384071448080c3e545841007142c0c4580c0d9081042e941d580740600d0740c0001d003000605000d079102c1f8019114180002e090b03d401c0b10328482c1c00b44000b980c0304c2c004021864002c20304068001000000e00d0510682c1030741005070650320606209041000001440700c403403100715003005d0a139010907600400c3c584e40303002d07550300b043d0180c014005100d50b40d01c0341911404a40240b01070440481c0700d84c0d0070041d42c900d080340c80040321020750361a03041c68048141c88060503a00400010001c000c00031291414821400895400d00300ca035180040310b40611110940c11350b09e0355480321600000181680701028018407204031580003aa84000348891742c8220360907100c1140855002030208440041403210b20071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369760566 1250 369759316 369759331
    0xf05011202090405010b1e030106080f0d030f110304060207020306160507060518190314040e04061508100608060a021e03150d0b1603090302031902070911220302030303 74
    0x500983e202c0c1440f5025001d040c9881e074003c0300101503038030580d118a04441071030208900134010540c0e03c0c0e0340705940e81800c6003151403640107142c402e042c4034001c1d4040c01007543c141c0000700d4039a44140e1602d601c1c0e0001c82e800c3c1c4176190005003550441c0740912225510400c994201180701109183c01060740c040c1c0c01d030040901d651180410f030700162216030072100c80c00c180125621080303c039120360081c0310121000c8000c07a2018000304510700180c0c0588040d90000040303e881c075611625050060100c0d8000d112518482500c082200b84c4144060040b502c2030b020085401484c0003000c625180c0010550b001ca548140074282d0b00100c254543c458107002c3ca20540c1d202e882d412912802d02c0c50380c4c000c8030386c82607681c0003d81c100407400da100e80c45801c00d02614991405424019003d03105c0c0090300400681040260751855454503056440c446514412a15101d407681040b074119100540b80540d401400f2030885100d581100c0748d044400c414a0081c00001d10307560100350359020250001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369761816 1250 369760566 369760579
    0x150201150e13030c06090c1e0b0d0b04090b070914010309020f0d1502030405060106110a05060f070c0c090b0a05031501060f0e09070f081302030c0d05010e0717010f05011202 76
    0x29400d042c82240c004d900303507401001c01c02518146180456006403a8825100321a013000c15a5003003130101c03818202110f00c00301400749040d8910701c1400040015406407580203a68a000c00042a8132100380342c8104041d0320307244651070034200e0704441c102c2d0039a00c1e07904143c200000200141c940f00710344e140e00b03201542d0042d03003044180350040580c0d07601e9100c00d00d001d01c0482000180100010014100c44480c0c0701d16909032031000070252281c402c20070180042d07014002250340c080700d030506140d21042c0340ca80050480103640c3d8000e0140300b00c0d4440b003425a183d19440080789800c040c040b00805044000342417902002d2520341800805128000c00d00a0340346c0f55480303003030242c1d0b1005011312004200a055181c085000b9012003c24203000c4002662200042e044007100c0e02c248684640045c010704203444110200404100080c008a43c03035501d4418045043c48100902c1c4043c0540210080351540c000244900b10303149000c4104105007000010010b800500c09052065030301503400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369763066 1250 369761816 369761851
    0x30501080c06040b0a1b0602091f0e0f0406180e120702010801090b0d02060406050d0609060f03080c0a12021b150f1803060106020d030b0d110d06090c150201150e 71
    0x46eaa140d441000c254031410b40012810100021940107140025003203407103280b020701e270130100d19650040f044808041440c40010b540076240480c49413000640050012504070f45032002410ba20329503a801ea030b141c50f205c04215400910900103c44a0205590000d0800400b500028420b0b9018030880810942c0c440f800c8101c0d480c3c2201e1a0000c0350060580740d03a885c0d4460f030040ca181d004c8018803003260b242c66000300b1040c0103800381c441281c2003034050007441421901c03868010340c4a0484070180348544caa681c00000d800700c0c000d40340484950042c3c60000454818108800e6890001c0c600c10344051040c0740d00c88108105030340005146031466612640440b464401400c0d1043c055039051060354000600e8550000f20380e250040d05540c1442804180ca0501c0058010003c2c0242a800c0760710461141b41440300d03403040d0f00303409034001059021454030b500c1c102410b91741202600e80740010b00a80032640900a0183c40c41c0c00d005080d0500340703020b010342d26051000d0888000c05c1005c840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369764316 1250 369763066 369763087
    0x61e0e010e1e070e03070b030a0b0306190e070f0e01050102060f04120e120f1e0a08071e06020a0801151d090910051501021204060203090f06040e0a0b01030501080c06040b 75
    0x441302620b101c041c0c102d559003521100c1c00122038104884048446040104818160901065150180c1240d8900c4035000c840c200c00700c0064507059226491034803030384000081070305081c0d070220010041d40c202c410350765051000080c10300e41c000f030130403c10a0b444030620000445801110450110521340381d07200e0034422000034005190000494001d00c101103000006200c0032842e20604060400784180c0400314a5541d519024000070103001900305014202c082900d4070000c00781d081e01090040102d115030b42e40c4808980000304a140000d04460050201c58141d0080303915003041403d0281c81c81080c4105280c0707924690034140e0240c20703c90041805854200820204440c05010610651074640e41c0c00c0d481c4001500694014441d00d50220b460704204000c0b1019512907501070351a01c6404010300840d692141d0b070268004000304000200010341c0e80e02140141220a0045031038100d90000606503a8182c00c046126001b481050405540b2181102c01316081e400105460340040305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369765566 1250 369764316 369764327
    0x904021b0307030215070e090a0209010c02120102070308010b070503031315060623030f011413050403030f05180706030902030f011b020706050a09090b0301061e0e010e1e07 76
    0x100c100300e9440089025810160007290440c000040108510004d54528200312040d241050b00d490308549881c0205a8015454004221901c010b04205014603031590120395104108090362846035404a00503040540c171092140c010010081040c1c02d1a85c1c40d1100b0307807a403001070030064110140005110800601204070084a001500c08202c1c0b00e40d28203024254180d0200302c070411007a20800d524a00040d1400c0ea0300541541d21944c0d5160708111032801c1d9444a02111039000c2c03c0c2c03115481d608401c50040034840c600c01ea40108446c400c4842c036000740c550103401012101244058441d1200000500314201c0305546004a250052400483c1c10292804105140c65007404640d55a044400c0c0a44140384040d503704c504040ea10402140c884c0a44002100082c440d0141000300107a5504940b2234400014000103000d0b580302002000c00718252900700050480102c00c000111000c0082401000c0769452402c05140c80100007046a00f92442042e408c9400c8010801a61042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369766816 1250 369765566 369765607
    0x40203100b220b091f0504170f0a061d0f100207060b0a0906050306070305010302090705091201060e010512061b2203050309040e0f06040209070e03060a230408090402 73
    0x200704106150f01d4050342089684070400d8580070b20300001280c0012070403102050300c05002c03a61800e0402c0d00300f0303c407410010401840031455108040b0b404c4600f0754148050500c945c801c1e0b40000c0c0c08100071203c01030901c0a1446021a50010603003420881e4020441d6981180c01070f0300103965810600d4010000c0500c800e03c2c50300045008008900840140d00000648100b10202c4034160b442c800120183c07007090000a402a0004003c40c210078000d1001d450300d61002411203013000340881a41d4212107640d40a20340741207144004001e0382c100050110945807206014042510705a000100d12400c010300114880350001703510b10300d086160441d20740000d05035581800c0641d0f44d00b80160b42c0c1c0c00c0850710510852402c8004d110700c26002460051403500040a804a95035540802c40b18100c001c1907802402042080b203069170b0340030321070680700712000000080c18070520a104407441500ba08680790340c2d605038091101007031038103003035685101085602595405d0b1440d00c011020440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369768066 1250 369766816 369766867
    0x813030c050102031326100603031b080f0a030b03060406150503121204140604110915010e0108071b0f150204050105030115020102090d0f05160b07020f0f0a06021b040203100b 77
    0x31070010000745d03001f40d0411021203000780d0310066200640c081c403190307800c21620001e103400020412000303035054090141c4190740b660308001624016040229013400c500f21812124255549110103003800c01d00300c0d00010f041d0a07401001c0768560b8072403405641c4034030100c0801c10010040003d08012600b0380c0c14440d16600015120941405e207400c0061000780d0540d68812030b088000903a00c0c2c030201c19110302c0414141c0d01d494841d1401c42c019901900054114410480c0c085074014002c14081020a17034207115180c0142c590500f82800186c0c0d48054515680c00c5004210401c01c5030380c1301080d070341956414000f246c86038841d0f10041e802445200340d01504400d1081c148018400e045002c0c45043d802902650244e41c442c8416083d8401030b40103030991030a040c441000503091200444044210181c40791408403401c17000600103032007590000d001a4010030b50310117540f191900030384a03c54240c80039070540c28101d18010401c0c12070301520b0460031010078101000740c041401c4440f000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369769316 1250 369768066 369768073
    0x1e020705030c070803090f0105030a1b120b04020408060c131a0d0c080610030e01020c07080325030206040b043f0e0a0e0606070813030c050102031326 66
    0x82518006449800c5850000114010a00e00040044000c011030f0500301c4002c08003040542d51034015240307030b0130242420088580c6d501590b00d500d07001c15000360b250541c40d102c80182038002c554250a80b0844810240168018001005880d1001400c0c80d0425030002c0156154914a401a03025100c15401024689202d80b14010010826402402184143c510a0081d000f000501f5140f205056420340c0d0420302498000c40c58a00c41e612180c14040310000240c90500300c00031551030300c5480d400c110804c0e000002c120200c941c0d220030210b00d2a801d07061f29402c408464801a444000c0140090061100c502c0020104003e0f8518814000580b650381241c0d007030344d82020141004400281070741c45110707259049985000f00761306811a01d006004584c001d042200342e40260340050302403600400140415400078024502910b0915072000c03400740040e06d1414010041d400690203241503410810145000500d00b0511703205850510703041c94050454810003051159403280058403902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369770566 1250 369769316 369769327
    0x12080d050709050f010503161103040506030103051005060d0b0114011709060108060702070b0304080901090308040e15041406190810060f0b03011212021203040b060103050f1003061e02 81
    0x40c0c000002e201901c0054030b11007011a0750341c005540c14803054400b1110103500804003a041c520645aa28681c545402503e007030a43c3c030400f041894000707800490302504100000c040e1130450b80f00d101e520050848100550101d80d0710b800204503c10700901c1000850301034841c110303900482c01042c082c00807100d18260761030107032021034035400213002d484001e01071100031460f042d20006892069400d2100a03e24541300c07650b600520350b00152081d814004020740004c082041c0304080c0005004207420108585841d002c0d9070355544c58295224442c510340003c0c0143c40107005a134684c0008284e450190140e44480c5403c11140581d002441501c5109484404441c050304680f08950043d0310001040351035194809683c0000d005480a100707640000b40301250b90008841c040111500585480300380c20380d0b40303100c19401120180c8401d03840704103103c00d40d689440307000c0d0302c005040740155090810302a522821134a6210240155807280e42c95542000c17015002c400760790b2254000c55481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369771816 1250 369770566 369770581
    0x5090103050d0e0f031914070602061909030503010b03100506220f1505070c080d05180a181109030a030f1b121103072406170712080d05 60
    0x807440201c4100005044005044060504c04003000304103c000f0050b104491039a55451510610a44d0540c3c0ca9071080314000c0c0f120704240b00c1c41d005024140d001d459180362500c0384201000c040350708481c0040c9454490000f00358000181c0c0e05494842a5031030703898583c1001d03156882c1c103640245a00c07000014524030100d04880182e8581b0b4049030852062944e19000003080f640c1503c01c2e002c000d810620011039080c07188000308611849100000c0c00030380c80300c40035480c0407040d007001c0000ca800001c120810300601107140d40c3c17502040300c034855030f54141140340c20011001d0401c440c1c40707500c5100e607990381032000d010b0721880c8002404031170044405007002448004451a0750020821510360142c80d548004c107844402a0000c807c00c4140701d101c8d1044a11611079100b1309400e0005102d0100010031015074110418421f901c0e12886216111310b181c2201c20940c0000541180503030042808500400c2d0743c012900154480d401100701390401c80840d21a400700d40018500c1d040030000340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369773066 1250 369771816 369771823
    0x106030506120609060109021317060613050712201809070c08270d1203060801091e0503070b0c0a0206070e011d0604150306300303090303060509010305 67
    0x203854119440841840b2000c46281c03111800d03030309900a0b07005040144010101f540082030402d9500f43c841c0c3c1e03620341d00d101c10507100342c010103461302940041c814010a45400b41050100004540d000c1001e4242108044d161201c0c0141080e415503d0b82002802414149514050f190004400381d5595100c034650881100558211a125002600c08110110302c210134600885500049251514498580c0f140c241613003110035140c0f01d1400e0315514141d44490b401202c00e24801e030b0303c038000c41e02a060040d06403101d0b50410350b05607162031080d03070204030346a02c0c1c007d1170789810079581c260001d50f0500d40d0840c440d5400c09098070014209104060002000a2005486550a96046482d803107000c803180314030304130128005800300d074060404200701464400800401080c0500d816960207040105480d00d4000c000800e42d01c000403c090101d0000d260302c8040c540c10103e851b60000041c0c40d0800022400c0a401c050751003802c0780c20103005ea0b00202c043c141c0206101c4580d07075a0320b4545c2d036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369774316 1250 369773066 369773071
    0xc170a0e07240203030c0315060d0608150601020c03120304080f03010609030303060f0e1f0e070504080705100203190516240e060601030209030102120405010510080f0318010c0b01060305 82
    0x1a200303500726a040d501d61000c01038134010211030305d074207245450701c2c070b07101c0038080301b00e0323080c0c1d611601c200a8609010480d114401c005c160003009407142600503c4905a403640041265056401c00b003004d1140c2d913004503201580c60003115070703507840c1d880e641401440390081c196251551240040081001c03900203441c00c08591181c2c1e800d00149132a820311140c0d10300588030300e00114a012000c54884012240c00540e41d00e0001900c0e540c040e50350483e40c1030884255142c00200d00c0006003070107440030501014018101c107440a540e00b0180d83c8000b0354038455100f644241103144405200d0f454414000c5032064040c440c0860b04040850030891020080c8074004001e0607811206030000798241d00403c0000c00c4000040d081daa5107910040d130280d4021000544d15550801000d10b036111000300d41800f45006400025151500c1c1480c0403c031045500710340e416611000800640c41000000c845004411012000034060b13220016038200b00027110040034961500e002045559142d0f11051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369775566 1250 369774316 369774359
    0x106120b1804050607090f0306020726180a050907050a1107081b10090b0319060308090117091902060f0c0f1c081b0f0301090204060e040c170a0e07 65
    0x8135151942101502d105000e845900f4241d0b0141c0002c0021030700550140440c2c2c1c0c05820000d03521103030794a8800e040c00741e125010780b5003e000f09541408201909900401e5081a42c0182d012400c10001034072500000305110b080003c001691a542486104040c2c0b448184800326400d864a4542660310385234001c1607030030600d030311900703c0e000761408901d240e080038010b446607039006040c140894100d90000705a00c840000ba01d00d554000c0740176101d074400450113078100c5e80d26425924001880290303081c9000710781303200b0030301072090326540171914400160480b012110752005604c0820054081c6400143c40250045071500c2c2954000c0396180f00180c102050b501c800650149034030440307a00d49601c2c4001694a80023a07074070b13404081d240c40442c804403007807400c00d000c1134400300d80c5a00c02d8221907403072a00880e04024064016409a10400c001c417418060484070100091034081c05444809000403441c011581c81d0745c01d40c1c403218070500b030380d000c0e518107a4583c00b0b42c4500d08454003414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369776816 1250 369775566 369775573
    0xf0b0607050c03010c0801030f0b31050d091802031b0a0809010c0f120e12041502210703030203130503030a0b09100807061d09160806040b090106120b180405 69
    0x4001445461b120b8140c0c1d40c800b4508a081c074607901e07185101c11004001c007848909030a032084414850b10031060300380b018258aa801034066180450520080c035503110244003039441c0c1030081d031030001c0d00708605950b41400140c0b03e0303940101c43d61003000c00515800306014001480c065007a403141d410761280301010024440c4034141705d4121451050001014006100352941d00000c26064211010300c02c0c0e07107030440e601c0e5121741c0c501c0d10081e4060341c0404001c00315003c81203a046d8040c0070303084580121180580f41c0355000e004510103841940d00090030141e00000040f14007042a074184406500401200e849240c544040c10041048004141c4600c3d207801c00240740c0c610b45007101090394404005852500c0c87c7c0f0505641046c046085003060711030041051210740c9030521124454402c03200343c00000c040400000d070446001a0461340520304004410185071510b81d039050440d8818031b00b2582d11400d0640d500000c0c03540c03e690b0b40d84030000c0529001182e180748410341c000c50240303065 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369778066 1250 369776816 369776831
    0x20717090924011101090c06031d01051003032109060b03010b0f06040501030506031c0201060504050a090f02240408030315010c11090414030d090c09020f0304060f0b0607050c0301 79
    0x2c0250044060a0710080d411990b1541c15654403d400ca4546422110004103d00c101d9075250001c10006410044c002544c51030894104405951640001c1c240b040003000141804021004950501e00005d02401442c0740001c0d01e10000c0307212074002c001801000c20000c110f601d450030280c14000c030342c0c1d4825820700c0e0389409039141c00031426100d01c900070700c00c030724142c5803030b0040d00549001000140e141c026a008100c00280c002c080340f42550450340001802d81c1000204003c991004c0c203003032911441c19541000049015489000107601158080d41c114000344001400c90f4030b010f9400142d880c0031400160104000000e18018003501c06e000300100029001103590400324580500030300d1800744407418a082860046401a0040d04680014003004440d6172841d403100c1d40c1c03004107681d5003000c1070600c034003020200081d240e0b82d48158030301403d031203410741a40000790000c3d00e030079590113002c503034580c00e90b0001496100140a6580f11401d60800640364040001441e0183d401c0c0b061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369779316 1250 369778066 369778081
    0xa030c0908060a090b151c02270f0c09060703030f0608033606070b0a0216050a03020606030d0e090606070507030b07080c070f12270603060b0c0c130207170909 70
    0x4040843c07660240c410b0800300d120742032258047e500902d080c0d170040352840168038003680c84010034900c2e4180c0042840c80c0d08246150030002c040051070300c04000414800c1035201d980f940b003101d00c81d640516000c155449000e000400070400c81e48866424070002030003200b00c580c00044480000411804002510707054019040d182e00560100c3d503100b00100405400200032100981d0040303503e000c010b040c03070205403489400f4450300301d0072384081d070141601404255041060603840300f005c0d0301401c1e21548008001c2c1c4101d0488041a11842d4840002a09500ea40c0199401250010300b00c17440b041d03032810407801c908800e0340e41c080000d800100050380340c03400300d04803010713203600680c05080302c40f041d180c83c844006859110410170504040c071440d0355a10b4803d8070b02d5945001c000340740d42840c0140280880d42c0307660100038a65802e100c4415852000700b0500030410301955a00200d003c0680d641c00244101030009010001d200041020305510802400300e14100341d681c4d002ca5100c048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369780566 1250 369779316 369779341
    0xc0b0318010b0a0f05090c09041e0c030c021b011107030303020c06090a0203030d180605010e1e06100f02070b0a080106120209281706160c03050a030c0908060a090b 72
    0x740a005885038030100035604110244540c00b03001f0500d282d05001110000606442e0702130240100d0341c00b19840b00c1e00d000818400d00703102d0741144c141040030401c81c0398086d4a034141c1001072802c2c81c1e40d0b1124251140d0180e80d00204801c20f800135502441d4480c03601400a400c4403100703240c50b105510008075521000540c445078030b03400800440c20140c0101100020b03100b5811510a88184102c2c402c0001d00d413030107000c0c06444440390003401303442c0518030005051912060003082c1040801408882e84a03400300c0c07244074013345041c00e4140300c01442a8075000b007a500010314908001008644194056001c505031003942e03882404a141181b40601640503e90909511100d0203070303a01ca84d0040c540c04030301d02c06007024820034001e039152000c00002d810100742c2c0441d80c001386e04001c010407860114605038200c07402c0c064002c8402e520700401ca80100004941410742c1e90200030201070050401c0d10043c10f4040440e545803501c5d48520f40a04280c4204032280315007003004c65103524048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369781816 1250 369780566 369780569
    0x601080a0b16111906050c040308090f03030f0a0309021302040803160c050310060e09190f061413140d0e061b03030705070506010603090305070204090c0b0318010b0a 73
    0x1449070362202e5012038204400380c0501800d11100420000b02070506000926072954041c0c10391041c507945003894002d0f12002484071007001c00403c005d00c0040c10110654880740415682620b03e020380d20082455880b648030b08203034102c0701144c5d4007003c1d68550402c480952081c1d0364070000081c043c94a500f43d0281303001c2c2e40d626400602c03010005c5080a0101c030740c5c0502894001c2c04282d52000420b0030404114003010408e500c42d8801d00c03001c2ea07243c540c00e1300a030b81ea0380100103047c0380038100b4041e8064180e0042c0031f0000340050f4014803085411850700e40400742285031007410701000102c8401401b202c22503000f141c40100d81c01d2440e000c03c481c003070040c55031500c1c078218000a040050a60100780c80070103201c011103520b1070382201000650300c00d06190300c0d0703e5a6520b081c28240c2c0b0303180059200c0001c0504000c4880000b0798004169181541e0540d0080f9000ca403e203000880c01c0c1e095007103083d20b00004420048180d44040b80001e5050700311008200d00d0f103400c0203010380746045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369783066 1250 369781816 369781823
    0x11030a0e0d080601030b0307151d03070302010206220204020a05040305010b041401060e0607080c010606180b12090c2e0305040f0305031008060a060905060f011e05160b0106020601080a 81
    0x2c150000e00e165009800c14040c2c0c210003000d0340e00003900c40d04140f070258014141e440019130104100d035546000c02c04d000289902c22001415100d01d5580000e6503158010200b110b08880c0b1118000b031284161700508082c1d90040096454026182c00109240c01c58842510a0360030f095103000d07907040c0f6204200850724401031b030f05c41c00c0c1e0a0030000d03a0544449180150045020412540464295005400c500007058000306900f8038042000700100a8400040c400080441d02000391021320f90844115400c4102645020307500c1080f000d04000340035500303603041f08030450a413012151111041110781380e8000c4c42d40c0b00700c40c0c1c90022812524200e40091016074840213510220b0b0140000e942d00401503014200c40703a840d1402141441c406583c1d10055a407100010b1294079400c2c010b0513071018060fa500b82e0501144800202101f14125650041380e011580c10b50040d88120212051510480300f40c0b0700a00151a20012400302440b0b2000140a0b060011400e55030104000310050f40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369784172 1106 369783066 369783077
    0x120106030c1401110d0c03050c0f0c01110106031e020a120f030807030b0d17040b040b0304021509150d060f081506010302091503130611030a0e0d 64
    0x2c0c0300e103007414058224540301409400081c080b0b5694018a0020140038182c00c0031341c3c4910851410b052280505590741c0f06070140011105c0c4074040a1b40c80c00181280040038908039482804002c207a80700d010409900021041d003d1940345000800b000c002c107a503200202c0000c002004202c0345910010310a60a154000041540c011900d09080c888181c080c0d00082002205103801020010082c900c5081d601c100d005480107443c010198554868485290740102d0304112030403445405002c5855909156120907143c95034005080c40b03035010140452280941c00c120018065265248000203000d203541581c10010150300000c2d0455084020020307800340401032545051500410000080d0b4503000103050b928503040f0b6085880743c681101c0e2540c0318424003000b0f440507090500010031400c00c00010350068105100402c08074400101d056115105400900d01248 = true := by decide +kernel

theorem cover : BRFrame.Cov 369604316 369784172 := by
  have h0 := BRFrame.cov_init 369604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369604316 ≤ n) (h2 : n < 369784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
