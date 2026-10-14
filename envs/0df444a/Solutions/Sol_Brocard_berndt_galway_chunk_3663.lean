-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3663
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:22.03329+00:00
-- url     : https://prove2.me/submissions/0463f89a-e479-455c-89ff-50a4c0d8c336

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658633093 ≤ n < 658812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658634343 1250 658633093 658633103
    0x10080a0c03030e0d12030b0604090501061106010f080a03050f22090e0a0b0402101809061802070f02011b1e06050601050a0206010302040908040b0c010510080a05030d020f0705030307030504 83
    0x40035400f071a14007041c044201d190820514062505401800c4005000c0300c0d083d48c0e403140c014440401d52203080e100d9503028049980b5082c40446007180350a190030b105911086a101c0340110600100308080360710900590b043c00c0031038031040c03120000c8207140a00040903618881d90030040d00ca10130f40840d0541103e0410004002c106c01a04074035445292000c0040c204400840102d00142032112090b08900240d14010494043c83c001c61600c1c1d000c2d5604c80ba1040fa01d07070005012603c050000380c2141d1003074000440c40e2148969032008800e42d40400a414845074201100c8100502e400540459034800c2107e801c0c0030040d0215030381041201400e0702c0b0a89050002000d40d40580d04a41d8005840d40050005a00c1e503802c02001d00405241144d0783c5d0b00510001851000790006070444100c030800110b501e103451102048040380c07582c40070301c195124814000101d0004000c5034141542000b01503075881c2c0c4046c86807040d100e401d0005220b4840002000741556141c2d204500880c456 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658635593 1250 658634343 658634357
    0x150403031b0c0c0609030b040f020a030203060a090b010609060e0112021902030d06060201020324060912010b030f061003080d0e07081b090c0a080a0e0723031203070810080a0c0303 79
    0x14003011261915240030003404071f01160040303008984642c0e00c40e8003943c0700610b00e003481901c0b54042424554155040103203151109440b108000403c00c46a02602c0c1074582582050301d403c000405100c440c0803002c1c1800074120b0b0198000c44280c040701c00b0788081120710b808030304003c14020350704c1c5d012222160100c0d10f000c4000c50b845c3e00c180200c80c01840b618040d402d8006010300f44560b081040c0170380c20740c088000c02c030000e92512143c1c2c00700d2400400303800020b0030100c030070149400c01482d42200e900c00c0c0c004901b00304211194018090a0301d400070b640740c0d00c500a0307220343c1c8001c04904104c910365120304200090160300000c2c0403225100f1041d10642d074448500b05010f0195020340e0030074604c0c0c0040c018031901512485017a94002c400c0780c4c1c042203101850300920308005054100c02071020021041105041034000c03020740003001035000341945100c1d00b055142c00e0102030115820010b1110201c0c519001d02030030f4801030003c0c40166000456a850468414041271008801140c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658636843 1250 658635593 658635599
    0x7020d02060a0608070324180b0f0f0c07020d050a24060f03020402070206090409080903010e1504030e0307180c080c07030e060d0608100b150309150403031b0c0c 71
    0x102d400368034122008a03009000d40c07400c40d6036003101c688038051141079181ca80d41315043ea0b414140549140303800041c2007414800c81c541400d200c055401040d400703041e1a200140003000030894400d50307004081c407000513201c10035480001c0c00c0385007040000d8038501c42d100c100f074288044010385601409488607075038030318402e0b09048000d840031031160500041d03115000b0009420302d600204450386c4018403d9182501810024044581012003918a824007207103850341030500744641000141c0d5034000300391401412034668a5001c0080008007000700035000b1100c2d81d1001c00804000e070000150405082c2452800c6400030040c40ba00440001e0b444400b00304030700e24403c01c0301c450a4044d0b56644103503045409020003075100c1142a4040f40e962003000808800034005841040000400440c1160040c41006280b0091200505440508105200303403140001204600c3d90796494103008556101c0c241a001405004100080ca1340301c0e030500c403000f0f40d01101785c5261500c24200c1301c42d13040d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658638093 1250 658636843 658636861
    0x30a020618013002070819120c030216120512070522050d030f02190b06091b030708090a02040615080106051306110a170304031103090f131407020d0206 67
    0x11483d52685071400d20243c08596418190010441240220309003440d0810141c181240b20a04010001c0040c3c00300300b030761000c0c09039409044c29858580c6002c0d410040031340d80050b0440342c80003001f4050804072900411f414044c00075110f00707400f100c86c00001450120b001a003258401d0745608a064078420b030400c42002030141410a40380302415104403005141c0d0705441d101d0300364032414158451150b1092604003c0010456413601c100d03030180003800c1c8001844040d90010303007510101050350710140c6080a000e0103480d44055030345080e6850762141c0e003501d420b1908030f07200690401c2c1048004607070817144054040c5460010ba58010103a81da81000711040d0042c100c2c00c3d500c3c600010070800200748250300c0d860b00101c41c0010b07510810305650360b13448039510521222440100200410081c035400ca40f00300607080307541010b0751400b61a200020309000d42e40101c7c0b4441c1040741016016100564080aa01d01580c0110a441e0910b8000a50398521600038207005101300d90000d1100c1e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658639343 1250 658638093 658638137
    0x3060f0522061a070c05100e09042607030305060402070f02090403050715090201111f1508030a210e0d080703090f0c05121b10020a0c1e051914030a02061801 69
    0x11030988d03481c14883c0e0800204850050003400036907810030310030241d10082c8002e0036035010001c0404c3c2c07a20f9844010b850041d0646400500c100d100c4c62040c0021000300e820b0302c20f031150b1a5411110b0031100da44500d001d0b5240d01072100041d0000f80140f200c03007107880413544402400e40c000d81304e151000141258035036441d076400b8001c004034011155030400c20340f001e4004900301c0f0a841403c1003c182c503920390a223560081f40103803002900400812440744821180d00e9503004581c0c47c10301c01040fa0001c41582d0300c1240c00c0c00800c21829400141c0f046101c0d038041007400342e200d0f506140c02410360400c00d141c03c90340c2c01018898034100180103088680000d1205040c8020b04203100c3d0b50310644200b041c0b00a20072621821360045c0510f902c0000c0300154024080d045034008414418a032500300340301d458035a0001350098040071000780c101040c489c822011140c40c100051a20318064010a040401c0c0c043c00940109001c103d98000800310146000d4518007070307a981c0e030350302140846030741a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 658640593 1250 658639343 658639369
    0x280504052802010e04020f0f07061a03070f1806031505040b0a061a0703140c07030b101404150504060608010e16050a08070c0b130303060f0522061a070c05 68
    0x21a41c015140c0d11181010b4015041f182c2d921603426043c0f0980c0420a039081e4000300741210100d640381d081c000d00043e031240d020205003040d40181a064140a507000e8541440e00501a41c90030580421422120580000c2c1c06154000c2185040c80c44080c07880c0d0140c003095a049403458000d1000070a25501c074030424040700c1c4140030f080c03100c00c40c520307000415500402041d020004000b0003800c8243c002801404003031410001020807501c4c1d4201041d05840182185582c00c41d0303e442002607002c000d15428000e4403c460006401c52059806140c07203030f8a41c00700303400604001c0000350464021a105040b20011880450f007903032041100815040d25080e0031004c10024002c00301d86030300c0342100315800900d50a020103400c0d01925184a0320b0b4048a0085c141c8800f608514101030b03040c0030f002c004004440c0044502030074a0001041525840c280c1d0f8200c22819124420000e42d40d04007200401c2203031a40b100b90001e22000c1c10095010603025100641c0e48000010b460424844007010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 658641843 1250 658640593 658640597
    0x10f0b03061e04021912050c01080709030b100503060106030c02062a0a1b060204030317040506010506070218090a14030f040501050d23191428050405280201 69
    0x2070746000a81118400c0300252061780c008440b03140155482d004440c0d590044d11880b003240030380c1a0140340103403070b185075104990304018140f420311241b2034202d200941071b65400094116181d8822001d103101d03441552242d5450700c40c020000a180f03030164010358208100b9401d0f01e03040c0e80c0d80c4084014190301000c820b0001c004100c014241c1156940c040c1040250078a00204103807204400c0c110301e8021004140c503090340c002010000c0542041c041403000b40900150602480c20340ca8040e15900705200e550702481001800320308555a0b00803000300810f2998519406050401c101307680d83c070003168100c0f46000c501c10f051006150000c03e5032450140c00058a19060034000111020f410549241c2003450301d90766610741031a02007580d83d00c107440f04c4005075034524040e840d09084100954800c5070355481c05c1013526070342e0042c00500381d00031a0003180310f0041210031903c640590044d5440d142191030881880100040403406240c078801700c0300030105843c0c51150031303070941c407070f045000380 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 658643093 1250 658641843 658641871
    0x7030e01180f08090111030c0c010905010e03072706150215041e02060702030109060902150c060a0e030c060106050309102f0d0c09050321070308091905010f0b0306 72
    0x3400c40002811005810b03d41b816008191440203461600a5403c03030316a030300203e90303010080d41d001110800401d000d181811050007103c000c82d846010038040c1049032a022203610800703c110582c9100150f003041e0082110540c3e07120a14040041f950f18030740140146c001c2c1c54010341122021500036500710303206500b55280d4486081c07180140c010100d0b0841418801040075a80a02c1260541d500032280818044058070401184045041050a80b01c0382885640d0b2090706c00182c2c103a00200c1c01d24005003844540480c42d02c0c42c0104095500a440345100204e2000c0e0b110000e10f00688808044640707003522541e504007918007205410340400c950205030540c1460400018030800c034154551450310001000301001d540d41403503c1c03404150100010080fa040401c820103006030b130040400120120140781010511854001130108000440850f541a5042c0140b001040c00f041203030025030300300c0c42c006000c0c01d0a10b180b2018645880c040700c82070300703010a550307200d081c1c40e000b180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 658644343 1250 658643093 658643123
    0xc151b0718020909091c0e0a09050118050c13060503040804090504201c02061b01050109060302010912110613050303120f15060a031104080105040602040e0c040b0f090f030607030e0118 81
    0x1f031345911040d50a6a00c030180010000f0780d443e032841200e01a00b0105a900920054452502d047d90406001c03000c084138104070340041031044200f082d00740e51451810300d5882d2910f0600ca91075018980004101d6450002070204110840019040e51401c10582d0070b000d814400412a1400504404284407250700200c10018941100101000003d1034000480d01c02407242090071114242c0040f410301d51303501400e0040d90380000281c0d00a00c2c600e80b1840240000c1da0b140da625006008601c0e0044138049160600c0c0c0d00100b16a0000d442c010f411251220000b00351142d40003000d070b0312069080100804501c0200e9282030744106144082d2806103042412541103005003002a80300c041c40006000100f4007000a004083c000c078000d2a0151319103040620b1902d0520025001c840f0301c1c2001c00c0104495907504090b10850010300d44a035883d40e05480110b9044900342c4801d036414090b080c00c0228442c0c05610201400460400807c4417000f941070b858481d0b038020038040c0020501e403400d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 658645593 1250 658644343 658644347
    0xc06030e1005061843030b0111030313030e090601170603161e06090609050d031b0f050c0a060e09040f05060c0c0c151b0718020909091c 60
    0x2560441d002811803d02e410715a214440c8a13201910f0a10040300c0c00f005142d01390307214480c0000d4480140006002c44464603103001031400d8000c090030145a1960400051350780543d154010206848054940c0c902e8070354141c2000b10146c65085020840c44072200a60b8100723081c000b031003a40103031200c6100c50000014400fa00d8001403200354540310f6181d002e200c640c3d500b80c036080280041c07908a5189460443d4080c030de0b00c11600050300700810040c080003030700d03403000f40c602c225081540d080703940c612641400c85102015000140f404100c001c0d180041140403842d8a44041c010700a07610409541c400704400c0512074801e010019a821035003020b40c2c60040141c5420910070119001805150769400341080d408440c034a80020022615003490f0b0310600c182c40c07002d2011079103507102078a40000100e15000d500c0012031030b525584180346c680a02048500d0150000900d003540c234000703010300c1e84040d42c0314401ea40d000702900340100707956201c0000c40213024043c01c03403102400e088039031003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 658646843 1250 658645593 658645601
    0x90b010203030f1008030c010e0c04090308040f2907030c09080c152803060503010615050a0314280515150d020f0c0d09150e130c0c0c06030e10 63
    0x746030b5404030130203000521003c08200611400c8030650001c145a404549141c2c1007412a19506000320b0070200000006a408034545a020358824443c69414030300d401d01c03c528a801d2000b42c90014a220220050341402c02c02c01842a50195014401981a00401c0f1605c07040d1f40704100c155400150b11002c1c0c1d01e0300c3d1a81003401d41c006508241083e6050004130301a0000314020300301ca4100c4040941c50f181d144c011b45002c1c110941c02071003041e28207a050905d070032111078180c00300480490310b030041d14800c2c0c11881d012122800d08040320b00300100b030f8540342c040048840c0c41911402d01c003c5202101405000d100d1040019800001040c15050182c01e628491240c056842d040181c0c90841c11244064204111310b802c1540e268241404198504940c1104c0c1906024600808118540503140c20403182d0555281c440d500a40400c0442d01500c400550355110034200788058000543c40104c141c2ca090261400541d4076030341f5002601103900002280e6045e8010209040018049400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 658648093 1250 658646843 658646851
    0xc031218010e0402120105011e0519020f0106080606131505060f041d2d180115241d010f0c0614090c060a12110408030c0601050901090b010203030f 65
    0x14038001440400c40043e080743d11640c680084c0d10140b01c01800384c0e580c4403294803048040a905c010030040f107810060464000c80e1101010a0b51480414583e84c0c0b00b031011812550030b1100030300c0040c0d01d80071540d80701c0004544031400f030341303828110705807040d07160090240d0400d248940b8074209051105021607584046825001100100000074040310303c45a07040c9540320161107007101d03060a881c89a4072200c3c0d6400c0448404400700d640a903100340350842a0440000d4175103031180c1c0e404602ca580940388441100f030584032a884002010480402a554070002010111403c88042c40040d101100c40317940402590a107055148115405442080a0701046003060f04060005a44a10694640140043c040c1c080c6e10306014454200b004030310101e030412543c1d1400c05407941401030015020a13680103585844403451240181010210760140441c0000e8030b079629883c05049940d08001c0c032410303001c2c1e080d580000800a880d44511844018168051461912041001d83c0b0042e0003074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 658649343 1250 658648093 658648097
    0xf090f110105120a230c030f0a0b1003090218090613170304050a05060105040b0105160c03170304140d1d0a05030f0c03120306030a02130b0d03030e0c03121801 70
    0x112620b041012801c4240c0f040c2a00100481d03049000c682280790501c09516003d545c440f08018410384494007400ea0740c3c00402c260400003ea9500ca00503000780250080003a00501040b05441079581d060300a2020f06000b0307184941d036201d540440718580c081c2214038000b00d8020350f01298241151402e511400c0b401007144280c004c41c00c04ca021740030351080d6401c58003903001c1840c0d5070410401f40641401001d01b00c500b08032201c40c080c000f030b01034450f280c070180d6241c3e91032605500f000780030482035001c1c642254000a03002005100315000f54410760702640c2080c200f1a502c541958000381803090941c05039940f0b103130152800c0100088400d81440280e22a5031640301040760b8508224000350030b070000c401402000d0007002410304207084510488022003080003080125100007400d04290780e8140c8000400c00c16040c0f42c00c00400003441000d40c08186245414280355068105460401846090b2003900c03842c2000c050740d55942001801604030113210881400341c0c0b13050180340710360b018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 658650593 1250 658649343 658649347
    0x108040503130e010e0f060f120a0f060509070f080316060b180a06081c051c02030c04051c0b221a15010c33021201090f090f110105 58
    0x1074441002c02035950040304032031818900400c40980402005a04840e0b0011140d803541420408660040f540c3e88a40740506400c140200464108000040500c0d404c0060f901e40c9442c01e11b0f201010380025104008070344a0b074400410700410b890000070403504000015841c207990740c81050604c0c010410306a900365903c4200304015120103d240b4042d4581d0070074070f40189410440d1030700712983c613000342c01690b102029a101503580281906071910403800c00c5a101d400441c0080d4540c071a441c0d484840704d0000c030602141d803100c04050001e4800c1180c0904112146440300301102c0326408016064207200f030042421100b1041261200031a82000180c00a015456810700d019803883d02c4003440400d071040091200c48010240605c15091800702040c00782c544600c4505d0f1811400200034114004001c07591841425500c418122171000070754481c000407400c0d12280400340b10b00b0308034901b00004d004007000c1c0380c490300790580c0c1e2011003075a40743c1150321800d000d141c000314418140102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 658651843 1250 658650593 658650607
    0x110f0706030b041d0d030e1203040803310303060b0a080402090405071a030105091f090b0402040918050d051e0d02070b01030b0106020c0301051b18040c0c02090105100504050108040503 81
    0x224989042002c480c0014001d1817680000103080315818002400c4a0300704400c1c6003800308802088a40240e04400016220f8945e8090003a00c2e021188201c0c510301c00f1001c245c41d1200c204620307144114001c0d1810000c00785e84041120240c410405200002081c8c03200007001480c1c507084c00c3e60840e01070b0b0100d61869071580800540000c0094044113000e5011004100c28503001c0001944101108650104058040c100003125820741c0030740381b035980d1610681546c0c3e49860341035900401c10540f051002c0300344621000082d440018090340c460042c02c11016105000d182204c0d00840610000001001c9414640106800c1031551407001d5400300580400f01d150400164040c40c0980f005480c1da501d0050b002c0d20f8004c1d03451846019174146410401c02a501b000c1c00d0400d031125010090707a41c00c0d05031141101c0e40401039501d038040d28190f00e00050640c0719030900c050038400c0e01c40b61126600d4008021030260300c04007a0f80040d0007003000340925403140c2e00c001d8100b407040c800ca071300f000b030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 658653093 1250 658651843 658651871
    0x1090f09051e0c0406080d110c150c060f0606090d030306120516080c06161e0b07090602210f0d05071205060415030803100f090c110f0706030b04 64
    0x1040118401d42d07118107500c0c4550b2800c0500c070190a0103000c0f80e0800c201031400c4070302520f0f2107109003800103000000c4800032041e04c0520404e16443e5008000d84020502050411000d400c0802d02070f460384901c400240b4680200e00c0002e00030ba0f030040c40b16003042c1c11801003100e4001501e00840403d91940d01c001a01c40c81e42100c070140c0c0384075101808100a42c0880003507015210b074003003800e581c04403240c41019216613044600070030032020028040b0900d070030b05140043c1e840e0090703c40a010203403150240446a0701d06030141185544299015070f48410403a41d41400e0404581c581200b102c08280415140004206000072032000d182041c443d604400211034007120240d02054032100400d4400c592403150700e0340070100f11020401c0e08034000ba80d00428181e800300800f101070000c0401d040a05041100004007144800d42464644542d0520068000c0343c0101010a128036403941103020003040901c03100c00a6001801003034904801180075201e1451304541041e0790b26090b1100c48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 658654343 1250 658653093 658653103
    0x9120a0e120715080f0c090409080c07150c0201082e0e150901120f110a061110110f0a050f0c0a03080c09180c12040506041205090901090f0905 63
    0x7220040600320561419103a10443c1030040c40b0081002418010400802d07150403102e41c0000c0c1c580f0741a62582003180114004100b5040c01403c125004140210014800500d2100741d59290100c0002e804d80c900007a1030034006103100030b0101e104100000c1c15152500314002e43c0c0044071070451b061030030311003150740759180903004519002ea04a00704000682c0c031400c09070800b04191151702e065031601044040000840030010700304503120280809000c41c0d56848401d910008040000503075407002c02501403503c1d100000201d005100c0350f003010403524440c0b00a00541d064116203040b8201894041a5000c4c0301400207110041c00107900e542c0c1c045018210310100391005040b01180d604014101d03202c0140080364442c1c0402c070420407500d07a2a500260303a5602001c4d07000a4445264941d40c0380a100c0c07408049517903e100b002705000001505a0040303000780c40d0754903111101c003c101c03528418440b82d02c0d00300c00d032000100710350880e5030b00000f40a11401000641001643e175094140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 658655593 1250 658654343 658654369
    0xb1906020304080f1902120a2a05030a1a040c1211091b040909020f040f060312030c0c0209090a140102250b0f1f030302030a0906030509120a0e 63
    0x581c40400c041c400386008116890700d85110800400488407150714000d0407030b900f0000213020300d0120720781d06480c0e802004035500036030348881c8a0703030103100c5002100207045c2e11440003e19044015000203017410b0100c0c415030b500d81c0050603c40d0704052010103000c003030300c0644101c070416101d280020308510070000c0e500c0918814890502584610340030031a51242c064030300d1700000d00885841548058072402c0b2400c94000b0000070500e052140001480b015003059196003041c288010110200002e44c40901500d12420060030804481c8030202d041f14105040f61000c02c552190391009880c0402c5003d5001c80d460046808102d03950380d4906141065040340c00c01e980d00400c00d000004414400c45541c6041e5040c20110340a990b21030442802002d01800c400d40c1c0c841010030046480385d61403c00c1040e441d80e04c003800c66940d1900a5403644000c0c49100026240900070034114403d000c0d85016000e884014115030142c0203405156500800c0d14070240701400d0035444180d182c01c5050440c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 658656843 1250 658655593 658655597
    0x209090a0f0c0906050f030604140a1a011517060904060f022217060112140706090501030605060f0304030f09080d0e1f08040818060301030807060b01030203060609040b1906 76
    0xb00b945402603034015a842600140d20607021070030100c0c15600c00040f21907109400c40301c000740b26a441902c49050021b003442c040c3c03114114030703100d140600281c08898100c0710502c403901c02400c1c03040340481d05843d03d5a8013003001105072001c58210f2501c44030341e507002406494001091044d2003061001c9a200c02a216001006d1300d0031008055404c101c0d410040501403122035210a019290381d8480c00305002d0b010484010100100502140d280b0080025a20004aa44035901d81030042c00b60145885035900181c1802c1010070310f41845130648042405001c4101c2c11034031103a03400d68000030044200e004000f42010001f0700013400700240740b0822080d807144051140e10030280810702d15403024403840d00624510000342a6400305005503c1600702100644031240c0ba041b0350b030091100e21640e0351001c07011001209000c107542c020624148034203410000d6191480042d0140d0104542142c0e2000080c000002c807418180c021010200b4010100d0070303941c0790f16424141d003401b59046540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 658658093 1250 658656843 658656863
    0x14090604030e01080705090d0503070b0f090c0a030308040f02040f1a12010606170910021b0d020c1c021201050103030309140c03030d022125030b0d0209090a0f 70
    0x3007419044402006010300a203400f041619000002401600c98203164500824031100c526050010600076259200c2d4468034941460428440780280c6280545400c101c9024140c85003072a4507219000380c040b240d25890700d040c10380c0c03070781c856221801c1a5502a40c1203600c0c4c841040104000744a10010319100030b140c2c0e501c1c501c900041c04280b00c4a00d0780b0040d2603150110500419810002c0189410301c41e503500000c650711344e84d40031f00300041c980c04101c0036800400e001e100c80b400d46013440d80810060007254040004003004990b9600c28000c07046d00300201c61128208489011503901540340054202040d034a520041c2a007110000d038810b40029984a207080204641145d04045040740c00e0010554040541c0000c0d850384a2202c44048440d0b0000b4444555030784100c4c007401034000ea0b540c0e202e852030114900c40d00000d414286002d65104075295080303103400b03441b540d00800e0001d0b000c8210080e0701c1c0c3c00e029600034080c02ea003ca5114002d41c00000529101c1d20078480391068004c0b03d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 658659343 1250 658658093 658658101
    0xc0213020a02070f05030312060112061d0c070b24150405090f0c0406051612021c020f03030a0c020a020a121a04050d121121010801020915030703140906 67
    0x3d0401400740c01c04003014000d02420401a600001610070304d007851903240701240c80381c7c03006a40e540e44509107040c00c0c500302113000030490303003a443c142250380c0e000a0212041c1c1e1180300e200200d1040c054000c000201d038031f0204000c2c0d82c00243d00c0c1c0301040c0340c41d000b03011002d032080001d00c05500c107803400e201405c00007014055803c0004000c0c0c4c2004101d80519240e0070080040d603264042c60041ca001c214000c5105000d9031000110210819000324074450001465400203403209480401c20048075800280a490790388000307981a842008034000e141562101e046100c0503220100311300045108010007440075070f89407000b2400034540b4440a5a0203401481c2003400000008109003480b4408c40800011490101d400220080356150000702c18071703c443d0000080450b14034944c40c0d142c022035180041d5139107091194109000007c0c9a18070f80e41c6490340b5081c0c0c414030b140c41e074124492000290fa0800244041d54100c91103080100c3d544c0c040d100d24129241c4100c40d80038850748008280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 658660593 1250 658659343 658659347
    0xf11010212090d14070803060a050a0e0a110a020d180e07050d0e12040e0910020c0102071e0804180e03030c070b0a05060109140607020904050109031b050a0b070c0213020a 75
    0x83d1100c00090a00c1c4d4880411455040980e00400501500d04000000014090740d02c03901c203200a040700810031811030340c1394544074105400403502d03001e1451420f410b42c04000412016943c05900581c021300d002090740c4412a1204508110303a0319002c00140081400f9164070001380c801c2249079203661b26001c4400508054484d12008066603411108080580008003030445055940080300d0400b59100c204038a85441c0c42032400c00c5002e480460304125200040d00106000c602070888a4011105500034500141a4440c028007280080204212820b101600384060030810709000811150303c1294900710b900484100a00c150001900405c04c140800b45642041c200300c000c110501c3c08500180008803940541c0e404182d03021203201d480c2d0707254012280b110f54007402507402410949070850180150400c1140462210f5010140c0c60960f040b00c1d84c1000d030400010400300c1d282e0b40342c0610444c000351208040056054000d4056100e40c0d61004642c000005c1c0140d43e828480b00c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 658661843 1250 658660593 658660603
    0x1a010305060f13080a0e0105070f1b090e07140d1208010321200307170c01050c072109082d070b0f13050910090f0b030d0f1101021209 59
    0x25450350001c040b00481c0400d44134401d031202c0c1d5850341000d00005543e080165050b00420300018008903020b4911005c1004402c4801d5210010001e2010241e4581d11040300f91002c0307150404050f880584c0401480000c6000281980740c064007401c0c10f150151a1066880c940358042000300b01c86800400c10010b0350503c101d014030407aa4a20781c40101d0810040c908003c0f2a4a84500c5120341c10000482e1410320032030701c600f0340c040c1c06140040c4801c0640b003240e03040781d40e210405519140c00500c46010030301c11540080c0d44203802022031070010b1200c000707160b42400301e0f1003080030b81403001c00c001000b0059140558540100e0943d03403c0002404200212005210003454020500c20404040b20000341c4500c1d00c100a003498540a8002d09a0354114096000580c003055007414403c1e0340100c0f00500d001c0c0d5054242c14004150b0b031200c205c0c15103145003a00c82c0c140e845082c001c0c400707510802101640c3d0a19143c94507403a42d0284005007a40c06c150070521070380180c2c3c410302000802c1080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 658663093 1250 658661843 658661851
    0x70b060910180b030123370504110609011d040609020a0305090c011404090207060204050a03150b0109060c02010c080f070f06060503030406050d0905070512030a090e091c0e04110c01050703060806060d1a010305060f 94
    0x5002030cd002510000200482c4070240000000c448600048049036200d801400103400000011516605ca900000340549801c4d99190811b019607420480c1a500c6905890608000c0140040c60649060381e02c02c000d5001110688003d40d080c40042855501c0780040c0c00118081d001c454048140030814600321280190458188001440308005c060307004200c00001940900700fa043c02846400c0807642c1d80b060303c0c4810304e032560004000080050681c161000b0390300078102000040d40711403c3c1582c0e032180c1c0c0541404aa018050b002003100c175a0490360b451032244040d40d03602592075002c280c407440e00001d03604c003580001c140341e8000340d840080b4100500e050060b0300c11307509145485541301c030041400c3d0444150100b000990f468010110a0700c10800070380108140c18800c02d40300600e802209405405e5406e19000c43e0b81e03584207000c3c00701a120010f002e8462502d80600300044568260000c035041000e22490448405010b14a240250300030b001400b080e150084141c170582800070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 658664343 1250 658663093 658663099
    0x21302030f1f030c0b0414090f01120303020c0a032601050607080c0c09010b0d1104150e0a1d041e021e0f040f0204060f05070b060910180b03012337050411 68
    0xc104450038410313903207103411200c0344140785829052f542002c41c0070340b0640b000c030845449115844410980e0080414400c08146095552510107600c81e45811034800e11500d076220780e0500070ba0004c1201e01e00200150840a0b08a131a0040c0110208074120001d91104036000700101d8200d0302e2003440d000700706c40350b16120201403030b086c01c00c5a01c41460402c5a400360070000341c5501916540c0324250914041c209000340c5240705542042100b04c1c000707089400f100c3c00c800107245e01d5030b50400e07421003800d1140c3c0240002c1044421103c12031111103012019540055902e03110fa5807034640d80b00c2c0b40400804c0800c0540c5d5642402400f03007114400b612072904100c400c00c0b058020400e1821a181c10842c1100d600f40a602c510156030640002c40d044080c0c885040302d404400071007960307c0307802004401d500901140d95034100d402c0c0c2e11180550540c100070141c000042c640714601e9200c00c400540042c00c611240300300250001c64840e0280c44410b40d940d40d20611040c045404050202c0f09000c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 658665593 1250 658664343 658664359
    0x16081209030304030602181f03151d100f030c08070503070302091503010f11030604060e09030d0209042a030f020405060406080a090618021302030f1f030c0b0414 71
    0x148010950b40e200d6880302501c4c503a404980c005071170b0f0520112000c3d200000304000f04007061080f40d140b0415800c0844004a0310784000881144403451060040791800d082c01d003001d400d60005120440002000003181030400e8401192029546280d40c01840c00750108848042c00c064034030b07290a50b0764000030303c00d5001e054100016030760207030310310b03800b252003103094500035400700200380504182140403203e54106000c14001c0e0b00a403001c3c0d445601c00b241c052214a41d42c2d00c4c05401110241e03414155600300f001808040101500200041c545c00783c4000b071140c00300b000c4c200d6403000c2000c007901d140d00503030f90142640307a00d4061410720a040c40400c51815107040002001446184660b2013070100d80f9002070010b000c00e900113100141c000340148103003e98600743c0790350404c0b1070b0400c0748240c80c104020307459445140300b568420144401c101c9240e8542d4298202c0425060341c01050046901d50007000241c1c1ba10f5000c0001c00304403030410348450400484902c49042003003003901403262 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 658666843 1250 658665593 658665607
    0x1e06080f090703030c1a07120c0c05370609030909020405060406032d05011505030432030c01151d070f0507020a12030f1707081305160812 61
    0x1002c03541a04480e490705008031645032a01d0090000c0700000450101e10040c4820010016041081d050448440c1c0c0f004200b000010101511f8542090380054042d60000311461520103801c0e0304000071404184410081216010025400c40c12482c41100c4850703e40b8803140416801c07c6a400241000b4001942428105008105503004a1080c0c004158941d0702070804a940007010301c2585040d0464080b106802c0b032440c8005c2c05083c45680d40c246009200740d060140b01d00c003501d004942c810840ea81685c1e00c0d1485007a01c0100000309041d415080c07091400395102080100300c00c902c14800420031b00310442c0304a41403540c0c0c1d070100e0030340d850300c4a240302030b04502610030354841c000e4140210145418031045031039000f0903000941140c90900003040050700c244034440701d14860740c3e036508034100044007100e03413801f4103084201c800000404640c42c04d018143c440d510240d0324035407001c0b00380191601c92034190344a0401480c1c990f140c0c8144100c1c00140110702600f00386440891070108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 658668093 1250 658666843 658666861
    0x402070f0615120b040804050319050c0d02011b080f070c0806060111030307031104091806051302032a0a0e15040204060e04050a02090d0b071b0c0302010e0a1e06080f 73
    0x1e03003c0c01c020400070040b13002800300000b500542e00a004041c00302d5151840b058200300c040d44000500b51040c2c400c401c0076403421710300152030f4024594103940f904041c04405025041e141303108a011110424188090011440e80340b000e010501d00880040d0400c40c036100c42107082110142ca010704100d2144144842030b0000070889800c0b03841440c0c0020035084030304030036046014030b0300141049070520803c0040050290f03000590140185e0b01001240c81d10b1100d0964052250802034150708884986010b81c0c0030ba6107426500c00e0014088504c414140002800c1c1907103540040103510404414060030902c1d803c4640d032107070801d8804610b82420034a000e002c00501581d103910558071440007481111054060381c030b003800041e110412018243c0382008403a10121003020001d1140343e2410b151030b91031408000440c2c1c01041d4011282d04540044800303a08540d00030f50408001e180024007851703081030002003c00700d140d41365901420080021300e00b102c040c1150940468507014000004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 658669343 1250 658668093 658668119
    0xc030b0901110a0e0a030b0c0d0b0d0f02120312040c0303020f010b06090f0a0b070602190e090c0d140106020304090c0302070209060f0a08010f02090a060201020307020d1209020402070f0615 83
    0x50783c904000fa45140040c00040303182507190002810000a101400b0840200f64042d142e040725900c1705000c3d60144009006110f0b4549102521841c244c11f03100d005810041c20b5055100703540d50569141c0303400b035800c48050100565007242e11f0300c02c4480070000d144c0d061100c032109801480c024002940a0340000b0b08500503202d500d84140c0c070130000ca01c00c5580300f810b1782d8010241100e940e43c54000c182862030003900440c443c039840c08042e40310300d0030b004c3c0b0a032841d107104040100500e40036101d0032038190440e0484150b442440755034500002c409000c0d90460b500820142d0f0003103039110305120000041e0341d0300e144241b0030705005002b20401a620b0340c40d603650082c401d9800c0401000d0050005031101c005600540865213885403401640503160001c280d020f200b6900304030440c0d0341e000124201c0c8402c680000058110710b5416518078031803071040740c02050841d801b0544607503c0e0001002c0768051841110781e0780400e130a800c02c0007880e00621280101481154403c1032400340b800d0420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 658670593 1250 658669343 658669357
    0x16050103022106130e0a0b0c040b03160516060506040b18060405280504030905420c012a0f050a050d1a09010e010612020903010204080102070c030b090111 68
    0x90440c0b41c00610281c841013002d440301410940d052040d07a07414900b890300c5480600f01a140600020300007202801814101c50459407402920351a55a80c040115500000c2c0b03200c0da01005010041090078a0b25030300d40d0600305001c0c60b0000b80b141019002c00c401c9031b604001450082e1014410a011039400550b0185d1080d4181c030085000c0d0703a60040c2c8284a110709140f03940007a074000e040c080c241c4040e8071041c400c521a86030900d41c5034880042240000c40b14001d407200303041a0486c8540d134401182c841301000c0c14100e02580ca1014131803262101c0d0002e0550708516955584209c540e80c601c2d212a6001d0510702c1d400c3e002c0002d600400402442426000d0b00510600007000307019188980b0071150410300d4440204103090100600c000380d403400d2078030782c0d109003904d0300080b42c03100b4009441412990180c0b24681d001e1034812820700690040134205905550a20000407011020b000408200c0d104140300c1d0295170441c034107041500c602501c424016890500c41100c145960b001710b40207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 658671843 1250 658670593 658670647
    0xc010905010e043c1514010e0a08010b03070b09180c04030602130302030f011415030f010f1508031306050c0a02040c1d0d020303070b1e0403021605010302 68
    0x24107203002001c90003408601c0c00d040b600703000d4250540ca042d005910100d029000f41651a110300b07078025848000c0c0c030010001d0820340e824805c0104070300000510240e440d050107041000c03c40b02c0200018013100e0382a449107610f0b0351562400c4070301d440e041c00b03601c003c0e00300342c103002d41855101c00c0821900000803004448003550786011500c009101002c0d070340255030102c0e065664510284001c0010411480124004e01c03614100da6118201802008150280c1243d5540e2990b5043d0141007205407641407a50140210030511210603820702480102080f10100482d04054032070351340c050722a81d644115a01d8005201c600705190190400c10201e1301f0501e007081e180c0100704034503424a200d444000b94454070301204601c00581140d00c045084030340c0400031581703005880501c55503c10016000b58560000c0101000180c84c02030031070f0300080525443c1480d940d0907000745805802c151000c1c0c0160b070040620b940384103400c10302c1d080949801c0c81d0a605180c101c0050100341014402c1c2861 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 658673093 1250 658671843 658671857
    0xd08040303030519060906061716030b012601030201020607050301060207050f06160308060a080114190603050d08010e010f0501120902010e0a030803010f05091e0714040603020a0206090c01090501 86
    0x14803910b041c1c0744c10201c00c022080801241c2e5460b25000000c00c0d840c4113010210b0045468140342e105008200d80c41400403460103000118040302c2100146403002c0c80c2c4e41840300c4c4540303110140301082c40d80d40d90340349406c017103c1a650560002a00e003000090818040040070001402183c1d404a044030403108141e40c146c0c403501201c800542c0a002d8482d485080018911090040c9503211b001d03c2d024920030348403202025180c1d120303d42607030544c032280700d60605500c01142810301040c4903601c0c0070800312000a480c42d2070341d13100c6040c9401503071400000b80060303005004034580351801c03a00400c20010031404023440c020020740600a40c400c49101569155074410075039000b00034200442c071004081c1320303074581c481c80e14840b01d4100380540001410f0b0604041f55032300b1f1a040ca02d00030320802010705d0440c03080082001d150f5800070129400c00602d040440400c004090141010340160b44000da11040340c8000289081001800c040044d484500c406210340d80042d04403040e50300a1034078103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 658674343 1250 658673093 658673101
    0x316032d020a080a0b240c01021c0f050601270312020d090503010c08040b0a020c1b09072f0f030408070819030e04050a1410060207050d080403030305 66
    0x106240e81415403148190340314084620a14641d00074801c07031465440350342c0140c80c1c0c118050103c800e40c0d680c244d0440c41100101491140c0d80305150180b00c9514082403501950400703841c01c1e40c000780050041818440030007082000c0394090700d40c50a0b08441d08100c1850800e0000740131680051042040c1c8003100504541031541401c1c0101030340c1c1202c141e00308445e0440c0000e40d50300744400700700300141c40c40c080071850340f4041c080c2980d611760551350400c0d251070325102c040c03032040043d24201400d0f508011401d2545004e001850760001441d200c85d01141043c0280b100d40840200305008000082e2500648982ca00b01409401911110110410420400c035949000c00391a8600e48511011600003200d04c000201e050542d01102c05407410100500f00b0460019800000180070582006030210300c0d003843e5001683c410305c000404610300c025500c00b00c9a500080c3c03001c0009941003001808240d4040000c140100400d8a0240c00c114150326141402c0c0114040102016100c802013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 658675593 1250 658674343 658674371
    0x150e060306060d060f06080f0d0201020c031207020718020912031e0f040807150f0206010608011203031b090e0705090102060a05130c0b120106030c02030d0906150b041406031603 78
    0x301a00740200020050710352284031f41d5540c2c151859102c5a98428545500302251044c000d451500d01070300c0c000d60800c501903007210252400141031008521441800203414080944407862403454040b005946411807030a02c81c103600c04046080c00d5030300c1000020b110a0004568603501160340d180c1c40d0300d501052440350014855a80804410701c03550303202182c0320601c0ba04a280401c11925000d00148005034246c0e11140240325a1011035143c0c0c00401c00121081078100074240719140001e111a41d030005030160102c682885c100007003065800b400000d040c0150740341c120780d0a0074924200740100700000d554500c014503d00000d9244e60106016034088030320626010f5100440d0941c081d11228106c2142e04190001034150800000019116010b0310a84881e00790380d0b4040c6140c0304234291000040c10146901321051a59a0503140e821604000c1c50300203012080207a0b40d54900d4518800201c3c0011000b007842980100144070041048400820b149070480c10003281c0c1050901d03134 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 658676843 1250 658675593 658675601
    0x70e0a05010813151a0301050f01031208040c09020f130503070f210204090b0f060d0b1f0902031920030414150f010303110d052d0d150e060306060d06 66
    0x703813000b078a05104d8000700e00801c10741d245041c00401d400801c000d54696104900c144400c0c40054852219180004512031054040d19800b500820b103002d002542c90841320100e910004452088400205614504074061812070700201001c600405616007420b1003011019024824000240d034a1411218071a05601c0c5000200d0b80051041050008509240b20521412a42c1d078102200c000c0c000340c1d240c03801d0213001c4034894100c00301d8040769072580c40780100c0e84056002e0390001d9203503100000c0c03e10154002075124138164100e04c848281c4040480007556000009594500000242480405603403000d07260f01c540c02c01100c0c080c0c24103402e095410207101407094200001103000700304005103441c0c01c1c14120b910070390b2202a2006a030308010703141c04c00103865800040701081039203d01e4001d210520000a210a041100101140c03003511641e400802e448415079190494403905621010181004080d54160320401c0d242c07100029031074440043c0036a01c504c1103081035034140103c5a01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 658678093 1250 658676843 658676873
    0x151801181805061303090801050121111002070f0e130f02011e090321120507180e0103060509060705072d1b0b070510090201021212070e0a05010813 65
    0x240c881d1414030204144d0240c84903002074022549000c000280c08605100f200e040340c4200d03010050400c080115055440ca9800090b42c14080c00341018419540300203400c074142e000c503001054010301d0aa030000c8010042c1d400251405502c00c00c04c202226231851200e030f0305a104a01c1e0792910700600c0140c0707180d00380040038121740075400702c04003010707410071082c00689004003503c0010602044031340b40d4400c2203540040010b1500b41c5007540707480250304655013000361070506540020301845c0f002c0d00031301142c0c4140003240804004005001d65072156541040215014060504d040d60000e4007a101c1d45038010001c0803004102c0c00030184007000e0b1450402c00b02d40d6920540940e040c10f4014900022940c0c1e100b101d244000200510400101d0301e01c554050081c00007401c0303d1030010b006298085d4181c1c1980140300810800700380400040800c070100c105038515500344044000c250301c83c84440c4901035482c100d800d000d5a0703001030207182d22450050350988034080714a403040005840b1a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 658679343 1250 658678093 658678103
    0x1801081e1323061b07030f080a1806020306041527060f0602030a0e0301051506030c0403050a050d0906050702092e060f1d06030402120c03061518011818 67
    0x141061444001107203440c01001d410484000c0c0a00d502200c0e000b500c160380001b00818212030007011058010000c19501060b00304002410482600c0007054158081c0c00488066a00100b041810b1801e40301c0d80d000d880564014007019410602c405e44030804052504110a022183c00c141611242e0454000b409107024150300ca541da40001968070340109028001141c0140003800107030405115803446240c1d640d03506c182410101e807e102035580080d10310035040740d0070000480400c07020850b200401d40700e44014030141c802c05000500c1c48416030401010000100500350241c0e4501480627007100828031000040081801002c1203003182c03100f0010f8204a50030009a002d8000100740d000c21300c07030780700c000d52a401c0d190040c1c84c04042010780359110b4814000b142c007605100c5401081d0071802821a0b03404141800041c1c50030104442000c0201c800f24040101414450070941c03030072030300b10000d0b001035041c08030051028103040541124540d41d1000440820492500e08034169001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 658680593 1250 658679343 658679393
    0x41107020a06050d0f09080702010f0206190b06160308060a0f14040c0309050a1b0605030c0f07021c08040303110307020a050114040b04030501020d050106052107090b1801081e13 78
    0x81c1c50a14500c1d0042301059000c00c0f0502c0c00d0080c102e0021a40d20f119103d6042a150300321107076100c040007080d40d2444130b900102c00740060321000b0624545c04450324040d486041e52441c1c90b074104810790380d05070000404800244030401c041394541c07070106d07080241120301086600140790114000d042048000d89240b00d88004c8206004440c0c402400514480c4071112a0544541080d10340d48030540b0041840c62080000350480344070380340549441403009014404050300324841d281464900102075401d4480040d04000300740e007142105590200640140d42410500e800269006407244034440c10b00c08100c2a55003009410001c44010b4a400401d0742d0b2116140c2c188a4001d4000704000102146094008a41300c0d0146c400d8640c00c4075008020480c200042c2690300521801400b2031041c80140500801c6903082d0f9401782500c40704a00f03404051203012000103208105c041e160036481c0c0f602100301300400c0c0401c145160301c0b80340d02184968120a9141105d848094512000b04405039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 658681843 1250 658680593 658680611
    0x706020f0906031906050d0b0606220b0c0d091d0a0f0903030b031501030528020604060f09050a0f03060b0f280803190809010e010203070e041107020a06050d0f 70
    0xe03113440d0701c400c0c0c6040411425071103000780f203401c0403603450148c4035035089000140343d4a0030400130600107558403100195007030b811011240b00e08103a00000c014000200320a0607509080004084511040c0303030500d030191610440c507145003100c2d14040744e050300b8940001d5010780745800c41e81e41c10100c008100244140c6080080085c1403d81840e8440e001c3c2448482e5040403040100d0305030394000c1c01404003d003424811405076085a40c4000004140d202c812015070b171988080d20041c14580c65201e50321100c0040205000e1003500310500c220040306060250b140c40f000c0a4007a03c3d4042c500140030404107000a9000c9000700011b07600c81c814440061030002000c01d520650708401085c404440e4071482003a490340124103200920244e003155000381d161155080c0e075041000e1f5000010f2881000070041c0c02c1e64404c0346d40f04042000802e10200c58280b5110b400d80000a0b1645282007414a500044c11185203200b03520812401103054140c1c140a41e10104212510110801925a0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 658683093 1250 658681843 658681861
    0x20901090e0a0b18041703090a050d08040b0a1b050f09090c090907020604080a0c152417030906030c190f12020711190f080a050d09030302030706020f090603 69
    0x400c00003801d004050042603000c1d0f05558040b12806207a100c0d011090641e22160481c41b141c20081046045129802c0c520000c110180408000c075407003a51011140d1800d07003403a20310300d10041c0a150102d031500c480c00420510954040d00b66804501e00503a440030f80440400a84c0100595140e0111410081c00316040742a0300514140c5000d0314001042e9a4004060f82c5070b00c1c0488020b48804020131034910550300c40d01682496030f03c180e580c4621045001507800c100d07140010100c26604140c074003080081811044030006015481240d200c444000b0380f12a1a40102d0825602454010000c1200017260000740d8103000c100c003801d546140210403004042003c03081c0e1040105200100141c0001e550340201e40501d6040340541582c40001814007017039035a0241c41e040e042c2c0e00c200f0082800c1100d081c03644000c02c000d000400b030b10281c030305116080000002545040c80400364003040000d4021054910250b000100140c4419240d0750324980c80c400e202a45601440c0002003241c440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 658684343 1250 658683093 658683101
    0xb030a061e080d08100e06040f0513020102011104051e010509030f1006050a1415091903050706030c021c0905090c030f162304120b24090109020901090e0a 68
    0x548214215032481c0a41c450139a000d00301600c05408840c0c0c0010f042c01051040c0809a4001001600c006081c1100318560401c03a582901c0c2c5490402122245005540e0b09025243d01ca4520310446032030507140000240782e20310440e00405498600400030000f5071300400a40d182c0c40c01c080e06551032220b031950703030b55114007c04500c2c5190500c0c0c0360000c10141440c940141c1954490320040850046040c10030210b00e04840110080d44010402440d040d04c404c0c8142010410900c2c8030ba40007400c1d0715000e400c1c41643d400050406207003400304550107900054001c1d540680f012050b0740c484500008440c0740c0296002290446610f038144200031001c84000c40c46a0751503102110035860f600d81d03500b5040500348103080003805d20800c05485040d8070310122100700c041d44200b8079003030f83e4a00c10320f40c810207103500f914031509010800ca0054441c500c014450203150418417940904007000401149040c0204a00e20b940424444c0c0b069009500344006403000d070051042c0e610f80b4101c1c1001030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 658685593 1250 658684343 658684349
    0x180c09060b0f070b0a0b060c01061a070b06010c03050706050c04090e070312030c1704060b1005040f0b1b010e01020901030b1807111c080411090702070b030a061e 71
    0x198503014000403054207103800d03100c2c1c000b1080030152912596464a013a40680a020080171a54030140b45c02e103070380c4500c01400080d00460011074028035280300d1a0b10100d055140d0034503030400b04044000a101c0b906540e6000009007001120300e400c60404aa050062110042030f540c54007041c00700c520704210140c0304031040c400050102d206103000c040c0e03c401540c4001000100a07940d8080058000d0300000394600c9103103006480c401482204511801090b038042e1501960340b200c404035418032054407514582036080c4245081e1400303600006041c203a111310815442c0200c1c600103072101c110780b0b2600f0a00180000e0200c0d104901d80c1d01e0003076001c5181207000c82c1c9401104445800c040c284818800c4482440c2c122564842105031804444d0010a415600480000c3c1001d070307200603282e02c49011255207800d032030301d000c0c90109038601ba0202d0880c46540c000c810010103680c001504401e8800c0000e41c0da8403078440011010103040250030803040000024046245041114034490032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 658686843 1250 658685593 658685609
    0x21080706050412020a050615060708070f0201200c13091a16030c1b110306010324021911010f1103090105070e03060411060f0403080702150c0c010c06180c 68
    0x40f441041c141641e13100f2104e00c005106401007400900e0f1482501075107410004041c003098a840d030150744090b0740b94040c0b603040720924105883c02041d9644100f00b0603180801452481d8203000b030131540c555510851070128480c00100200c00b903e11083e41007050741950003855658040e004071074241c0900c0342241c0b00d00c8900007031481d40840030311034091a41c01a608c1c0e110003100340030150700800c40725038a19060b200c00e404000c078014281c80c108442c0307008500410304620141ea1005952001d00b18003d110101c1500600ac2040c0328402c0503140c003090400b50030b010a180c0c0c1c00c0000320380035000b119022510107280120751001940104d009510406a080003001990f9942600b6030361188441c40c4190990704c44d03800100011150004c4615010004000506141c00c042c061002c1c2d6002c1d400440d2806000310791001142403c00d510350a1345810303903a107800c1c103803030589107546d0f8085444c0342070400c400b580e400428841c4542c80b41c003808800150014818030325091140c81c0840c94803800113 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 658688093 1250 658686843 658686863
    0x10e07021b06040e04021503071706030a03090b130b0c070311030f0705011211030c04031b032d060603050607020601091a0603070e092e030804210807060504 69
    0x11001a201d045064890041c5070381d080c1030074202209500c1c04001d10890f08100c260305c5040c51403018001a40c41030741175580d500c0690f84940e41f00d60070b0070000b0348114065031104039103d00103031304481141e041e15071076082d1686803116000d1141c503c070311079400ba0050300e0b4009001c1403045030204844056900407001c46113001c000405055079070002469400b03da41245800344444d43c4a0301c2c610300d201002d104c0106210500c1407a03104594825640c681c100c620002e0102704201c000185500c0d416401c404d60001103103103445448040705c0c1100d00c2002032510310390a18800365582ca54100054000c0750030001c9640300c3c82c1c8140c0da0b20090f40e21a01500c1200000070301c101450080b00318070100349079003016000c052400d1010319040031308a4401e0100c204a400980c1d1030300c5040c54452900e552890304280007030940d205014041c404040c4c904521020240003285150381124200c80313410f2166001081841c036a0300702c250040100821034100091070b00b09001458229500550082c01c40700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 658689343 1250 658688093 658688113
    0x1b11100e06030c07050a060c0c11010c03170601050d060e01030303110f09010c0c030204050910050a2c0a0519020a140915190303050d050c09030a06020c15010e0702 72
    0x18920104040c182a4480d404200082c16500d480c009003007120310a8044038042840742c0e445800b561218503000001540c6d007107028090203540140754a81000c00c0c01c2022044c88641c070b008250158080da10011070b003681d000f0070010b034400c80444503400c0d40080200800c40d1a40800902c080082c0300550010b402d00d00d401400314180300840301071101601603680352550000040d61004007003d01980c2c00c800c01ca00000140c1c5650207202d20990480002c4c11030030b000b07222400c085440c00b609400400d480c2040c8500094440000301c441c80800020800500000e003108501c1e000c0034400040c41030144503541c0320040c1200342d40da0042c9100322044a07015403504048000118041c118035840007119000c58140546401d00807003065001d080700902d445140c02d03240c2040c03c40d03401140022400a001c8408030b1061080039084540c0e4601c0da0700e0004000f0000b550b07503104800c003500744c0743c5c00954002124001c2059610ba021821744182c2d941d0703500c0d61604054617003101c8250260103081d0300300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 658690593 1250 658689343 658689347
    0x31f05090d050304030305040809090f060405090f0a081b0304060c11010c110607060e030a05120a0501050607021905040606052808010b090d1406041703070518011b1110 74
    0x2101407030450365194110380e034070b407004c40103440040e20139510316400b003088400380d132a080031480c0709042c4c030003801d10342e41001d10900c002c403400140404002c1c0c0194080003100391021506448d0301d03420081c81c03034895a141d8240743c800c0104410303a004522000030b0001e0f101d038209490000da140070740a00d5040b505500300540f00503c003180000c14070410500d1b1140d09241034005881c00500680300042d0300c0d03104d0b4000314615800301900740b01190010814041d00700703a0b40399082d4400300380314003440319500d0f0401040e054003442c00d000303202d0030085907203090f85140040010000c24004006002542c1c3e03495028207030b5405045a0368a0200800c41d540c1240300121284002600300d03a507601003680303071502ca408150482050503902448a10b81000840e581d90017590b54940c901e405002903052520300a04648410304501291280600401003080e400c003081d2001c0e1565403a0a041409024004030390065000c1103207413500c0000515002031003880c1e50a0003201c01c0c10b81c2e04c003260043c0d56100b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 658691843 1250 658690593 658690603
    0x90309030c090204080613030e030d08100b0708030a0908120717150f0103020a09090614031614040507110a03110f160b0a180803090a060f02030d0902030705031f0509 73
    0x43c3c1d40a50b11500115102007d075101c541e403ca40a441c00c011180c41d1030001074103182c0900b41e01c80000d6140e1043c4280000d940140900800300004010f10340b541c0b0795200a824000240600704065071441c00d0400d01c5020411101c0705100044030305042e15040001400308181a03180940d11140076000599061004036041c5407005c0c003c04d910403503d1a031004401070340c0030b60f1a81c070030070050300000600242039005a9000d822104440c140060b1040c082c585002070b070844003988030901c00420440c905000308000d1142c101501c001c98207a5940708195190342840c2d11041c0d003445820089030502d680a400c00c58054411810b8907640355a0a0318541daa0b03095001940011003104410810700e81000001d01c1d40d10b04905120391100b20610003140d8038005a407012004e40c00c0080c1c1000306e0711301003203200054081070900c80c2ca001082e5100030340c0c038044c158820f41800c0d69454542c095680820510000704401030445a50748803c9490140511024820081d502c0c10540815000080451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 658693093 1250 658691843 658691849
    0x6090f03030c080c030402030c13060902040602060105040b03010615121407020d0e1002030a031d0a12110a0f020d11220605060405180c0c1629030c1c090309030c090204 74
    0x203000424270f007000c000c25080b46400300c44109541da1000962001a400500020812a005451503614003000c5c841640c0811010a2082c0d01d40202884180b02e902d402c5000419145001028130903000c9070381000b0b244807170050035010701a104000c0300c0d5a002500d00c0c25505103540b003100441c460f0042c09004001c0d884140e000d41c00a009000546100e40d00860098441c2a0203480c0201112203050403c482034100b6920003440c0c0da8842005908030010f102800103050040104019544540441201c9a1030007842425107002003014400300d00d214803200035006000c0a5003049a204004080ba803ca84203d441810b00c0e5000459141285c280c6d011208082c049040402c5003008520340c4c20002868001e03401c009022600050b00100a44ca001c4220016000402ca08002c0450540b015405a0500c4409000c090200c01d40100c01a0703504005080342d442e458201b01f10901004081e03c10344800118036109180301859442074090703045034050900c1104154649500400307912481c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 658694343 1250 658693093 658693099
    0xb03180714060a0903020a0b030702061f05121c080604060501020c0607060203062106040c21030f0309020402070c240c0b070509030a2307050306010b0706090f03030c080c030402 78
    0x10359400101e0609800a15100400313280001c4401c2c0c9070f500003080b00a0a8214000090000c010011043d4040003044e4200e0340108a1041281700c417803014070014954010540240c20003405012591030805c00782188018104d07042044080e0458001c10140707080b58928070030b504080d400140c0d07500200340301e5800440034011070715200703140d103031fa074007a40c809051a03400000143c2203004c45401000850850300107200540014101800c05420000c06a0030184860003c01c0a43d0040c40005044001043e45410288480034220790190010542090044d42190000881004000c900d40070a003e40c1d080c040460003070307407411100d8454041c0c0c4229600104505000d5100403503141000c41d075001d402c601e401da18145135900441c3c00c151149104072102010344a8848854000d01007003604851007400401810345060002551344506104006043d10000f0b540c500744402c41d0080c0000340d402440e0180d460346107240050050070b0342c0224000003400100400c7c498034490003168040c640003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 658695593 1250 658694343 658694369
    0xd030612020a0b0f04080601030614010e070c0b04051e070f120b0f04060f1a030d022a0301020d02070c0815041a09010f051018020a08070c1b0b031807 66
    0x11040d10449684100103619000400f1701c00010b403010108140d6001e03520880700442c01560a02c40100da105041c1c0184a940c0c0005041203d401c4c1d0041c03546241035080f0b032001c582a1624104181441050300c03007003090f1040c0030844c00350903000050240032503540319507803030240b543d580c0150306082c80c40600034100043c04000c81c4811103019410380c0c10901903000091506103011001089401069043c0f40d0100600c00c400303600c0c5801c0c0403186c900100d5001034000c20302404a46141c070000f0010034101c2c1701c40f100285000362000d5041e124085d05002c000c42d5a04441d04060215129510604d10349103c0d1004080a0420300c1e075000740555448001102c82c0740d05030440c071358040700081a8000e0340d0368030b01c50400720314072501546010344071904264010034109184c510146107200914402c0a004004081c0c94681c040c061366400412171070048080d01d0646400201400c4480c1007403601c5c0c18070400456210380010007140a0310403c40380b609449a400f281903110070852003990058054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 658696843 1250 658695593 658695599
    0x120e0607050a09050402070b0405010c0908032a07030305030910020a020705040e0a17030106020c04180210021005040c1502010e07140d021203031b1201060f030608010e0d030612020a 80
    0x190029002e20000ea0900c038590725101c0d80401e08a070001c40003075a8120031001404203116080c400c0030700301030b020f241c82c0112b68145044640d51b4410303000000501d684c1c080710902951602e4a2141010180d403040d100041d603a410014443d41051305c1c045000c1c0200001e85580103c3c500c01c81c0d4201c410381d0064088180307800104001440d035600c02690318012403541c100081c02c40b0040118070b0f62808000e940b65410310b04c001345041d41500302e441c080d031700d410034001000207039803141550b840d41101c46c000048145807081b03050200d02c80c48042854203001c2800f0030445000e9100040c0c40031a110510720803410b84080782a030303181031143d09c016000f511040c0701e2211078100c41d80700150007410044013801280d008c1155148400300004640d0000300034803041c83c0400403844044404203801c41d0800d4000ca01c03e080410044c40b411090014480c41c200c03505010f90428002020341000801044ca24501c40d55180c42031624060b000904c0c0c0b11000c901140707040041501e65401501121585003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 658698093 1250 658696843 658696847
    0x12040302160e0402011d1003090c06020d08130206070b07030204150c081c180302160501210209030a0b0906060118060203040e15121005061005030619080d0906120e0607 74
    0x9403a08030307414030910161140c1400c7d1103220070204490001e5800040c00304003400e0220104150f6041102190800900b020a00c3e070701c143d00c4c90b0051804030740144020303080c2c4002001445022001405081071204101841c1d4055016004850703502c00500b00d103019401007151090400b02000307107000f009002c00115200c1224141c0c00c00c0203403400000b11810846610f6441800c0b00c2422001a0704c009202122151480322101c0102400c0c248452503502c0340d05c0c216021440d680c1003101c2541d02041e481442d40c0c04018295096800c6400c030741c0705040c8803984d03940700c0700211151408a140c51030342e18044090303412582d0803920103a02079070402c0d041c9800c004403514060000525000e0a80c607140150340c03896018286c581d141001064041142e41c07070002669402030150b48a40480440d10305656040012240d004c0400c565103110705204c2c0001c00e1003451186c02a441510481301c3d51051160800d1551060701c0b05070b1124403800c100c991080d425a4035031070044466800030004203804034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 658699343 1250 658698093 658698107
    0x16170406050601031d03130f03051203190501090c020c03061006030e0c1003050603100c020606061b0a0c0501032702091905100f05010f0806060c0a02030312040302160e040201 77
    0x42c4140350215112001043d08007103d170411003103c100b03400c00180d8051341194805010300a2000d10003110402d495500e4154131100ca4610b42e00a1440c0000000e401030200c039500d0012840c0d800b01000725585803c5090020200f4003507000161003845d8200e016450001030403807040e21018a12500981801403c5002e044515a101c12030302c203511004805a580d0741751440103003903c0c0d40000f40c0b0300c1e200042501c0d02580c5621034a0440c5899081c580b070ae070740825400c0e4000c400380e54a03039840a07003040b12150a048221041c1c858010700c104902006030301c0c102001101d400f42c5e000d00580140228403002039a803048014007d00c02d001078117006003000100717282d210a21541034031003100f24605000c180c4208980c135006c1d038009241c1c1880022210300c80702029040a2904883e4148400d00c00307083e030384010340200c3c410000480d600e6003050040058902c0780307502400762500d8407004422030111140a5400302d001d40200100c51034101f004248400c101ca002d2035502c511134665400540d904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 658700593 1250 658699343 658699351
    0xa0e01060305030304080a021e03070b18010903030e0d17061516060b10140d15090c02030405040b0402030c0703030b210a030f0e010c381617040605 65
    0x1552210340000c04160b040c40074501c960300812615540d00c021240090802c081c41904a00150a250300d928980f04c000054500ca1a80049000300c652146161644a06903020400800350b081041c00010541d01d90002010b50706820211002c03811401000d0761b03450300c0708000080002441000450510f08a5614442020000400e5261010700e40040a1448154400f691090744541b60082c0900300340c210b001c0d4441a5191202050000c007451007054030404200702a640d03112024080c014040f01004001001030171780401c0549070718030700607440360010b00c2610702c01e502d0884c11189030300b414001c8912903810042540e2074860680d4043e8020100310340c440342c02c1f2001200ba100c00f58110101005450041e20041c100c1711107502d8024031000500c82c0340c034100004049544581d0340c02603492054150b100d00383c102c0c0404904210b07a00f101d0040c180031a401a4214210469442840054041d196103050361411542d0360b001a00d80030859812010214166070016010070b905911590f00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 658701843 1250 658700593 658700621
    0xd0c021c0c060c020d021011070209010806010608010509070504060c050c101218050d080c0c192907050d42050105040b16140c1014161406090c18040b0a 67
    0x140027454001c42d2404809800c010a1035004000520420760401c0d641c1d80101811a0351a8180c078007c0c80081c00b0b400349100c0c41c0140300003d1040010040107100003040c00300050102c070b01c091840c0d0001460404a9040e6105141c82c00c04c140e21500e5108141515294001c00108041c00c3c1d0070100f1101c10b1070042c45c0c00202d82d0705110f0011240c2c420711a4440c04d1400e050a424280080d08214104100c0c904140181c0c010501c0c9002e002020300a406500034890b040413900d4640840c1b000b000351070b017012000c00e499549900e0303900744049005640543d103e21030100c0e84100207a010010840154003410b4041401448100310312016040285030181e05201c50f412468081d9a0318100c1003811003650030281c1001ca0900c0f21818900e031002d5943ca81d61a09415403402107841040c9885061402c5807039180f846440014030100d03880103151005c40d001125514039000c3e6005856a41000085100300882e4001c1c50120f445441e21500903900f12202e1403061b151815400b004220020700090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 658703093 1250 658701843 658701847
    0x9060c32121201091407030f0b06030a0c08010806010e010b180d30080a05060103090b0f010e0c0f090409240b0f03030c030d0c021c0c060c020d021011 66
    0x281a42071040700054003469460300c1c1c851404400c1c006840d001608032200281c50220a1889030201e1081c1d17503001005030800080c1c040c1c901c00200c0180035851810b5030803907000410300820000c1648056145040d81d982c084280c1d0300c41c1e030040d40b602c01c20300c00c10b200428080f005000300b001d03a000818041071500340c000c000000100202e034528081c90700591310b90480f070100065038014200480c05241421a58082000c01a01c002d0420310001e0082545181c4d120001501c4d40d0017030f84644003a07500009019031906d01030a202c04014400d024246500e403001010400f1455148103032150b580300860004c5c182441d207000d100042c150700c00e05644000600211418000c3c00740c00b550a050f04000c00400c90b0b10b488414032011110044600d4001da204100d48402482c011054900140c8030145c049821512110228a030804c66810106c583c0d1480c44580d0005400400c0c8403003440c8280820f005039003054005a031210070f0031402c140580c2220311000040304039540a84100844404840c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 658704343 1250 658703093 658703183
    0x50306060d1a15040903031406040e0709020d06051f110304030f0807020a15120b0922301b080d110f0705150f04240e0f070609060c 58
    0x241a540707081720540c0841c1d82c610750000d4442e146080a68070550554042c02491504003506036140020320540b100355601048007160229550040002440c00914441d03010140701002030042681e60000700100c0c0701030380f0708800d10340040283c80440341c000d030900e858481540c45402641d800300c0c0040368040c50601c1c0c089084407026000306480c4080d0760710031108080d03031100712088030700400c9914070400454007004100c20308141c0b0000c1170008903400c1c16a0f0383d041e1400b0110004492048140a51550280328254000041c8039048030142c3c0d4a02c0e000e02500c20000e0410100c800018049400400a00d0300f4242c09401c00070310502c0c142d003500c0c42c3c001070000d0418a0f4222840499294201c03c0248100c11014020541c021b152103408403403070b042655a060740407032608682400601c09071007000d61a182ca600001c890780c0c1040c15586588c0a182e21aa2111031502403071001c00c00c00d00c00484d600344200905540320381d02141d151104034a010302614135001c940d000c100000000400a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 658705593 1250 658704343 658704349
    0x28170c010504052811150c03070303090b13020a060e0d051e0d11060a0b0d0203011a101418150d1401140f090601090902040f050306060d1a15 62
    0x41da22482c02900548008000c01980101d075145042c0c1e40401000d48000c5100413442808100c40d402c5411141c03419142d030040b5080d1041e01038540e40d440180004a10348080c9501600040100c9108218103240d5076181220030308040c1c403120019401c601d00007410701c0700c1405103d9800790340710300902c000207142c1e2075950300303140400a042444041e600e50075408404134080020348090b11075400c0446a07505101c1c1c026a540300004c14101e0b0080c1c0343c0c0c6000025484248150002039000350083c0910389404e0351111540003030050542c02a01000c0c2c3c03403000300e07200d0032450b4441e820030510980b9000c920407242041030550b100e800d9100c80001c00300c2d0484004070005101b03441d4040c0f004548240030040d440c0d24504140d10100050028030740b650500e42d942000300d14060301c1200c14000944440b0012a0b002540390040750180381300040201d0140268941041110411002c0360807076560a001d00501c8240035000808580103207005420071001004510382c007404810a113204074a0301000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 658706843 1250 658705593 658705601
    0x3020c070b12070201050403141c0e340314030c01090f030806030a020f011d031603051002131203020109051506030c150f0a030605040903080928170c01 67
    0x11601c4521800034040c500a9450000c1552010903030008000a24042d140504240c454480300301d4405c1001911000100700d402038107041000c248000c02c00c0305105811a0355800c0d6006503814204441e88c0c0e11340441c090b040703403107008040c400071208200b882c1d0f45c0c0f081030f001c40c44400740f580d40c0001d0007001d4515400744134004080d8090304001c201184c0c141000f600040c00908441d00076040b1002d40c0c00036803200b84c0300503030a50081ca45000c01883c2c8440d1000511100c00405615005241801414106901964055a0042b400c0e24040c0d0000b6807600224411402500041c164810040045840e5211005107040c006c0c00003041240c0d140e9a6076003003061043c11009400d1020040c00f0107400d0030005900f00900c2070300c95049003ea001e01d050750b42c0c01001da15803c00341c000a181c041c2c0c54072980107000140f01c040d1060040342c441c1d01d03014014800446022109108800041c1c0749015003008110b40728618509078201c41c1000d40700e842c000140329a0704600060101700780d1820800901c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 658708093 1250 658706843 658706849
    0x714030a06051006180f03030e0105070c080c0307090506130e03041518061716091a220605040e0c0405120a0203010c0f020322051002030c0d09210303020c07 69
    0x40107100f4542081006800b001800c0c140c5c0e003040d006240184004e40a00e00e080c0d080d660135040602003407050038012036441c03040da017004102121060000960100c002111040200b0031001c0e280c00d00e41b0340803640d04840c001c544050f400b080c00798009440d68219403145010140c103c00356450725444010881c00881325864160014030b850594081060244030241f026010b646014964289005140c0424140c06000c1803d081600b00504440302d0050710100d00800c00c000000c2c0c420080001400c03001e40000b03228820b500601d4082e8044007445c100206e080c4c1f2441d44406040600303040c00c5210103400101180c495030010030003c25a660341c40e01d040c0c5120107090040c5940b41462040c9420340344221000b01c148450300f04040c80064010040d42d4008404004203207824041c00751040402030aa800b4a0704401b0015413403a81940c00704c028500b01c03e03004202c80c101a07808604840c58645031007400040150100703080554030b0705c810000e4a0038001e18001d418030288441260410315580c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 658709343 1250 658708093 658708111
    0x50f0109081504031202040302181f0602011407080702060a020a0311031305071a07142508060c0423011e0e0f090c030103080c0109060c1d0a03050714030a0605 70
    0x1c00c100130941e000082c00546000c49000303500309891680860071162035104503821a0512000040342010b440c1c0e440860780300c0c0c03200b031520100d80e00c000c040d009010104180c01004100d00000b003015000c0c0380702a003c0d81641c2d0040c042a510f550090009411030351010342007581398128104031146e1f0078041c500075525124008004041440c0c01440d01c01c1c95844400400a1011506003011000e01540e002e15008802a102c0c1405540b1440c10994148000c1402e0710030f180154000d2442802d50000380d032a06021503040351202c0303d200002d0302451003040525259802c20850310104003503060742160301814124280c2d6142d021412007064861100000038100c40069a01c525024802d0f00101600b560752410606003086c1c104001c3c40140000350011100091100d0b48440940c0000480b0303401540410545800b060018030382e903801611034102000c4a1100d11480c0307010040700048940c090000d088440c81c0c64000e503a01d00020344619031500a0302440340101d0118046e50b40b14507002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 658710593 1250 658709343 658709383
    0x504031101050f01180906020706180c0b03040803070f030b09010602031c091104050705250b151e0f090a0204080f12251a010503100b0307050f010908 66
    0x100c2880d42150030081c04070a805102c10300420840c1000e615105c507521081c000803500c0c64182c1082e44c060710400d60028102490300c2c83c2444124a00c2e04c09081c2244141c0b034a50419944040e001141d0205580c064050b2000f0000b082c08940120100f042900c071724140400c410501900082504400b41d020790003507000000d00e910500c2c2040d00b00329140f513844500300328058035612004000c0000341c41d007602441e81c40c00802d04a5000d281aa250010044a0341405869952400031005410301c82291020f141d076021030800d083e103000c0f1041c01d02002e0046500c220503400c0c091103590010b1107050700701481d640b0510150f10b0362550f00f1304c181a501000b587d598680021179207402c80d60507400c2450b40000c4255690381d40d2600494115003410803c5400e034008a83c5551140300302d0050013005580004122088a803008418070b048031421003d80d00c20701c0c2071364606004e460700031206503417580019509208a142249211505080600d080350095844c2c110451030001c590000702d90708049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 658711843 1250 658710593 658710617
    0x180e0a050702101503080c07080a03050a020705010c020f04150b0d0207021005030606030109110f071202061b0405120a020a1e080a0b060d060902090106091e0305062404050403 77
    0x400003511100030f2058104400c01000e0140d41c40f40c4400d0000070000b200000399840c1441082042c000a40081020b03148600f40515000d02560b000071804005406401400105d96000348070700840280c000c3c06005000170750b041080020121404451040280c590000c40d85038000c0d0054682c2d03d02c901c1d00140d4802840c01003146503a41c2c90450401c1190400c04c00c0b4041d11010152411103044010108100d0010100300040c1d005482c03003050040c01c0401c03044280844124418441d088603000c1d60017940b82d0341d490909092100f00c40340580320701040100214100807908008082605058484400240c2d0006901c1d903c15880001c7c040c000e10068074100500c50310440080c980c580042618040c039076207904030482d005103000e2050000781d441030240405600842000c40d4000c00b82015980c48480150600e441030148440ca400000380701a01d8102c0f04595009481c0c02c08001c28140d80c0c1d01d451440c80c43d82c0d900c1410722611012810100b6901c80380101c1d405503100c1d8580d001e02d410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 658713093 1250 658711843 658711847
    0xc0c1c11070b031b1e0a091401020d09060c11060c06061c03090608090a061401060e0a03020f060708071502090f0409260c1009030215070f180e0a0507 66
    0x2550700b0196101500704140003e212441207000031200f0360342501030702c4540c000c221002801e0085c85101c1d85d0840068441c009590101c10001520a40c02c1c072004031545907001207994094003000e281c08178660f0f507001d000f59801030440100480c031581801000403a00d00c046503240d0054404001150f0002c41401038520b821003855481010595400f6807003540707601c0051044101e440380000740444000840c80c0024180500745c0300503008071050040d04d0290700201000b2000340704920000302520420880340c500301d0700241c12250000d10802182401600300030150f40305180071224880704000700300025404401c0941425400c001c0140c54080c03030000e02416502c11034883c2d1003240f41c4205a0001104008501a596101005401a005039519002140c80340000f8090b41c0c0c8140100b12065160301e402602e8064400d600b905da21074242c0b03103c10b00100c003d81d00c40c3d0105485558050807103114403d01ea5800d4100f581c54a8440d80d64107d800b105201903800034181a12442001112a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 658714343 1250 658713093 658713103
    0x1e1c0c0503060408040e07170f010f05012102091216140a031e080d02371d04060306050703020310080f0706360608070302120c0c1c11 59
    0x907009021075103020fa40d9a15103204900038420b41d00100404228400c0c80744030307080202c80c41500a4030031b608112003421440c0000740301d01621000441004503a5501c46c08d440c800060891141e0084801212845400b07074006071550b5030042e41112521504030410001c0300308240190510810b4103007420301c20320282640381d00c1c0b41d0003608101c50420004422440c01045da0055810300d0200d0f1400789403030000c61003845011048180040b170b0140050040c44503411004503104500304440c010303c414400041030305000500402d00d02119011128001d00d40c040074003800410000341d258480c0c4d2554200c0d002a14908006540442041030f5100d40c81c40c114042c02c0104020700d207414445040035945e41460081104010f110160320740b00d200c0200d0500c41c90300048000c0741089a01d11003010110b0050b00c01c0f440021428000314440034024401c44030350140d0311040019650383c400c0c0350760303241e80410040c0b0303840c0c8190f415081c00341c1150041303c2e01d800b407280d940154038004002502d01d04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 658715593 1250 658714343 658714349
    0x30111270d2f010c08031005060415030e010c090317042c070201060308091012050112050610030c12051c020c1005270a18150e040b061e1c0c 62
    0x22420110b00301c0d485a81200600e0000c40e48031180d41d689031344008003c20f203007080380d0080380c1241c0081004200856102c840503030380c500b0303030303504021422848a681d0709880b007900011010694030f40c420700100e45040c1c1d14480c402101c3c0007061a0955454a6a4807046a10088200c1a545400b550400c68010080c03c0c0c01030a9031009200c00380c11038845180074410000302034440c8905004031818540507031400a00004000420006980e42e6988009030100c4404110b42c20b010b1f1400068018180002c1c03032090301d81203030440020600740380505a5100c030019054415100310304004200c000b000802d0900001143c2c09042280f10381c0081c40b1890b440000024103000e01807004400b01c80403203980e080d12580c1d81500728840c2d07610a0100c1c490f00c030141c2100d90039002e40714840c02d021510f0340029501102d2407840030342c829681c05c202c0154a200781e40040023540c05001041c03041c9486e4150041da440e00320440250b25400c1130014030540001e401e1040c00d038084415010502400b20030550003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 658716843 1250 658715593 658715663
    0xd090c08030d061a0c10020c010e031902190f020d02132d1a040c030209060a030b0f1e12012403020a0b030c0a0c05100212040c05030111270d 62
    0x1001c05c40e0640c01d44444040303244084199000c00d02004c80c5209400514041000c88140d07580c03a0030f0400f04003542e07413460000b0000341c0314180b20f4101041041c41403030078040d00a0702c80b10101405a080150005010000b40d0b0300c8a80080c07031285240c0b052041c40c8007600c021441000661f1140404081c003840700c0340880300e45280c04110b00903101d0704266100401811500042e031003958801c2540280900103049400440109440c1c1e6a1034040d8801c0f0f903c0c000440c1d0312406520301000f0400311100d40b6901e81190044d40c045081c0c82d040c2244860f02c0c003a69100007081440c00300050b0034040c0025508180e904608903000c02c258280760308042c000d0925103a155180d071400f5403800c1c805101e41e0728114100104080090107000050101030800382d1140010340d900c0d0064021071043c19425141610705071540080000d462505104540840008004103410841c600d9a2200b100140d5130070f0206000e8108446c001c1360743d4015000c0386043c0700b80c0803c681c020707500e6000c1c41200c0c1e0b88822929 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 658718093 1250 658716843 658716847
    0xe0607030b0a0e060a0902030705221809060b04020a0207061206080d080a140a02030103110f1315050a080d08100b0d050703020903011b030b030309060d090c08030d061a 74
    0x6595201da452a1054075201d000030f00300c9448041c085003552184e603001d40e5125101000b4400203c0d8010000e121411011840f0000c0c6101000c10b0035200c0824812000e1129402c2d2030148403002c3c1c0d8004c50b42c240d00801d80020701040c010040390a0343d0102c45440016001641e050183c1a00715414580000700180208440c034241010680d90350b600003291000e01010400050365204c00340c01003902100d83c961609030a05001c1012801794100b800304640070803260079440c0207800c04c20294641c80710010801120022900c0c8024020480c0004007202110400b1000c200350b1640800f050082540c04010640c81c000c451008111a5010746400240d01425808120020901e00ad0710750602030203200144503220407500b50020f100712512035425500b45070b26176a00c01c60012240c41340d103015880501207400104105900d074400c1240e4242d0094043c880d43c00c401405511401c009445841e0b13a840003900d0f0119645950001006517000e01d4840d9428003412854507020300820307003408a440c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 658719343 1250 658718093 658718111
    0xf060e01030b04080c0a1a070806180604020f0405041a0418080403060c1209050f061e04140109050a2103020a050a0c021906030204090c11120304061e0e060703 70
    0x40300840b8054005402c22002040b8840021400d10500c5001d03079000350f90904668800d21403400a840442e00b401c0455140300000710079003050303a5542440700f01003d03d41042d56a82040000039003004040c4a040301082c440407034103450354407500010852040303200308810006801c1009803400c4103440d112940e41001c850700090310720f40c02d407803c5d6680000080740b12001800704541600911404503c0c1382e0900720400f0511101103050b036200660441601c030309985a42c0146210411b00d02e224040101500004000c15003134220280002403103000441e4001503612410710b0314000820584450700201c0400703600d41d4500251007420b4021f400c06505000780008040c4c01e078042c1c2c2d00740b40c050105a00440c000c40d5550034061607aa0006000292119200c01c0010001c1d00079000d0415128901907a4600c0305000d200519040e91494006001003140c07840000c03001d070405030040b200e481c3c90364290800c1080c0700c50b00305924415810006010b03464440503506e440009003c13a014103240c41c00399 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658720593 1250 658719343 658719353
    0x30a0c230c2107271e05060a120f020415060801091406010906180f060c020405060a082a060304060b0906090712110d020d0605120d090e0703020d0f0f060e0103 70
    0x3c81140d8544000d4910302612100e264800c1c0800b52415048502d440794400c107406030806444901c040d00e00041290b503459009000101420303000d0600b48080241d0b5280015040c4407640e0022840034001158001c1c0311504500d404d030302d035000a070100f145600140510500e81c41f481c50705135030701d00d0001258201100043e0510445000b45010400600141c40c01c1d4030340380412000610840342c007400700d9a40ca08004000b611018000c0344200c0c14000400c0840c98031013100002d441008000d00030808001c003240c2c110400302949900d1110038022361185941e5503501440c425800303601e000c560004100d0420590501c020005403055140906001041e90301c0824100c0e074101815001522100c2c41c0400080d078041c884518810a0001074011244030241c2c010104071003050340c401c1c0701c4910603404c0a0300c0d5110041008002419800100401c030300c29071100745c2145180c100140380c4031311002000c0540703410401840026407180748038444400c0c2c4d48600c4004005074141c1c2c1c1e0841d41590b80e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658721843 1250 658720593 658720603
    0x614090d1211091201090b040b0601030f0e0c2b0c0504111824041206050f0f15120a050a140a020d080a0905060d0e0c0103020309030a0c230c21 63
    0x5144d008044092154040c08000d5105640058100070070040034138080c41c0c00c1025031011074107030340000c1c1001c00381c4808030881d0241404009209000e840c82100000600c803404005080c0f0040c9200c0c154414440c2002000c61081d0840c010102d0025450601c0e06201c184c94400c0c845981c220400c100e0390140c04d40c90800e0f001201421107050280a185001c024030404541307154004100340050001384100c015600410124401c0c0030a110b20b5079000464403001c0d90840f5007402c800b2407240091100280245510760130140203200120366600c40408924108452400321510781c4240310300f2041c8440700c1c41c2445440300140043c0110307141a8007040c0c01d2009924002d1101d500410001560380c0503074490005000080c0515484103400c00c03034100605202d4015510740d028010b1201942c3d4400e00899200d0f40d101c0005600e008800541240ca006205a0613245d1100d41440b00c21450300400c0324038a0701403030100a040400d0510100b2006056500b0303d90030002a950000c1602040455 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658723093 1250 658721843 658721857
    0x130806062b020a080f16061809050c0706060e07020c1f0302030406110c0307030807030b06031909080c010212010e040308071116030c082a04090614090d1211 69
    0x203244071055001d44086404444182c000480700c0c09108861400030348001510700e991541c903035070000300c1a5180410364010319001101c4060b54505c52091180240035002140c000c220761508a1400c41b468646000b180c14541113080c040c0588803d003c07444e42d04100f2681c1301e04042720b806849607061000d4042d00c1421011034414160044009000d0110365841001c2088540700c000d030340c0b0090400500d40300d9100c44001c80119074514040340000380300b44542c030742d80000900114a140c54001c200282d0704107000003c81d03030b240c495081d0000540742a000d05007040c0d00728005600d030741e02c000028086d464141c10a01c404d40b011410000030990086e14260481c2031400d0800c0e9415400d403c1c2405c00d03030101600300c02c1842c0c0100c00020080c0315074000003202c800c4026100d800742d03042c0c1107802c038030b030100e00101c09141c008000d0559841c1691000060790300c603800021394007003035030884440441c0c11504040d06070010840060b42070b4004c0d0882c880300240c60000c01c84180440d0403000d041c05020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658724343 1250 658723093 658723159
    0x60105090a150317040608010e010807090b03010b1306080d110a06020307200a110306072723120604030f080c0912010b01021204050121090813080606 66
    0x4503842280c52034082c00303402a5402440c003e03078140041502c08299441881204000b0b03000c40700000e0300c0c0054480071416507221f100038100349440d0588050280051404040d8555660000706409603501d0184000c00700f011a0041009d91400f814182010401c2c0380401c1400070b24406081c44507000315030310b40321a9000700c00513103035151000200c0b04040500711905030540e214414030071301c4c8400508058100c0c41090031071000a04a014540c40707117000d580da0408248010301c2407154028207440344100700707c0005902c0441e0780d10404681c0c003c006001c0c44030b025145007000c100c24202000034034045414000141601e080a0b82e0040600441880d11010000d0510124200842c08021601c0a0740010a103c4021241031661402002d5200c040340c058030844411000400c030600c262401c03158142c49107202145020522020301003101c5022080c0c0d036980d0750b10400140f21b00040c0c452181d650210118050a109001e4030b400000361416201d154500c00d514850418002031502c010500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658725593 1250 658724343 658724351
    0xe01031704050d0302010e060a0b1f020c040911041413080d14180d02160905090f0a051b01231804021801090510020c010f02030d020a05040611060105090a 68
    0x34412031a001d290881c1d40e0000c141c000c0302c01803584c15080341ca51482e01e90156242a110000201c0449000b411001d030488041e0080c0040b1007450b21107914441414010346468601c600001022510454000c075041c901d49400341030700d130405200d6040030148588001c03c4608181d80c09a40200c110b407001424851300040a10915074a6005100c1c04010031525003040d00f0044203940c40b01c2080c2e041c075012071007240204c0c0c03071071840000c0310980b4000300e010584c182820700600b10060300c0c00600f990001e205d1050803501c0e00d503007000b0882603e40a50080d046c110b00c007a6499126000200ea03040c10022806487d5801103408428500031000c080981561a070842d085404007440000003954007520118800d091925904844442c90009036600d0099684400800807400903260441c0c0041e0f000820498481d4000c07a03101c4944400c1e801281d05142030b03516081c00344c0e403200303441400107200824104111a04454040a0916104081c1c8031940c10800070400400c40101429111500c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658726843 1250 658725593 658725623
    0x110f06070239062d281b020f0d1202100207031205090c120102031605070b01050118030b040c090e030c060c0f13150e03151b0d0e0a060c03060e0103 65
    0x300c00c1104070568103002d0955141140643e01e6071590054100140000c01c0104240d8280001445c4030ba0b405c9016140c690400c180968640c101c807407400422a040003010a4030449580d070800c4450202d4400c503a0302d100440c0203c0003e00b0444071000440c40d1500500c14280029040320707025035459601d0200182c01d55a26011501d00b201c24003070a900025081e00280e904a010b400070740c0b00b0400e0701c0300c0501d4068041c0080f100d070301c80c01a000e0180400342d401030040358400c682c0441c1ca0b02d03409452050742504d9442e80e10240740103a07002c5803001d546220801c440c076000d004d003c805550440240d814480b00301c0189444840040010802d07500004403078206a48000c16121000507d681200801d611803140360042c0110188440204803240e81c9203c01e840d002482d08030300d41c421045107a00d03444452810000440580701803000600c14001c21070303c10300600c0f0320b038a0003a144008040f1464282416000c4900e10903050f4101410041e0901441d5074840c00e41d81180c1c0d01c40d91a10364140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658728093 1250 658726843 658726867
    0x18050124050d111e090a0608060c040e1b0f030c030103020103061202090403120e01061e0b1c050606160516060807020d0507020406050316060306080a030f110f0607023906 75
    0x2c05101d41c541c5c016540c00c1408401c038202c0d071150080d55024012030302c098a814880c440c190042e44165152180c1d040f00152042041401da61618400d41d100103082030031805001ca0707250011107502094460100040003950f9040c01094000e10300c084180c8042c0d00d95802140503020000c00140a010ba040001c0d80c0040030750f444400b0240e03100d402004880c1d20307803048400c042040713402c44410341840c1c080400c60110034001c995441c0e042c004402030f403014405102d006044028042076200b001807002900102640300145001c91062018000d003140d8070b071501075038403056007040c4208628581042407544d0000f80f070100c0800700e0304155854911034400a400b0f070009400c51601400b810f201c1c80c3d00c8070715030340c040e600340d03a07040e00d05001190f02c030020940d0f02c0c4032007900a07000a010501e10301300c0703034010300410f4503111141060b110310f46201b469440c03500c0e1090301e50500580c0700200311502125004048406411f0724980341c149040b45800340b207110032009a095110f5580013500303280040d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658729343 1250 658728093 658728139
    0x21302030603281110020c10230a08090d09140a0b0c0d09090e030712030b0d120f0504050f090720030d0f0e1018050124050d11 56
    0x80c107420361150240f14800080d1041e00000c140c11550035040524480007071401d5030095000c21501e03801040c070030f0750302ca0400c080340880c180d64100348500100b02050030240300c41000a04002c1c1600e10f60380c0c80285000030000400109030f20b1243d008640c0303200c10343e60700c861094111000d041900490308101c03000900304210319800525002c10000d180041100c1c0403501c26407111450701e81c0c005250340c40001100340d9503990004201500200720180c00503a0241078821210520300e00050350b880b01c02c002c1081013442075000c0d900302038540c10600d14594440664041c0e000189403a0341040d00c0e181c0815a05c022191038540b01c0c2100da4002250140f01e91203981044000031840200c00030130303041058407170380244030300300600381441100e09500000d8061104402207400085c54020a08041207009042d09017201001e03481c2c101c1c02c400401c2c024040e0880d484000319405180c05902d000312040c510290740302c940100c150103900307070100da18090000d00804065541200c40b03044400701414071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658730593 1250 658729343 658729363
    0x90e030c061005040c021f0f020712020c0f04060f030f0f080a1d010804261b030306120a03020d030e150903070303061a0a110a0605010b13090504021302030603 70
    0x28400c080800c4064201401c0070070032a00290707130400c09840c82e000c0490311b902c90a108001154151902c207403032400598000701e1701000080300141012456503070140c1d00071805080200680c4000d2100180345070a0f420000550f2003160300700b0010f4a02000440c80e0031583c4000341c2015220f0303040c0f43c1444070300311000b00001da0040455503215107001e8042c100c141e2a460703000307414aa040038807196500440241d40950b402111545450700d410315403850740384441c01d1060403000c003886062554000e08820046480d030403070113141c883c640b500c01c2c84a8403034520284e0401e540264400400709401282e0f210f42800399103400714600c00b2503048d0914081c0708400112074400d292040148840022015000c0d5501c20f41d81800746035503d2a0303180c041c00c09204409000b150411491103403902071300c00c1003c940c40d5181236844200720741d01c800702140d400b6800075100483c00920386a030b03403209240480292502c1c5404220740d040540224000885c541d801060b000d40c008081042540e0411402c011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658731843 1250 658730593 658730617
    0x1c2306060d020304150b031902040c020f011b2304050910030f0b070201050f040b0106211107030216062f0d02010b0102100b092d0a0911040b0a090e03 66
    0x40c9052a00d1726280c9101903948800d0007601d0b03c22034150615000c03540c60607200d0142d285100101d000d408000003020b5001801056129200302420701c850300303020700e090101088000c012300c00b0342410b01a00e5206550043d003420b5028602104100c410a01913400707480c42074484403800d544a101c55030b00c0300550b41001d0310b02e03600558008100840d007000e0b140308402c65030081c00542c540b00340b800e00d000c030143d80003488503d54400501040344a00201206060810351000c4880005c00c000c1381100d1000e81d003646482e000103540d07014035404000c0b00b000604c00300c0f00f0b00d028600c0e1500c0105980d80c5401c0c0d40701c1000041e100e002c005036a00601440381e111500942e2481749440b2000380c000d088401031980540a5082c0ca03850700003503845042c2c824080907001e240aa40c44a090116800551000036661034111035504000d480d19000c007886020300f1034000038109c0703603401c00080001c0d240408a105508150004a0b69250400440b00311f13030800764082003030004040440d085005d140c207a004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658733093 1250 658731843 658731847
    0x60e01090f0b07121b030503090a0204020c160f080706050306010c051b0103110a0806120106030b07050306041406011b02150a0e0f092503060b07081c2306060d02 71
    0x2455400070070091603814440c0c2140b0800c0c210395002a0317411103031501078414403c40001c051002c6401080210343c00543c40068510745030b00d0354000343c200c3c0c00034004850b042d84a03c01440c0c3d00000400307000090310301801c2d00c00805141000460381c4920038015041005804008505640d01418502105d603500c0000c0d98240041001c801e00041c1680c140c1c540082c0c140241d499000c6103000c115810200107036070b00385a6a8a00c0184100003031504100e245565031224000046140100d1941c010040703556100d582e401c041041105031041c840601c80b0300304141080c0040340c2e8004607140080000c00410151015590000408408102c3d090700b00c54013000030710300c00507039000341355903c0c1810840d000d22503411103205014038104200c443c0100c0d8907000d003507500c1034a401240750340c00c01c40324036021840c583c0390100890140c00042003154406004594020b040d010248551540300300e04408025075030002c00c00d507520400c50080d01c1071200c90000402c101b501c038a411a80107058900c8155 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658734343 1250 658733093 658733099
    0x304120318060f0b010906050406020d0c0c0f0303050301030311150f0a1d07181a01181a030910140c130f0605120903090109140d0219050103150e01060e01090f 70
    0xf0042c0031000601800920031080c081201405401030350190740c03c0e41d005021900d91030005442100364000706036080c5003a4680000d55131140001c08004d544607965454032545035185c0a0030048000802c50842d07000719801c410001d060500c5194840e003100f000c80713000e03150403601718000d18040c00c041700840074040302d409a400000070320008644504400f0200f91780403410000440d0500616118a0b000340c0707020750141d41c8180b14800c0c18040b0f100c0c0c00600160380304c2003403c8452410340c0b596026500402040840f00d800d100e02001d41190040920658a0b1642c1400803808003c000c01030080b00460480b081924510910004d00407100c85040c1c90360310344d40d0190040c2c1019450f49820502800001c00341d410200503602207038011f85480d1412424440d404003001090f4000a4201802d001c50b040503907243c1240e0180341903088000da98480c05c060005040c2e81e4981d5600e007031440c040404001030900b4414081c110703400707882e1131920182070310012100c0031075507403008204030340400001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658735593 1250 658734343 658734371
    0x60506030601050d1d1e1b01031d0a240c0807050c03091c0b0c1312140a0f020f0109030206090d020a0803030403050c0705040c05180f1309020306090102030412031806 73
    0x841b07000c4074944080440180d02007400c50303503240c5003039140d4049001c80c0d400e03080c90350003500090035914455009000740441001d42c1864001080000d4516442d1100c42c0f2108404102c541c4903c1c41d11184240200c1c0103203400506078845c09002e02c2c0c108000000c1c0d83c0580e40c0c0031700940303120b00c5004050103260010a1014407045014a600780c1d0001c000074046440340c1174000c211000101c0c07000818280c0c600d0706020000300740502c6404c0c1c1d001286541c20449020040c414521038907c40d240342815009180103115070070008000c654140a004802440540e956405907800400101c5500d0760802d018804160903004650204143c0e110220500c0304054012010704213403e10030040743c04150740c400400050781c001507521300110300f00b000100d02d0070340c400422500505000c0c2a1030100c490000126050100c86150040040c1c6d45826080031880e0510260b90040e102c1d600944c02c0d410143c4030425003c0100b4100002c2c180e942c1d203072101400b483c91101c05100d4124508021a158200f06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658736843 1250 658735593 658735603
    0xd08090906040b3114040b090a1e1a0c0f0f070c060c2021010608030c030405130902010905060a12091101030c080103032a0519020a09060506030601050d1d 68
    0x14108511012041d005081044d104500315110403117904800c41d10b40c1e445900000b40082c00034011070240e004100e01068854094400780303510501ea00b4900201c40c00c0ca071003894034808020100c000d400f418082ea0540403015121100c402018103992101860310001251103500e03001403201e8007051000079983c0d0440c400320300c40350041c0d00280440c2d4001d914481004803859807203501100102d03007801c0c140d2903160a1002c0c50f40510002801d83e0301c444811b0310395040b00f05c2803400c0b9440081c080c001820039450440025616200502c461142079001030001c4805004040c081d10010031030300c4106208100449420640b540204188491424460440e10950301c4d9203010a0500701500fa481e8855503a00341241d425503150f641d2402c5602d4802c0000a180101c4142440e8010b0f001c40407600a0012154811614400340e55031301503403041c0081300c2c00c960b11940c0038501d00401006140c0f01c0000300c80e031000c804d11306669210341c110388081c003e240c0440c4c00400b12000d00310502d101580003903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658738093 1250 658736843 658736899
    0x312010807051201050949031a0d03180902070317060102030c0a080a020a0c0e0a0e371505010623070f020102030c060c03150d08090906040b 62
    0x5031a1000d80c204082c00f9003614000d4448000380d0784400a07a0814054590705000352900b08039842900310000700c40d042d55011150400b925002034809503900064040c4501e2452007907201c032629400c00c0b0700c0c0004800e0b64203800081c0a0101052082000d000402c10f000042e004000086445800c90309004080014106d86054900c0300720707006c6081503000006481984240c3c40c000c0c01c0402999440303c0031500003c000d80258460106030f1400101c0c48210440130305800e008070060351800040d181c0c2918150391101c98103801095000b05d01d51440b000c40410001e0f1803410b40e05400500c4442c2d10f100c11210b801408041d07041000c0b00d4040e4090b000581201d445544846034400a00d1125040980c04e294221117000700300001000614440d10030f2041600500689081c4446200c00600700182243c4241c94140d0020030002c01b004003c000041d5000c1c00e803034000c08000c0e0b41e1344021540c410030b01441e11400c130003000208155642d81100c805100c01522104071944402c40c1708001c440110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658739343 1250 658738093 658738099
    0x70f09140105060a201e06070309170f090a1e0f21020f03190302070b04030b07030f0b041a0f1f0c110928062402031201080705 56
    0x10880c110022445086581a90001400e4034600038182c10300382c40705102ca171050250b00b0340004000c140c8100078850041070400c2c00740c21040c65400b946142e070400034003c04803400c0c140340c1039019020441c5110b180c08001d07031080301c10f951100b04910718000c80c0a2a000c2a60003100c00c4800f0840308041041203418030000181400d5050700d81e10800c041840c24020100d55140300803280e250b0002c42c0042d180324900140040e0b110f1203448001c41d0030014010301c018079641105000a00b0140d0401c5200002c2c42119030351414182199901d5100080280c0300c0003c00da143d20300e00c10401610b900c02800004020401c0000074110741c101481108240c0f540c0e44500b0303516040d410182445040c17200d0002003048415141c505018044d03c2080102c5402c0c1c5840c00300780160002c1c1c0e2111040203000b42100aa4014600c038a148020340401100000f100801d042c51410010807140b02c9249144020301c49000070301a00d04a01203186000304107000c0c2080200800000308000040f07903000c00d0391019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658740593 1250 658739343 658739351
    0x7031e060f11090f13051f0b120621070e0106090f1a22290a08010e072f01060b07201201020c010c0f0e031209040905070f09 55
    0x40c0400c800c49803030014031034011004000e0031a6600d004020103042c840000d002d040174080c51854601211003c450030589217020340c181505104050384440001d005130340b1401d1070106440e00103c12000d0280c4110b000b100702c440d51240c05501c04034100c1c983c203c00400c40b82d8145e600e40c00d50324126020710a03100442c841c1d00010583c8204c0c6d800d100291105c2140b21248443c45090710000340d80410414100140e580080c180d0714003200410000401d50120b41d40c480135959002c4030000c554203002e8034040d02c0204a0024030a070402080c41c11030b0a808080c01d110764800c002a22006100360700c4d00040801452800121070070b14101211484180c4000c201e41ca880f50559103c51081e098040c001400f448103008503060030065154104002600e4102940c861051250130390308404c001c2045651501e0000c030f170031640809414980002072601001c21040200070a45850403180709800c005000607001d02251565001010095070180444210315500e550a1072515164010021102d0038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658741843 1250 658740593 658740611
    0xf080a0c0303051602150a1b030b030706030c200708010c030218010203070510020c0705100807031103060a0302010302090f0303040e090c06030f060918010c020a171201030b0907031e06 81
    0x8124004d500342085800802101c610007000003010840144100801a22800000c0c501400c014819030201210789010400302520410182444681e4215104141c03400021440055020140c44407041152490a01c00d0041c40300d282d00f80606d03604498210341c03c0121460105505500400c890340810745403280c3d00d20240012a2280f2808002904030b43c0022a00302030391040d5402040140302260441301501e9594002c14141a0000c2d5483d000c03820341070410600310341501660f1940d14140070601d1440c030b051000118030f40e80c140006410103a02040900709a1181c140c3d4440780000202141e88450b55070040b42c0d6101d2040b140e184442c0a40510311800d41045400e07640581b8054068442c2c0b0360f645400d11138bc4da10020807075000e20504440000c2d09038000c0c81100030095007a4003030031506c4414240407030140a50004611a140c041003a0810100120350b201d064942c041d018200989640d60b80318584080d41d000501801c1d160810280071240521072094164032078001801000c003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658743093 1250 658741843 658741861
    0x30a2004060b04081c110d0f02010c030507090618120b090d020102070213090f0c030c05012c011b060e0307032c011206030b090303040218090d0c0f080a0c030305 71
    0x18a100342030302c50b8403402c034560390045e61001111629240b4a0011038070200800c030540f0344006002507001181901c111404c40703550a00400f581c0860714102400036041064005006103158400d020402540318065511071062a880000812185882c2c6041d1000340c03e04544421041d941c120141c468424081c00b000d0040c0241d07280550002d00903031a6a9000c20007201030f01181c0700441e0303011080f0400c4c07070000b0607401461020790300034400d40c3c039243d051070b0000d094080340c010140e862100e64043c0c2d000c0c5160382c1d00c04d4181c4400a280c001804664101c448000444207200240030038148600b04883c030000001500c1c00b1402030303850141a12200110030b1031440354064204020078810046e03141c40d4010b411501860800503000074800d60340741c45040407440e054484050700d1300001309000a518102400c000806268622316100741040c40d1615500c068001c032550600000d4850320f800d10002c3e1a003aa4440c0d000610140d40308509913000b410081c1202003107010925000204411030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658744343 1250 658743093 658743097
    0x5072706090f120b040305090409031128200d060203040201030c052a030c01020703090807050306010f1a040906120b0c09060f0708092107150e010509030a2004060b 72
    0x50706020f010507010025484140304400024002c1e41070003410400c800312512a80300c2d84e85000e0190f52a01440c0c05070101503428401c1d030908103d2940c40500c4600714000543ca01c4501c4940d00c80c01040b043c0c40c0718170400c14504400030403503612400c0303e42504244101c58000f0343c4614400d80e020403140d139540c00180c2d84e6009000c0c100000c1d640640340b6a40913508480503043c02120a81101e080c04509000710707099034040d04040707000800c818420000703d101086040040e00088005c0d100540c11b1001811402100380f107282d82010404220711890324440c0c00b120050950319200f03010190301c030700703494000d4074400d90103c5039078014400082c00d106000054648030f0b800100580d2501e0340c411803417200790300700e181d0560704054100510485e50760360241d450388030518041810301d06280c0c0d10000d4103140c05035102e22a44440118401441c03035106954980051017400c011f519584400c000c207140802c0148001c01c090007100c0450788001344402c0300f8010f510200ca0500601c1e0315100440014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658745593 1250 658744343 658744349
    0x2010e01021305090703090b090106090506030d0203070b100b0a200d051c0608010f050405160302030c0918060a0e0d0e030604030302033304050a0b01080105010305072706090f 77
    0x1888040314144900e02d0010000c0e40c0003031701490045400011502c0d1203000d03103015244401e180c4c0d522031301001591500d01820340c1c0004228003070650302c01e118070042d4880c801d58000030070100d02c11000038090300160029501400c141c540c804d4076603c0c19800903000c01d1f40616803207052040d41282042d82a0005600011508999103543c10b080d82942a041101611407519010644a50f00425090003d1050700d002604085000c501401d01741841420203001d03e01c10062003400c00d0302032000d41c90000e00c000b44035006841803085c85c1d0311a20103841d402c289044081060081105001010707a00350005020121040141d8480089240c004c0c4c4100381e11803611501a0020b034001004603029601440d4041d88a9044180300358015049000305001503000c02080011140c91900a0400340309150b4464030345402000b501036440006040000c05110700307410140c949002490300c0b44201c0040302c0c595810403074044241d041d01c01d0f091100009004000009866900c0015500c114200034011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658746843 1250 658745593 658745617
    0x405030a090e04210c0f08091804110f04020f0c010e100212010e04061104030f15020301050609090705130803030a0c030209060d020705010209090c180a080c1c02060f030702010e0102 80
    0x6202c0366003013448040c2d4101d0014018040302d2111132000c100c4403000c0c251414030528107103035102d864404010101d0000056a2415000c690070003001400030402c64511103011201803051030348500010340039114075122100d520030045402d6040d010150015540000c80400b80e60014001c0c070000400c0340a562200010f0001c0e1000411805068046854001d8051100400c100200da54124065441030b40b04845080c0d0300e0b03001009012018904210304100c0000543c950751421001564174040c0c160301612030300b40c3780d01003038086004204031031f06018068110b645503a90f40d001d00ba00c82d00121109a095810416940c5146109100302e0b001580c00500302410704489030007010003034000080440e030541d401c00030004259145000d86200e0012041c039156a010021100d41461410151450040824005c1031042d9200480d080d41d4540c0143d5501c885081d000d00c44c0300c2c080340f00c880b0181d04818006007031405020a40015071050340303103800900600356070902e05400c130702c078108118103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658748093 1250 658746843 658746863
    0x2120f090d0c060e0f0d05031005011403040816060e010204030302190b0c2101091d0a050304050609040f051501081510050a1206180b010302091e0303070b0405030a090e04 75
    0x7105039100782d00491307007901120fa030031040000c0586064400031519002c6007003c420440c2000e503c402d5403001c0c1c002032030501c0512401c3c0da01e049403070101400c018846240400d128004682d0103403030100b07107a0004e50500c0003c9c0c0085280d4000e50207400141c0050003680304116006251881321500954480c0e2441c1c02c607a654150b40034107401050a02c01d4012107001c6240a11001c10030b181d003e000306140000f070307809040d13003860b0a1403107010f000002d80d00040d00e04400700304d01005542c221641610010395800048001900401c10780e200c1c1002c0b28500310510005040c000c0004034888070a80b100d0134180c0313900c030300e0080c0c4002082c0050361061124240303018092181c00a040814040c0c01d0003810a000b400794003082e508650000f881c0009030340c1d2812003814040c00b034990010401c0c2011440c0c40260404100d501c0f42c2c60207085008480000c20388902d440400071901420f40040075010030342003601d44a078a81d80b101501c04001214150045120b84094a055021303a0303120798003903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658749343 1250 658748093 658748117
    0x31e0509030a0f050c0102030a0b0906010216090c0c020604030507091508030f1312030c0c09110d020c190605010810020903190302070f08071e05031905030d02120f090d 74
    0xb10f00880d040d807003104202090001c40201c0c0001d0020314003038110540302041c111030f0312003801080d02000340003038115407000b40d201010710641e03907941055583c104404512015610400d5030a40c81204009400010014000003488808108601078800c0c0c01340a211201c00c0f01400010040d05003d0480e07950020403800844d102004014207258813401441404242e4492005c038100e80e00b240c00340d0201d0703030411521040060401c40003000d4030b404c043c00c0000000150208155000d50000c09041c25030000380303001410410007040090081d41d41001180d2010351034920003400080c8951410342c03003010b4100d2000c0c880c0b030080e40c100c480c0c080c008151039003a10413840b60a08942c5800d409600611002155541c502503445014000c3c04d0000c00748076190900749640c41c00001c0e443c2c0e55038641c2034028402da90303000c2031044001e461f06800362205209420458214400c841800800c288000b4080e9070924030080300d01d00c1408800d001c1c0708503030764568989495800024200e03000a00c000707a01c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658750593 1250 658749343 658749347
    0x303091b0a0e15040203040602090301050903042105122205010203070803040b101a0c15090303180106081f0f051519050d0b060a0f03080423030d031e0509030a 70
    0x14990208a00e41550030001e1001c001c9000c0761b0081d5401d076240c0f50001038600750b0b401c00f402090740080c1140e0013145401d00c0c200d1250800b00c034020508001e46454002c22040c08020480c80b00c00b000c3e0000301540e80e8051015a4000114403a01c81c8240f2003410710004207980003000f074a440a8011007500d141d541c2d00c0c1e442801c90f0740010244101700d03003e00d0004c29501301400c210a0038104d02c44115903a5240840903c4c500200c941011076031410641c10800d5101020007902e4205046201d0401d4285104021070701400113600002c10030b200307206421010304000c1c80105000c01c0100e00801414850740b255905a4a084070b003103200c0311204090440c42c1c242840742c5040002200c00c505e082e00e445000090b096824410305407240050300d000c4c00010726000c007242c8002d0002034411700f111882c69030303034004a004511810304801c0c411000d0350500022255240c0007010002c00369807102d25417030740103001001c00908012030056104180b03021080749218540c09040d900008504100c500041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658751843 1250 658750593 658750619
    0x6090f0306100e130b0a09031803150e07050f0103021c0905070501140a020715170f1b070f030503130b0f040b0a020c281e030f0c030e0d0519050303091b0a 68
    0x208a0400c11030001da0204d10b002420704274083c40c8101002000da140c1c00d94441d085d01c056000803415038100e82c1c01048030760350350070340d8420b0f02c0000e0034056140c04100b1164100304035070303a9511000701e04103110b020411902195a6064076401d0f20742c7c075010101040c5090385405100908409030703000c000c041c0881c40b50008207900705001071a000c8a040c64102d10341c40f10b034806941d90000c1d40007190901048002078110640d210a110f00c510341002c1503502d401c42c1caa100e20f0700c00f074103028000000c02e00d001d54580d1602200c5820a0507030655080020302014080e0b030444050f40c1d1060850013094044a8500031168500c000c0c00080000c002c40500e241c9640c2001c0b040021448102400100041e00c441030754800c40005155071400f088484c1030240480c492000d544003013042140c070190001f5001030300b103100124140d40c0b4024140c10b902d0100c3c40c0c0b050540e807410840c50038152100811000000552092441c3c60a690320008501d400ca40d0422200c030015900c00700e506402e0000d0380313860701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658753093 1250 658751843 658751861
    0x5090a05070804032010050a0b100206010e0a0f0c120b010905101812050d0206010609060c1101020a080315030c0303030f16020c04060b0a03050708040c0506090f0306100e130b0a 78
    0x9090010085c070000c1c424500a012244688000c0c5c81d2010002d014034140310380c228282060703404006002414030001d4840f10140547c92404400801007018107149074402e02c040b089081007000207019250014100c1c40215640d0010103060040a0506511554003d42100d8010301046801d4030031407402d84010301c040d81c100c4042d1040c8a00052001c00d0250001c0031a030007403000c3c100c0a25003a600a080840c141c20043c02d022402d0b2042120a9100d6818584560405c10342d98240a03c100100d08000c0f1024000e094100c2c08014050325101c42078410030780b40f43c210f003100c40d010701c42d00c24183c89004c03c80316400c000c0394010028554540221511403250301c0c40c8196202c040c0c0341000203040750855000380d41e03c11004210400c150703805204454014403541441c404d43d00e803079036981c0c010880303a00a447c040e00c00851480c80b00e0301c42d5062420290300c0201911a1440c200c9894015030b031f01407041100d84881c100c045480e8142d43c11554483c1a0000d442c04a0b55907007807015000380804007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658754343 1250 658753093 658753127
    0x304032f1902031011070c1a1c1e020409150806041412040602060a18020f060906040e04140c0603090303011e0b030405160819060b0d02061305090a0507080403 70
    0x104030080c00c15094455050a24501d00d01603883e1b811904000e564100c1075080344480c01c3d8498980c001784002c44040c0d4413208260418290b0b0498007035521000380503030b203490900e0000c03440e01104507040c2c150080c2096580c09c8600700900010301c04802d400103018071804a04d900460041804a000040280c04d5894480d040740d00801110030750010581c8607a0192005801807001d204c5213a0320740c043d0b0310550031038144c4002d6203003031074000440014034224080d101d100005030f40300c16500c0e00002d0350700070010100190b160b0301d000d040814142c01c00882d649094003d4102585542c030b08401502c0c0104404001107040d60300300015a1407481d03c070034228415498801c00016414641001948036512400140901616201c200d8882d0001a04281c80c541c00100000c000c01616070090105140c001c0000700b0105440c9010601540c02076001a412807000501c484400a03900901811102c1c00d54403011a0782d101d00c06041117586c192406400249040d010030003003446210824103c560744 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658755593 1250 658754343 658754353
    0x105132f04170a020406300611040303030b130606050706020306030a060e16241b17070b061c0b0402190609060206010906060f080a0f020304032f190203 67
    0x181080007200c80c01c4000000c1580c4070300010804c5007090b002d01c0b4010503660201c5000003240402c0040240312550b03900160140b9000c2401c14440c0582000350307640d031100f000c030360b030340d9164200200a0300081c0d040d1405048450301024407045d00744100f40454826954a1341424215070700c1c0806540003a1025a041c4104052900420310b58401c0614556150b4014613128504d554455080c003000d90100b0fa20400c0f00c00e10040c0140e9a0b490300291407090710700048082e01400e40903206101484014001d141c0d80d1020100180018004180c2103004024001d0169a10f000300003e00c00d0085640400400703128207180064401a10380d600684014411400c85032800350b101c0c2c1c0c9d500d107070380154009440c6103010081d06030180300c1da0b405081d00d940280721860074280080c00329000c4410040c01c000d52800050f4001025911000740408024004d540d030381414100280000c800b015510216030b030660b0001741505c8206884c18040c4030101c05801c448501000030070110702000410f903051301903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658756843 1250 658755593 658755599
    0x21908070b0a091103070e070e010908030f0a02251a0d0905030901030b060c07030f0206040909150e01021201060815130609051305060c0304080706050f0105132f04 72
    0x144240542c0304111203000080c10b0001ca09100c0c2c20b030454094841d0003900005030501140422104680e40014503003031804441c1c03031580048440780c01660000105010100340070f0000d44040004040b814802e6080300c07442e09904004081e03084119a414214442e072410810120240a2070640700c4007155500d9410000d1111078001138410141b421145500b001855500ba90380612444005000c2600c8143c00c0c829170190850762041540400380000c403104e40154210365580080342e001c4e01500b4014800d0a25514104c40f6130b1071211103a440c80303814488003604a010510035074459000c0d0045040e000c2c1d281150030780740140d025008a01462a1195000d01c5455501d44226035120340070001039882e2420b03220904956001d010031380e20035413030380d0381c840458800030f642500000074000880e0b4035100da107018030441c0308a0304020070450601c0e0811001d4000024400d040b80c00944034030706500101c06041c403c0301c1440c0c1181201c0d20980c1000c0d000403110f54650700418249168091038030b40c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658758093 1250 658756843 658756853
    0x160804031812050c120a0f0f05010605060d02130e06100f0e0411130e0112080a1b0b040203100519021602040203090706180b031914072d02190807 64
    0x1901001030743d4036440009200d503207041c0f03501c49900080b0300001800d18004541c2c1d074140c0003040c000010308040a0804020188102940490010500140115541c861642c0c80c0c8000e5040360340c0d492a00e08401a0008403060400e84603403250a00030b001940c55010188190390a80300c81441d032081000018040169448520400b80c00441c119002d41e10f805100701002d14480c80e81e00074001e009101c0c4010026201c980140c207082d41da014100588500d02c58804540c0c54507461251821005ca14107200c0612050002d103901850081d070550b41115621003c035403d650040e11808413103004401b4411194001ea40907000c0003003900001d0400f0b44903600003400740d030400e441d113281c02d400c040000c0004070741060716805001c0e110903405c802d070ba10b0941901000e0100034140e11884158460040001415601c841c980782c042000150050038060401010090346410301800408048408100ca1220b40645030310124540d0040c00c001c009000c09100d9000a01c0e0101d032541024080d40002403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658759343 1250 658758093 658758119
    0x50a11040b1c0e0309101701030b01230a0501030c0c050d1715010f140702031006051c0c050d02120f1c0f0c021e04091a1608040318 58
    0x101c418001252110800c6044003141c0000090680c0d034140f0300000002038100100030f4502c0703014121440003a140d1004816100d0200b0106c220340003c199100100070040b101081c0c5050314880003210403983c07140468030b10f400320600146540039412207402c003c00d40c40b0b03030840300e81740c1d09038034124504403141e0359110f282640c2101c2901c0811810710500d400c103200c010a03544d2007030840d201800040c0902002034905803802c802141040302030b0a82a82c0e0b1a032840441e5900b070341c003504844d415600c1031054402070016000c0c0310700c64216024520b1a0385040d14401850540000c100070f65245040c0170810250304c070b82c0303080385c21124881a190700c114084c010b01c0800c02d203000c0500403903e0205195038140b445203c0003018070078a00892011a40e11220880d111541943c0d28040b020f98041075480380140041c1580d40541030045075000c00452030040d041e009012a1403150f10345a051710080070083d4403c1030800201d90038009000320b0301c2415000c800750b4250340c1166250b601c445110800d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658760593 1250 658759343 658759349
    0xb0315010806070c0807060f02071a01050405060a1a0d0b03030424111b041803120b040e03160804030209010605070b010e0702030406122d06050f0112050a1104 70
    0x210201004100c010002d104155100869140501c0054841c0d610150180138040c00500b1442c1e852000705059201a0f049980351034111844101050004140000d0100e090040c180100e00346004210380c0d041091071207050b00c5551310801c0c4503d10442d485001c1d0b400a0700444183c1d5100c00c1c1028490318180f00410140c4601d450580b1190140b8081340c3d408442030384800c003040704145203e07921450218003820072010000301c4100c030900c1c0708005006000c01841114020002100110403d43c004006200304040c407842400280c0c41c03902040103c4020703402d180d6080c1c1080007001d4841803c0e41426400324410f090700d60408c4c0d03e075004182408001d030800e4010503000a568001d2112502d4800d0041c100c00885450a2914110003902c902480c81440203004402c0701c00b003410442500400203050030f0181c40b0705c0744410f0010250046030003070500c00e4840d182c00b20104440c18200c006d00c450401c10b841d601001c00c04003a10400034400101124410ba6071195000030b120781c942d000b4401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658761843 1250 658760593 658760623
    0x507090e060412020a0809010809100c0f0206061f0818062410020d050f0403060e06061503060603010b03040213050103030522051c03050409052404150504050a0b03 72
    0x9500e01460070400303d002500755a000c2d503002d0240f08000516000480b500854207291031030442c0c44c0ca540352494252414050450b4070704228201810300c0d8800b0300c4030364001c6135500315442500d411082c40118440f11000400074181c5102c50207400d80200760481e00480340c07100d154005001030b01d6a6040c800d0070380d031059040601180b40c014400000100c06001c4400711a840d465004a0348040c1d911885046214144400496000540b0406100b6140119007000341072106c940c18104d00c4c1c4c1c1307501085500301d20070084510b0341420100b02c101524803902c405040c01c0e107164202002412160402032007242e202c00454120180d000681c0206802140310313031552512080d03c81300d0040000b41a80664030082c000c00c034104465540c4041d08554294100c56603006d003e07040c00c0c1143e55110300c0d00715442150074503050001c1800403a0003040b01c0c98000440c0700000081e4400c10081e2050118141e000380009001030100b0311b0306500030781c0c019480206c00030f204000b0101090500d00110340c0040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658763093 1250 658761843 658761853
    0xa150603030801060e0a090b030c03070e0906010e0c04060806060c2a0607020904060209030a140c03060a0204060c03030c021f02040302100503070c060903020a0f0f0302010e06060612040507090e 85
    0x1050380201645000d01013500341060140400004a002c0d80f07000d1007541c001d1500c2d0070340552107450500c4504410407003d01964440c948411505a60040981e2400000c0c40741c0400080c0351019202c101d03000b0201c03182d1140c9414641082210b8401016001951102d4204482c21102c03208100240d112280860098038508010104c0c05901c0f15404007030b4044c04003080701000513500c0d0005168055846100140c0710001040420700c1d01c201813038014a00200c1103015991141300051980b0301c06000c030200c07403240c0e90f00440e40703043c0e01580c070583d404180c4a0481c1e0b400640030390030103503c0c80403d20407981c1055140740102504a80804142040750380080d00744290704000740300413924843c5040440c42d60518001c024510400507002511a65035404d010741018400d20182e01b030150809034108004005003801031003240d10b144110055032074014980121940401c2c0c1e144130317070f03401044d06042c4003078030700740c160070450007881200c031402a1400881c03100850300c584a500413905004203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658764343 1250 658763093 658763099
    0x40611042d090b030c040f060b0c100c023c1f060e060d1407030623060d0309050d060e0109080405090901021c0b0103021b0d17130809030a1506 63
    0x3100355150000c60360b031400d0840741415500c00007400c05548100f81d500040b08244101507000820068005404218000410109500d80024008403529402104226541e03401e03c3c00da9886041d82104c4080c1c2c07505904d00c0398480001140d00e100390300b07030740c1107030190b410060007103410184626000000140300c1c00c1d000b000a80b1503c11b11014041020940c0300d1801d01400080301040f020b80e00034a002c14211183c28032240c148160002141d01040a01c1800e03981700e1070815030901c402440d0164000080043d445141042d8050000c5415840319038101e0f0404041c0452105403c005840310b0745c039003e418100c0c5009214207c1c07014000d4601c240c4031030405081010101002e0410902a801405641070f40310901c4200c042a0307481071000224041c0800c01a40680500481d114031203a0305030180b00000c6010400c295090a90303503038080c00b07200314028820450b40035942c82001030303d4221000f001841c4080200b01c0d40f40d0080071180007004650b503035400d042540e801040c0b00c545683c410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658765593 1250 658764343 658764419
    0x1009060e0c0d1e050a081204020f0402090a2d0e01060215100b090406082406010518040903090305030c010618020901052d0d090b0c0f0304061104 64
    0xc0042524219407100b0b61103540c1c2c55003081c1d450110010034619011a120300c1c10000200300d201059035002c046151030f074034495034801302044201c0d07007039004090005014400b03241900c03c94071604001001c46140c5e0f03003003c0c080c031034024082c101c80880440300380110108410711050b01c00200840450216a903051120090802001480d014000c050750010b00a0703920805124005442c02c24000b1a25103000b0783c00503015111030740c00445940200502110240300040e0079800020760172100700d95540b0703500c00440d090700c01c0c25030044009290b00c011050ba07103050380229003410701a14241a019860391116401e560201c0410b005c3d9a42d243c40420600504004640c3c1b0300d554103100b10704ac40104d40020303011380300798591800c0400410300182c4c0c2400c480c01d0700c2c420702400d28182a4569420052a40c000d008551082d5041c003203420000b0801d41400c800c4031461134198051a01707546441e036401001d8104400300307000c102001e10000c9090f204450f00c0b440462419101d02c1d6200c21000e60b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658766843 1250 658765593 658765603
    0x20d060b210f0103030e0415090b0f0f03030d0b0301090602030126010c0504090e120d150506070c030b0901141905060306060916090302060a05030702060a090b0601030b031009060e 79
    0x100c0c0c5a01485103040107200502d202010303046135090308021407030340c40440006000b01669040405c410464840102da42e0784554810741b510f0b0400c2d0b629040118500b0108003050150400007681540b0410801d44a404a50000454044060004200d03072200d50364040581c0c000340c000d59244e4404c0c015904070090846040388280b2011002042200c82c030000c010024031407030060034246074407910007034800601041140744a9410071100c42e00e9000c1000d801001d07080484202d8800340c06645e0104084c03500c0310445222640c0483d201031524919600c0401340000217181c002595601d48410b4804900603520920a0740510803150140c000041554100c0304042c1282d130090f40b01204101d019110607445542000f000c0d014007014500c5020111600070f81c40d00001e4003d2004110710f40c109800c0b401460040215409a6100b556000324810441d10301c10401b4041404810210f03503554000d5004280d00c0c24007806481c0c45441f80c0401c0c0d000d03956140d408684107030366103c40200104003480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658768093 1250 658766843 658766887
    0x3011a1801060e0f0105071a090f0303190c09030f0309170129030c06070614060619121d06090712020a14031906020913230604020d060b 60
    0x4241125410000b0092a0140c4041c0940c016100d841c42c4070007503805034040e18040d66021440c4421500141031070f01c084d000507a2507032468800d2558100002c0030100079240324104040071040f10f0b000c2c941020003e0020411910b0a1015056000c000300700c030a240c3c02c00480c0282c5400340ca951816120201c40c0150007041e91070b69242c60101d80180c0307400402d052020040450060500551000080c107220741c0510036030344090b0016822080001c21340043c3c0d00c581c10360b0815513590b03841ea010310517684110400c48100a407910b04000c0321500030f80302221000609030001680b880c4510703450510200c0a19485502d034004810020200780420401000d400030418403010740d05e299000ca119800c5500a0350115411036442051a45003000b0700044140784540d158120011800d142c4002d51081241038010444960b548518903068090740c10000f00c200c00c0000c085214107080c44010f4405801c0301d500a40030424042d048490317014180c00791a80c00c6d0b8180d5240c00c0e140c03881090f03000c0c01c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658769343 1250 658768093 658768129
    0x14040603030c03081510020f0c03010513030c0c05120a05010c050a0c0b0604090605040309290301140307150203090301050f0103020a060c060e1b1014161103011a 71
    0x1180920001c1d501c2190242d4031585030402c0802c44e1901c0401a80381c00c00e5000542d00031503000b000b40c902c0d0b0b0b03000a028010822284c1522052507905091509950088440f0111405800405400a40b0800581a106018984509149403504005071841047d41c860b003030581d106030340f603070103202c030a00c0350f03030a804c0d154180302d2b1414510400141c090002e6142c042e2820396810000b40e4a0b88858001410850f80240200a80d181c1454060000b6059000d0580402c2d408140b00102d02c0801c211440b16008820f001406e44c0c0c80c0145603806041b410048070782502400c00000740b030241c540c49081c4081e1442d00959114080c990a241c01c540c00280740c10340c80c40c040b03001000544c403100300e0101070300c01c94502000c1544d1141000405440d40c56601c4940384149100c41046030384490042c03000c0c0364125000c20104001d45400c50711310100c5200a0164501005905e4051007945004c020441c4113402c41d4540c081032200203800c64501d459824404400c0107080030349460640302102d140444030f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658770593 1250 658769343 658769351
    0x102060703051504020d110d1b030204080616170a0606030e1204030f0302190807060e01022118030c0f06060a180b13020a0306050910210204020c10061404 68
    0xd00f00d18102c2d04003d00281c065640014000b1340e42c03c0c1904444d4401c602021603c1e91002c0110b0740703000500aa51030350030300045081011141c50301c00c1c002c603021540f0420040c09a43c44004040c49880c155500d00e200303115035009040c016064901049206407051000011460700e0041d018081c7c5405060314505034010b00720000c02445401d041d5000e994100240d4041511903180a038542a501134055501ca4441c9181d07808200400340141201031244006216942208000038281d0140b002c1d164800790702e011076441e1f403456050025a0160076242d040a000c40e400c41514210341c844180c041c00340d007100d007555216400410a940c0c10080c2507a13992002407410b00c01c0481c040305c001c848a905510703502001119601c200c005811900c10aa0455541d020000e01074010069841150b01400c00040054019004c15009504481c90382004030010f45200303c031080341d28000c6004a0b4490703402c1c005014400c00400100c02c01408166001030b0340d9081051304d85c0500c40c5c0c04001407007a420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658771843 1250 658770593 658770601
    0x40507030b060324031009060f021611010e1e0a050607020312030a1d0d030c0504050d020f040933060303050919090c0512010816030215040801050f06010206070305 72
    0x2041c0403240e22042520011420b581d0164080c40342d03040c00e13194642e0610800801d50100b071100d5003d008428800e58041200840e40a000002d03401000c001640314405007032101c000c5001e95100d40c00000051410020324620000015500702c8000c110701144040901c0e10701140c1801c1c4a00000303020221011030410f00c003035000039a1001d005000c1920520080040f13001542590000d079003003d0000e04201815002d0648d1135526483c00144800207800d0070905010300b80100200c0d41a204c014194583c600c445030240030f80405c0c031440d0281c009a0311500100811b080c4d03000824038081244030f204400900c0b4004040d510f51070107158000c030345410401c00010ba0008204c1765074075400d83ea00d00c0c0c840721040e000d00e01414207500c03221480d42000070208005078001c0045c007045c4426140d450a59884100c103969a00c10401c4001c0d070041851024405071418940c1c5500c2c1a01e080f8031646010340714003045094940680c1c1441c40b6848040500580b5078061003000e41c4030000740350030005464 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658773093 1250 658771843 658771849
    0xd0f0509060114060d0e0a06090b060907020c0f030c150415020c06070605090a0611040f17031227240402090103150906061403070b180925030b040507030b 68
    0x3c140c0d03001030300c43c602c001170031002003400b900140c80304400002030b01d03403000c0542000c01c05440b20080444082c00344400003010351411241240c05440f079075000748000c00040b024010042550030450f5494400e0364154189580c4045000c0b862182e00c0d02d5503034903186400d45203814030714940390040640d04162028071642c6c54203015920700da034000c8804101034443d40d803500e0604d694284050401424401c5a008012441d401002220704248000841594030850741d205c4485d26500152031340c0080166103601325000704266008983c0c5814661041c1070400303c0c0a880040381a0521241c0104100d074400d4032400d00700c0c0d40100142c100d03a036614503050b40002c8007180c05001c000c100580b990042554a0040c1e8002c4a08035404a000c10a82d80c84e10301e11070885400c190710900c00d1080742000b14612000c401aa449100c024004004550200040004400d0010200e4408900306c004558400d0b0355007900e18000601600d0020701c54503200140f00680e40c00070400380a060502105e030507152 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658774343 1250 658773093 658773119
    0x1020d0b0a030f0b0415020a090f33090f08010f05010905090613050c030f010b0f0121020c0c060a05070c05030708070e061323010e070903081b030d0f05090601 70
    0x158080522001682e4a2034001c00c01b8001041c0314004600c003185000100342c002072584240c45202e00050030055031001008200004024010160280c8551466070400c2582000c05030103842d0400c4e102c0310742c684218500900300d560103105580e440d10f00035031901c000d602c900c07030240c00c18083c00e11051510090b5503a0350a4081d04142c0740303062280c180d81c00c3c0036060100000002c40101900e15035400b83e41e455019107202411584a647c460301c41110f00e60280c0a030130120b4410111580d59000328601c1c01c8006d4002800e80c400600a040340070143c0d0303488400800c0d44c4500e64407070f40d840d280319050801d85103140f5003283e4041e80c081041071114250018002040316840300300d0194075070b10b00c004a0320f0442c0038a6018a054140302c8000041c0d4900741d41040e034249002100079050f130366024499400401520042c0c045040c0140c24000f00d244400100b0f884560001c07481c81d400c0303115100c00e1440e80590b4840101390f07611002113140000301d0281980200e0080001c055650508105d07440030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658775593 1250 658774343 658774373
    0x6052406070203011e02090301050108010513030c0f0609060f1b09120804030209180f1506061617030a141e0405070b190e090f010915090e01020d0b0a03 67
    0x240401151a0003150b6017500800511030b00c911146100d020074a11007000780d000750751458484e500f40320000ca03241c0070520403035104901011010300038806c25181928034810607541031355024940301104003c28014020500141d100d1140001d03e8001c5100103011203101410820b00e84540b803054503001d541c04240c947c1502d050710030300704414805180a9145100710382c030081d0070900e030703c04000c01590761015035040b204019051b107008490660f80396031a02c0c0b140380c406075503503040f1003c502e85081c00805004031182404600e801130002c3e4a8603008203688040346005010004200108101c00b0700a501500307440d40e122041604140d08e48200700c0b01141c640c18146440d410002e424440204031003002022a1a1400c1e5258031410445031041c51540064000c2800c0c003001c01054103140d40c056114111a44209051707901304038804000c2c2955401180080101290208011f0239034452100548002000140d449041a0781d44055503100c1140612a094405c4104046501e00341741d4151 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658776843 1250 658775593 658775599
    0x906160f0302090414070216150804030c020303070c0302130c0219020109120302060103031407050316020301020d140906100e01170709060b09030601080c210a0816060524 75
    0x35146442004030000c0c001c1805495125050008003d0700360101c85405008020641c00c0d91032070966080e02c0d035044503040c800e80324002004126003040c00d01c601c0030030717030428442e00c2e260300e104405400180c03854201c0c01d81603440090040c41007086140254607080a03020182050050b00c62400c1d029440d5211085076960092501e10175004682c46081d005020340440d030070600003440d0504000313540b00024081280032809044843c06c00ca5030725415554101c1c1e11400031031070310601c10aa2461282d070341000f01c0e05903400340080c0341e9081c014081d03e0909001750b140307038289261201c0c00741d14285000c1c002010307900c407104061020000028016042d104807440c039209130030900520600d0146903a1100d00b0b140d00d4008007058540081e0000d007070406044003100c074030f0703601e80340c2490312443c40c000c0c5140e00c4000d1354080300700c944101d460001c445204505880a100c490384038980154449a000c103d00d83c1c03000c0403d41088858030409400200006040e0440300903a42c0d10605400e1607003120348 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658778093 1250 658776843 658776857
    0x10b181f092a0234080d08090c0d030f0e060c0d0201050a051e100f06090303030f05010602072306040303021612020d030305151921020d02040905070e090601030308090616 75
    0x7541c001305200308090b8500a0280003015690b5414540c6688106410780b001580031008900c010000041d00e44684030b0080c00c05010481c01d5405803440c83d0b04020040c2440b103694030045159482070007030031290240e40c000d405400c9459800900f100c01c0140b0030940f20303182a0601008800121551502c6685000d00036026100e0440c8440040b826521001c00804401d03004942e06501003600011030f4401c3e1014800e0050000411040d10002d018090069000c0b400812840344582624a0703135600b00d620300361082c411080413580a52040e0401d9000d64071210126640c08400040b800081c00c1069107106c0000043e0700213202d00d5020380d005401c00d510342c004102d04c1c001592259292a01c020300c0001c0006030204c200461100621076120081e040c0e581000c00d04c07240301e0b0800c5e80543e0041c003803842c128a503400c0000078840a9402d44a40c4100c1e1030200d1901d5100c5d041d18040c0280800400f103d40c954a401002c001c40103018601a4100d9001c1c01207070f03800c51401a000c1200c40c240301c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658779343 1250 658778093 658778143
    0xf0703021c06030309150809100c030908030a02031f060e0d0c05091302100207050f15040b0a05071e02060904050a0b0316031103010b181f092a02 64
    0x100111207244400811038646000042015000605007048594440510142402c4c041054400c1001240d2840e81380d0410115a107a003456688440da260289013000500c010040d00d846c100358108845102a4a40c00400e02450301c91603141000000b00d0060305442c1070303080c014003d12a40700022054000c101c0000b00600300510201040081e16002d0045440c518041e0001e1505d803800260170703030013056110b107150750061000c20f1000030390b000500f04050f41c484000c2841922282d8420481381644140008a110018000240590041030750350340e41300c80d424140168102104a562082017659081250040e1118411f0382e10440040301c00151640d00c558035400901401080b040d41409440c04501402510300d0882003628020700000d281d0b000004145402c071032007241000d600461581100a8000da282859035206000c00342000b088094250b0384100c0d0845600880700c8161502c03070541900d004280601d40444e1180050724180b942400069103440c9001910070350420105450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658780593 1250 658779343 658779367
    0xf1505071b0e0c0918010f0506090310020a0906020f1504020f0f0a0b0c01140129091507021c0201050f0f090d260a020d030c1b03021605090f070302 65
    0x2400141082ca868107074a1a06112540495000f071000038414154201c0c5901621500104a4181c41c41c001300205014244410840309402c12030b601075061140c9810444880010300150084080c561200500581031090190600c0601c0801c0d644035400582188041d03500840c18030707042901501c0c02125100c10f400070641c80c410984400f0340000d0340138000074200b80b17154010042e0350000f00081103a600742c0342c002c0304917001c00e22660120900350342480720400d01c041d9481c20175421075404507150200e140d000c103810505861f03e0010200c800b013560006e50078250410b840c003150141c1ca4610007000d56001034960301401600105000b0007140408040c0c100781c088600c07070000107102844446c65417403c001e544640d0f60781414221030714242c1d981c58054420540e40003c0ba65000f0302040300e00600218024010500354000b00110b00c99013402c85900310805008280c02a40075100c1c000c0040f203084254001c1e0303440903004001d04000c0020642c03411003459007104043c540980e070b0300203040756 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658781843 1250 658780593 658780643
    0x6040b070512220c0b0315040519020c240106030e010c081515070f0203070501210213030b1602010c0513031e1a100e0609040f170d060f150507 63
    0x10080c40c40318502c44c042a0b011200b0003a5114002015090b113146881c1400e102c2540c2060780c4050030582c26070b041c0b45240c40726402400601182d10308448000701c3c0100c070f410711094403000040c07003070398130400511945034140288009001c44400030301c01d510b0a88001460140001c0150801c0c0c810722220070f110344d8415880c0c0311108603c004246c1c0f21065414103824440140d80e04a102e1300ca07041d400185940135a00d4544003000711400b90411020064400d4040d5200c0030b000d074103540a000002c03000031504000c0c035004101c80300c070301c1385102c0602c00d01030300b1100c401c0200024041d007800801004246031400e90300b5603922100403400c81007921007107650241091002001640324488000100d40c058910a00c903403180390f407145100d070383c4490740007a480c2c0c140d40c541e0700110400001400718a94540040d6018440d0388808030242450b004005180c0005522207500c1d0344030042041840f41c1212800f0150080d101540f941e04001c1001600754440d4000081c21203d907840c000c0b64511f10650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658783093 1250 658781843 658781911
    0x8090304080f070807062105090c090a05090c0a290405061908152808010c270b03012615160c021011010b0307060206040b070512 57
    0x400c8031500ca00790000c2c141c0343e00c264058500684107409001510034824080344504140c040d502109006080d00c00d000600f00060a05541e0b22030511120134903240c81100c0d6114049407100040c040c14401015400c060300c5c00086403140200010038031012401d0034600b500b00510700e2524a44078650100010240500c1d407015a001401045144040761000d0360784022000300d40d10300080e55a4202100200c1c10f401900301c3d04202d05185260035954030189820080113000703411740000c0d903101c07211803c0d81c01f01150f00c000120129400194020454504030b044820340c1000c1e1041820700c0001281030005200f40b0f0708007080208040941c10032194000340c0d00070150266100302c3c10708201e142c400c1070705442c01100140784601c2050f0851090710706020b142e900809041824483d403204076511144e440701c420313555503940760030b01b055502040300038000c04098003d0180380c44c1504212130941070041264060003030401c40c02111030b10030011150302c41e040c052801901941000c40d80b1901035a10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658784343 1250 658783093 658783109
    0x1e0804050613120c0302030f030427020c100204140108160c0f12080f0603010504150c26010e011e05010f09080a031205180709050606130b0c1006031208090304 70
    0xa03d1010900560500313103000d4074001d0701100d03030b071b4038031019010f07901d01c00d9200c1e015a408054080c1c01403011710001140014009500140c10900700c05161401c10030300b02c05218880d070b40020204025441c1060388a00300c8401d00344021107181009000c80c0d414540f85550003040f10b5a1404410408664190811030703802454030030540032450790141000341d0507540d1980b1090751200107162483c050103114410f5502014800360403040c2003629010384900c0c13410f5414040f00c83d942c14501c0300ba504120b405401084085841549083c600c0c102005041c2c1120500702490610050b807041083c1071310040754002e10b08412070801c42c0f0000c89185403290807840c0ca900507001e0754000e155011440040303001c0ca030003040200da210705070401c04071010281c0071070060700011020020400f49600040d8080805400d4515002c40c000c0c034a4215140c603002032402031070200c0c607000040010005020742a1103080c0c100211411600c8068840f600351401004000108000a40c2074400b402a600142811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658785593 1250 658784343 658784369
    0x6092e0503060a0f06020c09040c050301091109010902030c0712030914010903020606100921062f0304021305060d0210020a350d09120c1e0804050613 66
    0x5168020540c0d4015905640314081611010880800a881c2481107135a141c0007000c0445a104c1440080c4c40000c2054039a500c3d00b01c0009044d44087c024400c80c44e11400d900e0001c01224030030050303c401c0c10703000001c95a106008210030700c0e1480c030440c0d004035048030100180003803e02c011030280003a140024440c40f81d0807000350050405401032000d4920980a0310034076a695000d10020442e0b240361100050f0540320100640d008900c20071074019a0410301084a10f03503906d0328000d03a602c0b0030102d00c0c00800841c40c807111042100300f1b580d1451a4012281c90341c1440c0e000034203c00c0c7d28403c1e5507400e9903200041003e80e600c104566030f03102d5002d02480007500c868071004e501e403800d0358000d40f20402c918800a03161507112500c2007072003944108548040c01e03522280c08558000340181e201981d5141030749404100800448803407164155079116000312035140c9407000c00c508020809121800d039811200198503c0255802c3c1c490655045071102120b41880c41400d0150380000d001c0310714 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658786843 1250 658785593 658785679
    0x302040c030b120c01120209010311070b1017030706180c03152a081306050405030324030d18050603010b07120203070b010b031b120702010612020609 66
    0x5030009480d4042c100d9501000c1101c1000d500d07100c0ca16505114000b416080c0304040c000d103070354040c101c0c540040c03500050380b0407a150343d80b1056008650549240c0200e004001c1207241c4800340c500500b2141e40c0d020344d60b480f0201e41c5543ca009003c00109120b44403207101c400c00d003e0300d04804031150007400d8100059560300b08642c400c03a800d24900b0005040503000400030030343c040d95000c518818240f0403850f00310648100e4842101400302c0c4803614403a404480031400c2e45c09401d0044e40200080c6d50f03607061403c50302c0b98846000d04016003031803003055003500320b0754040f60038130203101d06060040c54601d0442e04521300e800309800042c0d20100c048004142c1801d4400604211442403540041600d00c00341c5c107a0382c0c2c0c0102007005210074012801440358080c03480107544c200500490b0115401803c01c28618a80c211140001c640341c60401004000c1e130342400342c200103110703011021501c0300890700455200d1241000c014001d010340484140c0b07031a04a80b5074000c94402c0c0780c0c03030450800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658788093 1250 658786843 658786847
    0x7030e1306150f090902030406020f0d05060f01140a0806010504091103010f0f0503100c030f0608010e3f0904090309031502040f0303030b0f09010f0603050c0906030711070302040c 79
    0x28902544445604003011142d01d035000ea05104540c0405031190041d607132a00612002951000307000b00da010350240130002c1c3c0405c0a50146c00307903a44994020500d850440d0030b001100c10504096810816072485e8065410034450848900c015140f41123880f5550f0000162860300c1258400500c040c504684e480811544d1000346050350040e12072100201e58803100d954a481e264016668503400160101800b80701d0b03030348110311070a203908010403010409405401203031441e620081441e5101c2094413a584402c1c4520000100e040301d66034000e5000c0940060ba40c402c10b4000c16003000c501c5507500360f4000c0d190640d171072810000c20500c01c0c40b15a1500401c0c0c1003061000710303150102c0001d5039404030298002c0d034080e10803031304240c00118507685045001d483c401c1c031096041454580e00075115100d2810715400782c026a410f003400145044401421148002d00007a80d406061240e07034215a40c940480b5000322507440c1280945164034555400c1c0004d541c4020f600914154810303041513 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658789343 1250 658788093 658788101
    0xf0a1e020d0b0a1505030a090b0f070f0f02060601030903020f0a0c0e010b0703080402010516171905040503070509070210020a030506040b010e03120c0a061a0922060207030e13 77
    0x3070390034014041010324805114006809025010130314015181c0030141501c507201455001a1844001c242c02c202030b29600c601c500e055908842069070f090800141903004a446007105180740340c01c1002141121001f5240d034005813a0504250311600154149407080101d1501200c1c00c03c15500c00c5203003031a200c03660103602e1082c800010401000002c80201c12800d40e10743c2c03905901c4400c419aa1035004440701d07484050300304c1c0c0070302c1243d9100e00403540c0c0306000181e24183d009500d585441d509903200c6a10400d414210802000b00420b224a890108802045860030b4070b50022a03101c1c4103080c1d04080d0400c0060040c203201003a034011041c2c0c10707084203000f010280c5080140d040c0300001140c0024559a1850301030384465881c0c0480301008004099101b820419105407400987d196000d030380a00034408601524092403407082e00e44062103581149800381004a100c810721a84072084110380805040180e000c240380d000d1501842d8054858403000304150300300110020000014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658790593 1250 658789343 658789357
    0xc0c0f010c080702030f0f090607150b011d0604170f03070501060e240112060b070503090a0f0e040b04020a05090c13061d0613030204090311060604020a080f0a1e02 72
    0xa8141c201140700c00340080112100c3c1d10424094524100c03418240100039880446095081a4100054ac000c2884074407070001008146001113030111500f4001844a200841800948032a02100f81d00300d941d007004480440340d009901ca0f9a503107440104909101c0300d0f03903d10039139000014079001040b406500007400d4400780c0002d40300d0340d1290020b40c149a07581c84110780c0c1e68110b013102071905601035401d1469180880d20041207103038039400300e44156000b1841c00c9485a002003908001c1d0310b000c40082020780201002800650b01d807014080c116407000d0005010644510003040039500c5607810f840c0601006000c400d26803c00e20b00e05a1150f205141c201f80608068501180c110300c0744041004145c031840360f80e80c1040107881048440d030b012294140a4030042000000142c5a40c01a5140c95029489120290200ea0b140504090004041c282701e14030401c10196201e0300051203c2d00700010380307a9803a00342c0e00c0c4003402008126000ba0b510260032000c580e0410100c0a800500070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658791843 1250 658790593 658790597
    0x10b0a02010501061e030902031c17090d0c03050f130e011d07091401090f090203040203121c05090c03010e010f0f0605060405010311040f0315270206030c0c0f010c 72
    0x3a60703030303c13402143c00a82400040c403ca903003400007048042d02c41d40207407160314001000e4038010381e101c0c0c02d50f92004102c9070310400800c0c040007150f810005403503403d592080181000e06007403025980b004040881507000202400008102c000500e4030070005d48007007151255050f03510641350341502100060900c111550111020781084100303140300c401c54001d40d0192207402500313042c411064050098003403481d0400507000c60001c0c4ea880c0b110410801004100c2005940b802c02d07005250a19003c1d11600150302410003000410313181c401b0514503e2030014400040c0c80e26100c00b083e0a00147c0b4040540c0341d82403c4040040040c190b00001c1300c07691580342044514800102e03802a10040e11a99a211005100c10031040d40203801c090796245c000302c0628a469103a02c1403100b01400c54000ba51102e202a001c8502c4104612807501c142c2480c601400b146210410942c408c0401d03008001d00845011003c41c0001c11282c2c1503690403032030103090300d0840301d040c084240203010400b0040c2c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658793093 1250 658791843 658791851
    0xd020c0f0409051203060f0a031b0614090d060204151215050f090403090503060405070501030f020c1c05210405010c030612060e1c020f070807080a02040f0204030803010b0a0201 78
    0x42501e0144100035541d50f2020141140782d22252240030359410007000135411204440203002141e4400500801440c881c40c60078640d000c01d4580030b0094003154004206000c80c4420300c442c0103030400c09a4201400031240701901803104c2c80c1440182c042c55220991803c0e0441d000c442d00d54000c40b800c03030b038104108410032203218101c000690208943c402c0903004942d14482e0000c901305072804640c828024107002590580d107030003092803d28116420f983c0358000c071600b07010640e030502601e10a01c0b40500150300308003600c200c2a40350080d2607904180c10401030b100494182c00750381561aa0102100820300700314002c5a83d184180085504030b816501e880034441446001c0d100382001d4502102c90794150b9032042c0d40c1c941c0103001c41c403a145c1461241c0c210081ca90f2a400007039410b1340f09503a001e00b144070400001607182207066042040e994000083c18000080001074280c52190111030100301681c00e119280002d110342c4d040600007900000c000300f40c90a840c1c006046641e61503000300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658794343 1250 658793093 658793119
    0x1020a02010b041e23040f0b1e011206090b010609090e070f031704031203020c06090a0b0a240303020c330711040e2d030a0503180d020c 60
    0xc1340c407520580005100e045140c29006845684005034401e003014064610010304400020148001ca500700c031030500d00d0004104100300703000d200390400d0f143c004c0106040307280070000b40c0c2d085050141d90070401504030250b080c8519904040350258020181442ca0358482400400895103402900750030303403c08405100b6004005a1030080340c1c942d041c0c442c0014116960908031194050218003c04c205000200201c1c40d40b007444403011800d91030069031140000744641c20701c40001c003080807603040000c551000c203a0400006500c214441e4000507440c0045440e50700e101c07210080e060041054203c0070041580009002501c65400c40c0c0300e1045075400661484804141003000c458480700d1003001024107144d0015041c141c2c4035a628070a25200c050105003125401241e928403940201715440001c00104c0813010102c090b03004002200000007160b559038070803803080c1c008000d070010014159280c40740700b20841c21019401da40d904015144001e544081043c02e00d4480c104508c408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658795593 1250 658794343 658794349
    0x5130b161b080405120f1b0a0b090102060703021b0604050604050708061012030c050312060906030d140a021501031a01120210080910090c1805040305030a110d060801020a02010b 78
    0x1040c8141c0c1c0198010701c0c040c1004c0c2480340e80b40c3ea0ba00d0b980030300d10581900b00c00902d0280400d100c2800c801799900343c0d00e5416010485e5400190303209034845202002407070f01c2640d02083e51031344004282000b60307454030200c0350001402d0031700124407018040c0e002444104200890b41d0f5005500030f5084604242d11500e00302d0719041705541e840f8004070100410040442e1342c0d0078258526000b4100342c24070b140d2b203894203400c45e404405d0305018400900e0030465185044002c81d41c104001703400502810000c0c80019080440301441e4842c0c001022a900715658800c20070f0140500070a020f002a55950b07180000300041c03c0f1015510360070403d00041001c1210242e000061600182a034400e0403002000303803042e000241254180c0c0c050070080099182c02030042c07043e0309100318280d1428a06d0a00031030060f900110180802504083c1407102107903000301a81c2e08a850250001200a0300741b004440328441c22004231000c80c1841000550f1210642c003802c242e60280d0001e0007170000000070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658796843 1250 658795593 658795637
    0x10f050f0a092606070f20010902010f0206090c041d03070f0501060608070f03090c0f06050903100b0f0625060f0b100917030c120a1404030b010905130b16 68
    0x107901220b9100f400024841131007050400409813035420305610f0001f91800d00791068201042d280d03c560b442d494002c04559002409000086e41440688100d0600302040b907152030034140d00521039600c5104004c00500240405140040d00c0d508807541e90115180550a982c032030007003500c0d20751030000d000a401d030080c1c8005119880c180d03140c188000c0e141a068004240541041d510008000004210369490003100e1000d440a0340319140c840c41100109450714001a0300075070b0850034000c0c628000e407551204032001140840f02c0c1c40e11114074400fa0002c1c01560400100ca03449850341c00c8c030070b02101e41e100c00c44d0045210400d0211012600c284164041c900c0b1603100001c081c2481008424520944c02521309c041e141075900d0300088107090f03440c00c0c0081402d00134034400081e000c0380007a0040b5403010b50340b070400365071801c0a1542c4c640c0540264144502186d05441e403000601c03841044003030100317480d40591080d42a060a040c1c450316071000140101c085071002c3c00307101e654044554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658798093 1250 658796843 658796909
    0x303020105040213020f1e0918100914010311180a02091201090f0b0603120d02032703120a140a0504020901060e0a091d0345010f050f0a09 61
    0x20101c1c039040c00f40012803107080707003050b81d50303000c80050044031955500c41d5180050510402740c1c2080d141081070065000000a5124140140c5080300c42c1c0942a034400c041030449411640b025007440c0c050012a0885c0c0340d001c3c4a40c0b205200340200300c3d4602d25580030742004182a81c82144200035030480c58201c1d14010000f0b080c0030196080100024400c1c01c523164070000140603540c2d03190380e488101c21a900800c2400d921240c0100070401c110609501d55000480c140421141480070703440c0c80c3d51684900406100000d4460300040c110607050b0f0004800c80340c5e8902c40c208140b4140200d5002060305603012803081140303000000d40f080c070813a540411058001c00035001d59117003040400003455040d160110035445543c80b18003400050020300f40c035100c0c1c000055000115241e180b8940e445d50029040c04a5000c9862001103246a408440011083c03c265901d01c1148900380c0d42400340040400e840c2c000020350110700c2ea0700880c20801c030344458001002c007150950301c040c01e00d0743c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658799343 1250 658798093 658798117
    0x5010e0303030420030a0308041b050d0308090c090c09010e101722030f0f0203070b070806010909151806080a0f082701020f0f0d0309050f0304030302010504021302 72
    0x4804140400c1302c1c04140d581c16480140045400c01941001c1384c00c050f030590040c0c0110b9009002c00c400c0c0a400340d001c2d08220303100da007080e0303845003004005100000101c40c0681049544000620190340400c0080b81410008080c0511881d18003002640380d40034861060006140e40c4a09005003400b141044902002c0d4642601d00039400160011000b00100341d14107207040b1001d01c4800040c1320790946003182c000c0c1d560280c070310643c040103007070804144500c0003154070412405001c40c001400c81a00000383d843c00c0b400039129076004803686c14450300141c91b4107140512801c900c80b00510700c142220f03111003c0c1002c1000e100c01245c2150364500c24070410b908122006000255082d084a40241c841d0789100d080c01c0c19071542d07403001380f1082c4201900d450420324044403580c040003400b40c00600907000305480c82c1840415a1100d1144200e6428181c0f5485404c0801c20305102c4003201510481c100c0b9111956400c009018040c240d900f41d000b0b10051012182c840030300c0c02243c00ca03511103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658800593 1250 658799343 658799347
    0x21e07150b03100903091a2517070203151f0e06030a080915301017072c0105060705060c250609060b0402040e010b07050f060a060602010605010e0303 66
    0x4007800f0003030310280d08102c08021919402007000d8100e0003029243c000ca040349540c81c0c0c80391000da1010b502036007411a000d09100c244032400100c1c841d500100c00d0b112021440d80740c10b4140f000ca49400322004c0702c007800da281c0c9001c1000d0746c0040480d070401c2c4120725420150596540c0d6800c20101001c6e00c40d281c041e00405c180c040402c078a20000c0c6840c130400b6220158504107010300c0500d40c2c00400c3c00b02d118002c203402882c10003056020101c51100301914019107414a2034040302100c0341c900c5401d00703000407400005281e00050050710b000701407800002c2e0440e1a402c2d0003100c032000c0950304803000808000085520b09000c42998142076010000341240e448000c1214010380002c00c80b461004015629002e8401410440e00d88485c812000410000740c40d140580c1500c0303907105454001e038414081081001280300c20070341150542125140d5070300310360400314100b429100d007a81d200d100340000c1c0080c00096901c40340071614a540200010340e203450044809a180e407060035031550007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658801843 1250 658800593 658800613
    0x21e0a0803041109070c0302071d0a050a020912030405031501031a0907120305030402100516170f03160f020a0804170a0b0109020a1701060804080a03021e07150b03 72
    0x940d00464201d40a46000006a80018005012818116883c3c80014501e024050405030100084000f4046020b05400fa10f8040c540554020f64024500c00c0200c0c0c840c0003040c1d08800903070443c0c15006014158809081c48144400c1d03880c3d000d4410540030307108840803540e044d10701c1888941620341c8a85c880c0d040c11100c50b440340c24880090004a02c038051018002007000c0c0c5d5002d0418124401e03100c10b5203926240c01009800c2c51440014414890104145250540c1c03034914000100e520000300700402c40d08101241d4071340603900449120880000522140c2c100114146118044560b240101c03581e010004a884640500000b400480c0c00d200502070b4a44188100380070184c908100c40162001d40c40b8a15148420fa01c40002640d00103542901c00da0b101c1020002801e01384c05210b61540b51100c01440c0302001403008d0410440890507140d40d0f4031a40441e08845d40030101c0309000c10040b0b140401d180c2c450703a0100c50b40070b4004511083c1448a024000c031410303004014001c03a0007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658803093 1250 658801843 658801853
    0x60312070606050616051e19050a0f1a09030f071e06090c0f1707061b05030304030201140702010b100e2e0906081009110405120a0201021e0a 62
    0x1082040711400c0e218038000c55603458401c06480c0c001c00c88101c0d00c00c2560141003103410a08011100301850515907022034501400064000814400101c010104010307403e08038105501180300402d05810b00010200348480c0c00e9074800484a0303013103481060345880020551f284100800000710304000e03c0064081030756007000050003402040705c20003007032003603450808030340e00b203081101c40118940c4103000e41c49540400344040d120f00d91224586004c03c80340305960b00054441c0c3c104201e07546040c0d07050780e40705010110546030700208136038481c2458500a0b010308002610401300d450414001441d5510501400050b682e0180c21800c80c80000902100c0e0341c050704440795000100010040c1c02501c1d401d01c0c116040e84000020680e40040e070900a043e405264051800c0103070007000d008960b043c10f104070013121034500380010403046150040c002406283d0001398050101903500e1550303080419000070440c800d90030349084103441624045200056150500c0319030140f103039031000070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658804343 1250 658803093 658803097
    0x504020f0409051021020102031207180602031917040f02120304060e0f01020a032a0210051804050114060d1b02071a310b041d0c03060312 61
    0x4289152a45000c2e11800d007202621001d07038505511400fa01c0b400c000d03040030070101c80321240b140d440011207040540c0000b0342c0c034015104540d40820354080441c16050103040910501ca13080c0e41c1486460b9990f401c080e480c0d800080c026542d000c070035100075082502c03800004403152606030000c1141d4440d51600e20300d01e0301114040340c0242800c2c4012500740c0f820400744c001000346640c1c0a4032000310030244406554400c500f207042d5800a1101000241c00c0b202d41204070503c00c00010b00300c86c089030280364004080740040c1d08151006000701800b81d2050052810740d01107011070b0b0403c00030400380005ca42c400d00c6822004070724804502400c0c039004c5c004000141690502250700d0000d1400c0c2d0b5100380612a0b40300250303010000c200215171600d803800d03060941e4074607036504080e2145010300108030305203500000c9203038960800303001e0310031800440003400c0c003c145183c5032515012084508010044040e0708240900000740446521004681c4900401380c00b41c8140038290031146055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658805593 1250 658804343 658804357
    0xc03020c220c030f0609090c15080f15040203040b01081912050a0c0c2c0702060f0c0d0c11010e030f040e0c0708030405011b030e0c061c0f0213061701050402 69
    0x5403a6881544c0001d52405050041c05c030400c00000c2200307080c41e24544850390366210344420401d40e00c0516699401100c2d0b80c0e40032210740ca440d400c4c1d59031700c44504039000d030b03200406034028808408c2c8020b01002d0b41d06103042e680d8100880d1215085a514800c851529020050650580e1100d4048403032084005d00380b4444541081c3d40c20440e10780e0b81035100c00e01500045804181d243c240d400b43c40c0d82410240000102d01001c00260400100003500e540006220760341c00300e52280414010501d107003c58035440d251000800c40c40f0001d900c01060b0b200700002c8450150b00304088070b0a000c502104480d280c43e400c200741c0346814a031000003071840d040240f140007002c20900a52001c5084071004511642c420000000c4008040f10319074107421885002c4401c06141020543c64400b0001e100c00b20000111245915919046040904210042c1949101f00d0900c3d4070510b0007000e07500989a64460a540c40d00e07140d865034404c4441041d6100c511107071010450041180f403c050b4000e04407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658806843 1250 658805593 658805597
    0x15130b010905150331060903110f010c020f0f07090b0d2a0e04020d0204050903090307180c030e030307050c0c0a27021905160b070c03020c220c 63
    0xc0c1d81c2d41c8a000542e01018240022040540041009658440d070386900d03030076445400c89048402109600b100d040001003100403c00c1c5d030340c2c4005005140c001c2a06000c8005442c080f50004145824818040c2840600200151054050380d50881e1804a465000c030318510008001039850f010380200a45840d070b24040d00a00060201d401040c0d08214515448001880382e8401c44041d0b5000d0052034129403210042c000010103000069a41c5403150314103540450f004071b601c0e100c1c10a5541188a66030850703505200d00c110005000d011004400e41d045100c12041041c0b2414030300c29015501142c04164003074200300700041c4110b0246000e80300e207030118400ca400485080303020580c0e096054000c04500c100618240d0300a00c280c0c2800e030300c0701e0b900c0e89003503080c0540469400e200454030040c0b141800000b10f9051040e001081d4034402203600aa1208080d080c225009411130400c8001036005000d0320054850700c1c1002c203000b60022000c6000c1c064100c0e521003504000301407001c81041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658808093 1250 658806843 658806857
    0x806011d0418140d020c0d120503040201030f020d0e1b01170702070b0f36010c05100204030b041505070206060405041401090305090a0806010b09040507050408121215130b01 76
    0xc08070344482c3d0f001240e10105002042d02e04e10542001e441e00c01440364840c400d44c44640034000003030100c0c0740c1c21031886840c02d01d80d0b06c1e074030396100680280038001c4103c0001440403070f0314201c090b0113400c039810b00d080090649640c0c800c403681d006010803042c07860341e002c26070302c06c164810078002d840e0007980019148140c07441c0399142c0700f0860341a4020210300b2000000484c242c96030201401c0c140c1001c0f03110403608a40240c419140582c10114100d201d4140060601c1d6001400300900c5070203540c98460b90119500c94032031401e650070220580702034070b20280500701144240c8152081c1d0340660007035001462156204401c0101928005100701c2d01c06449883d89a4095000d00481c09003602c41c0c3c03035881e100d002943c1400603441e4030703511100d499403003140108000301c43c01c4202d5009003401e82d008106030ba80ca4a0687c0c41d4499503000c001d83d80318030160710f606031100f040540909450076026001c1038582c008290030861506109a52142c610002d0704015141d0b50300403080c0c007606040c481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658809343 1250 658808093 658808141
    0x60f0910060e06150a141e03010305010c110a11041107120903060e070b0711030f07030609051606050d090519050102072a090b03011401080c010806011d04 68
    0x1601c0c410750021410180c030302d05001c2c9510b41140304903080701d07008070140c2c244241040b00516031200e90684490303050340021485001f2103800394103807207008640704041d502d5a5034a44036009092200e141000280307503030844030380701a000c5078414816410000814820440604120080003501c0980303002d1708042140c4d100080019603018400c04194642c0080d06155003805010385041c29869282900801c0080c4400c060800542e100035070480703080c80d403103081c41d0042440c2c80412b6001c11030f18411030200200304003490300046410340c41042900e400a000b80b40d03503028005107010f94404264188200300340400313146d000191181c000ca08a640e80006040b10034840400b00d002a1080c3c2d400040c800140004681e03034000c0d0004c8082400c854541e4244000c0c0201c109000f03030702c8203c2e201da200d9410b50b5002d410203c040d0f14500800c804a59440d0700700da030345103c0e80001a0201e007805001501d1580102d00282641644601d04144240d6030000c100040c034488910820707070500700c0610f0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658810593 1250 658809343 658809373
    0x30a020d0e210301050d03050c030708220902040e0402040906110f0a08130807020d030e03030a0509010f090509130305041e0305150c1b2427060f09 65
    0xc0d00c0d40c0c80d0394078054800215600151620038420038521a008603040004105030384449003010b014a40600d001501c903400300321010709500c201100641070b80b102040c00d0552002540d07080c201104c0c100309c4010040e644813444801e0f400344d4030410741c11020300c80025002d81000d40140310014803d10300014000401c400c0160280c000740b129005980020402d0301c000c0f6000040550400320300c480b5104507404a590718001032280340e8009004400351500c05080602038610143c990000a0940741c540c40c1c103800080180e04584009400141e1840e10f100704280540c1076001500d401412034002940c4140814144010035101141000741c04c000008940440c0d282e1500d06503d081c1e0140300d400c4c80c1d03061561030040b02c5807400c1a074030b4039002031100c90940041102c0d65000d950f9402d80048040408481c28a2040681030961000042038109001411165035104044800038500c20352a8071540580c050614004580e107036010601164000b60040d1020350b10480c0352040354640c000407145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658811843 1250 658810593 658810601
    0x3020606040e011812301503050727050f15120114011d13060f0b06130911090303160f080c0109030306090207082704140a0f020f030c030a020d 63
    0x709940e804460602d000001ea4405286110380041103142d46e560f214020340c01c143d40c031a106039603009030f035900581002d0092101c480001140c000d41074404050303807104030801e410303003400454101c2104030040d06005203407840303800d001d078214030b904030741a80c1c411070f071210038010110390150b102c12a00c06401d10b00101b401207018450b00c8900c80c000c01c0d4542040960749040004140b0a48422202005841d01000030706891103a0064000300d620308403424944010706540b0b0344260044000030707040101c010344103024011078001070401c2245a6130710075403680310700804440c00e92682041021302000050040784940c8580280c54025154105036944012036004460044447c0d4549071408107054061051600038004944203502d0104244d0300c0410500c92011040300145032a14102d2020801a0840c516408050300404c00250110301c4464144022281d8252241c203200041c03144014034025224075031030510303540c0d0560f101c2c41600680ea4100800c550075681d420700c2048841551406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658812949 1106 658811843 658811891
    0x20a08030a020708041a070506010e10030201050c010209060403050f070b13030f0525050316050603070f0c060c05070b0703050903030a110d0e1e0a03020606040e01 72
    0x41c14110702d00890300010031b8242c004c2d84a807002213100c002010000e0084044a0051380e035010030126408040303440158a49403500300b0401540a8000b501400d00060000340c02d04c00001c000c16007940040e80251110fa000505520034003505000d414042c03c0003941e40361800c0700551805180c025584802040500c148407804103111003072040c51981094200c00c00312141007521907070300b5a0340ba0b005840c820300420703070020021070300c05108204071600074204c1415940c03a0b56098400b907098691550900451007a1900084c100d0311401c0c400d11041e8a4154803500701d800e280301c0000c03000300100b050500d050240710758140004281c03030340511003040110b0001c0c2041b4017040310707018452489801034201580702c92544008540140b60f800300c0d05001c05851000c440899070341010f41406009600880003203604da040642042c441c0460040002c00c56140481c0c1d10400542005 = true := by decide +kernel

theorem cover : BRFrame.Cov 658633093 658812949 := by
  have h0 := BRFrame.cov_init 658633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658633093 ≤ n) (h2 : n < 658812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
