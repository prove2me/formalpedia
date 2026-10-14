-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1711
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:23:46.493559+00:00
-- url     : https://prove2.me/submissions/412fb9ff-f2d6-41da-95b9-13b21347514f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307553956 ≤ n < 307733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307555206 1250 307553956 307553959
    0x106030b0306070e0f220c0c031e0302040e070315050f09220506090d030501060819090503090310060504140105090a111c090c0f150809120f031e040809 67
    0x1c440c080c04004a04007000d2850802d030444c040d100c1b03c185034450304401103015210041c007048070150000701100c01c2d1100040280108680a01e04c11442c456582c0e0b021b549191414090b02c2c1c1a5614500c041c5c081d01141c884002135614034184880c111840c001000030101100c012504003d40b03400500f00305d5000d031441d2268007407048044100803030361103403024103608401926128030b0292400c540303030310020741c00314002032500c400404e80c0c80c051088203004a0070a2100c01c446142c1c80202d50040c81d01a2065a15210030300c01820745940c00c114400b500540030a000c26140c0c500010b100c2981d5480020107500340c41c20006021076141c0b00c0aa0b907104056007008a11030100000d000300310b102e804082c100c0d842c603083c10410010070715008001401d02c00d806070f041043ea580800324240929010b444201801c26000501561098008a802c040d189040c0e4401420110041450b6884190402c11584000c4200310988510001103800341c00c02400103005803401c1e60700c04500c0d00c2481c507032a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307556456 1250 307555206 307555217
    0xc04050d050109060615030b091603020c0c041a091e39040302271503010e03070606060f030e031917010305010501150c0804060f051c020d050106030b030607 69
    0x900c81d09411108406803c28000c008080d102c000c0c00c1e94003480301d265500803d0030901031400303e040c05440c00d485809103007200c11201503011002c1380698080c014100280c0701d000d90510070356685100b0b072001e0f801003803032210564654070107012003c1302c0107290380c501e00343c4251402240c040d41890654080c0c0b040c5e28051311040c603120703005000484100d03012602007400c8940c030342ea07008510003041580d000300d0301201000450a407844d03d60030200e1408207410f905901103249040d040140204110009002041c00b4150308840392458005c04010fa40300d03622038000700407043d00038060340c554482901e802e004a031078007000c190362482040c1c0d80d842c00c00103260040c0d00e1075110380090a485e8060303580220b0300d075a403401c10034068031003030240300c030885010503054000c0e5000e40c2000c260194003801903402e1601e442c0c425140c207040b82d0303010320a10000308a0304d1103c0444c495502603c03114807900680718403c0d04451012544143c101074113061411940315010798001803450307409112031424 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307557706 1250 307556456 307556479
    0x70c030f05070308030901051806040c05060f0d05090d0809120a0f1e1808030901080604020f19050706060f0503100510090c0e0301181509020415031101080a050c0405 73
    0x1007440c2c01080d80c806850810040300344000000c06400542c0200384042000700301c081c04600c4c0c1503d40405850061000141a804000b10300300107004e000b4800c0440310315420840883c0c1b0720410788004441210064025444090314075800c08001c94009244000030110792008444001c09441400032032002d00c0401c400c000080b80c45102986c110000060a54600c44001c12002d00b0b40030401c5980c0c0e9186a40100c04034070b085000040c1d50715017405a4802303419889010901009601c15001d1700c22201040100c9012402c4101d0181d41c0b5541590700c140d651919400e01408840785504030030505c200c0403c007008244d400040801e0201e80d40b00c0700107026203516002038541c2c0c1441d4050780c5c0c95800e024100044541083c0c06403100d6a0513130003484000020341c004000380e080654000c102e016a000500d8858029510411000784050320000b060f024414640b564801c256104560188084042e043c85581c44109140c02c81d111360400d01182c00e142d29003580300c7c010740c000c81d4000d0008050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307558956 1250 307557706 307557713
    0x5071106070609050f0729090406030b040305130801290117070201020403060f050705040b030901150b0406030b01020a051b010203040b0d0203061c030c081602190911070c030f 77
    0x221010198400000c005022142c130306503803620940c40c4000642e0281860000d4880d051a00c2402c4090903100d1042c0c0d80d01c0018003861994006103003094219030784003004000191010f4000303014030300a4560945945042a400c2c1800c02e0036001003c00b64142411001c80c01c0d800c0003001c40d18001c01030000d02116402c00103c031000c0c008000e550407000d2034024803400c150190f000740700742c9014a00610901112100c08019180259524000500c0c100020042e07031801c8809903400c48866000441c0c40c07524040c1d00511396100f41c0200c3c14514000508010680d0944184800c4220070b001400c00e2424688a09881d03001100e40f0b028081040008081c45078420b104581c054006442101d444482c0f10f040c1000a4100b02c0b00c09000302100803840e04402c0030001003007009649680e070750380076111548d81c0400e5504803a44c000c812028a0070b0756001640c404e100d850f000c440d966270f078160152600b0320103400d44070b8241c1865001c1008101d2200402d902e0783c0c0321019281c0180c01e40f07156501c14907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307560206 1250 307558956 307558969
    0xf08030a0b0406090b010909110a110709150504050619090b0112180b090a0506010605090f060703180f033c110f041406090603030c0106090203040b0a0903050711 71
    0xc1c40a90007880c000c004101039400e603212901c404003c3ea107104a150715104207400b21810385c0850855a03000740310120300c0318070a802035608005000c003611003d41c1d82c0c0c0c00010a542203400400b61101d8007070b00c00d010505003889202c0d4414406c0f54101c0c002078030170300c1c158490300d481d004000000340c44032200040e907400340040c40030414244004000e00d982510381d02011240301c0c0700c00c41c0d50701441c802150310214009419000c154001020f850b03582d1030300e00d080d070350740d40204500c0e034120f902c0c0502002641d4820009c1c00f0140d01070b89400c01020b444003100c1525601c0c0e5088020304000c1e041c030500c041054441070a01044074101c8410704440b0011041d042c20041402e18580e02800143c0d5404100c8200a28641709400f074038030b0b1801103091004c2005507000311b0788400c000d40c8160001341080ca801e82c0076541011020341a00d1400c0303054030010b0701b0741d00c0c00c3c0c01841c48650000107000c1006482482d060b4010141d60082100703240584c1c0041080c400e80b03401030208803a01c5100035955a812 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307561456 1250 307560206 307560221
    0x50c1606110c15090c0108010503060f041719080705040803090616060608070602010c02010b09041b0503030c0f101b0c03090e07080604050603010b01020c101404062a0f08030a 77
    0xd001c580058032038540058610000704e0301e406160044000d407036543c2d4080c0c1070b424140c800c003c0180105690704140c2c403418200040042d511034141aa550006044030001480345910300500c071000410f0040740546044c0e4041c11000401104000070000e104012043d0b400d9418110f40d41555480c180c1d0038000800c1c9060340c040c02c01440c0c80c5001030003000014508086505a80080c000b40300c0c466010b90032a03131504042074201c2203940000300014007400c50b00700080a0303440c20145464580c004289550400351651545038041c807001e0403020b0042200c1d800001f401ca50522607503515442c20f203107000040d8804024001c082d181c8c901054040c070745000240402e20b001e6901c0f4600110000d296060036103102d4001d52410021840324181030184064500043e00100300c0d5900c0c6205200d90f200070100c0303003410465662000790b88451504024801090b86554040b9030011100801008421124015403101c14045080d400070b650104514217460304446070030b4490340c5540c00a40a407800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307562706 1250 307561456 307561477
    0x7051002030a090b070f0504050d051c050a031401260703050d02030702100314010302060904020f0d0510080a031413030b0f0f0615030c03060102190803040204050c160611 75
    0x120400142c804142d010ba11030600035084000c140c2c90302507050381c80b0300c4291070305c0f000200100400d02840c24000c03400f00d10544504212040b40412020751502070000124500000d14000b41c50401c15a041c0904000c6060001c01205554504114100d9030741100300310091981012544c1001e104051000c5802142c01109072610b10201c5200252031381c0c84104100e10842e00304124141e000d03c0b0b4468688500e50400311500103908503001c000b60ba80011030003035801b0340c080220080c05683d603005090046e81c0014041050305040ba000d80e104d1302a034100700400d80c4840d040c0008aa0710014400740d029100381c460b591038140c618441204801d5800140036850a0424040741d02c1191165034800d070400c0102c4c04040c1c403403804209400c4002c21403811200010300c0860160407c80d001140c20140500444000c0f80c0900b200140001c3c0d011700c241c80914000c070400c01941413602070194030143c3d1413111740c5006200d0380320245d241494407001c1c140035520656810051150300c00c0350280d440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307563956 1250 307562706 307562711
    0xc020f0a0b040c2114120d02041d2203090b04080d080108010c090b0f0409090b0f070525020d1e030201200901110a08030421080106020c06070510 64
    0x1040d0900060109040d1011500b80d5112280001c200c201e003e02000d4031040d01c1e01345110007070715460340f0700c140780d4007480200180102d03001048a14001c0c80102441010300e1030158480e4644503014180ea50310483c011203104040c2c0800100d04046ea00703800510070802c00301000c102d001e00702100d000003140c01640701c460b4009800b04404000155210b00880c0300d41d65100c880c3c0e202d80c5442c2c2a2424a82000f0203d052182c0a00600b00c00c503018140e1030994202440c2800d5072445604c0c1501d40c40071707041c1c1e104a03102c801d00070325410f0741d400c095004d446030401d41d00d01092a0700040c074441d1030710b05109101070030700c2a003c210360700c10070074002d1540c01c100515401c1e550b0304114043d40c02c59440480c0551b00e02601607128280785100d440706001d0707405c000c504210382000191420070004e6035880880c000c200d8040d000900140140d80610301450000d900d50090004441038215180c07926001d02841c10010441503070b000487c5065070005a1f409520b0f561a40313041480d201141d483d1800190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307565206 1250 307563956 307563973
    0x504030c080a05091c120e01080c090d05010c030e070902030f060906010c021801080c04060f0501030c05040305030703050706060801020c070b09041811100513030609030e030604031e02030c100c020f 87
    0x100c0c80341030444c0321b00403406500d00c1d0305111800d4075813407585403086011401840000b506140410007810030150b0103050140602c03400c0d82c0b8503086880d43c6600d030780865038503a501200c1010411a84000d0030150710218558103010440400d255030082019109030300400000380b169101d1a89003100f50b038060701c4030601e09030401c503010f100e803024044c1043c0c501c10396208658a02d8503019580c101e940c0305801e098100d080900440203000345e000c010061180c01c000001c0001c45c2007004145450082d91100d0721682c0c44e1804000303495003680f20401ea42c1c010f011002c0303058004a0a80c0c203c89018864a54031144503002c5405004825191000c40c4050100742c814801003c00d0042c103100c0440324075001d20303040c010545940c011480050b000106c1000c0510006601d9802804568000d061a4200541002c00685000c03000ca078100c00003240b51852181000f180003100407c40424000b03141490311b00701300c40e40da400f02890780b0309560b51160000310b9078a0083c17100300028100d1006640c480c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307566456 1250 307565206 307565239
    0x20f01050d2903150115090b03040501061806180515150306030d031b0509010309080f0c0d030c1409150403051b09040312050910020a0c0203100504030c080a0509 71
    0x2c07000407911844011a003021524a1a0100302c11440010a19000409900301410241c0800c00b519510060020800d808544c409950001d1803050384100c0021038000c2c10300e000c114440c030748000c000c1300039400c00ea801d02c201d0b0550741c100460b80e0012000042c2955680c0021302c10641d8462040c0c2d004683c116107400604003020086208030002d80840e456003030b414204030120340104218802c11200c0300080303001140320780001c0401c1c000500d80494000050f80310902240e100d0000c005000300001000000d10406020142d00c0749002e007010421034209400103800103070340f41440604140000780a056681d00c0b080380a44045107906519256a101d1400540e00c0c00500b011004000660302c150407280740c10807480784540d44c9a6928994420074840d81d00c040e1a01900b82c1001d4000c291813418000d0040c4041c01591166546240280c0c6850050506200070703416402d4104d030900041001281d04129621021548140f08071754641141030110340c14000c42c21940c0d40300c0800030440d10310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307567706 1250 307566456 307566491
    0x2070b04060c0c0b03090a0f0809060409050618090607030f0f090b010501121a01030c120e03131a040b0c0f060a02190305070e0405132301050106140403020f01050d 72
    0x4a4460403c1c410060b881e10300c40311580c042100d03c2c100ca580b0071100940041e202400c182c42d070512807032078541000071002c0007820642054101203a15903441c002c001f45494903c490011008401100041c00c1c10011519900d451008240106040c1c40f004501c0e80c411065100f0222801500420886440f16140c1051000c0c02807065a00245032401002c170350907a984102c00c10002403001d548604020040150060002c0c008044141710340c1714249200000f0038043c42120085000203580d50340d243d9503441704c005a0b10740100545a1502402040707404c445000c0301c090300c0c0800344840c0c07214071001c001460a034021104001a00800d8140070034142e65801915000e41210b0010501c0a003255044040350030440300324000039040c00a400d15410943d01164000c840d45190790401103141c0c4a078080816108003481105c1e135825188100c03013000b882107501401d45460b1000401e00c00d0654025140114000a80708151059001c0c02c83da006100320340126031504800d000c0320440001d1600ba = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307568956 1250 307567706 307567727
    0x408030f030106020708070e0f1806090606040c0e030712230307030f03091a06060405120609250b0d0612030f030b03060712050603030403050a05070f12031e02070b0406 74
    0x141c41114400324200c000400d020701036400310f42d001100c8ea6240d0519084a8034042c005081e00c0490707140c0110803010a22030648110241d00c01030040741081c0b41403101301e03014221000104040081d0140c0b096401084110444034007440191040215081014820101e455000d503404c03108442030303465903804005084894000c0c0ca4801d040707074085400360107681500f18000d000040800b0042c08580c12070091580140c8080c00c074905103901c079004a00c561038102d0a80788168443c0d020807181d181d040100040d5040920720105000c040d0103041c1c11441c100b806901200342005c01c45403103036036030356000f10014201c035042c0c602d68104505001e010745030b40d010200002401e2070318211260a001641e45c0c002d150b00c2da01d18480c503000c40d02e0407000f030a01030a5194103010400000001c110b040060101d03841c011409801c00074a8041d010021000f55880a01c003605105854400300380c11143c00c2034110244800340c1c40340062010b040741480b0041d04110301071000800d010810ba98482e06224 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307570206 1250 307568956 307568969
    0xe150d0b0106090b12010e0a090501020a02011d0c09070c06021306091503380d03030506090708070212030a0b090906160c0807080a14070f06060b0711040c050408030f0301 75
    0x326004d440c1c1d6028400b6201e04500720f00507034403400040040040205103581c1c029403468000031660403035601e40f400da1b880b034840200140c0d12140b000d440c14040b0590f614021504100901d05100c0d41004985002c000500b440d06029444014809200c565011a00d00581d0303800903250036500c540b0040c0c000300003401003441520a4101141c1100c0c061310522011000d00c00c3c1c0c4441c88040802e02c4c0c82486847c0416210b150324950800e80991107401c14035126922070b4401007200d240060602c403207507100410803000c100c1180d051018564020954800040082c0e0310306550ba81c4889400b07000d05041c1d5011600420381c4800c1000480004c2101401580100f800714500161200300300e0b48965900000f80030358408100703c070001002d900080a10072a40d040c03040d814541c0d8040c9244a402c8048159840b10030450303404108060361180ca006401c00340801410280d280c0c032407459070307040d600c5a02e01881d554402942441e0155040d240185803440c00c8958464a00c4c0d20350550303401c02c0c892079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307571456 1250 307570206 307570217
    0x11121b1f0e010e060c0c01110d050108010b010c120302030a180f060501080a0b061318030e010909060b070b060a0b0705071d0903121314010b09060f0a0e150d0b0106 72
    0x594080206000780f40309124003000034070351502e40031041c055607404540d22001d00d40d0b82d00504600d440a038400741444090305000069070758580b00d003403403d56440c040818100458100b0120002d064200310f5102c2440310316005841756640243d08000f04206089292084d620341c0c4040b0802002e0b2184298003071044605000d6640d9840200e070380c820406400910300010f41c800a4103d003450b107498130b80400b400d440890600c200c5003200d0311006400704250002141407160000c0c558101406c00010b0548a1040100500d84414074400d80503440004107004c1c03002010941c1d590307480b0644400707488c001200399910f0449240807030352240d0034400c00b000004aa0300b415140c1d00c15807815031080c5c0958002e145091000b203052020208c00615000d12598490356a0000c40c62050365140041d840000004000d04440d080020300300d07004010510402c100d155074010b90b15005070a1080791b00314202904c0d5a184c1485104508000e0303020309030005200c0048a06002a12032554105c0c0c0c2c154558 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307572706 1250 307571456 307571471
    0xe1309020a0e1e040510050403080f010e01060e0d03020f0313090f06050102060403050c011e0504030e0a150309020307050d080306180c0910110a03030c0f11121b1f 72
    0xc8079100c1200d040011a810511816074055103d680030344c0540302c0c2c0155981c405149802000321035041e20250300090b0804200003080c00d07642201809045461801485585030000003001c130001d0004160154a01000d0b2404050081052084414011050b60b4845401d07400d6000038441c184a51500715003040c2815040c0d54003485400151201030f40600b103070b59035030f403400d480342c1e40140444840766682e4851800d2040150811500c044011078000c280e604060030010309583d50041d1031441404c00540801c10007860380320b9092004400d00300801c0002107400068140b4102c0d50195400100b08180c0c003040240b0030000794400c0504071884003441c1d000060707003800c111003103910782d401803000c000c40a0035140414602607045820b2a050707c0002c04030103a02d0500f465800100d02082d00c54001d00082d0790850912180c0c0c220a190402c500445c50300b440756258850317020700c10104000990b580b428850b807902c0e1550450158110b41036510b43d42a2000c400c009014151a070034940300c0b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307573956 1250 307572706 307572719
    0x51c02060915010b0d020313140114071b02270408040503070821030a0b041a040c14030f0702012a2a0b0702010e0a1113060602120a0e1309020a 63
    0x19014103858a0130b00407030900140501501c000e520251484102507040e140440000c0c070980c0d090f040d40c000200002c543d80d04000180141c54101a18003824070283c00296640c18100c6401803041540490320010400410103071201c0c0740c0301194074826076042032001c00c4203001c01000204101e40d0268111481d0650b528801c3d9202d4001141c0c1c1a1085070710350305140c031000b01c000075540020030301400080b1071102d840014210340d40300c024441c4150000210245a14103840344105108042c00c0083c1d400e50042941d0b83c0510009089100c1c0c0703445500460300c00f0703100754030518180c400e802c40c40b02c01d94440f181d0b50782c4e6200d1109582d0002002c100e1a804040040600d06020218590014880315003540d82d42d012000014280703002c41d96910400000b0b8042005100d44440c01605030000100110b4248a10070071260ba1300c80c0c0b01d0341010b004003c610b0340042c400250405134030300a038a503200c6140803126084417820003548180c01e00b66050308000903611901da0740e80700f1520902d400e6030380c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307575206 1250 307573956 307573993
    0x5090406240807150201060609090209060922110a12020c0a0506010605030114030c0a030f0204151206270b04050a0c0b0a0810030201080105040c090302030a0302010506090903030112030507051c020609 88
    0xb48c000186141000700040e100d6500900300f811801000d035800d110075078001c01c5126807014259185c070726080b680b041130401a072003440340c4010351502ca28544103081001520300007440707044a80c0313103a0005405040d94000c0c441c5c855080c4c0c0c4401500c43c0d55945e040d00801c507401c280545150030102c002d942c14585400104103c98400141000b40c0c41840d41d01c541c90f007017500348402d980150b15403082d0310300c11a01e038074030f0720140c68891130640124400303040ca001101c169171109103110024503514401c400d8218005000c1a42c4072150a02d00e5441d45406c038105500014010900c0943c1803012901e04192009050740d082156034001150b030f030760b0001d10716880192101038085001d100040c8002d003000c1c0c20060b00d1440b941801400e02d966613000c02c2c03502c3d40c80a401e40040c0d54500030b03c0641d113403e8591582220781c08000b0360845d41007a5603501b0030911000c00806100000520b1400c000080c8000380703203642150022000c40b410903101035143d0340100c0310503110307026001c0002e03203001035030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307576456 1250 307575206 307575209
    0x1080711060118020c010e0d02100204180e250312020a0b0f0c07150609060e160c11030114100803071a0601030204030b041a010f0509040624080715020106 68
    0x64001d01c0141d2030b00300442800c0300707109400d0482c6a0200805141440c0901480c0f1480700014014611100c002c2402420b00000342030500940d401040204290941040031030070041c11113000040e0500703014035483c07500b0942c10f40c02c2042880d280341840b46051211a14044030f02801c0b0207584000c0d6103c0c201e07200e80c000000100002c042d50081802a000c03810540d901950311640c0c0d5103010450340380c004404c83c1071201c2c80006a112070003449807007800c0c01088000c208800c2030000707909103545060b4050324901c11040820107074520403c20f028290301ea4000b0480081c0080101c1c48070907a8452a00707000b12411030803003201c2075000030b6084000080310444c0b900500d80b0303140134030103041004141c90042d181c039041540038800030001c500d2030329509004901c1307500e4542080b040102200321035001684103145403200d042041001d51607915815510552041e400103041241081020700405140342c8c0201200c80c5010110f5404000500e00c8161060014030302016400c005c0c0890984645 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307577706 1250 307576456 307576487
    0xb0f010f0c0f0309170304080f0601030309090f020405090f060108061905010e030a060203070908060105010f1d0d1506090b0402091f030f020d050717010308031515070809010807 78
    0x200d00780000c90740514140c80c4440c40b84c900710103400e94401001e0003200418040460581000408214a410400c4009070220410000d00340540c510344024107084640d00c80c00310742c00e40311900000310b00c04582c11540944001050312050342000d990740249181e0071146580031854820100310310745481c0163b181c0140c844d0311040c00080c100703c0112144444020f480390144074140d103210005800303001462150b80582d803200c0b01e041c603000c08c5c0c925045069105906214501d00c1141c00c1e035502c044648140b9086c1800c0000d2540c4000224a221a82840240528102e15001c1d86070b0542d0741c004508903100c080e4248034000c80031040008922401c003013030313a00200387e4185001c2401c0e52400201c14141500700080c501c5421460001079038001c5844003c52981c0d4000c124056401c401807083c80c1e021034100d00441d4ac11580c40c86418480035041c080c032110079680f242200da440c4101390182003480111603454108a142031040c580081c40b1a502041000000031321241c07080e45a8880800c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307578956 1250 307577706 307577717
    0x504150b0901031707050a080d021905040b030a1d0708010c0909020f030411030a08041d01060f020d080a0b030f0102030114190303030b130e0f102a0306030c090b0f010f 74
    0x444c00e0020100e40d00208080ba1140244521103010596407409080058200b0314007690b100314503620b80f0000c104044c95102840000c0c4401c0c03049a4510050f0f960165400600280c41c0701081038030a0800d20090b0300c0003041c854010041910003041d0401d00404081c0c1d16206a103039120900041a0300a02a031f12040300c0302480000c1c0441d801d03100d00030f121140036003680c403003d07016100c2d08820342c01904a070340c00300503004501e040102d40c41d80a6004121030302d041c01c41c04280c10002500c0e9542c0034203074800c0000c0c0c0b0303011030a620500d81c40480c48000040455001d901280f0b50325010f900240314500404650801807001418906080502c06101c041c2c400b02c8142950781c250000c0c0f071070326000f80e0003600c03a9424803481e010070301c18810100700050042c00c80305520300c1801e01e0610740048404030305090aa21245a041e802c1d6118054221481000c9903030140b160100c1c010603040c1d201510000300300c2000a40d4210302c0d03000d0345c0700d010241ca040605100c40001992402c2c21b05009600044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307580206 1250 307578956 307578983
    0xe010b0711190b04030609020307050103090819051909230303030c0a180b030609180a0b060402070b0c0706060e040b0705070c0b030c0a09090b03030415030b03010504150b090103 78
    0x688580025058540c0030521107030b207600c610380e4492940080e00201c076200d41d43d052070000d515080001d10000c107001d00c0e051001c048140d4030b001460285402c07032802c595086c180b040d4014000e50543c0c13135003041b00c0d000e9035003809810001054000c3c18031a0914507200d4140b20700c0c1c1c0d0484807071b216200c2000a80114030b141c8488012480d550f1005400a00b000071031111902200a40d03205e00b0028040c241001d51241080d800f0002d2042015145656141c041c01c25804050404500310101c26004540c44160790383d07600202e0064450010002c01340c03400d02c01003000c59813525018020300d17405080c0412440780c440010301e24003102500c002d01b60130003003000110310034840da0080802c94450741c0000000790756002d0302540d5800645da440f40305030740801d450803c10b5012041030000c0036910014440400d01d5808a03489100350700800d0001c003882c9124442e924040e03004681c1c0498090300800c150301d0107003070880d81d282e1907090100003a801d10080d80240c3c075044101c58103803504548000d0011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307581456 1250 307580206 307580209
    0x302060f0d0b03010213060206130c06050702010e04060609031a010803030a0f0912030204061d0603160215040506040b1f060509010c170702030601060807020a110d050d090e010b0711 80
    0x1d8000310050400d880d01d40300c0c46500c40c2c07002c0c0043e0280c0d10341410003840f0b003814003070064107140004000600c122410204200421a040261001c94a141c14220750f280c00900040b5205001c1d0405107401a0030000001440c0e6070083c405001c8900a0807224a4040100d800002a817420310034902aa4000e0020581b030200582c4191155140307503900084120301c9030f855000009482c252200400d60100303040103102c0d00000a008542951200b45108030440b400241d02c90001403c4100c023610a07603040b07142207008101080121064400141c030601d083d103481caa80d400100d03000c58081c01081c01003503014092203403aa41c60005003410b0100c1604040d41284d80380c00100550381003058441c152808654100301c0541c0c1c40c0c51502c042c41e95201c490050514116060340804c007001a888100100c1c02d6020401d0203c056000f441210104c080800203a4ad03480b007484068418000c1503400741055030801818411510f80d0b03810340c3d00d5a070f60f410301c0e00c20900445802400c00d0302c00a1849409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307582706 1250 307581456 307581487
    0xe070e030a121409030109050706020f030705150a090206072a06202401080c010e0a0614070b0a0506030114090c010809100203070507060b03160b07033015030206 71
    0x540642c04080b130400d40d103040002d003514000d0400365004d40050000307208080c0e061081c010810780d000002c41c03400907141e40f403070b948000714159060032202000c04100c03002c03031540108405540041c86130f074480a00d424a0b03501c070340b142d08801042114001e074554424181c1d11407103003156066294844a113860030390415900e11151090061405212030b075920342e01c100380c0d19500303a00500b036201303c0942c18401079615151030700c0300c0359041c0a0722003421215aa070306900e46040d00c0040c0f0707129150a94248510b0f0303140c0691000201511515800c008002602e80c1c003e91150300210024003192044000f5200c100d0015074071340690f50030410b01048154001ca9a2681004502c022280340203481071440040741c00c10340e10100040c10000d001000e104640c0500001980102c000e00f000807600681c0100d810b80f24410250075847c081404824180580c55415000400f10300d0045021f169450166510350000320170994240380039054048070000301181070070350390701401a501d0424501d40d903041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307583956 1250 307582706 307582727
    0xb0f03070e1023070c17010b0402040e19050702100903121802100203191101090b1f060e03060604021b0703050102070b2503020a0302130e070e030a12 66
    0x303110796104421095101c10344080c100760300075642c00c000d01c2c000b21075000d401500e02c00304101c802c205002603c0415410281c82c021a03045101c0d40081c80412841203024140200074180c3c4184045400582041e0880c00c1c0e510a0000007101e0b80c40c072070b185540c070741141d8082c3c40550040c1c0c8000c40480c4840311940c0540101030007800c0014000f120400d550023503640459140710320001c8201100110f00f0103615003848804180042d505094517800241210510403450350704110b800b411100200c5801c2d80a4041c0b950001198812440c04c203440c5c1e004074004c0b40c080100000c428000040c4548510007152079881e004010300344648581c000c01019402c501c80d034000241100003650808c0d101000034800452013800050707220904d40c01c054131414001400d072050600c020b140121411404a20f00050003454100181c40740e0011307000310028040e04240b080e900d41c1c0e00d03801040c100d50040c4800d1150781c99980c1d02e404020417206041d120035803400010700c456507568507640c0d4980039544120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307585206 1250 307583956 307583971
    0xb011107140613090207030e03030301030b04151d01060302030c19140315130b0a0b13050c270a060f2001231e0603100518240a060b0f03 60
    0x90400000f03082100c1d42022550002c51083d40c002074400c20980c2080d400800440103d01443c159855621031032079410000784009c00003d24032a003002ca2044941c040c404c4404040c0b5002007114120450a000340325034042039101c0d02c94020200380d00c0c0707001110803d01000840054400c249000e10f46008881000501907240c0035a40046d5001440800454481d0024110100303074200d1b18100a000d050002d40340280c83d50624150040e140c1b25000050360740c1949c6000010503548400440515001d00a03e007951002c82c1c19540c0c1d900701c040c45034401e050000b11000500c880d43c3d00d02c140d4440c03502604d46008aa00c1e1240c80083c80d010384031002450044800201d000740071107040325041c214500d10a500e807800c14040c410b078080404520b56090311040055400341c00c2050019646100310700004200740d0300c4000165030f4440504d6003180881c0b88800716a2106481c2c40a80212599400b4940103442840009220078030680a001c08403204080c61a20380413040c500000c4981c0000d1072007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307586456 1250 307585206 307585219
    0x5041703070b0c040f050409030503061c050607020a06230105061602040c031e0b060315030c06070302010501061707090b0304020f1905040b120d2003030412030b01110714 75
    0x603030125009650b81072192001d40c880e1a9601e041c040c6070002860240c100c1030165260522100c0020303000012250800400c0710840703851242c1c0c141c0701680300c0086500510700d025441c14000043c0d000561b006c1e000703110b80c0d014080020401c0310310001c108007461110100c050300300100240c0c10880d00a01000c020451040c540300c01700c3d0082010303070701d00d00c141c180020b81ea9a5480002501900c4000c800040600c061200200d044000351284c00041c00c043d0300f20340807440901903a503080002307030400174000c0d0803541c8800039414013900a1009105181c00704601d00000014161501a014440c400a440307c40840d030505040c0900f68000520032600408055a0301d0344030354841004a403245250020054030a09000500c81580ca20514043c01649114a0f00d602040082000c045941840c94005400402c0031020b00c20340c00c042d4040d2105010001c18041400340150611900901c19201402140d04075001140d20320000101004143c006000610030017031415041e901c0c400d40103218 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307587706 1250 307586456 307586467
    0xa020d150c050d0614010207030b0c09041e0e06090706051c0513060b040218040f060e15040606080105060d050901110c0703152304051e010c0e030d05041703 69
    0x14102110400820320010802c0441c2140e43c41034940510000380c10080c0d001c840380820480085d40d1401c3e9400001c00303d440400018076008045d0b070a4500844c03000300280003103011b005891061400401540c0b10180c140b550301e0480c07032000150345001c0d14024006040341032520100315510b4106110000d00354541405007800d04013103005889c042c46c40138030b414440d410303e403034518102c030403a40010740154014080c51240d004000e40c180a1a0001e4a0129803211045542c41c002c0c8900d070002c059031081030b4140060010601c800050a03003041c1c904008141d198401695071b44002d10074503a10400030407a8400e5a01180c00613a00040120000302d104d071015451501190840c400041250748601d40810502c03403c02e0703a01d85030078000d81c42008549031010803d1035000d102d481c2c40c207500c15141c01003000c00404205000500300b0b11110303580e01d801c02d1030300203003e81342501150000809040e114845440e000c9068600c0240f00d07150b0500c1d007454a02100003c8a04e05e10144203800305004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307588956 1250 307587706 307587743
    0x282a03181221090312030609090b1806060d061e050f0f01050d0f03110106030819090906030f02061602220b01030c090618030b040c0f080a1203020f0705010c26090a020d 74
    0x14100c1e08612969442c4c020345416241840c2c0c0c001c01d0304051915500802c03d0003824ec48011850f85000c5e0084004070f18002c180c071070b4850b4009564134010606144c102080600b03206581c0031805402d4030002c3d600d290340e90301c2c10003011036402400540301404c0301c2d08d1100000d00418003105403003001c500110b6000c2c2d03a40ca610320079410035092001c581800b00d04806510b540800440041c00714610b04100643c259254880f450707000a4001703018a04c0040c850444140981d40c0709821070f801030043c9111903500030140401a540e034038510582d81032a1503031003030358002e004603459005e01e90380c3e4007186860306104072950900d070101000c10546085002c0b010400201d03019105034007070240510103030725201400c60a21880d0380102844d41281034800000740360f44c1c0400400c40e50510300562503604081e403200d41489003480082443d840d042c011844681c101080c5441940d9003074144070030460030700c0c5041070501d003192040ca080d008041904010710b810a9000090b6005184c400e0703103690b4401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307590206 1250 307588956 307588961
    0x9240e0615390102031512011e0c3903110610300b31121106010312210f05060103060b190201090503282a03181221090312030609 57
    0x3010300149c55107915105543c943c12580e40d000c6c0d44500010222819070b40d02042c010802c1350f03505550b070244541d800d401414429084035082c49984006e860190610920b1058071303240d07622400c1890030300040400302d03a044071000c00e0b03581072100d60480c0c83c1c0720039035a17001c00c0e8810003030801c86001e4081c98011030380d040101496480804984d5058404c007000d060024010207100b204004205501c40b040c01c0b0340c60045401c03811a58480124504134040c203109590740c14a030a5011840201da60014110100c01c1c0c20068201401034810804c688940e4011402d0b00c44600a50074111010072080c900d24110b054109014a058400003907c035005030740c7c1274150b51001419031848100c00341040d00f0f281403800f0b4880008074508006a6101001d0740850402e10501884420070000314800404d05024040c1c4110040780106c07140c409540300c550004c24000302490a84800784903010041c00803006802490030081c0035160711688034038542e41e8130004040b12072030000f0181c4803640000c04910b1030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307591456 1250 307590206 307590251
    0xf1e0c070603020c100e0307030e030106030b040510110c0d050d0902091603051f051207090204060f080912030624030109240e061539010203151201 65
    0x1654056910131030a140140742503105605840460702d0104401c0c0c4074034000003121000d681c141000005032007007100080c01416207034005013100900b03800304010010085001d0f124505d501e0401c0043d032040c480540810b01a5102e43c5000340c0c13114106001c2917004601038158522903000c04210041c565010454404041e544c220180c0c0c3c2c1000c400d04111b4141c0192540035a00407444100d462041018090905c3e141c402c4500800010032560a000c40601c8036070081d040750785056695a83d108002002c00345109079171750000c2c6850010070f040440102c0c510601120101c400c0b41582c50b04001c000c3c0c10424106001e1001c03c006001c1280100e2100185000300001d410000d46401542078654611070802c40d20392640345070400c00c0c0a14040802c01581001d002e541d48210403ca000e0384070054802c07140c039414002c0e48030ba100c5648440e4108000b20306414541c0901044592401c503130b0903404203565400040044130000405800e18107023030000e5500b00000828080f240402400d1080d000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307592706 1250 307591456 307591469
    0xf060207021f1d06090120030f07020108070f050904111b07140d02031005130c030b15060319050726060307120b01061d040c030504030e030f07050607020a1a040501080703020f1e0c07 80
    0x30034ac1c00c0070740da00002035541c0b00080b0b0900e040d0f000d8100340014401d10500701074074442e555440c40c00d58480000b1055482e103a918507107090043d6010340545560354642d10581d50f0500304815070300801c7c00c1522195a61a40c00b400401202d010360f03040350050710f80100300203080002c1c4501306000c035031902d1007240194002d201d501241d0900411001d5240840110700d0300032002041030040881d03401001d0044400d281c1400034494030340c01c0341200c0103200b0000c8002d032840b004200102010014a06a0181d2130072811070702d00380d1307843c02c00c0207110316600c82c0030b800b84182074010403290340103582d15142845800c001e00024103050000800b100c1d44062903500295550003000101034125034140c032008422001000c00d184a940c825648107414000c290180310701064880441d2a0403210030058140b940481c02c2c10301d501d500c0855290014840c2600055644010519441c083e200711040c0e2001000050325054250311080030201c40c503451004051800c011800e4051010300088018024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307593956 1250 307592706 307592737
    0x60b1903110a05030c0909030405060705010522050303130c0f0b03270d0e0a21030e090417130e09030d0e190f060207021f1d0609012003 60
    0x8508156804485440070030b4001c622955090141d5a00060f01c0c030303003600c8115024902035407104411415806203610554002c08085101c0e0200001900035130310402a45000340c560020784c52003149407030014180075000750810404500340400313101140c84050b02907090045890742c0c4081c01c803802360036a40322040a20000c02070203d4121b48440440815085068880c00003551800043d224101e8001ca902845100000300c81d05448045803100240b101c944800c1b0f802d050310b61151090a0701040071800100d4088014000346440d0224074061904102d6052032407050111a00c1e076548094411042c1181e0040000380c1c505241c0c030b85c47d1091001c0e00c040d585400140c142d01059030913035030030075030710b50440451a20807074104a105488a42c00030408090720085040c0380e002440f81101c040d4200001d480411094a43d08050711284981d41c0da40c081480004006480c44c103c0454030b465000b08200011056503220791420380c00314082d5069945241d41d912501c610315840201ca03050a0503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307595206 1250 307593956 307593959
    0xa020418050115022a01110a0803101e03120e03010c0225080c011b06020c160902030f060f03010b12210408030405061e120604201204060b19 62
    0x1001205400c43c01013800241000a40781c000303444012855012002c40d001c9240b02c17090240c1c0f26005041c0340d001e003a000d4401314451400c10840d2a0b2007291054184055210005040302c00c0b03a508004070129500d1180a2500b107580303c60142c607850350310104000c60707001c202905035020f100308600c030700094000b421101074142000c11140d0480158550840a120082121810100e561007400f9424600000e00c440c650b04002600c43c03d034134020b00b020b07102180151941d00005108061008000c0c143e641150350303002100140d100032604400c0602c042c10200e40c2d03034201a200001140801000411342084c074034003003140744405401100b415404824091240c2503130f1440101100a4400c256151904020945030f0b80e100d81c0c800c681c0501c90028021441001170301075410030740361080440744e40b98401d25015450743c02c00c3e03400512039460700c00c0d601d400e0501d250390428501c100d05a141d0500040300e0082d20240c40c001d000750b41d00c58070383c1105802940c0b8040e12960640200c2c02103240207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307596456 1250 307595206 307595219
    0x3022205010201050105060a020a26130e100302010e210109080d05090604020904030507051006120c051c0807150c1d09040f02090411130b010210050705030f0a0204180501 75
    0x482043e1b0000d4094502008045240e03075000c54074000e90b5400c0125000c13803c2c1e6103045e00f80c05898144000045a002040303000e2141c2d6076400c22003c0350120303480c116075611900303da0102e09465101c0240454204041c0c60014107004900803068002103401c90741007451701c50000d09440303941c5011204500f0008159071303045150311542d03400c09480d800a003c03524060b03000c20342e2500f01400141c140840400e218080040800106050143e140004d00281e5500e0001c4030420300205c0085841442101c004901da080200d00c040e07040403641060711002006444010040c0c0c44124151f59513001c0300f03c01140351200f030040d40d0086500e566803c8140345014840070f4046000c40440344100002414440800c40d4552031740d00a0390122005121a102c0d40381c440b240182c51282c158104680e42061829a031081e401000b08500a80135589860108115401200c00c2101d00402040701440070810500d89070080a90010034140c1c014038003503d034a05a111840d0130200c171207541e41c4400050001e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307597706 1250 307596456 307596461
    0xd02070f0806011a070206040f170f100c020c030a050604150b010806060d090c0608100e012301090b0f03040210030203130b060109030f05010f051006091503022205010201 75
    0x80c40c021036100389103030510300c07a642c40c0c5906104942401c1180c101c1071001004280407252090381c000c000569959403183c1001c1050500d100782008a2035406403111b080e0b402050016050341e641c00a00320307408807681c00000802104100c0713002c41c0708400b680100c07610304200104805000e500148441e1800785400905005042e040c40740031400c20828041d00c1e43c00151f21074000e00c041701c44c60b0301d6014100c00e0000406144402400611100c2800202c02c2c2e00142c82d603004880507040300c40f2140c0c0b6850a4800b1803000e01c1055402c0380448940440f81040950310814600b0514000c04025a5902c92040c4c1d50400da42010381c2c101e000040c002145071003410000c0c81200343c1000c0d821440d06d0400c050b00d1032103509000c0c245906100018510343e105008a40156038844400b01c9090b0941c01c24600a0400c19404d07910b240c0f8003130100300082010300d940b01c1150b26a5580d221910b040440020a5804400c2c81c00c041c103030240040102281c018040e103e1105c5200c6855072001c0ca0400024203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307598956 1250 307597706 307597709
    0x90108010203060916050f03060409080a0f020606040c080c0c0a0c0f050a0f15030b030c12030d0f060305030a03020d060b07060b040c030213050618041103040b10120b1003140d0207 79
    0x17450024107061409500070058424099150020544036921ba01c0400d02030038550b54024249080040e28008540d003103510524028000d9007101c034159280700034002103e080c0201100410101030014075100c50500080003e10001025540da6840300c2d0f8410001d00070b5504040d40524010b14280720324101968104000e0420748030101c1418a080102c0e8507000703000c0d5400080680360404403445071400c01c004011000040d00d91140e444c00e6440f0740e9140d0300002c0d2510012410321810505440c150700400e4252504400914949041c02100760b00940c400340c0d50340c604945860000507030b0040e00018003d003500425000c01c2c5051044100021182c84013004002d01d4030501c86441d00780c103540003120540e042911519550902a1124281e43c0e40303503211141c2c001c1c00c002030000003066000165014074410001183c160f25040c41c02c00041c042c038000e01151000100d040808600d40050803034118503c0b400d084082d41c1c80351550585c110a101c020a40d40d401481c940c0c0090354100403480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307600206 1250 307598956 307598971
    0x15101220152506020c1e0120070f0804120204050109020304120c0f0506011403010e070f05060c030f0a170106020c0102100218130507020f0109080f13090603050a14030c1510050901080102030609 85
    0x2320f464169030301018402d500e8401ba4420021907030404110501d090218000d4000d909180c890341e450702808519001c24401705e010b141400c00008901074240252406158031800c2c0d10300d500100c81c8220381790350050b00e00703451b1109001b0140340810424040039018041e95000b010940c440101498259400c1e40c80c03540071603128543c1000052580800c010941e002103c256a4034030307100d41d09030f185010701d000c1102d0403240005c2c020402500f005080d01c8403140c3d41000c048a84e40d07103a09036101c07190700010134090b070494040c02c40740d41c01c10b90081c9030030400300789507449000c0400080b5003602c00d821200720809941c1c905002d2219010405202d03414100030084c030075080b4a55401c0b595000e490740c0d1040748600030034070013a41140000008050500300c40c0420038659a403c00660701d101803401900c00c01c800c41000d450a03500401142d64400d0340308020011142007000c01030740c8000c024840c1b424140d520b000820b413907130788140f41c4d4001c20002001503204d007484410030040410203032018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307601456 1250 307600206 307600211
    0x160c230f01020a08092b020316080706140412140f0d12050901110712090603061202240f03040c05010905010215101220152506020c1e01 60
    0x80c4a0703070703400143c0b129066449020b040d1114088804140e40201d00380d40440c0d988010a081c94080e9001c2a42c545218022030488210510880000c1d403407103000c1c003410500e5000040180b2003e4013070031600480010070741c00a4a42903540b01c11440b80702030500115144605007210a058407401c000344412590b0b5180070f000b1058120704058260840c0c114044411030b16280043c001c0442076011071020f402a0302c0060303940100e07240582c0069044400700000c1044040301140c0e451091190500356046019401d80d050415000c100245084020246461416200100c5141c000801404017440785181003512030820b0314040c4031810070781e04490704018006004012980c0e00240341e10343d000c4e40a2160055844058180b0454406900a5031040a80201540401080c0d490b03d19103a2050a000f02c6810100400c00c10349001c400e1804141040600989040b0b01310408090b0744e0502c2992403204084181c0d8902d401d91704906071f038421582119040784000c19081c02030a03603400c0808001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307602706 1250 307601456 307601479
    0x23004020901151d0307120507060f0206060907030f241403010b010519110d050406020c220b0d0b090106050a0e0403081b1209010b100302040806060105160c23 70
    0x2000c0252000c44c141c2607010b0003004034441e0720188140c40c05403086c48030990302d06e801420659940c0ca4148034800c0001d59401d4686001c40c0701180060080000601502c42600c0d140e001300c0142c14a1801030700c0040da0786842c00c29106081c003000514070b46443d1015070640c60150769805500c3c15800e00c1d400b90341041c62030740c1507a83c060200c6007443d400060403000c0313111052045076115150711f4000500d03c01c400c0d00b81503098000e00038004603000769080354240ca10950a00c80c0d451b242d014559403004414050541c507a003150888014400c0260451150f249103407a80700c9184015600c00d00c1e80d1359180c50078000303400c05d1000c0f60054038204504000710701b803d0760010320040c0018050030002c0c07500d40200c1c042036019421551606c035590500d0042d410512080c0303008040281002c0d1041100805c032584083c024026103048600c80c5003d445140d50314001510154412143c2001104202c2801030010302200c802c0b82c05041138080352283c0b10706600c80c0300c604240c102c2d006407144840b09031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307603956 1250 307602706 307602749
    0x20619180b0705060406091407080318190312031401090905061f05060918160f020a051509071701051f0315090201050d0c0804021c08040603023004020901 68
    0x6100360000c6c0c0c0518006403490007070504400c064014902c02c17013640507110380000c01060000290041e20404451848103c850404100101c00a40340c0000041c80801301040030400151126200c10201c0c103020a088011000c0b4041c40d0700241c2002c4044c9548191900034800100501c1e07603c4440c22500c1280800280300c41c1c1846551481503d00c40c4c50000b84812068031400030411030641c04411040c442d08114000b04080c001901070384000500d4114000c401910025100e4001078021001d8007038458003401c5003c180d03400030301510652240100001c1e0354800e0640714030440a40b030b000003d0604244010080c0c200e9400400c003002c940c20351061011810007100d507160189486030021b01180030b40f0043e01e5074040d904220642a01d046c240151468100700554030951085500380c4c030403500540304180c010703080b480c068001c03031003804140300280c02a03009204240f096403214820045411900e0025450342d5880072100051f002804110300741003006a000d401c840c0145081c05c0c00c05003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307605206 1250 307603956 307603963
    0xd0c021c020c010914180f0f09060606070602070218070503090708010c0e0d030306051f030506060703050703110a08030c19030b01020303130224120c16020d020619180b0705 76
    0x1510390028840c20301088260b1b07402240340c1132a04510007942d841c3c0b5118034010000a012189000e101c001c0e0400541c0122010940e28401c40f0000e0180382131010a8841e4802034010440032a00103203004529078503515020300d0b29105a401c0e41d2015641d20b845c240081c01d18030785900c140501c2c6e050607880d101c07258126034698800601034a20f0b1022152604003207025056a0b406581c1040c400489107480d180070085488900f602501c0c10b0140e0b4440d441401658031804d080580056001d02008000a1107410480d07280703242081211150119500d401400780e1040d1000d0091100c0001e02c0c801c001900c0c455501c1c540b8813814204685510031340043d48070712009026501b45000f00183ca401c5503616881480b4000c89998044103158003903034492042d61012800c101241151000035601c500035904075448080340384003001040c1050703401d010301c0c10100b410072a8032030340500000350440401c816801c0701080542c2c0769140404006007060342c5013080d8000d02d012103400c0010030302281001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307606456 1250 307605206 307605209
    0xf0c090f120f060213030507060314010e011a0408150a0c08060325090e010510050a030f1502070605091c090b09060f070b040803040c05040902031b01050d0c021c020c0109 75
    0x40c00b203210011441c60301000910803e501c0f442501c090000c040709100c0c2c0001c0d0201035038082c2d1010000c0100e40580a0807402c400d10655440c2ca0103031005016002d9440a001011840030440d50309154403041c42505020541c0b50720b60b52501902c04100d1015100d006030200076416091a51290600c5801b182e2141c0303a03403400b800c1c10103400301d85542006102e5203410013040391003000c022a03500d50104a018202c02d582030000c2d22451580030810b80380c2895030340c0480c1c3d408807411130000b210743d8030341d0b44d10401800100c8601d5402d104500104185000d55441081c242c005080d0151154041e0041b100f003100c602c40030845000800d01407458039500322034050303008859403520390b003400304610305a105500000b4a800d0540d0203010411071b1000146016034421407000301001e494800b0b201c102c1d404184040d40c190301820441c8903540c004000b840c0200c40c185000c5140c45c9000540700c0c1640d03803403903880005174085d141c0b80540f44411402c0200b1120380b80302611910011000003840695039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307607706 1250 307606456 307606463
    0x100303020a141e031c02091e0a090e010903110105060a03061526010513080a0c0c080d050a1206050d03050d0e12180109081009020402070203010f0c090f12 68
    0x9000000c082d9010801072480c0000e103020020400103402030703542ca9401031582409407111428802220000e43d000f0f0ba0901d50b4041d10138401e0340c4824034180c3c1030840121203143c0000c6110004145602e16007c0c5981c1031000030000305842140c1c1c60000c102d410800c2d100500780e4900000d1108950750340f010b0b141169000200400c1d00e251403451111640500e50240c1400d1900c0c15011201c2e07141c60042042070f4031080000c0016680b0308e082d40d02c0004e5003541c003c00006080004a03d0309004514080c0d0f0503014410040c1042d1b1210011407400a5001040700424000b2070b070070302116405201e003884411030642c2404640d02d06008600e030881a0807000b418000c0104441ca1241e00c1580b0036100326003d2400c0b0303100c651080c8802d2983e580700c00c40300c5484400540078420194016540d100489403031400030605000410101002415480d1301207a001e5003c11608bc050b030350074026000c54400810300050340304590000980050400d03031200300c174008550300c20080c000a08200300e094682 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307608956 1250 307607706 307607723
    0x61a21071e0e0405040c0807172a0d26090a051c0507030b1006051c0e010b060c03091809060c07020a120c0513200a020703050d030e06100303020a 64
    0x814800e403514440c2d140d042d030300070303107808100018004102460f8003115014001e0710925501c540d80b151105010240e40c1c0441d50010f0140602a0034028085200d00031540604464108050014000c41d080180680c0c2110802c0610610072100c0d002c41c00700850b146240c1840c04083e031000c980740403150700c120b503c2522080c0d0180001e034a42c1c00048441035010082d0707001a0f4484c0ba080b103030700c1c50a50b43c100b6244500d80c00412994007032401c4442c03141c1034040c0d40a800560040314000350a0b96010441c41d5525100c0b907602c2500d80c48060008440400061500d0b00c03030b6442400141c00841d10501003908010041c04602c1d10082001a08418800c2c440740c2c1e42d18103400468000002607000040404c00f0040020610034a05e00d5074050394821111940c040302414244420344140b151401e0554103140542400399611900503c0c0c044843c0c0103441c441035580d1182402c0c184a0400000800d46502c000b0130485000d01080c0da11039001c0d810380f4581415501c000759502d0140d14000c20880303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307610206 1250 307608956 307609007
    0x601110a0f03171305011404020904170409110903010506040903050d1a0a03080307020d08100506031323010b06040311060d0e06130312180213061a2107 67
    0x10b101c1d43e85950000c09104a1602c02c0c01d04921320842c1c0744544506032800e510b0b00c1100a0680605e060041c0950703002008800c0d5912a0388488040d0909007031041d18540b070805c0001008440d038003800166005024001d40c85000e4041030500751a401000c25224038a40401040029000800ea481c19400c0c1e0130002f50400f4944420b14007488100300b51540004030400010401c80c1c404011841b07500d4503402e441500b0400c1d0340c181c84c10181500c1c017030184c5c407035014180b005040c01005164000803ca10f60494090240c5441340c0c1248105054030800d101d012030922100c0d024000e1420b200c1e070507580c8034a081d1558848007c2c184128901a108540015440c809801e03681c11840d60100000c0c01e503107841c01d16941317009640e040140e0880c0070559078482003c1c120704c980b04010440d2070100581030390f00300e0340d4200070700c40c1d2a803006030341d2580e52035202140c0a400e01d1000e60400c0706083c2001c6e030b98118850800041201120b510070300c400700004005105500c07070147e040544250f8100c41419 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307611456 1250 307610206 307610213
    0x6010c02062b020d0513171b10050901140606030a0e101506110a050304060804020d020307150909060e010308070c1d060901151413091e0b01050c1c0e09040c09050601110a0f 76
    0x401c450314211591048a19000704100e080d40040d0064070bda800070015402800500b00e881a02151b101d03034020300c1800003a20780d290540081c13020444da6801d86a0411000b00e810045408007204445840c08908007481001e810403610001c5072040ca00520032584155112a078a110700d0189404010f144408102103458540d18403038050707401401d030382041c0e441c1c5561602c035020880d00100002c6001400003002056845048260b40410720040c0c1c25a007140c0b111100c5601c00d113001c94030000d81480020788156800a0078524100f0501c0400d00c1b42003402c10071100f40d01c10b0308402883c420b044081000070b600019405c1e01c151030520700701d84030109101e1400c43c1c01607a501c1110150f0520703508140d02640c041a083c0502e01900c4100008061200110703883c1c01050070b02c508951107000400350b004106401080380080c185032003100340c40c104010603070029056504840c400c00c05001488002e000f4010b00383d000b0300c01c1c45d000c1007600a800075660f444400604c0a814603017402c01f0b56060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307612706 1250 307611456 307611487
    0x230706090f0807060506041a0a030206070305040320031b091801060906060305160203030712050a020708040e070306050f060a032007050d020c0906010c02062b020d051317 75
    0x3802e8009405a84071002420040c02901c400c4481d03612461904185515611711040a035214610140901150134256828800b1650145070190b040c01014400080025031104441c5801c051500b2140e10810340c0c0c4003810b03d400400a03441c18040c51f0000400c140d5101c11085c564450014081c0049240c0452240d50050440d5041042081e0900001091945d00350700a980501d100400046501001c200100c1e00e900003602c1c0e2600142c007220072006948902d4001c644c01c0002d4520045ca07000041d581d4648982c020361200440b180200c04026080c1d82600c5070328004c2c101074a00f008500d01c07a10008007244100d56180302455542c45e89504125803040c0007854140c03900380c10650b1a42c82d03081642d500c2400208020040c41510f0400c2c901c0d0034501107641c000c010684848a0300782c1258200321843d0000703070380600720000d00c1980140c00044000070710b464450809005940700c11400723458003980c00c010045000030380388010f410001034036105155980c600c0d0300070f1035071940224a000d044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307613956 1250 307612706 307612733
    0x10801180c1110141021030513060905040b0d0309050d031209080301030b1006050a141603031a09040b18120f0d0605010c020315100b130623070609 65
    0x165481001010902480554000c0c43c845a07a00300c0380391a43e440d904030481140c0035000d1008400042d008812015628400c50f0610340c7c0b1904249003010001c0ba01d00c0e101802c25840200090b07d030300341c00c00041c146481100c440410540f110400300503507407409042c4001c1846014010f0510280c0c00040c18800d012150b031981c509842402041c1d140d0400a101e80c1082c0400e541d101030010200e000100b2501c558002c940450304c64a00f4030010320800e0721000a80569801c00140400194540f03040503000e5521061084c2c0f0005807040c400225040c030311000c007181134050184401400301040c7e030f0303a040310f43c841c02000c01c0300c504140e0000d010341010914101e01c40003903804170f100203020700c828001d03200b80b1090181c2000499aa6401100e585070b183d00040d425810520411070285000c88202d50301240c03171200ca04400c1c0d034440b11041154488040d1004500c0c04503c18800039030300641d40100d13040011100f0700c1ca8101c54144a00b0b41c49100e40c001d00d020350326440c240c10040c420f401d014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307615206 1250 307613956 307613987
    0xc160b130807110f0d0c18021b1c0201090c03060e240f060906060d111917010501180e0402030a140a0204061a0403060f020c070b040e06010801180c 65
    0x15102d034040e180442200f00e09000076440b5184d02c921000250030301614454142d60420050040c0700e1500090f11040711441540e44281074081100e607402140d1b40141c40440204036009000040d180350324002c0716040c0d840e9000469040800c1003000c00c40400d0b000b802e0701d804c5580010040c0c3c00c10910fa10b482154500a803c0d580e407643c0e25010701c0c07550030181d4861500c04015a401d684e038902007120007030303045950651161040c410014202c0381c4d9800903909081d0780b1180361400910f4041c2a06540c001d0000d100010304a51002034031036640044140108820b08103032a54940d40217a44a032148180110000c01c0c04005c0014290365080002a406c0340d00583c00d100040e401d5908544c43d0416040240d001d03d0411200180d04200c400b00c05101286000e0b0b2142403500b15038a08000c3d050b06540303911039540a01c0031106004c07045c00090024804203004960301c9240942c22020b03a100100204e041c406e10000410094208060710780718010f044030001082c0d4810075080d07401e540c142c849035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307616456 1250 307615206 307615223
    0x100906141317060103031e05030109090204150f051503012907020409030e09130503030c0a021501080d080901020a0903121b0501020d0f020315040c170412080c160b13 73
    0x482c4940c01041650689001e566482c211100c01610284460070310440a40003c1d800c0004002d0000c407603105440013480100042a00b5036110040e0b03281010b642c00c104106100e0050400182c60a0352103680c1d281c040c1c281c910300f1585080310b4004036450704000f5040c03c01c1c2182c00401c140500c036084811032580244100001d0340340d400d004105410004a490165a501010559140e0880d002903078503980034000310325607928000032410304c3d001100d404081d0700c200300b00350010880c01401e450103001104000e21803203a50600c02080410081c0540b1626403041140100450b800044030095a401c184608e40c442e204082c1113582030340e5039000050280640c41e07404100081074000300245012180140810058680680f080344000c7c4c491100c041030751020400c0600385134110f105800b02c907080c21036a03040061600c1d8150f0318115011a00038041030280458903400040007500141c0051035a402c10484542c80f1056582d48000503004c8030300c250005080c01b1095800001560344035441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307617706 1250 307616456 307616489
    0x8071707090f061805060912030c0303040b0f0114060a050d0c0c0201030b04020f0405120109080a050a02010c1e18080a03031b1404030605060d080a0e1009061413 71
    0x3844420075028002e401c40b112500054aa841920081e030090700703011580c20454540010020a580925135042c0c1014403105400f50440041c005821442c602e10003070340c2d40f840d20f441c0c0000d504400415203165070910200612092400113100305000e0b405543e0555100c43d22001a180ea001700c59044403ea800c181500250607030140341e50101c54401c1e242031101c016650f00700000e038020221000441d203c144400c214601e800d01401c030744d5090350400050b00a400d5240c22072181d00420101d03010030b84c000340d400310141d4248038070141d64483d850320b03032050090409207201100f4000103031030820028100c0001420041c0304160024200394080301c0c0c6407100d074039014000d030417000389d41469489401c0c1c2d140401400341c42c03045130350388201d08920302d032038219a00c6e00300078107000d00115013104007603d80c00e0004086200a0402a0305600c0384a81450480200090044036803c400104031400c03804005440d0400401c3d00741c104000100d54407411030940c0180f213042107501c8074402c403404508 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307618956 1250 307617706 307617721
    0xa06030605040302030a020f03030105010f26010e040b01050301050f06010e281e050d02090406020d090c2102060307030e0c090106050a02060711121614010f0c0201090f03080717 78
    0x502c082076187c0c09441d40d4580400d051522400240318550120300340c0c40707040b40c1d00e920500502007820070314204a9080c0c45003070148401c640382600009039400d218800d00c0140304041c1d6026006240883c0240210329000358040030a0401804250510140940791301d180e0b035410500281a0180c206080003481003102082602c43d664814551059401c0c40e101545540c0c06400f1025280c014002c1d01c40d40c1c10b6503080c480038250040007075510560a10032a0161426402185015400b81261b01a0141006e1494a80405a400255400f071512440d90f0061700ca00080c0c230b51200c400d090002c6c50b1b007045104c640c244054203801560200c1c102001160720740d0131070301a05440140c2d03400c43e1195a100c10003920100700300107802d441130f03003c4502807440f2409280188500700d1140411a03032a40070341c0d2981464080243c0245880c1d4403040349820300c14440c420754a010b03505100910202426031600001040750400103030800040c40c000410750750040041d0000309840002d00d11041c6031900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307620206 1250 307618956 307618963
    0x6091c060f1b0c0b0f10210317190b030c040f0e16060504031101110114070f0e0d1115040305010e060a0c08150f0307080102030105120708030307080a06030605040302 73
    0x81098041e480e4249480c0c0100f44034840c1c0181c8103034080c402d18841e0700c59242219a0170320051003010a00c10700080403461024030f15588404031001e040002c0d001000d4940135011240c02060013200d0f040500410400800141407010781144070040007074403224102c042418001d202c00950b40003070070f122400c1030303032017442d4000b14141000000382c0d0701e0f854042d1080004017840e40300712800100103110a01c0824610f1503001e8031a001410260b0b00140040c5249081d64920701c6001c0c11480c02a041001003504000500314442c40c52405840b0b004a540015225812803600a804000c0c1d000090540742c80d80c0c238101c92034030030021030701d074590b50f503468640d010300719002c40c2d04485c1c01030034045001c140c0c00d401428070f0a0300c5c0da11007041c0d940d00c1d0706030003114140e0900841d6005400c010000580e41702170000030041e12040001595940c105424401000006d591411690348000701c104100c190200c00d6907001601032900da2a56280c0040140180019400180c441440d1005200c101358001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307621456 1250 307620206 307620221
    0x70809060714040f180b01020303040f20132004051c0512030c0a091203080105010305090c06040611010605031b010c0c090f090317010f060c0f0501060807030512040506091c060f 78
    0x301b8003480b0301505c01240c44c0d01090720020220f4003410b120f6030001e00012498007461ba8000034514001d8800300000e207070812181c1120a1103503a5510117494540d4000c1c4103c0d080400ea50b03030750b01e40342c40c0c84049092201503c2403000d8174079034250140300b000b105018542d4100302103840b00b500ca0510440050390b991000d420500425050040001d4046c070541c502450f164144d2240c4003280e01e80001580a008014003d404601609940303011070b9a84101600140081d81d442c2061030340003003245821180341c0d8000310b00c2688541d05441404410440102c0c48000a00c2c04c00307441c6000385441500c03000540c0103100014100704c810355500d5095400784003058000c0e034030801e6103017120103a20300782d0f4400c0c0580d42c120700710100240b104d64001d50a801c601c07403089c040214040038030384405085482e1030304100d01642112408005001d420401d206428103000e140394542461304000880c24420014401e000d51861050500d2a5190079aa6500f264120750203001c4d000c0326082910080071075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307622706 1250 307621456 307621499
    0x8090613051002011a040509030d1a0a0e0603030a0e0607050f030307030f051510020309280f140108070e040507020706230906090402042c070809060714040f 69
    0x50203841c0c490584140107017001e032100714030250200740081c01030002030900100400400c0c4010007207110b2200f1103108207402c880800a41d000311260240400543c80e030340307511610000103680c0c1444203030394000c41101c1024016050080030b909600d40401d0482c0103194010740140109803804c20740b00c1010004601c5280c4995003000400c58040d800c00031200c050303a4428800403c800d03982c4e900c0c240001c00c07050003d43c50048a080c8200c04d0000380010b10841010828517000c0c11000c17415600f800f10400103040341c01684010542030174120b81000391b00401c1c4604005681c00401d0b030b22401074030700901c4203c0c054000e1000c0d1429200280d80c400f014420743c0000703084854651800c40150034442c103880b0303000c100702c0e00e003090400420080750401c11089030b100ba4200b000041c2e240c0c1c8100204c20005410758201c8050190740001a91180010025400c5c02100020020400c10100f00140d01800310b081c202d2040491240e050014000c80c1c0264500202c900ea010070310300d00d00104400f06085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307623956 1250 307622706 307622719
    0x150304050c01030203162a11090a0e06042d110109050102010c0e01032403141204030c170106082508123403480809061305 54
    0x10000011000c91000b101c4840030480d070781e02d05005043c0b04101800f001d201046002c0030400c82d542140a1f1031040d03950441e80c103c44440d41500a052030303412998041d907400c1080000e0351654250607201c02d0020001410981e075004042c1d4141c011141c040e5411500d001d9030540c070b41e41442c00e10707110440c002c0074601082402d20001202d6205001d02c4500f02082e03580d2021001100005501600d2070008204862000c1c2d100c4c0320152100c51907003402180144001c5c0d06041e9003200c0d681c1405007040c0070340d103c50010041030000c20100c2c034107442119a00090711109141c0e001c2e49900411164000032110700449980d04180c0c0701d002d50a0350003031180c0c0a0380c1d40c940d42e5000029603594441404002038201030101030840381c2c1754200c000b40c40e0345880003c0e09072441c10701d02c003250746c2d0301002c1100800d000841b2140707500307004400107821001c0e0300590388642002d00c8040603a07582003594515415095500e500c20800c0003810b139442c044020307081035110a0841045120003d041c010240100c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307625206 1250 307623956 307623973
    0x5040b0d0f051b040b09030f0a0308011a090901030f02010c06090605060a08010213060e03100507020307060b0d0b0109020c0109050604050c0103050f10120305090d0605100602030703021b0a0515030405 88
    0x5083d0300921289000000d200d51a2070301e0903840300019088054507075414002c2d0044904200810b00c40f5040291080d0b40d034244660518a076854100603419003038810382000d119080c2d050300e6030750000f410341e50070600342c2c04050801e100407100f50150490062040781000e00483c02c2003400d0700001e0056104a9060900c0313034560342064200e00800c0c20070f0681e00c880d00e40800c003907805010b80c0c0f4146000074080c1c0380900c0d6079480032801d44000340c40010040e803000582c082840032900c0754504a41d012034600140080079211281c81184c18042d107442c0550004506441500961000c902542d0220a03981e079460281000d64541244481a60100c0d04000004020711040b80c1410311a400340603146000600700b0f80361020682900c04100c0600c401082424038036900d4008641040f4800c3d80d0208007860507050b03040310407040e41d011406550080c08108002500822103426040074041c1030216500144001022120994407440c2c10481040c90f00c80282d0102008501c22030051049a2928 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307626456 1250 307625206 307625221
    0x70c080d0b040e0c01031b020304090b0f060301030506100510050901081f0611010b040b1005091504080109060b01031107030309080912030a030b09040f030f030608060a020702030708030304021f05040b0d0f05 91
    0x7d034103090340400142c0003044213000100c01d59010306540d03900a058000c40106010114182c1e0b4000c0c1c006a03400d43c000c001f0044071041c2c1003c00d80c040e05041c2e0350013500407884d00010300340340580313500e0720b06005031b160004a40b0f0300070282140c4440110010601e580d591524041c0680c41c004416911035400d00a2400036414680a039500404c1c000d4068020b407c000c0720100c600d42c01010760107910140c202003038050343e1002d030080d101518081000240c0c84e20149421000c42e65421046410305040404002d4800380b840d040e22246a098200070800c500745d4607281d5030314030480001c65407200446403582c40050300000030b0700e00c0419649040000491702e804010304d44408640003032954444104000029100304400503080c04035080108640792103401d220300741107080710281c21043e40420342d00c3c19842d04000c04030082c40100702940c80c604194000c0382900d04502d06d10904420f80c0008400c0440c070943c00c0b24010800d504103603032559040c0c0c0c00d0780040d010102c10146110300301000b09010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307627706 1250 307626456 307626491
    0x6061e091a010f1106010603060e06030109200d0b07020c2b060b13050412120e060115090e010306020315010318020f04061a040e0f070c080d0b040e0c0103 68
    0x481140c0c40302070700d0390901c0380044868050304000300003003001c1c000f1503890324001040010301030502c549003c41c095041ca030802601030f10003800103100e41c3c1440601320100e8803034007911a16440c07180e801d4000460540218040b01c559841c0149915803a408010a030390f40816220204441241c500010324041180b180b0300003840990036890340d040d00c560000003a120b6000038006c9602500ca034020740f02900d850130450702c04407402c0d90810300e400301180c1120380c0116150805031311071004008024007084000e5075000305000380c45060f009903843d440802d01401e107076401080e41452a50340d40d80c403450004007070340003620090940012096000038942c0a4011403200c001d4600750380640214940030400c900c203010345983e030400d54401d00030a28540c188486050101405007095a55140651b1040e0746d0320300401d4800360005001c248003000ea8007210ba0b5029980181055464210032052040180740121001741d0091401c90546107001011a205403800c409880c20072000d07000885203001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307628956 1250 307627706 307627721
    0x60203131e090207050703050d170f070c05100902100e091f090212060307050904031b080f0429090a0314010b060703090e06060a050f1606061e09 64
    0x51059881061090900003000324504031214401a124180e40b00c2c01d09007280e01c0001c0682e031035085082c09209110341045110000341a52034921b02e05250360714011b1fa518000f80c21519101e40c050701086500e441943e08181041e00807090318400099003400000414084504034000c4040c0001c0b010f601d40510152010a0000780120401c0d584080701d800c0006504543c03092034480c1f2420128a140540c409400b2208058081540600300304040602c1c03c0308507486540328140100402c400250f0001082e01d41d099035034a02c042c40649854031442074000d030703503506800705400710700061400d0300c807490f894180c84400b0000201d1801d24030501d81c28420100000e401103041e00003000010b00f0900421040902030340005071280003640003d0b03040e4444074040d0001143c1170428000041000c0f20541c01440840e0750741e191961041000e0718602a6132039002e880384d80891641c0e10640c45600280420b42d110204122454440b0076400303880006009480ca068131040c8045417014151040d0170 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307630206 1250 307628956 307628977
    0x150c030c0d260c03040501140a0b0a0803160b070c0506070c030f02070e06270f040b160c08090d0f051b030a0818030a0b0123220c0e090c0a09060203 65
    0x38650780d122500c0c43c0c0030b40d1000d80103e80700e642c1c80154164446844c008203004210300b02c804250310b9180000c11101c00c285402c40840d40c0c10400c503001c036400c0d4035500440101e52050074800030347e603a205c00741d507140b4203008064094090607003006200c079400038a807078040f8803c1e02d500341c032603103901e030304980e42c0c0d213540181c28103818030001088191500f41c00307840001000301071544021040358110b03135080700103607600b01c1c6d07151059090004220718526081d60160722241081c1c0e407030a6001008126114044024040342d070000740c031030700584503040c1c07182240f500b18041252000052400980d070310081041000c540b959100f11003503910f402b00301c06903075582088103e410020b040c2414854031001d200303040e9140c41071101510001d01c610002078020818000350280340c02d61103690840c2014484031140c422260234142607003020781a00000040f000301400085c09050707116003640d16441210116a20071191004c000802005000070007400a0a550312035095945120a907524081d0040c4807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307631456 1250 307630206 307630277
    0x40b040b1320040207140106060f080403050f0310030218061e0312251109070f210f090605060307080f120c1e01090203010b060301050d02150c030c0d 66
    0x1c00402c10803808a038515100148018602140c5507604401c3c85940319004005d80d442c0d01042200c503802102c8125450f54508010b4420310b00390307800034400d00c80c80410003181c641c0400456164001001603401840d0301401c012a10002880b401d800810125082403042100c008800c0001c07100ba044c260030214003500030002040d4404000c15660441c07106082d81c0c4d07a40604031071403e1800314251100a005600c20b01141e0400002d10100e03800c010880e07000d01140440c10b10100fa80311100c6959120051076101075036a0b01c44511300a460210f4000d410f29040080c240300b40026540b00c02c0c01104104c0031250216a00d106031500c0e4503002031a9025900584002d061684418009015010000080c0e40c20300450b000c0303801c20480d14040c072203641c0e9134545000b81181824070480c280320301c2c200e8000e800c5616000008005400c1c0c1100203000d91086521386502e100d000c42a140c4505001050b80d807203900d80110560b40d140d14000c184001841c1c9900c0502000003001c0a51482ea03016842 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307632706 1250 307631456 307631483
    0x90f0906030c03060c0309010515061c110f0903060105090106080f070e03070f0603050a05191e110c0d05070510091a0106111e060112021206040b040b13 67
    0x412855090061030150103024900c1800100e507400e02241303202e5003100380c500f600c2c0c0c100f403c0ea1508641d002041404288038002c920340f880c1e91184140d500041301f8401428100c02d00004a4028150307554a10011010104540c18503246000203054140415012503140341c1c3e0b2501040ba904000b807140c0000301e020000840c80701c0c54841c00180c1e11007000d09112107a149001e010078600340e000da101c0400e100c5c8448090000303551500456410200e4520140440d00749800c40841c18107046d016104543c3c2d481d00141c02414031025010003c000c4030380c04110035104016065055170200d43c40060700c3c010031104694044c09074041c0c54000d900180145030801480b21204018640b07a101070b144265900aa2855020b4820095010300300d641d071544042c03003605480910380844149040c44550b54618100e500400024101d81124110240c52003440400e001260920506000320a0b160081c84104802d1120300702030701d03000301d1141541d090260341e41041c001090540120003000304540400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307633956 1250 307632706 307632709
    0x31106030903191701090902010e0108071404090e01050609040c0e28090507081f020315061206180f13020102010f2307080403051b0a02040c0203130902090f 69
    0x396901021800403070386010b4a2040c80320100002d81081c000180b003e40c00d01541c00300d010001c3e030060074801418070402c0031660010307004541140506040007a01400503403800d00c151426007d032560341c01a259281d07103e981c0c2e1406080300281c025010b40c2410003185144c1448104948581d800003170380900503041210102a0400c041d00d040010700513108813001c1801c8004501c0b482840410000460300b100e850301c14200700c0154407191164101c050f2a107042c4444040b02c1b07440f07004483c00181d90765a01103100d00020100030010b03801001c0031075079501c003080441283d401460704440b0194113041041080c0403142c0f04a904416044050300880c040d03582240e10b407a0101d04c140004910441c084038070b00101d5101e41c0e80402d038001c89695800ca8011140d05240d045281440d080c40302e4030340381d1000b5185202e25115851848081d50301130700350840502c003400440d9030080007882100c0d450310b0020b55035008074202c04c415905c0140002960300b114070881e85a11405403204c024800a20b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307635206 1250 307633956 307633969
    0xe0907030609020411040b070b0108070b160f140d0314070f0507020109091a2103160c090f02090906030a03080106030f090b0405031903050108070e040303090c0905011a03010311 78
    0x2c1c00b26003290311544908401100070000e040507000f000b02c4642c95000d1400d144490001c181d025410030f0704200b500703000a01c00282241c1c45a00130028114180c1d115180250444001e140003031301c481d01b03140f44800040c101003040800d002141d078050144802e030462201c1d075468180c2c2c5820102c1c80b1400030088050040c4041c0000d10b0050418201382507407100d145056444004002d0b000c0f6401d04480c20403440e04980c2c1400300c489070824018080500386e100c582e240f082e1110305038204100c1241070100310076403821001512000c8410300070b040003002e81c040070b5000802058415030444001030504d080014801003100e07015640c004050b4a040b009400030040106004a51611400340001085a03503400034051885180150340d1050700302600c1e00540800d688601c2018105401000380704000200d2105481444001c8002c50b141c0b40360541c01004c032140c008124404007140081c0d610000d5000604880e8049178103000781e0845000784440b48006d020040c0303e0300c40c0207142141ea041c82d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307636456 1250 307635206 307635221
    0x60e0d0320070b0c0f0111090f0d050a060b090106020309150f1e04050a05010503011805250e030601092d110409090317070c0b072003090a0e09070306 66
    0x4005003a010003550311060600c89560480ca010fa800040e400c0c2c05810304028001c2031a00d4400208425024503082502a1040074441031080c01020184c45480c3e032099803100c12146d010f401c65210501c82e2608101409850004030300c134000c09800054058004011546025002070904007885050826200180c0040c0d40c0c0e1540c00c4000e103d680400c0f14002d41084e5201c0301c41c507005480750320f003104108099009800241c10042c051004000c05902c800c2194081d001c061004079659540840410319000d1950700748440341a44081d0700071490b00310003010f170f00d49010750a0ba140d030b83e02c07000d565090301c04600c200001c2c484a06815100c20605444c40d054909580101003050307618100725030203030740160700700c0041d0f01d69407484a81007603084500e0804405520300385403400e21b4090405015502c00c414041c01030060a00040c0c10349110b100d49803c103013035204400000c42c0241c1c01f1255207412900c0014018180c2500c04240b082c1444031051003072011800a00a207401e40e514480a0180b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307637706 1250 307636456 307636487
    0x1101082e0b070302150c0f190e0402031f09020c030702010e030715021c020a03170a0b040204080123040203120d02040902040b030a0c0e09220209041b060e0d03 70
    0x4005000c91001c101200400119000360300404075517002003602c900c1d02a020b0300042d40854100072121803000d00c6010f480c40c0006100c5080c1b00d0b5840d1000954200214441d42030707100e4400820000c41480c1c0d2003400f03030540d865982405a080c2c076440002c0481c4603901103000154001d004150056106600311519940c0142c2643e950a9440b030781c82c16402100c5c90f915015800c036600414101c9aa1490600c501c141c0d807008201c45400c58402416180e02c40084200c0c1c148800c0001e5420708054201994102c8003400856455035211000c500134920320124800142c0b1645007c0c0743c01814010301c078000ca4004001d04041e1100540d05210340d4070125043c010981c080c000000c0344c0c1c50503c040c00040002c0d038503083e668980881d22104844c030854482084c0440c1c0b076885038050b1100c2540aa0058400304003140031442d180280300c41c0c40d00444002e40c800450030402c01000400c4c0780301c506501c24001d0503604152201e1003507541c800540c26a42c0c10000c40310100c0c000c01d02c00d00c00b1001c80d401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307638956 1250 307637706 307637791
    0x504090e030d0c050304120503010f060302090d02030a0308011d0105130902120a031e0302070b15030313080705150406020613060b19030203160e0415150f03110108 72
    0x110ba199071400d035000444801d0119901108002c280042c0e02c070344103000d60f01458058a590b0424070300901c4c0c051076016450403d44d001c90b509581d61105c0441800050b0001c04403900d050040c600117200220034010121121140c403a03040d801e540c64143d01d810784400034500c0e02c68611004408004044195061340d0100aa4090310502c010a00291040c41d0007642c8000b5a40e804903441c0c480100341e001180c2c10540b040001c813002c41c03120240e003500848100c01100e90980514002031860080e1141d102030161600700c0010180000a0054211103003a03c809500c80411b81445420b801540b06000c05a000702d8000b900c00c41c11480310b0950580700c3c440000b001c0c0900c0300440c0d044074900503040d06484e2030650034019480c00304a6800103512104040c0300a505000c049100124080c000400c1140c107100c403803207030603040d400407a4141c1e400c02401c00322944c0e0f03000d541c00320010762006940312051342c0000195075104100183c41f41040d21085400154180c0218814100c030002d10564031a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307640206 1250 307638956 307638967
    0x50c0a0803090c060d0212060607120e0307050301150e0603070302130506060d0207030c0501050906060a0513020c06091b3f030c0c030601082d0304182a0504090e03 72
    0x15070311001390008081003100147c440c403002191000c4003d0241080d84202c0042c04100300003842e4880f1505c2d8107480d89400d40300100501c01180c901155500200c1d410350904840001c10075507541020225116207815900589490050684403010b41c0400b0b900540103101282d88100d09410041e0815000b82c9403500d481251001e003812604801c00031400664000001b4040c01804d000e07840d0451a04000740155041c01800545000708600c929801086440c40010011441d981610041030045007521031307619044040e60b8507154400710207030000d20300c51100314007030610400727940100110781c100c9000c514190401601c550b400e00203c00c9900c41507107291042c4403081c0041c0488400c48802000c202203410105404e181050303700e002941c0c00143d107100401c070040300b4002044161502280094180601b481c258807454010044041c00f80104020002056010b15a42c030400000740d010411050700c00241001c2600401c1c0005005000c00d006184c855406602c00c0d162101c03c032407500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 307641456 1250 307640206 307640209
    0x16020304060f140406110624040e0307020d240501080c01080c190201020307031107021f0c0c120606140307050f0a0e0a05101d0c130b13060906050c0a0803090c 70
    0x82d441a0000b05c00110980640c0071480000c01500b600700c0c1da6040659030310300c48080b03a101d01c0c91809a10500c070303a03114501e401d0b060800744111140a50042e1101c40490a84d041080c00180e180c0c1440c100c5440441c01a001010244101030507141c040016108801485004560481e0068030140c00a11308002c0c1c030412041c1c0f07010003801760b00d664001503203030314005002604690006101c41c400c180100300290060395030305c07031100c41044003030603000c0f41540f2100100d4070319140950040c24080300c9200490070480c0e05003603134a400d01c80d6805008503a02c07a08015110010484600d4066014a10501141c6482c000741522040c0282c8049041c0f6680c0345a00034124080e00c1c0707100c0c904d50380c2040c4010302a14036a034001500101019010141d910520111009002420405512401302d44100c0088844c401070000f400510440c1e5211041200e444919410340d2150102080001d1400920140120141d41d10504030201400c441c40340340d11420704980c001090482c02e03002c3e190502a09 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 307642706 1250 307641456 307641497
    0x80d0908040b12160207061715060406020a120c0f0b0901020c030a210605010c35090301050a05152808030703081506160528020916020304060f 63
    0x401c48162200c20300d030812120030b0244c0c0c00a0341d02c100c21508840828400039805c5000b07030302c01800750203840704181d0724100c4455200c4d030aa41500c0e48078400103030000381b050380001c40b540e4030340c0070306c1030081c1c0380c601180280e40380e0031803240003007001810308000c50105a80c0c03442c0d83d901001c0c45c0005490a42c4442070141140e03c0442d00c0e078040b609140191542c031400319407541d00210101020130026007004000790860307800300c40040044071030441c4d101400d40001615800c0001c0368803a000c8038405902e150a1680040310314600a40c40c00f070000307428480368000c160007010076000c0c83c0080340c001c13014841e00042006100052161141042c11414042c1e411040208101c0010f1500d49500d850020190318018002401c84201103c42d002e50b03995000449000381d2141c1d121003039000b2f8500d4180c0c1081204d105a104896027100d0181900c180c00425030f4803c0d01c2140c1403107003a030b5010b1034440341d40b001071409001640203010502c1242e0190b180d0019160702800c03c88030810040081540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 307643956 1250 307642706 307642717
    0x30207050f010c180e0c1204080c0a0c0e060d1e020a050a06020d020607030209010219140a0305030105100206010e0601030c0921060e1c14040320030613080d0908040b 73
    0x203140c1d204032002d001c01d40d13038420b4050030035403800550310300304081010000d00031844041070b0a4206401f040400000b0011180e050350130105487c4c89001b14280709000904c144990300044802100089041c40e0502c2c0c0d4404043d403080311001890201201103c094868400c01c0303800185101010a0320355400c000c2d83e0041085a00601013408902e100034101600540020103050050219660a0f070300400d1940c03101d45050240c1d0540061420840204680d81c288c5500728090443ca1100b07043c0d0103401141a544103803160500d04100c1c100c03c903a02c030409d2141805110305000031079643d6103c0d401190070300002c0e00e002c00c1807076204c000310050b400418142e05e4a021511020504000590041e0151442070002806100200740043c1000c1032038011610104410000540d010060310016100a503400103991910960780c04c1c09661840608181c1c10310034402c200005400000c903501303082100390300070500c504044100c001803014088054084505140521000c668111504042c06 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 307645206 1250 307643956 307643981
    0xc050924040b0d0b01020c03071d071412040c05150711041d0604050705010801060c0204090519030203040f15090b090d21090816030b130501060b0406030b0d0b07030207050f01 77
    0x5041100302c001a21f803122040080d4042c0e0480c00c002c200c0414040004855460745403408100c2d40d9072001c04440700c0c1403a458400318910086010095416441d0400344a144120302031123036030b5165020044c00000140700c0140d4a202046468000b4881000f103207044c041c0900040b54080e031304500c14884413043c1c1000300d400d522020400c018020104000741c0200400c1c03c000c0120350405000416106031054041c0c0140c5e1201006420031201b003044404c01c40300c040400b1180010352800a480740c1c050310400d100640c00950205107140181c1003200000c0f9192a4070152500d4000081c0198001a4540b6440340d100c429280100c5c02d5030310000700004208544c5038101400900107400300c480d81d0000512540a144031440da6030500c0d4480c4140c982105100c81c0310359498503000086050300c0801801542480700c00170300340180c9009403041c0d40c01900d003485264040300500c1340611350080007929400750b190100d00e402c3c1c0a6402032800c40d0042044d1620b52110071500c03820f58080c0295032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 307646456 1250 307645206 307645211
    0x70506040312080c030c19020c0a0f170706020705150405090a0e011401080d0c050f0d08040c120201050702041e060f08070602010504120f02030423040c050924040b0d 73
    0x1004820b0f80304007040da10541c2000e94504505081c100b818450140800c1040790868090307031190200d000300003400f41180300900b00c3d14040d032030321440360030040284504074214580784000341030110041102d4040d29680d60041003480c1c50300003001021118404011001002004003060948401e07000d11310910a6130000704006010030f02d460300b1101e8070b0741040b60404030b600c0180406a80403078006c82c01c603a5403802c0030310040e40b42400345c1030440744002c40c510342c49111416074480c1c0e0000750342c0d03100f54060644161219a501c50998042e480008002d0000390208803c400515051344030f801241c407501c2c0da808200c0c001c00400821214503411000b449603501c030080014040400184010740200d10080c030107410300b0b6542d07a4030401c2c900141d5052060080c04000114800c10036540103000c0c400d002c1c4e40704440c0600c058106104280c40030302490801c3e0031002540e01600450703040e5600504441d1460103038540402c00d480764861850900b600170000040c100c60380342c018115840500c1c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 307647706 1250 307646456 307646483
    0x50706020c0f030d020706200304031a1b0a03050a020913090b01060e0d02040e01021e0301031b030201080a0e010605040f0b13110714010b10110d020f0714030705060403 74
    0x40000c240c0080c4034852003540000322008104d9400306031902202c120742440350f04e0460464a2070100c5a00d0412a5064480483c00100307000c9000500d025054100746107207882c1e203483d010443c3d07140d03035070025a10b200780401066440c2486988043d601c095490b90040c00d00405800284600c24003517a02c40750181c40c0c0c1d1b0039109000800310030034010309103418882020070f900700108840c0820540080c2c4079507235031350101c010310800390102c0c0e190000024461024203e40303400c0000682081c042500c00c2c2d0400c1e6440c010030300d2285007060070f1340e40507101c04a1300c3d031f0740f412494081c203280c216101c500e5485081c0015141c50368007402500203903012003c2181c0c10000c0501000b40485955030401b1070410041c4003424140701c08a50401d50000b1112600c036400078034480c054091314004e690001d1000d00e01e441e50640c0300e0420114000107005413030003101600001c0f43d0b22041040c1d1411140c11501c41000710f01484200070303607401009000c0d0b904d80351762140054070355000790344180c0b0f2000307c9040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 307648956 1250 307647706 307647709
    0x703110304050a03030c050703081303050708031c0c0309440405100201060b070c030b0a140a0c02100c0305010f06110c0609040e060103060f1413170403050706020c 72
    0x1241060048508015428686003100051400300f6911000d02800040c020071400c2c0802800004091904001c8440c0c1d98154000280a80081440181e68901a41d4070110b2141004011266441c1820302010095010000d00c3c50091040c0e0607000145a0344103071174030028000b8054102081641c02c08194001c1038140b08158420f0a800d114003500c10080c00c84240803112000d172825a041551903070540c0950046c264010030464003c003940316008290241008142183c00b1b00b907a20407501c021943d00c3e11050704007501e405812502005921300300190000c012035104106a80003441100c012161071515482110701a801c50000252107000505c40203800d10f4074100140518940f9084103100880856251041d03420340910584c03002500c0f81c0c00f0354894101d0003507071480c64242c80555039030303251480007401606031004e151030500c20700300c03d010080d550341803107126403841e0360480301c000d40d40b2074620140a403542000d982081c00044085407042216001400650300144130302c810100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 307650206 1250 307648956 307648967
    0x6020c091b0d0c05190809030703180e250302030f0c03070e13060905220615270605190e090307050303070306080c04051510050c0109030210050603070308120403090302040603080703 80
    0x6401c0b0041c040121b003071080711040001207a02d80c43c0c040c030b08460300c03618102e55131a090505a018000c240e5803182440300c0307913440c802e191003450121104540c2c00c0021410580c141c0c0000c54040070700800041c00291014840d01c015540440b10b85844500041081c00140710043c41104240750544e0383c03174041c001d000c9280714980d04051000c5050703210003030001c1d0400850715440c1c00200b804e51038046a00101d02d03031503081d030041d0032620320249858222403000310305180100002907400d030078101c001503182010000c8640d540240305030308951030b0920060902c071000c00f902c00d03169444200004000300e0000c1c40514000c0a84c0e503408201540f030003004a00d00b80070a80c4051107949000244401e480081c1c0380c0855480080d9400005100010400d80300d501a00d00000010350134146071508040e4003041a29001d021505c04218913168a810b059641c859400003c0080208004c0c40c400108a0303844507a1281c0b00b0318118943c2c54481e03021906449480c1c0c81200c1d8220086030030b008064010303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 307651456 1250 307650206 307650247
    0xb03070b0705190f08130b03010b1909051305151504030308090111090409030e040516110c0a21020303130e06030f0d121b05090a06020c091b0d0c05 65
    0x5021200c9612068541100c81130110070002d000300c0d00061403200c03400600c50000014420007555544030760751020104850351250040c6251010f6042d0075905050041c2c2d290780175103901900300f4841103c00404d5800500001c0c00000d20b5003401c3d80d50510315512552103500b070702000d501054a03035246103006041650050000f03e075690620480c02c1054042c0c2c81515107101e000c4030080ba06503071030700b006e0301d08030658105640c0141c00d0074204a81e0031100b800c080005042c2c1e030b4483d51a0081400a80d4680403001c488a80c4110302d001c0400505800741e80340c1c2e5200c52803600400e80450035600103451030b0310480c4550f406040032007040200b1808000015881070040e00a49440340c120707668140c07135004500300c510a100441091121b83e209a60084030341c0c1007800340301e201100c40288058030719003001091520403003501e4004504584042015800000c000e03009034440c0e125000d111140c8039009a00c8040b80300c080c07140b10310b1030140303000301420050380c1d840c0c95a171074030b400f865259040944e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 307652706 1250 307651456 307651483
    0x150813150e1f0c09060807080f070c05010c020706020d05040305032b0c02150705070b0f0a0f02180906220506010c0204050f010e01140603150120030c15071b05010b03070b0705 77
    0xd150800a940d502300740d1407507000084010052242c2d42d5800261111000c550020744990300c2c20042c6040103800290303007801e4401603000c07503a20545504c0c040320644a00e01004125810500000c50005115200100703035252166800d010002c07000025000c89a01185542c0143d006400070400121010901a00803501c0d10b0b210f468540e4a45070000302e09800340003200407080c0c0c4000035110303138081c2e0320644404400715400c1d95140f240b4800003003181c8510791040d11030303000040828054645803c0c0c1c00504030b14210700606802104010400520006240a040c000c007107400c0d200598a500c600f5200c2c240c680b51046255040045c11008c0c01416005048450302c4032426607450355811041d41d61001254813000c0e45040c1c2080100c1d46a4901c844026a000205040121403030020002c0c01421b04820125041c0140c814201d628aa0065503036402180040520340e00954050300d07070f1140c080c050400071501d840711078007082c078041541e400780d03c01c043c0120ba1401004010301103050700075030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 307653956 1250 307652706 307652717
    0x6010608010b03280213090902130b1f02030405060703020609010f181e17030103060b040b1503061f02010c0e0a0503120c010e07150813150e1f0c0906 66
    0x44c507204040110048140c0700300a10609100510a45401d404407070380f10400c0c040400d44c0179070f00c41140380540301c0120102e1240b02451b58a00786016030344188282d8240060400c85206500202c200e0204107500411045000c100800b08560316000e004101d02c0e8401e43c002d042524081d54010b08455514201032551424401d05400001125501903031503900200c010000c45c40c02190f211005485420080050300c0300b2112486070000c2602550480b07002d0001806000500b108000c00c865000f000540d100c01090000c0d25082021005154091000303485a01103081100c0f0020b20403000b8420440181e44581c140340d6080d9102ea2402c15800040e074007070100904000000340c407801146040b002e1403a01040c182d509002c00d400812000c0c0c000f90580300c2e100d8564502d51303484070007d031a500200d50b0740e6003c41c2000603801e860080042d0001c881030458242079a1200241811210f29043d520a404219080070150003c01c6c41c00c00d1400000141d2080d440c201411103220303603000006006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 307655206 1250 307653956 307653961
    0xf010501050a0e0d0c030b0603071e09050c0912010506010908010203042a0e04050604140a0b0a241805010608070912150227030307111c0b0906010608010b03 69
    0x241c20609860809106040c0407902c03a000002041440e80210005481504842c000006000c00350385e2035801900c040e81a968029190411142c240c0c0344442c40c2d46491f038083d00c0030046207480d94400d0750403402c02e80200b0710300000b090000d49c2035520b03000b41c05440d955400a0118542e0840024070061029100075800c510385901d5112450202c0342401e000f00a1000c1d900c103851869480b2400035180325094a901ca06003030410139607031b140480c0c08540610085803403c0d890240014400903484e4000e802d040303e07036140d550387d01c090a01051044000c00d456469848400c60400c440c001501c0c02c102840f0069040d070380d014060701c07410703407200e824002420306004615600141e0751040c0d445580781e200c0044013510b0302401c610b00e0302040c05003151001c10030020346503c0c5c81074089440500881c891704c0b0320688081545a1081050007003c1801d010000c140e9418416000703000044401410701162032103444401701845c08444216503508800011302916410800f0140540500f003860b40c25031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 307656456 1250 307655206 307655209
    0x50a140126070303021605010306030503031302120f1b0906241c0b01110d0203040303030b060d02040605120a0c0c0602071401020c0c0a051008060d080d05041401050f0105 75
    0x4040600030320000c01c15a140401d030305000c5140301010560020121048241c1e03e04000f0f40700c18854920300003202c3c8695001440b517100e401404281c0f03400a0241d85036403500400c1c0040c4001503001244c005480d1007908115110621a11043c00800806860b001071608822144030341c1c200602031080c41010103001d003546070b43c9001e05080c1d0030303001d103459101d600058000d404d0095410340941200c131809180b5000b012900b1100781c0220a889102e102c0b40500c00d41030312280d80381030700001a0300c00c0c0010404280320350443c003480080540454035000320400b000047e6849608070201040c0d001800d199010b0240118560140354014204481444048003c0c0200c0404101400840d0040768690900500500c0c4011000489000715528050000c0154403000e090b0140d620549480388002400d081c85116101d503000d25075109809503542c03a00f00012214200c60640d04401c09100180c54180d20344100c900890142100d003140070341d03002061342901d2000b0b1801c2010030300c4c2d03401049103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 307657706 1250 307656456 307656491
    0x2101107020904030302090405040c050102100504110d06060509011d0c03070504060e030c0315011712030c0c0f061e0106110c100215040c14010f12051512010c0201050a 74
    0x4aa0704544200031500d4506007240a8028410b601d5401444d0406200401401c01c851104884080e001d60b041c02304078941d0f003822a2411a8003408009803901400000e213040c0a0080200c0c0c401c1d4400102e80c0e4039900414200390090304139080300003e101da406580c4448880180d0320144000301c80b40303036141105000b0700c14080d80c8642010301c03003c1c50003200c041c0d40c1401300004009000d030880362030000b8903d047c0f895200130711940c07582400a654020800d44040b4408072584a4a84614510740350043d242805a01c04000710700a805100846c46180d203041c45524018407a4581e10814111220600704103e80181e00071030030300000112414085a005c13030f10325000042100c1c0d0800c40320320b00006074202522a84022411407107801000304110940740d0500c113a41c90700544804201d2400300540300003016041000c080342214031317100500f1200750085c650281401c49551505c01c000008502d07560f00805800c42640d440d0391200710309c594248079603540180c0d140c50921509a030444160f44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 307658956 1250 307657706 307657717
    0x904050c07170f090405071205090c0108010312090b0a0203030412030c17150301060602160f0533030403051b0606010e060d1112041101020c061819080a03021011 71
    0x20b440041503e05482c2200c406a84070500040e0042c482450182c10007005c034005100204441450100801e1651200003102c40041c401a141c0f850181d00356221001c502c1807020810007084840070f40402e100c0154405080400d02503001907032241014548002c4102c4410000000c141c40c00d244007013000e5200c526201070010010048011351520303068003102c5005194029055800d184002404a40c0080c100700c1c4680e00c1c441d941021615139a81c01c0c020b000a10901c0e030301407042c080084420320054201054001421900003a01c070342540180c1c000e0704100d40c103031302040000c00e20032113101c0742401e6417441c0d88001000c0d05d0186080b03400030308604580c80e0000e0148401007880307295400c0c41d41c0034030031500d00366042503107036995080f0403114044200c1d001c41c2e5a03503082d101a0310b15400042d020b648160002e0259040020540703182c1c004104a010041e4440301d07082c4146082c46a4101c04c0000d0305810000c3d20300002c5509003c0d142041d17041c1a01c07542464840d0101541c480c900654a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 307660206 1250 307658956 307658993
    0x150906050a1209140304062102031003080307020a1a01031506290409050127060605030a021818010920040509060d1703040c170c04180c0b0904050c07 66
    0x41000076030130041c43d542140e60341c01c605032100003000b041483d0820320f000c5501040e8101090780c1c040d94060303002070340000d580101e80039030302c44001d02c00900302e10059903000c921841211140202510346441107a03c01c2d80c400c0c860381c5004018010b000b08800c1d01440c40e0820f05042c0700e918030303081e0f0100d560011011100e0150b626050441240d407290011540108803801060103076513112081300034481981d281554071058000ca80060040d540d018000450b4042d8482c9130960781c510611030003a6011000c0d2039101c2d15000390789410ba0742e45030f54005201c0524070700d1038074541c10000b02d0000c513048c0c100051045004c0d4507115601d0200d041c00c8805a80080d50000c8041d120704010400000c2038080c000c086030b050340110b41e540c01180025610607401907800014ac0d41c1e407640c18005d03504169070700b15403580045607480d406003440e42181032041500707203254261500c1622400201398103a0400c0d8400c50001503450070074501030141d59080401000020b140944940c1c454003a41c41582411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 307661456 1250 307660206 307660211
    0x30212030703020c190324061205031c02070803270a080d020a02011404060e0d0f051614030a0206040215090306011509050d06050f0a0b1027150906050a12 68
    0x1144901700a6500c0c0299842814200000c0c400b809601d80c1c803030700741e40106441d49482000102d040083d20719072105500f15015500d8240e81a000069246030b4580c8d00040b1502001080000786440307004501c01c2200200f80001825442d104d2400745802e0150440c3e15070040b0f8540000c20308010460303849185a2b100160b403800502401da0140040720709000180302031404110603c0001c0e0000c034940381070b5000366040c250b00054103032642903511102c4000250b05110b0038145d00c00d592170740c8000034060340351400039080c80300e1071b9413071036200110100040e0040b40074081141040c0c2500c0009440f402c0d4124103011030700010070350300c880521400701c02440c2011045255400b80f100e1501515020381000c008a01908013600980000d95001401400c0b0800180e00385a06108070022107000a1510b0013b500491040700c1440782c981c035890100c240402c90356041181000d07050010311612141000543c4052005007984145a100c981409010412660625841807598800c03200c0c60a00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 307662706 1250 307661456 307661479
    0x4030509120106210c03050f1f11030601110a02060301090212010803040e0403080a1808120901060b0f22150909090803070807020c030d02030910020a080f09010c06020d0204030212030703020c 84
    0x5c50300c10400750f2000d001801013a12003008001d0104040101444070f48109502d2006410b0903030455030b004500c5c00d0b03404010700c0403c80340d41c480ca8928294090000440700b1046880d000201154001ea2204c040036070f000440940c8020307001c6c01e040c0100b003400c01440c205454480a0981c20304010402000c000100c0300040c5600451f034402c220745045003c80a1a54031603181c4403a40350f1010a03c038040c4600340c4005032000005000309802d4518005005d8101a01ca181982864200310250001050084003100646044824401c001d049642d07941a4240b066200904201003030340010302c81c50f00b004481804a0b0b403120840750004468680742c441540e50044c124140050303e080b40b903140c010002802d0010740d000024147d4104111542c200596070718100340e9803007148200c001d110b09418401c40800f500a100940389404040c18018004016656007400303c0c0d00c005440300003d5404a0180b040d401d0001710b220740c24031204001d6280c5807035a180650346009028680f440340740701618 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 307663956 1250 307662706 307662713
    0x6040825120803220f200402070c030b010812030606070606080a110901050d0c0924080303010305010f0207050c24040f08120708040b0906040e0403050912010621 71
    0xa052008108071020071103448118a480740280d803041e24510344491680003201203207041001c030703400000c2d44851400a0b000380d0f503032041c42c0810a810301c50142620309203d4503c684680c002803103850f226058510320541545042403280e070701a0410100340e031103084010803106a80b4100d94114008036441c60301c9003018504000030344001d400451540c085e1825a10401680783d44d41d502c07100d4215084100d0342c3c0c907202031040e0394054040103407200c0300f05582000306140743d50043c1d1141080299840c0d00342c6140385640b40000301130740241c3c02c5510000040081c04000e100b541ca1000e0303004001e61030034429445041d611992910ba0501c108584011401202800a003c0041c8961070380e015465507915404042132909500c122406405241944e0500d4400d0f081214002d80d4071040303103820907040201e80c01107034105441c02c80c0c000b01c0400c0041525a45044041e2245109680f0980e03039500880c00d020000702d185030b400f107040e0706040c0140480c403007240403104090200740b01e40c2c446071000d05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 307665206 1250 307663956 307664023
    0x3021c0b0402040902270603190207060b030319020c1c0b07020a061a0102011a06040e091207061a040606050315010c080301030521030702060f0c0c0d08060a05060408 73
    0x40c05606850b10020b03c81a031003043e520081441b51402c01a41e0804481005000c85448100d030944548550103d2903c842800ca5001e8022300d40a0b00002440d041c50030003007461a44811103140490354800304107010ad079410010000480740590b141e0719604003a0740e1030407504041003030080501c00030000064016100f04802004250016400d2120000200d2031483c13106108247e0b600650a004040c1c0310003450740c004d0f03564400041c01941c13419140440c030044080c030161107407216010b040065861000c5c00c4000d0711405000b003c00080ea07001402d680482446090703800c9004606003c0200085600a8256548040c00842c401a295202d0340101c40c0e55840f40d0009081c1c42000c03002200384000001c401c00b81032000c4400c1301c840700c023800b0ba802490000719086030041c3d02c80b030000740403a0015011650001006007132141414809140c0605101841d5a01c80000342c0f500c00f08021484c015040000501050301c009140609014005484142500c0260a001d0442c00a40068021203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 307666456 1250 307665206 307665209
    0x90512030d0c0509010f031103040b04170c0601090c11060106051b0a1505071b020d030c05190c0f08060619030b040c09141611030904090302160603021c0b040204 71
    0xd95041101041d8031001070195006040580d00280320042d40c00c0c6c00324042e20a0105a140c00b290440c215626692541c906440050040314405414000c0f01e40900805015003024910007000e00380e00d6040c0b10041c01100d034165080f81c100204c0101c4409803000100b05d450554005141543ea00c5034480d542d512944042800e0b118188200c100c650244141800c040d9410b02a06d4014811a11810002c40301b02c440c040414062200325a0240b0040ca40b0070809404039100b410503050340c54843d01c9650404a480c4c01030390000c0080c0e200c0c0e404000400c15900e024142c101c4014405d00d0411040c16600c0704010136140c001e050310313914000d006449020410065034800030f000d54a140c41d1074026000d00240c410780c0c05d0030f030030540d0020044a00f517250501c1444080107000160b4403006e8200c3c1c07110002c844400d05400200300d991841c1d01c49000703079490103010b5001015450b142030080214040d455121400b003610500c8020384038503900d502c000380d01d80b420b000030035400b80305000500244200d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 307667706 1250 307666456 307666477
    0xa0620160b042405040c0e010b0f0d0605180402010305010b19081302041b02010f060b0703050a110f0304080606370806130210030b0109060309050102040506040e06120d09051203 78
    0x4003056640001007035040136225a21501119403001da64a410210a41c400e0050b5440305c041030118074810b000c00700103404901c00c569004100c0c159984081a5400b04442280040410340020001956014003500f8010111000e0b80c900d413120104076220001c40f050424410881c0181c0170a000d51105d1480c03007084d9030003c004000a001007440d03c1e401e04e4007018400055401d000034101007054522070441241d4550002615002071079030700b00c0d0141e0003000400240101600c0c0e8110b00002084100322110410004542d1282000c0080385400e900034400b501c160182c82d05a455204544000500b0031203a2072842c006640701000d8007040e440e2030f0080c200360702c10f04081020b01100d5100b928440d078003c0d00d10b18181f01c1001170490a0354000c0e5941800b08410741003c00040348a9480060b001d03005400050905032204006080ca07842544194186403220040c4101032401d90903005000140200411402c41c1002c0003030a43c840b240b0465110780b461148444a018081c406c80720b180ea00b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 307668956 1250 307667706 307667753
    0x9060d0606092c031219021308010f110c0715141303031707020d2012090114031918212007031104020c0a0620160b04 52
    0x102c450030a0f6000300005070300403118980e84501000344a021048406a130761085005245654810041c585c0129101c000102035074208041c940320380e212803805010b030100c2c4001081c203031301d851500d506443c41c088901140d898100107a03c3c40707200c000344a07003c82e80340c1091814081303101d1106940c081d0010364510b421503800213031100101c078405030810990b80f09440b010008041c2207015180050200d90b03002c09603100142500c0b540b80101041c0704201e505020944007801c2044020b03013840010f003441d11040b60049640fa100e136070002c1c84003499002c03032400c079811403502d13000d41c0f100d03034800d0391500380700a40c0c922201c8001c000c074500813070429800010340480d1141c508090040b192488070305100103035014040c07072541c00c003c201064134410000c00030000300b070075a01c0d40b804119000083c107500c10750800081c40c21281c188903615003135002e42800070f03440c0350004503001c03501c1d02c101080c84800c0c0f00700100f42c52240c8210034154981d400800580055032507203810240d0011075070a4008045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 307670206 1250 307668956 307668971
    0x41a060301031101260a0e21090a08011401060c03140301080606041506020a03050306030312010f18090305030106081009020c01022104050309060d0b0406060f0e030c09060d060609 79
    0x2c0c0200c804203c40c42a6910300303040f0144401000002d0700c4405854101c4034010108105100f1500300d9450041d1010994001405e46103803031700150f031107100040101e6000310b000e00107854071002a1000304a918000d0000080000c0101c1c0118014000d681c180f00340001e030303107003410300c500c000c00c00e07442100424550380d5841d003800e9a541d480444019104609040c1503c290000603a401000c1702d500380c000703081d83d81383d55400340c80540005110f10f80610040c89048041e80029965600070100c070322a0507046c0d81007007200802c00d407003144c1e0898802d0419902c040023a41c8002124111409460008029120200724a0580019610013154035002043c1001c40790010350041c441074280c15001c40543e079140700708054002c421580503295810500014036182403920043c08481444000096054808800034007152420b401c07000c00620b80900103100c041d001003018555000450040c1210884040000c0d00703003c004100b01c3c01800030039454400c10145410035800381c45900003d02100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 307671456 1250 307670206 307670213
    0x3090e0c1c0b130b0310090b0a020912060f010302030609121605010212010306020919150f02030d050103121214010303051318020c1203070203030a05060d0f030c03020c0a0b0702041a06030103 84
    0x2030443d81e030428406d000342c15804440c13480e28400c031b01c0320980c4101a44103594501d107040d002500880803164024181c060100c124050500449101d00c511403400740d51941180141840d000c001000c50740a688400c07ca0110f03001e2580580d0302e8224584034031b0500a136145030440c0603000d80b141024100b1b044d24004020084c6c550081e2504260aa680100c035800568201020740b07114071510040140b10541d400c58148039042c0c15682402a0044a1030b0000c03181096044410076402078070002c1240201011999000404040350344811006004502e40101d100e23541c00700610008061101c00039500c1815081c0c42d280350000c0154154403a12400c0461a0030060340c014441486140107541000c4a00c01900c0f00b500d010346040e6004509550702c0369600c80040001400e00780c0d118441c902c00e5000500400c40d10100d0501ca591b4044c08500e4030710300130b45490030710f082c01885048030042c10303c41141d40701b0a444910703404030b40c003091030310f82130107050b06150031800281d400c11030000c004400d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 307672706 1250 307671456 307671461
    0x11030105071e0201150e040309030203160311120c2202040f0f080303070804080705030403230f070602250b0a0507030206060901030b041b08060901060303090e0c1c0b13 74
    0x305645114100602c40040c8089080360025008020321840075002070000d807425000050f8818480e003404403a140c1c072034001a2400b600307502506910008203500f07104104c0c542c4480d14a060b82640e6000008d45101c3c0c2c1240c640102e030b1806805804108100030f03050306100c406004a0b40c0c17880045503600d440d042552503161280c05058481c80301c0b08400501e41000004492060300d0300e54813810f0300d0312256590040742d802490141c0380b82c401880040003048208030080c2c100c0c3c00700082c401020030285001400c10306200b041d66107582290030100580c13600820707800c0c000d00300040b10310540120020600007100c0d83d074109205010700400e4a40520780c02c08000c0119074040e4003210f9144c3c0e00d940c00c02c02104800d00004040025000120703000414442034204a1002503130305458060310b5032079462802e01c1c00c40700300085079143e5000304203058020384228054400d030a0b2160151828034216a018031445c1c14201803601010706c00c0b00c074100e880c4e000c0d41d13820800500500c498803000440201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 307673956 1250 307672706 307672727
    0x30c20090606030903090d0602190302090f0301060315020a0c0606080601050909010522051f020301050a0605040302030a02060a180e0106030c0503041703070201090212030a0e03150a091103010507 86
    0x1800003000880d98078546041074910524035913000358542128401072024a406d40c1c03908450040d02070010180c0c0c0640049440d1807000641c0e00140c640d0714103001c0000c2c0d0000b4240c00c1d07020341d00d07040d420320104081c4104840c0d40e96032500302503a904000142259211049400540302d60b2800e0710224018102149150480c3d6013161030149644440000c10300700c480640c1c0c07034400d048020b0030001401c8907040002180d5802030042d41e12136082040700012154000c408a501c460f4000b00510840c81c19a04a0000c0c00280c58140d003480e0a5a001c0f0351b80301440070300640b141e00f000c03600b00550761040e5061008000c0008501405c04d0f43c54000902d6610203014200c0400c1c00e0002c0005036034440d009803841607410555040d511518181e03200026480035183e40e0841d52246008009602e62203041c8071076022050045507542041e140040040b82865070031807182d0030070520315062502d81d50f48190070100c82c00f4001040b80b074a1500c44d0030580c1c610070880e050b500705004c204035560051140131 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 307675206 1250 307673956 307673959
    0x2040c05030f0403182106241403030702100c0b06090c070212010b0406030812060604030201120b04021603030b0109080d0c060b0d0204020c061509010b1204030c20 72
    0x8240418019221030000300d0354001150354a4000802091049613414014101e0004103c511601d443d82480f01401d403036103201451000802407010480540325800c0c8015032500d01c00d211180c060203400c0c0c41141441411071080c1d106c44190840e9030103100700c0301400c0d401003940340c1c04100c20001800d01c071a039074000c1d60b400c401c03000001c40c641420000c003445803070307042c0501d850501e00d6820003003e21001511032080d50340e1544111442c0c0c9561040002550043c0049912a00c1444003030f2424400200040e000c0c4909000400060740c0000c441d003100310442c400031070301c080d01501140080c01034840107040002840c00d402c0a0503056440408100c2080c2da0700e40c3c0c0b40e61178140c00b0740c1e21030800d0030440c0041c021007108400301e0556403227520f4a0700010840e0000808503000a4240d811100240c180c0d5005441403001104020300090000c00e4182c401096070740c90f00c45c03490b009000701109407a42c8058030f40007408140c410b181c0c42c0c0d0155800380030301c00031110b0043c2042000c540c10203c80e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 307676456 1250 307675206 307675211
    0x73b150f0d020d031e0c0c0b040f2106060e01051314130c0302090a020316020705061603020c090c0408011a130b060d020c0c01030501120f06020306010c08070602070204 74
    0x610103080c218059511440003408114094640398203001d900b00380200150204040d81001040300e03034001c186842e41d100b656443c1c80d03c0c5200d03030521842c040d80300c1d03100340c0b56041c08100030400c1ca0510805c81d01101e80010140043e11a45580401406d01e01c00c4010501c51920402051412089000a041c2c1c2c006035200c0d030a109850740c0d182c0461b001407030400c5500072042d001411406a00344014562880b5a1382c1500b4150b4039408115a10790a0f944951450340110802c01403594201d80928910358520041c00c1084c07400011070014400c000d18000c0a40b05031707140780d041c98020000d1100c0d1040c09000140e052a00041c0310240740c101d400340605c10f50810949119924458100500d0040014001e141c50100b203c00c4400070a003c0350003076000714003030003505c0c0709900502c05412494000000f6103c1900d810000404030741050304189805c00c03621650001056408130b01c01c4a844d444000182c2e40d442d4600142c1d101d044801c4d0040c100140000c0080c2005442c1c0c000c0d01e1110300c203031001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 307677706 1250 307676456 307676491
    0xf0b0102010504030206060603061c0b0601030b090f24120f070504020a120c090315060e0f04150b0103110c0a0b0c12040f02010c020a03030809150702073b 68
    0x128242c8000ba0f9010b00141d00050102e009454200001c54104000401b41c0d21003015800010010480550090315441412010400300d56014001e4240505086807416a149842c0840700041c0502038102c0c0501802c091100d50700d031180486a400500000b031910040281c60b00c103103030b0349040d082141a1140103000c00003e40e400e00f4000c2d00d50318001d0b600c44110ba1802d60501800030400c1c0d07a0840100040b809002002c546040c0842c25200c1143d100031501e64100345071a0340794500908503000c1011082d0400001c00e21603070074003000d02865a800f040c030080c80d40049010b004811780321072000100256401d1040d0000982d030240d54030810108207990740c3d1810b5400b00d80918807200e03860381c124000080000e4508091062880e00c14105070200541b1070b0044ac1160700c041d0000c070007081a510603c40140c10030090720b51400b2102800c0781040ca400000251208003e10541d20400c181003170107907000403520062404242c001c81900c1481e40f802440066500054038006a0034110520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 307678956 1250 307677706 307677709
    0x609020f0a050d09060c1e02060f07030c090503070f03030e0f010203160503121503010506042702030f030c010506010807020a12051812011a030a0f0b09070305030d0f0b 74
    0x80e2000301008000240c106124140c040c0e40030350081d41d040e03048070343e91142c5800082d401d105a901d198003940e540000c500921754898072a80c54031191006643c00b0308104194a80c65848480d0720060b42d01e00071480700286401aa0300c6409a008640d140c02443c0c8003140d851a040e007032000301c0c0d000795580c240590106050144d40455051080d0042c0c10400c5841c59142204030505040c40c822000c0328980101108010020b80c01074540840c422084844070859240c00d0041a404c840200d038100040094500410700c00d0814064040d403241104031000d003503541c11b201506099901d00243d03a0744801c03400d4864000c0408890107804581e2000109661510021703001071150791200c0210420101140141c039907420115020b0303005910300c1001031070741d1520000d08005100c15400456540d484078000b04085511040c958041d600c880200e20118a0f08410340090b150031100050303980c1c031030040c210b041185a410103405440001901c1c03941d0b200503031210980403c0014100034001706c400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 307680206 1250 307678956 307678961
    0x609030f031d031207090906090f2910170a0b0a06020304030308010b1b0f0f0705061204080d0b190f0603020f090112020915040e13080a03050603070909080309010609 73
    0x4002041c250f10a010004d1403004000d9081e4118032181042e0a03035960b0380820703601341d4000d034102486440c3c8500c03890455408074010b00ca100082c0d007078400c240070b2082d050a800184d1480c8428132400340c0f086080a140d0040c00fa1518000103514800a81d01d00300c42c0748000382c00b400b980c0c0b50041030700401c005680384c030210540d8252a4913035a81c800036484d011011f05c16030001e00074580b060280000d6440c144804001c0d004803101030744040c040040b48410040d080a1440d407105019490812908890305517010320b56901c50340c880403085d00d440d11000d1510003010581b484d83c1d0094050103d40080c01524210340e81102c540c03c2e80ba005081c2c17210000c030241e00401c218030464503c01e00031f030036083d8001e00580e217000444440060800881d500015294403400103419200e441c000b41c140f241c450442c855583c0101e002c2c0f00080401842d50b174040d05441400c4114080582d1100818101d80c0c1c1072186000824102d00140a120100c3c24400304d2a403041d210041d46620707003480028400d4160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307681456 1250 307680206 307680251
    0x31b0c1703040308070e010e13150803130b0313140a05010b0409030c02010e032506030621080d0e0616180e0115020106090c08010812030405060a0207020d0609030f03 73
    0x140e1314503030f031516001e500381c40001505000038140f01c00320115400c01c0d1926548407085401c01c00000c91580e00304040800140820b07003080e0b100c1d400c10001488600c2d10098501c01f125103000c41a42d9076a070390a040300c03030308038600c3c0010100c00c03401a04180400d000111050550b000b00002c012a08070042007104032201600004c002c5041f018001e80558050282003d4001c0081c05035456941030040c29990707030000c1400ac404100b06230b00184540ba07070610400c5c01615590013038450300c4425024080d08404007041c02080808006441c48601000d600700c4d5083d4102c81c0121041810b01070304041b020355944d50480c0000c3c01244505825040001da14070441c1c0740c45080312400e900b0144454003000620040505564aa40001658a003d88521a00404d059a558085505254002d42003090341515103111010510a03c40801d1010a00d0741c1c101c00080f50040e42c0d04064070102c0c5041c5203181c2c0180c070310343c54403540106054011070000000319465804104403075104c100c030780140d03014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 307682706 1250 307681456 307681463
    0x3020715020d0807030c1706040e06090106061d0303180a080703060b090c0310060807110303040606030b09030f1614060a0b1c1a041406190c1d0d03031b0c170304 71
    0x20710107c00c0c41c49035511001078202c0300282000c03600302c0c550030301185448400d840b03215050b9965a000c200d501e90007001c030404a00b074060f01403034a9040c540080c0d500d008020081c11050315400c55003a807a5911140d61006002c00000d0720480740d40c03810202c004100154840e4003501d05400001c030b007001184100d80c46072244a03d40401c00d07007003c80032110bc05d8020211000d00012078004014000c00300041d41c8100e2041c013010440302d08500c0d196101200180000105a0051100101d640000c205503003800502d80c07802d0114940b181011402c543c810140e0710711038000c03002071128000f072076000b003040e03000140d405012182900c4090040d0b444000c201400e58459885401c41d058044011144c119004403400c4d001c07200000305103402e00d0019581001c50310100e0045515004260083c004120014100041d04101c3c441194020500d03100d6154440c0740c032103e550080600035444003410042c4a0642d06101c01c0842c0f0140c146645a201601c00344c4010300e910b038051a4a0080b02d105551 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 307683956 1250 307682706 307682717
    0x6080103021309030e0a030c0f0602152d04060c020708030903030d110d060b03160e0906100c0611040314060103030c03051b010203192a0c03020715020d0807030c 71
    0x290002c8000410414004904000031064009203d80e03030b090403803001c3d40c040e00502100c00c0c5010040700c09568103601101c00d64003d0b0815403c0031051910290307010302d29807001c0052503444800304d1102100084410a40a04801030006126056001c5100e003181902103441c1c46480f0b00183d82d403406410381c2d6540c1680b080000001c540c043d504001e042080500e049818400351003404410b40350369400980c100c22010003001414103e81c0b00780043d0446606000ca0048020001f29506050041c000e50007080c8800c00b8500d01341c4203c5008050541140301080100418020032400b030b8441c0c402601d00c2600100c000d60399403408208603040301d500d9125400003c0295401f903c2c140c0002456104080c00c0480c030340e21034802800110720a00816500c00655401e00281c0812a44440114112205005100f031484603456400e00c00c481d425051941412010303140072450442c40d500813400808403420034121840d000101c0c0c131000d482d151a9003030f407956002d03011000c40300b90401e210000780307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 307685206 1250 307683956 307683979
    0xc0f070f090b030f0d022a06040605070201050d0c08070e03070e0109050405030c070b090103230a150911030405120a0504031209030f0b01051f0507060b0d02100210060608010302 78
    0x1040d0b40050204403001d0141c0390b420907441c915904215041c03850f0000342e0051040d4a001d00c000c9030400840c000c200b0000c00c55124180007081080c044c60050700c00f800400034080040d6030042c7c05480c4000c10048051240a038440e10081c0307450302c2030b030b40c41c03001c02c282908846151401086034400c0d906050406452a0710f0200110080c040c050825949800f040101c804403142c01d03c0040041c0c400c0d16902ca03603e4001a0006003102d80c8080c1c0154054491030003466031100100c022500142d01c00c40200300000a07200030403803101d03136920a00485252a02e42070b004801a0041c62160380140f041d600e0084484284041e98401d2104442c0051000c00c0184001512011006003904840c40d041403440e0300d0b540c5030740440c4540c1c0800c0d102206000c00401072860300c0d0403400b00d2000081802c00e410504252701038164003c8036001883c1c243c8030280c0e5492034540c1c0503c000c000d50014a01d141e401130002d0040c3d207440000c0e01c80c0b85a5403d0250204002d4081c40030581203076030140c02d00d01d0b0754 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 307686456 1250 307685206 307685219
    0xe010309020306040f0c08060115081602060f0a020c0a0b01090b01020c030601062f010902040b0303094c02070603090210110c0603180c1927110c0f070f 67
    0x1794000304100c60304035102e82d0109030400100901e5000c4d15000803d2040350024190141c0015401441c0e800e800e0341ca9800229000da0104080e50070205407055404140c41d01071b06d04019000e6003400d12942c1c8103c8020340f0500103801c000604847c18220b0800031450540c004984a030070282242d0b815a20150040094511038000e10b41888900c01840f0300c2041b001c491100c254588014035400c6030b4450040380c0552605208a800050f02100254030380101100841c155a00600d1641565200501200d00106100100c10b15100c3d20449007500101100d104803035901c40708901d0707401441012004210315010f0300c69010300c1600203004c076058400c00e5500700d130700141c2e500c101d042501502c1c8000c0215114440a036014501e43c10b41900b40e1501154018070300360504d000c40d881404c4450508034180c41c81c284007420380b070620302c003000643c0034062880421003820503c1c032041454010340480f4440d04101810102e8102016240443000c00780700c2aa440140f40200030080c0301942040101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 307687706 1250 307686456 307686473
    0x120e0d0807050705070e0103020906040507020c1e03060a021b0a03080c0703110703051c05030c0403020d02151c06080f120313050a12020d230d020d15060e01030902030604 75
    0x148035440d006140800701c4e5982030511609601c51030520b40070034014401c5250800d020756001c0d800780d500b00005e2800300c10080d43e400d480c1844501400400010f01c42c08d0003405146a000c80c0090200c072280c2c108040b488000758880007410010901c03048002c00700c4800070805400054260f174031000780e601e40c2660421203a01c4147e04a05100c882e1082e84141e4009208400c002d45c007640289c00c2e85d0340c24038070f54030714190703d001130b0310400100304100104000c1c07500c00ea509603501541c00100c65091440840c46030301881d020504007480114050760001941d107c0740c3c10256500d802440025500c24855942d03903015200c1c071400d80c001228070000442240003856000b442c02201c0d0414060307036110356051501e0380c5026179a4514a05500003d140c0402c0303221403c105501d404d2054124410800c4c8202c0e42e00e130881d2546100c0018070050700e48842e016220020a40c040402291455055109000c81c3e1741c072891005c03c854000c82c100a41c0a4418541c816402801910322a500c9076102d40c2c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 307688956 1250 307687706 307687711
    0xf09030209190c030906110703021507030212160905090f061306050d080d050f010e0f070203130b190810030809042a031a100e0112021306120e0d08 65
    0x81ca10304064010b4a2489070158040c079030450780300012212428202141952007044004030300032820421200000d03800600250701da050820b03e90b0503038540c0c0208402a2041c418000c008a858030244420109203110304a048030094603190400b642c2c0700203201e072030003080b950510302207501c2e40004c0c100d051103078590204101d040000200552100001040c48045100070344410780089402c40030101c031449181d8011490348081841d43d8945948814840d8006000501034407045000c620f105008100799030702c1a03200c01d0026605a01c0e00b001c081c0c140c0000c41c06016544119409400403801240c27658001c1c90411f48200100d821611168410351025407150380266507800500714551a1031080541c0c244048028407400c03030540310041c182c840380280c0c04038802da0000702c130800e03a0307880c202d071440741040d404c0441070300d40c0b6030380141c803403038010715941e158540001080c80101040c1a04c1c0c40a40310303d929210140b960050303000d41100c0385003030b805860f540113485002405029601096 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 307690206 1250 307688956 307688971
    0x21209100c020301050a0b1201060e0412020319270e07112107050d0905100c03020a0212030c12130332150702010203160809030702041401080606010f09030209 70
    0xc8040d03030720350302181c01c442c011191068210781d505003807845403410440207081c07100c004000340001410104200007008020f00000d000010409424850900030f0081e01c8410030340c580d00000000020601420a030303d48002480100c1d5102c04031481e0b0051400d07034000342d508504000c00c6582c2c92410130795003c48050001c440d603200b4250380006802c4e10203820441d0001013005141ca4150784e290403458442c125401e030060000b010807d01a1341c5034415032a0000200d03141c103841c0b107130003030800f40e017414800c10010350804810f0100824170407000006100c9208980102c0301c440a203421050030901960b00034ac0b400410030745081008c0740680320b40040c03a5078035179500e948140400e04154404010700b003403001c00350002c40106041c00c030385040c03d550000c201e000a514600e00100c00100029507204804107200b0300c4008503140e103808000b554070f50f40c0d020b041080841520040d044002d0350900c00d94005201c3c85000810031b5214601e180d0340d1048a4962000301400d5500300884840001c1608 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 307691456 1250 307690206 307690217
    0x150c0213090b06060d0e030d0b0a08120d0f0902061219111c021209010b03070909030806091503100207050601050a0308030c030601050d02041410030506060a0302031e100602060702120910 82
    0x401b91844140001c2442160145c0005100c0f4001424402207020ac0d0380030010a40000c4044110400440101c42e480d10720031200003203182100c6c62803401032070075900c040e40114021039016220700d0382c00b914600440340448512103040c400c600c0501a5801d11a0040c0740080034030007201c600001400f004c1c2d0355103041d400503050207414000c0e1184160304070366042960791513046200486c1000d02110025028030303a030501404800780c50140c007600010340b5141c022018000000d840707181e0590311480014004040d280301190b04070821020350803c078000e641c140141d4000007810301c0c140c41d010049a9201c2400360540d0748422010501b60030041c00d16043c01010011070704490703410301c000d0000c0c007051b0800075003005880f02401407820380f6030504404c0c90310b0300007849081d85d0b40c0c90a039601c01c4804c0c030740582e40c0e03510007000c460708900004140c4c40003168082840128901103d45a0513280c96a003114103640d00c400c0101c3e0341c1c1e00041e100580da840e0802a0303503203a0801c00c044441e1021b5a0918 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 307692706 1250 307691456 307691471
    0x150a030303180f08030a11190c111302070c0b040e0c0d0908040e090c040506130b0319060606020f0105130b1e040303050a0e07050603010608040c150c0213090b06060d 73
    0x580a030008095011101084e000042082c101001d12803240b82d00d0000c01c0640c1041c0e29100d016178280500d804c4c08040c440703c840000100a141281d01c405c5110103401640180c505410b254080e40200d0003c845e800780c5440c0202c0e0b40110f10040d9401c60700000c650101ca41c0b54000000ae083d0300c121000605551615090f0021a0320300c0010001000001001c074260f00d014070f802401c08406011a512581c02c0130706010069503083c0c6000d4a4060303880c8000341d4410614000380ca0712040340c2c0c0e0804603d00e0311041c0e4050004035031044c0304941c015001e4421546105210a00700e900c2180e40c141100b240c02d07a0b1101146800c030103190300848160034002c00290b41a41030076080340840c0d040b8006074070b450030007a800f10907000c0d100120301c1400040900c1c80c1404006242400140209410000c0d890700013414000490654bc000f8003684c4400342c0c03210300101009101000920301680912801001c81d00c82d0303e514420398200c1c0790400101010780d00d80701e0402a242e4000403d541241e40c0701c006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 307693956 1250 307692706 307692713
    0x11503020310260607080f07030b1f050408010e1e07060516020d1a1602030703051b0a0f0c080105131a18030a020114180706030e03070b130308150a03030318 69
    0x144c0c60007222582c0390182c2500d40380c10403415003d8010305210400d030401c280d10365540c50b00b040440e058441d424041c01d00d41091701c81245c8a015683c000d10311913007050411541d55901140c1f81c41d038080d96021140790101c10080241d030b5002c01c1d04c1814000343e000c110302480c0d025a20b501b07401d84c92004107030003880207041d00c5000b0004040711030084054048003d0085481c0c81c01e4406a1690300c2d07001031030500d51039071000381c175a000300981c0c054240012400311102880500c941080c441d03114601d101501058240004c2c42c1e415801020969803070b000118115003c070710310310b800340369103c04e1b42c0c0c11100982e0059190b082c4064801e03400b0541550408100d040284080c181c5881c0c95800041c03e410b4950090f082544c001c0c010200e00940046002c401d000040b80c81000d0711510708000c54443c071106182031551042c450007078500441c0c64240110141c41800b007000d014025070391111151141070900300388555008020398030003d200c0b02000060b0180d00030342c48800d8007410000e2220a80d45 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 307695206 1250 307693956 307693963
    0x904060b030103030e0901090b01020a0813032109050d020f12010f06080c0a12030503130c030615062003030112020a0e0702150903031e0a0e01060e01150302031026 72
    0x3002200030072203101c0007a105d8201210b0003401016200c406101e41c1005400117500d8054002014001520014044407034600030f280303000086611920302540c80400c0c20b00340c004141890901000a10304050010b0035145c2041d4000400d40c0084c051003400c04141d00b00b1100b41d0300700c0c2009034655250784004195039124840c0c0c800503d0440060300d1405c1400c800c101e00e40c034070b5810440e4444418424000400e9100040d20b170702240031821018581c0280c101081030320700c1e950001305000d05001c0c49a41c5428a40400800c444142d280c0404044494102031000c2010a40d00c0c010b80e4000e000400105d0b40031402a00c07828006000d00f209591210900740c07030301070210752500150748001c0488030741411001d561a40560020061821410030121040c1481c103100c0820f155145411b01045a2100c0b070760002110040c507a000b046410743d43c1c00c1c0480c0e4510309228034914000c2c101c10b5454518020b0080342c0c45010350b640b21408070360500ea03051f0340a030a50b0307458680c6100e5820400c6a800c2041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 307696456 1250 307695206 307695209
    0xd1e0314091c1b021009030611071208040201020a06200d06061403040c030609060b0405150a0504091509050f0d0804170a021c0203090a0308070b16080c0904060b0301 73
    0x41d002c0c06400301840c58400041e8074012007401084241900c1007180000f1031104035400340e0449907034182c621500011a05440341d030300081c240038503218204d00d41148140003042641d2040b082400c4802d02a4416a03130103400703c9011b07025030022040c603400144035130b0200690010072024103401c0c903d00c28030241550041107800130403030f80e100000d11000340c10440001549480048903451841d040c0d4030380001c6100ca1000500c200d1700c598603102000596000f00070080c00143c003c00040c608a600391b00141060410140101d030107500100311420280166030055811010031815000c5001130800103003100ca4054038940a02d030740c0c0384108030052254006600107a6500d40c0c10303050a0034504003010302406451104141084108895600031814812490075000245400401105c080e411071040c40d0320b040e03011040c2a00803041090b80409404910302488004400365a82e00342d407040c2c03002d590307001c0011440700c0c0e00040301c10b59404001e19041c400030f480031801d140d4031100c0100030b4000303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 307697706 1250 307696456 307696471
    0x31519090204090617030a0309050a0206031e0a05151203040b0304080d0b0301200a1404180e03160b04030c05062401020c130e0102040305060a0903110d1e0314 70
    0x4007000420300e280204d9000e41440341c60b0104034007040c0b400f942e80c4e102e03044160381450340310216001841000e2200d00c82103030700941700f16607030314080f03000480c08034150b0b81032103102c3d0303a243c08122101064451a4401d4015007900c1c6980014013003040070107180c4590400180c84100701c00300e46208410061405188260b40442c3c07554110540a416121314a500c00d010785e150101084082a160301111000c82c0d52100041c1e0711f5100840481c3e4844019002c60010384c3c0001c1d002079905100c1401c01607810720100700f0840b10380c000031099100d10600c4003c0346654103804151000c610b0300d0f4142c0e5006446420160804076040c0d45050400e9800c440e040140c070529180780070341420341091040000c409102500c3d85031003450028015908081051440c04e950380d5941e1100c05096045401440d0030008845a80c689250020043c0400c41c0701100000d000a0010400e008001030008000308991504010404000500320b50000650141010542c490b02c40d1640c1400c1800301030301501c00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 307698956 1250 307697706 307697711
    0x18031c020405120c130f020702120c04150b09061c060f14030a170306060708040f090b06070b0a05040213140105010906020d09032009130204050c0304020603151909 72
    0x141c2010000c881c40b0900301c400030f54120005200140e61a070400c655a0314411400194010343c04240800034020b240c4020b4000305c2108940740c0c411000103003508102c108580030710030070414010a80b200016407185500c200c0050221259a10702500540f0045150004003844000b0b14103c0406a5505030300c114090043e6820500407207121102d01481c2c08402e6005210b002115550441301d40312012010f114420702001203010782c1d4503901291401500100f10356140c2d0b482d0b001740c1c40702041e2440fa880c1c9041c500050b00d1101e0801800751649a0f0300320400401c1c1e661560000006814010012680f08400b0201e81c5000080c0e4461a0036140c2441803404096040000142007100c00790040c0b403d42d4044035141500c00d6000700b074001a650310510443c402c2c43d00103603020b14007919402a6a201c00c20350308102c01365007040d0413000b402c1d00031101030140d6110001800042c0c4400c1d02d019401650410004d80702d0010f180482e140090701030302411001001204010300800203810912010341c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 307700206 1250 307698956 307698959
    0x1b26161517090a12090b0a030b03060a0b010207030305180a0611010510080712022103031e150d150203090c04051b0a0c06020f0a0c021305040b18031c0204 68
    0x10740c0300c2008070310007030030102088060801c41c120070340c1e070001450020440040e0f5813241c0103480c8202007200041100284940e1280a000c501a0203080006c1d002c0e4002c0c030490002500d940540d0054814444068000d0042a8210303141201c0e603901000282c913044540308840340498880e06220f00007012582d585404d00031704180c1c0d0a094441c003401808502d509a0018441550046074450469160700300340100c407a81c61012030800302d0684d581480074109000d1804500101000951107455030b20900d408410750000300c0d1400c0203041d290792643e400511402c0c0300c94200000c0e44401c0c03034001e0703000c4010012251580c0c01030364001c030f804101642024600d002c1ea402e040c0511904150284d08400c102403048448400e0703406803903c0e403070801038030440d40002c2c4881503048a000711202c00301241d54019200f400b924220001c1d90490241d89210b21041e15a441480340c0c80c0103562000000080783c540c08620540104110001c2e0b40e180010000f800103582602001c0d40072410904025031282d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 307701456 1250 307700206 307700249
    0xd0803040318140609010c050604140d030905120f070204052d010803090f1207030b0117031801050c01020f0d0603050705150306011b080304030306031b2616 69
    0xc0304082200c10500c80b005006000400c000d0143d003a031444151407003900c691003100100c99409500501500f180620310900080c09480341800b002131410004982d185000d0030401c030300b1124000c00180c400e42080c078044408110070001041010f12500e102c03400c142c52600083c0c1103a0b02504c62000300007030741c3c03500028101e203a8210417038214055002c000e150b00d8600015100d1081002c014031640110018820a50755800341c2140903440600704c401c1c8075202d103440500043e00303004081c0070b0421420501c452080000444460714038115600440c200400015202c41d000f08118851954007848283c050031400c001500d1612031008011480038a50305042d4144581500b0840c083c02110580c0ca480403040c0c400c45c1d40000d4203180c5180c0040c030804412180c17030140680100300c00703130010500003407561540102081d6400b800507001d51200c3c031911100703041105d1180a514600141200302c140030700745407803e061a005410740b20484a0080c140d41640819042030a41d401c49a4424251 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 307702706 1250 307701456 307701467
    0x150c0305160306060903080702010915020106140604060e151e040f090e030a0e0301090f03080610030b01090317090904030203041d2203020708030a030c021c0503180c0d08030403 78
    0xa45490508100403404d2100040404a040c00301900203a40010403000b1a44200c0065004110501407030201100e590402806840d1911492492014600c0d00490606d006030488048550645031050014140024032049140316104c108000d9400e124150380f103c603001c0d100d085220311041c601c4d940d904290000204054540081e400d4178030381416454400c0001003200c840000c0303800c1180d5501c1c00394000a01500740c00d10018030002c0066034420405401c17142d164002c0b00220348518800c2103d03c001c40032500061161800030383c0a10040000c01c6460394006070003802404414900b5110501140007004150303821801a80009410440700d040303209485001c480071800034a17a42400550701544812980341c211942e10b00b021210105402004110010b000e400d0903240c4844882c14042c0c01400510803400140c0105c000c0c81440071740103148440000b03215140c80342191035002c088901842c1c41a0341c2c0c1458854281007980c240d40f440d00d409c1c0c00602ca101c00d6641c034902450003e09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 307703956 1250 307702706 307702741
    0x3140a030c0215040b0106050c0a080f0405011d03030301090207050f0a051e060906060f060910080a1a03100b1203030115092405030705090604030b09122104150c0305 73
    0x5081c0c3c2e04800c1c000007410350642c1da41101c03024989103403220010038141c2d081404050004010410000d00b007203148403404043d200729130090f25000b00b5880a01402106103800701c03582c6070f02d600200011300c40d010480e40502820f80c020310845540780b00c0380e140c040c609407440700150361541c440d0303010910091280c06910f4514102c1c20107000141401d0703425566400003d480e403032290304520000046616950141e98104a0003800115403d5884d80b010344403100543c0c80c02e221034104464005a01e8205e6903540000302c0140042c80180c560720b034207078014400400010340c4a83c8041e401203041c5c0040000c3c502906c0000d031030310000e869505020b0880c031203903400700108040024403c241078500c581b10704040c843e0350500c039039a81d81e40c0000b2900ae100b0118915480840070501105002c104107a880c0700c1e02c01c000448081020428441806002d001c001201820741008a4028240780031143c50b0068494114900640180c070720307040c1640e100c0919200001c0e50f8908011440102064191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 307705206 1250 307703956 307703983
    0x12120207150615110d0f0c050303070f030b1c02040b19090c09050a0e072a0807060605030102030f0a0b01030906050c030615030108030f0c0a060e03030108070509010b030109050403140a030c02 84
    0x48960303004c1c82080b6210852001002c040c0b0600200c1c030b82981e07004290340b10030603600030b040e2562858407002c06403110398082a001c0c0003a15155504003681416658107030b92540c00c00d600010b85000d03a007004040d1046003541c03900a0b01c400c03104001102490001000f518680300c1c08510480203a40040c000520fa031b011500c1144007a07070802c0001c86100400760401d50500d04042c54480078400f07040154a22048070207a803001c514030b10140721012002d08034140c0703c2c03502804020758071002c16003070380000e5811600c02c50342000420707170404a5601c860b07280b0f103040c140841e110307800c0e484550840f0800c48d804817011600104000b210302c2d003403640c9003181e61644070203402c55040071003c2d0380d85e0040c00002e80c4c8641d000030789040050380401c200012590f00880520020040d030710000e440350800c0c45030188510a4072808500c916202031494161071310845031a00f5070f8a0205140007811010f0302c2582030004110288003c2c01c0c030f8500810441c00c00c0d44000c00c071a0f1140c40020326140d580107824 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 307706456 1250 307705206 307705217
    0xa03180501051209010b0a0f030611030906061002150a0506090703050435040314190210030b2815080636010303020601050f04020712120207150615 65
    0x1809107a0b0800b0507259030410310000b20b010781d5118409540105900303500507a000341000000682407a04941d01c2003900c2c4650000d010030543c120070038203180416100000941c0120002a41c9414030403000c0005502c00d00c100d40c14052130b204107808007002910460089030b1648200000b07400c1818506070401c15a1031300704094502074030340341400030b911700100400c100c0d80c00e600040c40c072642c1400b9030510490b090103030b40c0ba1340c1c81c686281c0d079601c04119440c05029000010201d2080d5455000c2400c0c7c010b00390302d44501150380100d00601c401c407440d550052840761051011400c4068510240c0042081085030b01d0501c001f92004094a1101400300040001007010b1a1207a0f100c0c0301c4001464128031180f01d58800c1d602e0b1040c03c14003c0b211104c10b000300000300741507000840c5412503000703403180c03ca02600f16062206038415120003900d2484002d188003407a510821018050030007008005041800666178010603a412017100000a625800180000d641c0005040360813002c1d070520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 307707706 1250 307706456 307706459
    0x150602030703080103061a092d13030f03180515010510050d090201170f040b1b030f07020f011503021908100209041506030c090b03100905090a02030604050a0318 71
    0x800f0204140801085a5200c1804a0381310040b50b0003011507550082507100301303281034805010003c04822040300711901402200b00101c040302c1005008104000c1d104c4c2d18810143c0f410f0720040301604981c820546d407240f5070b0700040504c40e4026034043c1b162000c0e00d6500b201c8621418494010303000369100b084008200d100c01c98101c0300300c0d0200c94044001042c0d41c03c4900051782e4100100c950413000401c520100101003072100a0540320301d104800c0702d80940c07208001c4010030900903030301c070001ba0381c10804900d20344010092580c1c09101c510485e04469008500d090030349610080c100c95603240300805004501d04805516610003544508021644c40e040405541c0d44501100a400a078002420589901c8035084004006829841001c00503511440180240f00c03004244e400a091040081070b02000308080328000c00588003c058100d091080e0600106000b520080c0300313210309506d100050720305101803071040e8003a2015000c00482d504000e4000301070445c0c0e04004140d03a01e0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 307708956 1250 307707706 307707713
    0x60c0905010e040f020c060c1201080d0507020d05070305030c010c02010b09060102030412030309020405102d051504230913080d020706020903010e010203060f090f060f031f1506020307 81
    0x110002d0344122000316095010402c0200240304040801441e401550204408448100010700c0726185200160790141c2e40c504246840710004a106000110100100005880c0405091026900860903107014694a6444515583c00801100b01d5651a03c20780c1c00724540a10030000b51600a41d000e0300c040c942716000079140e00c914081c203240d411582d0060018980300c1e07032101100f04c1e805081082030341401c40554000c0142e0748159070f8903041441420f81014a0320042d1400c06407090301c02e5070310906040070440b190300a0480310311480744c140400a5080c4220007603440d02100661080070040001d014091800c100410018418a40003120400980040304a901c590b100300001030711590640303843c10180c031541d04019803660909105115040301940218021b000c215040c5c0c200300c14201c01e018800034111800708100426000040d1203007000802a0030226008056614900c0908004001a08102d070319022603907950000c0344656401035180400b900c0d9900041d0304144840d43d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 307710206 1250 307708956 307708967
    0x50f0f070509040f1b18181a0c090d0f021002060f1f080d0206060310140a020705120d090b0106094403091806011e0207031e060c090501 60
    0x401c010041100b00c11840f05229003042030310200c00541d004500302942d94003140304002c4a001a040031b0341e180401c2a10031420315036035881e0580e8072140c3c0449142903440540007602c0d0041000036030000410512000f1b6440424000a9a2241c01040c040903058011300a0b40e40e000100d190656001409000e801c0b042145210b600800c2d42d54514002104100841061803856100391058426203410074042a0003059041c0718120a608030f410381c003a411005d0050310080c5d862509900e20200100365801d850380c00408695005504840c0408851010303e075040c1d216000129803140d035800c16a0801203840c04c02401403240d40b501d00111404d03c00c4100c3e03004c0360700315214038507100b0303200740124030314a80c4016200c500848403810a405c900c1140300c0d22584440e1038075110740400004d408030000311010090241034180d403400161007800e00301a5a0742c1484060300154812041d0000002d900049080c00d40b149001800d00000802d250110654009046000c14081c0342c84d41440540da004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 307711456 1250 307710206 307710211
    0x80a08070807020102011401150327020112021b1e030310090903090503060a02090102070503030c1218031f0e010504200a03170306010f0f0504060c1a04050f0f070509 73
    0x40c0c841039540140b40f006034010080c418844c5010b0340414000500e11204514210f41c0c21100d850502412407a088503289003281c91480a01c104a0f00c1300031000355200c1c140c2c0078448072040d071005180c0700d81c00e062098034011044841101c0d0b1300000c401c81d4999000e40314a103401188000640c01c40c05e00240d801c5000e94030b4000d10300421b0755070950300c0605201c3c2241000420010f015102203003441e0070f2107400303503011840d014050f1288010006e541e04001040303c441701301c840058095040110881046584a64404502103526a464000a0398244280d4401c1070041c030700c5082401c00048402c090310000086111142d140108000c0468803040499034484a43d41c1c4070310b1300c4d96401c0300040002c4841e40000d02000740c2041c1c1c10f01d8a0710b82800443c02044246c0340c01c214480041c10071034a1000c441035840006109002c1000014050401c0c444554460750807501401c8008244074203005007220702340c81c2a48420403042256a0502807a007842101e01c0c05440382074288400318a035064003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 307712706 1250 307711456 307711463
    0xf1e120609060b151305090606030106050a0c14031c09050a02061b070825140607060f09120e040c02060619051c05150708132d0b01080a0807 62
    0x1105a01e10400c001540805038585004006070380803028030340c0080d080e40003e1522004860000008509441c10b05c5400c0c0c85040300130310440c5180e080400484560f0880c540400c18001c00d1810b000c001051300072200813030b06286c0015502c0310008506000341e03810342c008901d203442c03030706d0410740c013044003c42d80000342501680d00554803a4040c031010b072981d0300760b01116070350302507084042a9444082517190000500d01d0000c017540446006154001000b4031400244602001406d200350800f90b000e0070707885000d202c0006400c010400310700c013a2030f0201d004940b1046038942500416400052100c0c07190f034156410001076011200c045e660380c0b00903008078403480141a150701e0400007940c5001c081c01d0080d2105043c8241c00041086400c1541421111402010303241040c40345007035400351055450740c5d100c0c0030315101c90345003444224200905460590310301c81c0007819468022410010030303c110281c820318840c80d050410301c0c1c01060f005a010354010791105c00210303041030280e440f621380 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 307713956 1250 307712706 307712711
    0x209011205091e0105040212030313170f03070809011a1311090406030b040510020a0c08090a030b100315090302072d060c0203060702010b01081f0b040f1e1206 70
    0x121108114a4031040404a40002c3c4421040f400f0800f811740025004a00c247e507801620300000700029241e010072aa0180003100b01c50b2150046120300c41e19403140c14190034824905003682100071590f81c01181e4450100d10328030b041c0004107000744141450309850f46e1711003d03000395100000d880e0307980c41102020340380d0312015546400d81e00d202c1200d150303000060040124071340d039242074010400c01300c43c1564280500100c00c103035008180202c600090495940411b8142660342d00d00313240e000612101e4000b13001d0300c40440059056103181e07014003039020000105628520b0040700e40500110040c10450800f4443d200080e0009010130542e0001d01400c100e407407810b0b42203400d01013010002c103810328030040f000072a681c0140348400d041d40280c0650311a540c03070800030b07800d850300034480030b000540ca10000792a029040303408000002d03528a00b0092544d9a00056507560041d80081c100141c0c80041000340314682c03071000c0300010302d6031441c003821494100c100502c5071941c0e1000c0c06068 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 307715206 1250 307713956 307713961
    0x3061b0a14040518061003060b0301270f05100501030e0d0c02010c0f0609030311070c05060a030209030105010803131a040605130803070c05090a1406131401030308190209011205 78
    0x4070009880180034003400301480940c1a015040d1058000d540c4a8010000117400800143c40b900400040d900d203920014910b07460040000c4860b48003010591b241c0d8900010101c040d00103002c0c403507101105d80307001300780c9050240700c0c40300ca01c099a10850500d45881111100031030042881641071030a8103012089224030300040e2a0301c000340c080204000e00c44907203e001c02010f0b0b0710812400d40680d40801040b1a400864290740c80380d0000981042a00135042244d442c00340024880039a46250250400052038042401c0d14000e130881c800030f40011849031512960124050018545110040c282c20380b821200c06141c419406403004000b40050800421001400b0050090091030300b141d0742d6200c1810000358100160040d28403503407030342c80440c00007030705400f802160642d44562041e00d600c035013003000640040004915101c0e40c48030311806c541c0c442031500500070f5020382c8802605140c407000c0d550001c2038944074102c86500c148102e0903070b47d03401014241c409a41540015441c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 307716456 1250 307715206 307715237
    0x2090411010e0f181b07050d0207050103180f0312180213090b0f040f0804080319081e13080f070b011d0109021c02030703020706060b070201081f090207030e03061b0a 73
    0x4903a181c0c030201c5c0c40000d41030003040b0000802d004000c050303500740c94406803100c004406850a8442c01110490b0b412000c1010032402a50340010911a041100f80c070a610f01600c41507810580d01190701c0380462240000f90700304481c10324104512413908000e092419a2403401000000e8184c01d42e0340d8400300010200900001c5070205550443c00071350300c40703a03622981540d03039005000042c40d1101851014508074091900c0314015950925041e20301903c5401d0740580460040c0f90104401c0e84000c2100410282c03c02051580c0c5408100c580d05c80315400c00009110741a8020150454042501d2021340c8581d140d603030558140050161762606141e20004c4909a2107211000c0301c0e1001080c07082c201d803d64024225244500380c103110381981c80791805401d01405401070701080e464000204030b1024003000c6a510003408200d10460740c0c582000310200c0c0c002d40340880105400344031081750b40c40d007001035543c0000c1505210b5075114060946020034041e40e604001441041c1703400f41c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 307717706 1250 307716456 307716481
    0x8240c0c010b0301060e0103120c03140d1401060201020306120609120c150c040503161206021c2d0504030c0318050909030706150305030a1b02090411010e0f18 70
    0x80b818000e00a202040d1240140b0742c2034030081c44104c5182d0002c4241c401c00500844200f6500d0360140c4601c2c1e03800e0340b13061030211554070400315801e0031640c8000c014207201b454150780b4080c2189500041e02d0340383c81c600340403c2e44840407407020103511080400c02c1041000481d01d01c070810010241d40c842c0000703150245011202c2e8004000241400108650307144400c3c050022282e089080321100c060158007494201064000e40840301c050104c4000404c0103600100128840940130001200b2410015002c0342c102c8110740151079060401062010340801096081c1340c0200e07800c004505169030007030501c00322440000c0900500070103460001030601c981000401d4050701c0c5007690314241420321b480364412841118003e00d00202d081e48260000d660005030f030790ac20000d503d050748070541540e1501000d000044c100c3c60b1407a00200603210052480d024611842c0c2041900c04004005072084484008190065299100d41e03295540c4491042e8240014022150165100d02c1e01178100e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 307718956 1250 307717706 307717721
    0x403020405040f120c050c09060109030b0924071209060b0307080102070b01080106050306012304020d140601031e0b030c04020a050a1116030305181908240c0c01 71
    0x1801480d200401040c4420303c1d00c00100c1603c101000a076260741c1500a440084400c207001d4000d0b4800500c0d00e9450410042294000c00e0505208880e150b80f955240d05080003116841e09680205407120000e030300d03100051540d448547e200e454180382c800317001031183d900150b019030020b0b00c40703000340140035542c3d110300010807003d0103540300c140c0c4952002c0d010303512600e821900300c940c0c28000205000d0600c20241980c1004028003ca64038100c0440c19600c0045403003440c0c1e4803000d81c0c500c516030325403004000c440c03180c02c4045055804003587d9807000d04000c0038241810309016542d201400c000050342d240c0c0c0603035000081c14002d0800840c1c0303013400c00302c0c1c10740e009480001c9250201d90044044c00c0c0700c0103950780f1012000303c564201e80e1642001c94841d02130340300800c018030010780210701914100c0030a00c03019841c107081c0d0300080c1c078145a44e10355402c0d03480506018480440140100104500e500c1a00001110b0800d42c8a1007080010911440108003050080803010213402480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307720206 1250 307718956 307718959
    0x41a16050a1215080c090a0603080f0a1209030905120606090604020d0204091122150c020d05070623040807051207090603061d010506280519060f1403130305040302 72
    0x20051a01c0700c0c0c1043d1742e801c0d40b2428a100700401400a00b49103190700030002940d500c072000d28244880704648140d03d40010712800d050004114010319030714054071944020601958604a0191414041c01544010242150040c0d04040f00700f181640380c2002d070581041f81507800503668401400d0090003402142c1040303a1840c20960304201d0381c00c0710b2000d444007815851000340460003c1e10000112603251194441150072140c03441c1226005940700184140050221921036480b030742c0f224180103103034000f05c0c04210b01d40a04e003441c1814401a00008440c2c02e04203103001d0030b0840423541d8402611800344505150815500c40c0d540501180c1c0090600240034440b8030740303a1429102a04840080c94415004242054081d03001401058040d80010313100e006a4a0300c50101d403031241c10069000040f10032a01c0c00184d0f81c0b551700c1110302420f01c002e4000e144034204000180020a007070090020400c034402d00d1000d8045002c1280c1d080a42800d149001c02030b00d2074140e07000e01031640f02a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307721456 1250 307720206 307720241
    0x3050901020a081204030306050904030c020d0f0f1a160504170106080609070501030506090f0412031b120e030316050310090c0e0f041109011b0b041a16050a12 70
    0x1504e07402424546401248039490600890703485d1ba080c4803451004850290001d104454408094100540c1214482d4021101004444001d484039009400c501008a40c5404042c81000991440300794142c1c110341c0803100c089140d18428001405809140503207031030100100040018403a00f5844400280091416500f40d07140040301039486245a105080c0801d090000080003880d008110503c00d0304e1071101c9950f41d03100d51300d85a111110902950080c55910a05603041b120030209800c54480b85a4072511a00e000250b0f940a803204075200c01c1d01580103005101e02c60000301d4040840c540c05160003500d0740d0350414410801c44040c3d008401c007520300004a1404c03076101002c2d01c0c44240649540040d80e902d50280070442d150b610108030b10840500003201c0030342c410368008100d0300345100d110404c142c060f00d4041c1080310544040304d08450610440c404564120031403680718100c280e110048200c1c4080c0034100d84141c40c03101040143c40501c6640070280d070303488504001c01d290401d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307722706 1250 307721456 307721467
    0x90d1d0d060c272103020111030c091201050702120706091b0e070903031e03241508060604060809030c0d021b040204031505130803090307020f1c03050901020a08 71
    0x6460f480d082c00e084110071000b050110440342c80c2000480480f0800074811426a6400b00c558000c24040c420840442d500c8031901024541c4030405140241221040c1c1075403001100c00308003804510f4104a43c4990501040000e070b99008101145d0400078001e15950303030410b500e0b000d4001c00c20184024200302c010340b240c0c80d01007000b0384480e05460030004c081d40c0790b886600c000d41d40020305100003000180d001200d43c0032405105c000000c0b1940d40d080201c0c903041211040c0302d03030802c82c0340c0400b00c1d4207114208002d1a810240714040200f803500308094141011000305915103e01d010310424403c0c0d20000c540401010402c40b141d080f283c3e400e0f01d5100c56013140c02900c1d0f5081100020607210047c02d00911880c144c82181c3c202ca40c00300c1e940802c3c018008040000d845d00910301c3c0a11221001e4100210302c9480081d0b12458901000e0b503941c003241c5c03040100d0019001155030003055001082024100700d0642e50b07807101d405060180c1c645139641c00403403130b00324002001050b10001140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307723956 1250 307722706 307722731
    0xd0219060f0f0e03070b0c0312010920040b0403060c140d0e0c030d0804110609031009121e030506040e07080105060a0605120f07030b04050405030d05090d1d0d06 71
    0x402250104107944001c00b01580d68000c40d840c00d00c0103096a41600110010031200c100c2e0700c010038482a04a007502d00707044481c050f0a9039142c091703218804080d201e607050001c080286456403002009081d91038145800e10145401c01d018902008004554400210181500a80071801d03035402180c01c172540d6401c003110700c0c80640648441541d0074450713101025010720380032950b4000c0c8941650340d100c065482d0b84410049088202c00e031034015608112881060303c060000100100907044041081129864001c02c1ea50141d48045c040042c0313005c1d10347c4031001c48000f948400956290100f49900d514000078000c01070081881554070484500040c20035064202d02d102d484110350303124a40303543c0d81c0192820321429a034018016081c1d030000b0507064056a180e900040c05280001e4081c1c1c0706000b01d4115401a80d00b03695035400410b60070034000c502d00a02d5031050100014000a2034914809410200840407050303800c000114900710320713280e10382e030030300c02c903411440c1801604407118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307725206 1250 307723956 307723967
    0x7110102041503020c0f010507020a08300114031f151806060806030c0109150e0307090516020c09010b1e030a02070314071a0a0e0f070801180b04020d021906 69
    0x400b5002c19025900d1a101440418486c82d449103401d600905080e43d0740d0b560352038265100840d88122110005644181c0e4000e00000c0d840c107499090711079a65504002c03423f0000340300982c2e200d01c00c0d407012004003d01b9144001c44103418901301000b007201841501401e40018954101600d19031800b40800040c04060300a90100c03022500c49800e60b40320701e0141a20b071a00d140d921808907401120810400d4001120350521200c0c6241401d10251403000080c00c00101c1e500c850507450b100d4040c840d00071004207140c0c2c00300c0c80600003401d8000c00c0c000494898070381442516128500803c2c500044030100300c3c034203817150301d4180159403441d04102000080d0424001500003070b40050030304000e070740408102c5410940100700c0700300e41c04580f0300250b1000d1008007466903403611a08036155131a0304111360301701c111400025001441c05c0c0103140d4219420f07181202e56814502c808600400e0000100a0b04a60199585c0c083d100e91030000c18600d07103849417a0250340403210400910994002c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307726456 1250 307725206 307725217
    0x30d02010c2304140607050105161710060f050906040e010906050603040b0a020a20011b020a150905030906040e070e100219060605120a061409060711010204150302 72
    0x2c0d110726070b000382c500680c20038484000c0c0750700000c980100020f11108880c42880901084010038443c501903c99840e41c0c00d440041d505502d5a00010f9606201160000320b841e0015141000104507032910950b101c92040d514850f00061146c2803410520091050080314081030001d0301d01070b6900e5030740c0d0a00a08810911612403407034517000000c150762a1400807240a25041a22036201340c41e04c01c003600007035110603004c40074841329151041180c0200349000c0c407421004400050542800003601c54842440004038046400c0035181d080024441c014403002e0902074140040d40307642600d4071900c2e40c03080104c020340c080d0010030001441496001d809203d400144c0e6005041d1040906100a185407546910007580002418003082c03400001c0004116000b4807010403055652000f0481d18082c450201d5016080a46904117200403030050040c80c90030180d40f0720003441c01c0c40c512030300c60501400320700400030400e80c0044442000d40540d0082c0108180c031840c07142d0482400380080d80706 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307727706 1250 307726456 307726481
    0x40201140417010c020a080a0509010c021305090609030f07060b270109110702010504030803060103090c06200c010807080a140c0c010f06050f0409080d0c050309070e15010f0e030d0201 81
    0x1c0074148021144003040c10000580d00c110800d0070104041010f45481c1c02850f5001c0c10015682c33060000340ea140c0c10001d050032900302c000903107070601c81117490030824000c1c0a000964000c1001c03d5009a007002158649600400002515201e0000183c02d40c8000c1040308240f0001040c40074448201c41c0100d0f04860645400700034540c24100b5a2115006001020b4081001844100040390b4103070002d6038001c105240024130441d00d96200b00803125160880f02c0001c80750b6041d0700e000c01c81c08a110301148d2807803006100f00001800024002c40b4000d0142007000312a8004c0303542840150000207075112059101c5200e0316101000540c29086162107008940c20320044c081480f40910440c2c0035600040e082030200c035500c006100c00341552504c11a0440ba0800c00409010000e00c0f980d60219004d80e83c140d52400e28502161500e5199080009088e42d48800d1100d504002c80050000d44000c0c24880c103402e4108400b030301da480c0c1040342d05426010b206030f03c000340e55065001c020301121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307728956 1250 307727706 307727711
    0x409030e01080f01050a0303080702011e2003060a140d080c06100510140a020c030105190510080316060f0e060f0709050319050f0a030306050414041a04020114041701 73
    0x203c83c190180180f0081c42107035004200f020040c40824461148141d2280c0319000101c0d46601c04290306d003003a180e03800b11a5003183d581d900b82004803409826514ac011529046a0440c01c001c0b0000b40e08103580c0c81090b4190210b0460400f183e1a05505000040d07000b01a082e01c551415080741e07103e200440744144803200c03a00c4045058680034401e02240107150790b522503003181d40c0b031a920dc90f501802824043d40309050f5013280a507404d008030352243d82941584042642c54540c4501515030180c500e00d070079400d021050200d80c0000007036803000c2d104803942c0031a098490401c20000c1c0404c24a4a1402d41803204590801c107000600b00e000b0360508a182e1140d5541110440ba403002c28040c556140d044440e0460540380780c070300c04518490040c401d9818110480d4031940c41c0182d00b040460200c1d403943c0c0200024039240c820f9180080e48070700440c10b10b01e450394914003550202c4084c0d01341e007207220004c902903911580e040210402d5019241b540d40d0349a403c414855030030380030203050560 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307730206 1250 307728956 307728961
    0x315020c1e03030f04020f04020f0904050903040e0c070c050d0821011a031e0f090705030a12030e0a080301140a0515030106050705010e010c0c1b050f1306050409030e0108 75
    0x120207400301d60029228000355080d40c85060300413900e020040c0060783d01c0105030080c0030b46992144010018444920990f50ba1000204144800d8840040203050b10343c00034407003080a994440350300d075400350050340803556a090503c2c0081121030103402035500800c4400e800ba08001c1040c00a292192201c10314000b084000503002c1000c4409004910b041180f0b40c1aa41003094034401664018048017441f030a400120014400c051408135103003820403451030140005c1d0142400840c7c05403000341c0151004500300c2d1a00e0b814441c0c2c02c1141c40815940d11249245050240558070f4411343c400106943e03543e4842c8013103540603107041e03001d100d0030807480005001d1900c90a10495803112560107400d50386007510665003508415410386a81d5200c00c0300700d203441020311030f056905400c1e80302e215100400b42400004010003449003841d001c52410240110369403140c4000050400300e070b414580d03101c1d8004603006001c017640055000390900b411403042640000b01a0361102003a0b0707408041b507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307731456 1250 307730206 307730233
    0x3030305151f02010e0313031703040302190206120703020a03180c030b060612250f14090406030b01030f12020607080601202a01050a0203220315020c 66
    0x1103840c400c0e481c0d00c01c88140c80c1a120400080b4403030044a910b00000402c0640c6403082400d660184000141e01c48914070117004000c0380c0e82d502d58000c2c40b1107100506514007550301941d1945e0402c001c20302406581211011991030340c1c21500300040290000d01d040c101020080c0294006016000c0800d0900034034511540d04921001042504490792220083c81c41c0c691155042c0054041900a0000c02103109181c003c40c544e07501800942c1c154100c0503800e94045400700100300070714001c21840d0301140620652004d4804031304110303100d801da601c01c070403000500105040e0f403004203101c201c000000280700f6090b400700710300c45c0141000c0018000382007040303881d0a801c442950100b010307000816490b5216000310212801200c81c98400000701680b801d140030403045442d91844200d48001d5400c1407a0366800160b64002e00b4114200440c486000e5168080c00039075016110b100a49002c0780c0fa51a141c5c140115000f8480488010702c44a8080180d403000c00103140b10310903100e03180c019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307732706 1250 307731456 307731481
    0x50a0e0a02030c0d06060e04030905181512010f1104140103060b0f130f230907020c040f32011514090312220e010501090e0702032203030305 62
    0x9640d4020b01a001c0240300c0c6040005000b030208007550100d64a040210390318900e0952180500c0c003980301e0041407460f145c204904090080f08024951640d0410b03c0035141640103c80c0c0b5003182243d6440c0042d002c14680d900410400f610913450b60b040044982040c400350000303105441071400e40c42c0d50034040d0707001901502d1140c40341c08850344003000340320202c00700c80300179020355001c00c40f1640c0582d035540310500c40c594460300f280c04140301c0717040701e541c2c111590401d4410158040c0d03031561807498001d50194a0b40501c0c4c0300b00e030040c2d880710300b00445140a9880360105840c510340d9407090350490520359412403108000b001d0000803400000c103141e1491490b07640364110030342d1070f1907406410b99544010f6030840b10310307142c041c41403956220100241c5406031181701c2118091070050114401c0401203400d260380081c00501c1008014056642d20400c40400c1d171b84502402e5906440d0084102d180d881845006190252040550610710042820b00f0003124040d50b0140142c9d10740000d882c44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307733812 1106 307732706 307732723
    0xa0c0503040f1805150604050607020d0507060c0311070e04020d110a06120c05071707031b08040306060b03070e040e03040509010801090b07020307031b080702030f01050a0e 76
    0x9036200c040c0703e1306621500a0340140805103010700854507512032802801c1c001c02000445500b0b40d11004061101d0b01e92003800c95588070b660300001845443c264078220005402401c00780c3c610900003500d1310980d05081840e1001e03840c0c9908003c091889018120384024038030510602903500c41120400421040d01d800600501e494600c0d802c58414040e080b00307100341400b0f8040441d07074100600d89034103001b07d5283e81d103030542c0c1010754101e0200c850101e6030030b0440c540ca00030450701c0e001a00c122449000b0a029081d2034505440705030000b100c9900002d01d4040050222f0701d41034102e209050b0603407041e2450a6102c00116500202c00d0304100a169180c4800c0d01c101700010007071550040e0300d803002d1802d201a0750f034000c21203103001c4c1a0350b00381c40e0301843d503006211000044a1606a0040440e02c0d424405141580a848200c0390102c1c11490504c1b450070300745000c84c83c40e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 307553956 307733812 := by
  have h0 := BRFrame.cov_init 307553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307553956 ≤ n) (h2 : n < 307733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
