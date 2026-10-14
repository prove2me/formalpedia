-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:30:59.823706+00:00
-- url     : https://prove2.me/submissions/8910e322-ab0a-413f-b634-358e2e5b844f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242446043 ≤ n < 242625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242447293 1250 242446043 242446049
    0x30412020c1c3201050a06080c0109060c02060f030f06012307022b080a0f02070e04020402090f04050c0406030e1c1206090c03050609060d020901061110020301061107 73
    0x1e8030154505040350050884520342c10050a4080da4482062000d441e1a024452068414204019880c2d002600c40c0038003c2511417890551405100140000001504c1c03801c1160684802c0903461520f5000ea44c0b90b4410141603810480c00c2081c02e41038020180194410352109040b001ca03410315500050010f4440c881811100c0c62000e000e5020b003e001c020349540650480c3c0300000071184084030311030340703452213a4219a40001c0c604001002034600160849400765941c0348c091074105d041c03c0303a44071454414408000040717400b02d00503003099002860001030240564000b10700302c0b000701e070880f18200c8070705005400c08141400400d6250191650580680004100140c1c040032198032700c2c03c0701e800003402d00c0000c40c2880035403811508150300800020a0070000b01c046040003501804084403020300c9101c480340080c80c0e503d032400b004410590041d0141405a003061404c0c0c070780c40123450494002d80f045548010800c441400114040c4c071090b83c4040c00f8170043d60415180101d0307a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242448543 1250 242447293 242447299
    0x170609041707030903060504080406080f2202040e1e12031504150e0f01031101031806270c1703030f040b28050609072a060e03030412020c 61
    0x441804041059060752540210381d071030071a550396400e8a801d45156215500c000c0000d0305020070031050012900c00751089803000d8594107403070b41d140400c40c0d00720481200c0840c19080c44048c1d8020150f601c00e0502403880c0b018000007440c140701541e040c9000061004040c1070340418110140074581030010154196850102d07500b1801c11005202949450300500380c01155503400032281401101003910040100c10900c40c41814a010412810103090105680502240b10404d5040d4401e100340144403030143d1641c42e48214036510a409000001242c0110356815040c50403a107a0060100c0c0401d4414000a11910b24200c50010300c0380d00d203020727011190814010401319400c0b4505182c1c2c401da00c8501c04031039586e030883c0d10103406074039500034011000516079001c004265030b20460060900712030310410b40e0781e081400c84208920810030030303480220b2244c0303851020031b0f04d104c15a041d10450021517402404a01507184d5001142d00340c91803510081080a01901400314a41c22a026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242449793 1250 242448543 242448559
    0x10c030807140f280906021f2a0801060e090402090a0b1c050106060504051c0f15020a090f06020d08060a0b1c0506061e0a0c02030f010e0705040510060503090309060403031706 77
    0x1c52806920341c1902082c0c000701c0d9003040308c001c0102506600c43da02e81c010003800201c082003c5000d81c5200064085100040b030014400800d5050203580c4041581c400100680d820707950f03c1d03080c0710300c800002e8003100500744c4880f0360a603a503450034980d1180100340c230211022582581406800d540c5180c1c8148140702c402c0000f800760b516000219480b1141c80940180b4002140c5441c14402e580c0580c00b504142d00c01c05090403407070064004003e0031000ba41c90000081d11480003546c000250301c03d28025900540002c0f8800d4001c0d85041d038420b20081c0a410f60540e1050130445680c000d0011410030002885810381080342481070a4201e0780584d546418900d152101c4a1245861848101c641e0350100f1404011031081100c0241c1a501a0582c1d0b644021500d10714003a00200e200c000702ca008031280426142400d00c21203129a40c1c41c071420304018901101900c842d44007404007800e50000700110511900c0e00d100900041d4400d0381c4602c40700c40350784500c00d145400604914410400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242451043 1250 242449793 242449799
    0x2031e0309010c0302030904150305010b010809030921030304060204031e020a050d0501090606090203190209090621012d02120106051812010b0906010c030807140f2809 74
    0x80082511030350502802c064401c0034460500743c4c50740c0074150446501c40e0508410700c1d0346640107540001160300c10340c000d0240d5082c00c40159240e40c401c80d181c9000c2c0c1e10505c1500c00303034038147d1540c1d00c440f08100302c40030040056500c800d080da84121010b4480c0c640001d800c1040008011401400c0d081c980b40d56014115140c0c00074490b1402889100c0c443c0d040c1c1c41035607051180c00e40c400324550350321200410403555151707000c002941044034282c100c0700d00140e102d41452400e000b00c487c2480010044101540e40e01e0401298100c50003280958030510803002e0f00003007091042c900314400e8900c011a004281c14404280c402c0d100f03016410960044c0030103821461520103085c15103601e82003a07074544001103102007480c010441c441c2c1e4041181032114001d0501075101045506040c1e410f070400d0381e01c44e0015910320700741800040008004600107442140f0a005221b6803004040c162413424140000d8008141c10548407020070260160418181d00c5052004c9160300355a41030000050745 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242452293 1250 242451043 242451103
    0x21315020d080a1b091401021b060c070315020702040c0c050a060b03010e071d0a02070206030103172106090f16030504060f09080a08060612220209070c0203 69
    0x91400a50040c09401004902030b1407613500240100b00655003142d80301e644c0d900005101c540248038001c152500c001d015961540302184002042648010046114400b0000c2c80107540c0040c041d08102d00035544080001207020320700ca43c00000300000581c881c922401040110780c019000e030340c1400034484030304000070000310700142c406400c154001a1400700b400400e014040c421841600d81c0035241c00468030390f0041604c6211840140040609a030310720700c6441c202e108421010354051401e000400c0058a02070802c0b60001c15a80c20604081c6901c00c801040140c21080d071411a5264081100740d083c80c0c14680e9000710441503102c01c500344031203200c0d100da158111000c10191220001400e1000a070021021441081410083d80400d81850035080d0030401c401d00004204801140f1a464043c00ba1448030350b00300482c01503911012580012004402c1704417990386501072044015907100c10429105401c19195201100851300c101428032071041c9002c11010220054602201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242453543 1250 242452293 242452303
    0xc070b06031506062a0d0917070b0c100501091a09160e0102070e070503090618030301140d02030609011e020301081e0f0f1b03010207030e09060406050901030602131502 74
    0xb030a036141966417601a01c2c1c0c01001008043c5c034000c0c9803000080100a800c0000d40300381c0f0490580c0d8804103540c03262409008803d11000c2d800a41c1e124030000d104015940c402468506119012a01d04010b0078040b6000d4a0007684900c2c500c41d0fa4101c1400d204180346500503545400311004902031618101c0e00c010083d2151444040107034044c40382415074001c204400250882c1c06441e0040c3c40e145600800d01e5008560042080c0100350204500f40841c2c07015801002d0f0800180d07003907038205540c10105c1042040c0756540302004641c2140582c406000280c022128640042102c00c403002003521410080b050481d0140c0c810801008030702408140d6000360b80c0c05840402240740403070b8405281c0b40781403c1281e041d00500c01c243c442000300064041058402400341038215502c1c00405080b800707203000240114141c03810894261030100c031015440306009000041440c2c540c00171842e405404d81084400d954000f5112940083c1c4680c3c46000b040702000c507610303035040214001d41314 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242454793 1250 242453543 242453551
    0xf03060b040c0318080a0e031506040c021f0b06250302011104051509010e090106020105160503011d0910091a01080705010512060607021f030f02180f0d02090c070b060315 75
    0xf5050114544a04a207d000c04000c034080080445094a4a40c800551403d50503a0006e02ca189001200c405c210300224020112001203150000ca820445210304040c00d5000a06035220104005404c13451144c640c001c1360b00b540002c0b0f01d4103240741c0d03484c2c040d084980840102c41041c405110030402da60318980c140c2044100d80c8002a16440000016142d2581041005600c07041017000811200e605600080c41801c1b08090b40d02c50090060301600e2a1000307000720f005502c4c2c900c01d002006014074602941251465089408400000c02000115006008101d460100410790f01c0038542c2a8480365000d445a40040d209036483c05001030410721900b113501020390316803400100c1c20754803102500c2056801514211044500303610f0402c0542c100c407450000300346054414800001c03a80300f6100c0b41e5428000354031510b410752040001100091710b0095000101e40a03035001600d07410100c6c3e00480001c1c0c0240d40310b560b50714000000120061500e4065440340c140c000c07a02e1041c050071500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242456043 1250 242454793 242454803
    0x110a081b0a0f031b05120a031d010912050a0b01080705030f01230a15030804050108090a020f061b0319020d0804050d14090d030f03060503070e0703020f040f03060b040c0318 76
    0x141100f03402c0140c040d044c242d101c164480c0200c68031440c0080301194415045102e40d0352145042c0c00c02c3c41908040c180714202c070307001500481040c0709a0b4028000003400300e004800310f40381e08035941e9483c00340b030000340c02148143d0040807080080341002c1120751a82010b101c001c0c007140c100b1013540740100f01040403580c4600c0040000c1000c1c412182d001d280c07038100d04501d1aa0046c0c41c2c0c2064003e0b40d205100740c1c0e001880420001b00360103404181540c0c0385074000c0201c040d0740b0150042001c01c0c4c0100014603007903408807000c004c01c0c001c02c0004040d1080f003010804060704080202034100070030380801a0902c460401000000780c40400c098003164014141003444038440010401580242c8460540041800400d00145a0444501120380300d859a0602109407104149525284c8074814a202808050301140c1d815010360060030042c4030b6a003e550801d0380c0c600400855403104d40c01a07401955804003140203041c14024540100454101132007101c40d0600b220f29008841d1401801d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242457293 1250 242456043 242456063
    0xc0b04080a11121224040e010b060d09020f060403080a051c091b0504090305180607020d0b0402130b06070201030914030714010630110a081b0a0f03 65
    0x6914001e01241d24015a42d00c100d5541c0900094607494a81c0012121100c0b0a10807001031003941202520f2150b0662443c10507404080368420310003e00228140e182e1a552034980f80849925480050303e0072440391000820001c2c10381c018018802c0050070014020a8100300510200d80050105c0c2c0643c4108e28095a644c005400c04d255517a031b41d00c158013031250512001c0c000f805590034003040880d66808480c031409030380d0b00c100000c84a01c0c48006000c41c01c1440807030040001300101c15202080a0662498980d4a600190703215100c02e000b00c030540d00c1c1c0d03010721096040c00003190607040c4104004000b2a860340d400a0b00714002d40200a0415480b40ca10800300310601c0f03100490096498210703a140c19451501e60900d91060340c00c03010640c42c0c49800140a00101090031504c2c40d80721310f144070014400345035001ba4460180544d151141d04071a4269920780e0101c0a0007400004084c02c0300e00e000c0c3c00812319020319524881e100e42520002031040180c900198411283c0c0111014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242458543 1250 242457293 242457307
    0xb0315070c0b011502010501050102030c2505030a050609060901021806030601140d021c0203060a03020613050603041a0601110c130b030a03050702011101020f0708070f120e100c0b0408 81
    0x58800d0740724079004016200010000402071250354102c112000280c00900260ba214030049a481c001d200240711036a01c0020441c10396465600e0030400c40e4910112144065200c10120b440c00444038030444460b40711104101c100070703040c02007a4000d40d51500a61074400306080b5603800300210031016200c2c40001010481076802105a2260064114521074440d02c00468000c02500a13070400e00800c0c081700c1c090750700c42e4800d10131288200001800204040c0c1185c0900c1020307085002091984a4881c03400303e405d0340c500c0c0195100c1c80c03045071034900500d400301258400400280860341407002404207540302400100b038200f00b118003692100300038426100c0210240c0101d0714142d42501400e089070062541c400d0080040d0390003a00c601407a906000d0250b801c0344660000088504400d1040ca0009035203140104281070141000d400c6040003610740203010341d8402d4030840460300341c4107185e6040c2030201c042c0300341a41c2c0e1b00b418100e1801e82d494000703040c1c0c2c00400003445141c0002e80b40d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242459793 1250 242458543 242458547
    0x100305121c050108060601020d05070b0a0c09030c03151407080615041e03050f0303131709041a0f1804020d06060f081605040b280b07050709050108010b031507 70
    0x2a0091409012007030090b035940e030070641e40780d10040d11114018049d1303500350050f090150003141c3c1cac5e02e540320000b0100c0d560b8584408004002c94024901044a41c00d400408501d0f1012101d02540c09030640d080690040d2015074200ca0352504c0d20f2a4101d000e038100114160040d142581c829001d0381d2090312014000c8030b500040c800c40e000b02031b0106427000202c40b414450900d0100f80ca11401c221a6808246240d03070380e50b80011031b40f00d1a407490b02e1100c8030014151a075041858150007030365030b041c110084005002e5544484054213264480705d1341403814a010000074050220a0300d281c210603808000603000c180005101034050074402425604206103940007400030428859040c0400f42c40d00800e0341c4030b0b4820301c1d07002030314180000d0200307042ca058030070940080b074000c04024001510640c50164070254420007007401550140005482c100f100023011401c3c4204003800c50241010070400440b030060300508c88583c949107442000e5180000c040c4840041c4074014281946c1d00502 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 242461043 1250 242459793 242459827
    0x605060a030b0114130302040c020106030b010b0703020a060606030905010c030513060e070e090609010b0a060c0210030e030a020a1a040809090a02041503020d0b090903030106030c020106030203121210030512 91
    0x9140078000003d400031440e07108101c0c1400741c907c211010310800000d010200e007030390300c039002c080c21340d411000042003880303441002018428401e006807540214980c40760002ca52459104802003a00d030318000e000c0100c01c2c80f90441100c0b05080c01c00050612108030209002114402070440b42c5d20981d64040346010440342000340b500c0d03403a5644a203401c09805490710f800f603a5140c00c660802c5001c0800740b81440b0b56205a600503a11040741c01159005c12014403030b480143d02c05c0c9a40d4564058590300203000901d005191600208011800c034544410940901817400d44580a50b406000010703400900311400c2e900d00311111708054503140f5414009100d0740d03000c200045074240614100c0d5406402170045004411401c00803028aa001e00c0007102e001c98064459800403c01402994041d90007c410b414140c8000030350b154496000c2882d20b07034191141c40801d2804200d0410b0941c0b44c0c1c1400d0b82c041034111507d01c00c11303d140e079129a5030201403030b044c0d081000820005520100002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 242462293 1250 242461043 242461067
    0xe180c03010e0102090a23040209240c10060506040902220f17010b40060f08190303230a0e0c030c1f110f100506040605060a030b01 58
    0x200500d00c071a00216000794805c0e41d070b06015100b45c00d4001520b0201401c00c04800400d02e0f01038000c145001c0420000303500c03010300d0301da03c01c1c00c00e5982525110310081c0750741400c0c0301d691900e0b42c1c3c0640d80b040501c0e00b01071268200000f0306081c0107006c3d689a03d0300341c0341203a208800150300d8500240f030759400c078210840750320443c4255020025008a20201c0a001c881c1010340c40212031201103040c070f007619890914507810038014038035611091a0b1640704a4009c404103540859402100542c000d02c02c43d25001c8192035884400a1104580e02200c04004001c00300c01400c64124540c40f0b03500881d10740c0000745c149651140408150310b5851011003210109844e200f2940c684822070710024140f0705071150030740c40f6484e94020207050010704c0c20702d01c6800034051041e20b04400100e10410995204030010481108114040311404115100d080c0a0003406400400880f400c0c0f1012500010720b4940b03e64244801002141c64140496000c040103103804280c280140d001601c040c51240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 242463543 1250 242462293 242462299
    0xa03020f041b03020a1704020d020111010e0d0804060e060906011203051b0d021005010b0409020f0d0c2006160f0903020a1d1f0501051615091b0e180c 66
    0x2512041d500b03030f040c0e0040035418400d44542c00d4084085403500600402250025085480c10800741c0c05907024a4420030640003460011407030000303048605040c000a40304d440701103170481040c0020040c5034002c03c030300e800c2001d00034891860902c001a07035904d0188100306070300310200680000d041c8598101e9080c10341c003011038480c01000d01c014a5481c2107420702400103000701c00084460f0b040390f0007554104e480313500c540360900303040c4070049000f9440035088049075642000b00424a4005c0d00a030400c80313119440f0100182003103030403541e0a24080c4800a0150031030740800c03112402c01601e006a040051a100c03011242800054580340000d41004e0b501c00c210b40c000007400342d1040401c016100c90246d60041d2621000f403003600c0d00815005034841315500c03410034441544554054004a0195040c041d855141616450305081c03c540c00d9000c11525241c5035814020100b00e500010014210026070b0307146003814201c96001c02410071402402c0c00340d140c44000400300040d01240c0401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 242464793 1250 242463543 242463581
    0x10020307020901030f05010f050105060906090301020c0a0323040b0a0c0f0c23010503010b070b1f0e0402040c050a020a020f01020f060c03060f0a1d0705040815190b0a03020f04 77
    0x2c0c00c03e44424021040b041b21a50309104201d44580c2c054002c00b07049400c00b8108506200c0c0c108204002a0448800c254066509003c80b940c010f408200800265009440f03ca5000c10240070180100351901c05006500c8000c04c020040d24900c6401c41d04d1600445c6004103030640a440c2651801e041400080c200700c0c4855400b040400d04280754004130500e840000041c294000010b480b6400240304070b1001650030710030309011a06840015901103504010007412408a10b0081c0040200f900700f40e1801700080c0c200411804c041c4038501c1b607030032103046c114148280301030025503501907008000d00580510424050590081040c58984402e05096544503d4000c504070415001207442a11030701d490a910140c9081a01031070003601c5881c44c1c010f071702d8800840984900200a40700c3d00820004100000e44002c041c003007000c404000010801480c1800403c28500c0d440305003181c0061071406035460525940c01181c00100c940c1540c42c010785054110014005180407080c0000030406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 242466043 1250 242464793 242464799
    0x7121202310e33060a031d0a0b2a070c08010513110d02120316020405070f0f11031908060f04051003030e031501060c050d080415020702210703030305010806130210020307020901 78
    0x160486003080c0015101543e9911040b58099030350080c2000140000c091340e4045100a40704181220384041e2449210924610601040d0704542c014201510b03541c480ce48103006036071080c0100c9820801c904000501202640c0f104140c880401604c54418102901c8120440d140c1c0c4404070788a11018082d640c842c005c0030010101d6580902d0224030891611700080d000074019103085054008032f82d0340e00000800100300366050004001c150301e46d4032050103a03001d84210001036a10000f0301d5900c1d017006040131414004a0110840300d90712460030502003049102c801100340040300c1c0c05240080c0c5404e00740000c00e0600c009050040301043d10b43c800415801d410a2802100d107100b10100c0d0f01640000174100da280c00140d034010b06010502401d03504001c44c94010301102c0c1e000070f055801e0200c1c110f0301c80d0321181181200e0b42640d0407200c0c0400c145609446202c1c0140000c40140c111072410340c40d85030303240080080003803046d81400200b002142c801c0094030b10300e40d40a4244405561 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 242467293 1250 242466043 242466047
    0x3020c011e0b0f0a1a0a09081222150c11040906091202060f041101050d06030309051005120f040804080303090703060b0607121202310e33060a 63
    0x1259515481c05002c5040f4401d905081c22403003001120b0240c081e120802c0e42c0750000300d0140e8004103006c020001b1000700880c5041c0c00388030803940201205e550030303640e1074103100c1b000c840310704008202800708224808000c0941922440c000e0300700c840ca00056442d82c6440c010300341c00c0704905540e4215103402d04e45010850550f02c1a40c241d0301500c4410040c0a01c4234049a607804203c0c0c541c50124419004200018030041c03601083c104141481418030500900c0030b812610306600903000201d5044042105080980082d04854500c5c5840c9281440985801400f408041d100c0703241c02d00005d0004060103405400d13030b40581944803d0729580d04016330a80ea65400c64007068406600d840320f030403802e140c04011030b10650fa00680150010345a030605481c2d80543c00c0300b94014075000c0201c1c0c9401c00c200e0501040c1d081440e42d0101c40c2d1700c402805101c003207050f03401964403584000103002d44580328620006400c0c68110504000000402c6101c1541440944148d002540031400c10038140d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 242468543 1250 242467293 242467301
    0xc09120c0305060c0a1e0e041506030b0a0b04150c051b0f0a12020d020f03010c0206042303030c091c08030a0e01021606050a0e160e01091b03020c011e 66
    0x780120b044822603291880c8a241d50300c6400181e0000c100780700901e407030394006c86004403c20340741800e0050f079000a14000c182a20f0a404201e40088004401444401c1e0544101e245018041c0c9000c1410740c280089807000344035500176601581c284003914014a481542e5103054103601405031412604070100c1c01e10480314030307000d03144220803a40f00402203081082c0304100300e075182540003407500940c1c0c092020034078120034180d800900b07102c1d00100f262000d024440030105680d0040c0800d00d03060608800b1940b4264140d200510100020032894400200b41c980142c3e000c03050a59801c1203030001005400c8a20951800300c40811202e000c0c403102201130761003030307400c3c68003402440c1403032101b14201e10402d1041d2a400f0310303012a540c0411a00c3c0c0c0060352045194a00164940080d0f481500d021011a217102c0c1c4144c000000703020020100d1005801088054070602c40d6509041d108001d01d230b01050540304056000c80c162620705000d40000d940316904101e050000c001e2002c2682c050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 242469793 1250 242468543 242468549
    0x405070b041e090b06090d02030109020a0b07110d0203030a111504060b0f01181a0d060b0c2b0c02030312070917031317030d0c0309020901080f0d030c09120c 69
    0x70715410382c0006030350621405003400300ea5004024624040481c030030483c0c400181181030b6015036075107140c0c100603264032680710301602d8603c00d035946a14003450500c083da4140c0c0d10460260100366003410058400100307440022034170b1309054007446d40080c00a0302d401000c900d880301c032000780024030042c05032503440724015901c03e8440754402080040103480321070030740d14081d1803540c05110400200795074040382222404c1a0003c90324003a204c3c0280c50075142603401c20200c200001504030032001c0104450002c0c10509c009452401c10260000d00350f803044400110140300f16006400c04650701031045070846071094a0104440c1070215009041d588140248094800d03240760424206100000391a030000c0e21000d10400d042c1442c0300d00c2070b4080c90398001c0700d45210910090402d42c84178028190600d40913680001c5444060042007646075060b40440f032150004542180000c43c00b00f5003194480c034a050200701c1441103041144c8601346503000c031701d644100c0c444090400010105580031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 242471043 1250 242469793 242469839
    0xa0807030c11090f0411060d02040803040905060d08071205070209160207061103190c08070b1f051e060c010e0a0204060e0121030201060b040e040c08010203090c090405070b04 77
    0x51441d902070042e8410251201300c80e1240060000c3d001621100d09402004009010360741444180d126910a0b03801036040468560070204003400880003910510354480c604585c150103004064035401c03018400c45c40068807803000510200a054080c03c01ca512440e8003516003807240ca00794101d040340a1001001c0b20043c00b40d8103002420030303c40c551000340c1c460480d015525007101d5502c0c0000c0c5000490400307003880340010301d2101045100780945500c82c01034166124501e800071114a1070110001564000740c0710f50005d114585a210000404c0c4c11400c0048181c00d01010020700f903401003800d5428190b0900740d49003400b0724040ba0f00c0c00068400e403014080b0310b40300c042e00c5440800901031540c02c0c0c1ca404500400424400604800081c007031f00000807141c0e258000c080465019401c010510b05424060108200c81c00007140e0003401044000c50442c05c00c00100c1d03880d0300e140181a4030400c40704022509215052100da0024481c50704210b964551b100844000708083c01c0c0c01d100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 242472293 1250 242471043 242471063
    0xc0b13060e060907050409020a0b030f010f050105040e0f0406090b0901090b0f01032a030501060e15010f0e12030d0903030b100c020a0306020f0909240607080414030a0807030c 77
    0x1e451900040040c091214100a0101c25041000f800700078088040241d07400a402030f0f00044000a4130300850003803281d501061404e41c1803010700d907040842503210030704000003008200b022003c00488aa00b02503040e41c1810640c603542000c1e000350507a8440074290400203c180295810154031160380701d441115240c0940d034805480290104091002418121041012100300c00007800c0404140600201c1001100d031030384c441c0c0c1d003102c00c26001050060010350900c95080c0745400e441160b900c0910300501501202c09004190048140340d6a01420180b64680040348003403003501d5417800014410030007142e85082c018050510b0070095405501d4034151152240d2040300c448141640191164003c1850b40c1d803160001e5201c1601003c20200601110046540d0840c1c014000c103884d465200540000300f0915040c03d40d8000000d01c904410840c510000b0a250150ba00302d8141955218041c1500c82c0864108441c99400034000c1b10005103203000c050b0070004100d982c600903a8045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 242473543 1250 242472293 242472311
    0x1c03060906030b070302030702030f04120c05041b0e030c1201020406110f0c0d0c150906030e03041a0708040f09060807050402030105030307061505180115080403050f0a0c0b1306 78
    0x40c12100c0901000e4604411800003411103400f90700116040041e5104032490000003142150b181c0c3c001d42c00c00d0f500c540d08103101c0b105112031540c2034806040101c1d404c105a03e200c0004908000f0807507050014071045440c019159a4180030452003210040c03c1120307400001c0300d02e07a000b584075000740f1020802c800c00419001e0000109003020280c07100080c4038240002d0100040c180d401d40040310180c4403054040ba50741c00da9201c1101140058803840c00082c02c2c040040c6c244c2d030118000300943e80c41404108014504034021034000702c607000c0219a075000500b0207021038440d1750401180700c0101d440028150500d40e00038811500360070140c481b01611001044244d20080c481c1b158507a0041c42047c001c81c01c0359109044402e08031107210440c0e44c0d00d0011030307200c10302c81c0341d4810501d2040d401041200040841c1d102180881c3c40c0c002524601030764041c0942c0039280710660b94040100310302144500400100e00b07244c1c0c12a040c18014a0045c51358848146e148404441c0c2e1402e00405d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 242474793 1250 242473543 242473559
    0x80a050304030602030a09080d020a08090c01020a0f020301150f14150a0302090a08012c06041e03020705031b1305221e03031d0c060316111c0306 64
    0x5404015404009145003a14640f11440139410140000c040146c1d58400d40001403001001009820008040940c6031014404060500e00e401042400c0d950405904014980ea004c5580c6510702e40c00303002e100101e445400406c0c0107080210003500961640107021031140d941b202240d04440b5494880c040071004507090105100029241f2086010284000a0014000d80140181c02000b0f0882c82482d943c0d04a000d094078048503822078008000100b0282c180d40000c0f06101c14415900140b001d802e255842ca51140d2002c02004013014286c6960700415209020160003800028100c815110401d801e6001003248400003510840e4008010720194400340500751003a0450344001c80070300c0746274010312a0503007900c004640b81ca410500b0b4940011036503014030803d070301079036001500c030041c50030700d00c020034042078000e6a0340c2c002c049542c0c15955800c11030303520141c3e01c0422600c2a8a041c4181c0744042c860305005054050203207a200c244168411101c2e0702886581c0900100740d80f1313141c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 242476043 1250 242474793 242474803
    0xf021b0c03100e100b030109061b1b020310020a09080a210f0c17070c0e09060108070e060f0a081903030b04150312020307020901031505060609030d0e0303090406030c090608 76
    0x1583c82d450300081c0c0007010706500c0f6803001070651009400404c45006903603a1408440c5452341c9100c03022014001c2c1880240c2c001610450801022031990b550301444c0c0000b81e83e20781c4007008840150700040d10703100e0140300b104020001d02c1c0040490f030140805160000e04c8641c2c903401440003880b40000b050090b44074010000c0701c2d1308151036550b0002443c1e15070750803a1111040284075003008001240020740d00f414280001c0c000305034001c0341e5040c0142014141041a4001103261703020030405d004070900000419003058040360070059031306114010032032591b1550f00c076815a0040d41c801426000138981e0002d102d521a43c1c0420420b00d44070100002c0b2403401c0441c85030070004070380c2400010313000744c4d00803c3c5403010700490742040b20315800101c030070100340c1041381c01c00004901d00c00c090000b4059603410030003c07a0404d0a044540011030b545001600c00074003002204240301c0e00b1a1000d00440d404400080c209000d0f0366143d04009003840c0c4e45225101010b4035100380002c04010101d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 242477293 1250 242476043 242476061
    0x403050c0a0e0609180d050315041e181406040c06021b01120e030327030a12051504020a02010b1c0c03030f0203040503010219020114060604090f021b0c0310 69
    0x4442c2900e0715148140402e1000042410304103100307402881000c0c1c6020084204a00c101ea0340e2a6a43c0c0380c460700b1412070300c0c0201d4100c2d004a00700b0862910b034000e4036480c824103640501d000914000a501032500c00ca1403401c0c0503142140409032010030003c0810b5144c829800740407009a11a91840126998000d82a00650288515103030201641c41202030340401d201250700032940148602a003415640140c0d040306d80403469040d4040009071089040e015002088040c4d0b04200036504060403207144800028241c0d070344e6400082c2c203042d0400c0d4811442902800841d15a2010740d400b0340206074154000f0b2040c00f01311241e4002c0d0201c1c40210780c10603804003007105020306c1c585e82940c82c0d41d100183d441c154007080c8004106501d092014105e04480c14102500d0a01c8a00000e803c4900526041d02c180c50358000300121a1124000c40e411180c1110000501c1603000000c800240280ccc003044010706107900c5002d00c0b4031000150200d902200b24140d994542c40a916401240c05482d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 242478543 1250 242477293 242477309
    0x3051609050103020708071a070914010806010e040912030b1903020d06050414060c12010902030403020c0603090106030204020d0605040e0f0a0f0f06020d050a06060e010e040f090203060c0403050c0a 87
    0x10105000315403184d009021040c0c41004841d04100b400c1d500d00124480e54101064000004d0040002c400d0780592501300a00d0100d854032540c1c565000024045040140700c1410f000c410360400b500c80e11540d0140004e127420202c155000d00100f4030080150550b03c0c03040d407062003042c0082400c190341a0f0954116a401002100b01c11910350741d410160100030420764042c041d030104c1c0380e0481300501c0700038441c0c0d006040041d40e4200c0604001e0401d0010b811801c403041c8107004100000350000f40145140504440540d00caa485c101c0180c05400f8540000f0340007400800c03003d25014041d08000d0540d9000c88043c00120813403030b040c0342e503814044080c040c0c55122151171404980412241c196481c02120714180081c031039160b03501030b40e01c5407440954441e6a07004101c9009614420003028102da0b103031550042148000003001010951042031082d59115099545445154840525158094151001458070751001096034010703100548140c0998001400d0500d4032015102c29074641c1f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 242479793 1250 242478543 242478557
    0xb0c070305010b0103230405150906060301050708060108060d0501060b0d0b12030a20071508070908191e1208190204030c03080702120f010603150c080106050703050d0516030516 78
    0x6e440143d4140140c01034609007d560001101c4001405001c1e11034600304005002e141402000d04d421502c1c000c084c1c10402801d4003d0001e1303603a1001d4110b070840411900d509441c03841c3c2c04e100f801050b89a11012088000088440044910750800700c080c5004940000c15003041d4040c0940f00c0c03198052070340000781d0304070040b008050068110300d00c01c180d50045400c215151445c500c0b580c190250782201080c0400300f002081640004000080c2c0180005000c000c1810b8802412089500000901c29041c800b14801c3c0030144c4401070308416001900482600e1000101034141c200984d0062074016140902c8030301d1441c140200c6088036440003d038002c481c60354440e420300d6002400c089034400c006032206141d81100b0462200c81d0541100001255461403409106940d060360703e00d40703250b060800050050360482d55140c1103c4003801d19076500c80c80c9180449180c800c805405c14018945400d00c00e21044a401190b07039165181c80800850712820358600640720000e800d44001416 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 242481043 1250 242479793 242479841
    0x1021b0607020d0807060609020d0c090303050a270e04050616120c120e06071709061609030b0702100b030a260c060910142e0b0c070305010b0103 64
    0x30001000f0580c000e00040741040815900c0c981501d440d50300442c0300940100d10050304800c248203201c903070f501c2130a103200c02074950740d0064024062180d4050501036034407031650300038000c11070008181d01100300c1c242100b40c4035a150b1f2145001075405684a104540015400030503a40d44c1d9454100030b5114070400c10f009000310030203030016000b62004c0102003030b0000f8000d500e81c0144c02d1a40242c0c005807442c0d1811a80080c0703911040f1030062110f0500600344129600c1c08144c040d0800c00413110346200444610081e1001400c0d07074001446682808100030b01c440d80402d20302100d42400c24107100340700b600c008041d903848a0000103005110410f4040400300315608541c1c8860107082106030918194a40b194100903003226004807075086040c481032204c046106010714000700790105089400d0800e0100380c0182009a81d940c25041045407108240801315108000d10200c1c0c11580c2c1c8480c0c12003c4ea40f52185484110f9043d82032100b20f01c015070081c01389008502c0800c4202506401d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 242482293 1250 242481043 242481049
    0x1905070504020703051b010f0c0504031104020705010207080c030c06010b04181509090503090306071e080c070204020705160b0309191103030307020d080112020a0b09041401060c0201021b060702 85
    0x301c61401242407040070800c40306d010014440b40d207100600c2c4c200008914032902058030554100745019000c000381044240000f03901d01c841d2a0031f8103014ad50058640c511450070380d0081c81024005410f000020aa0307034140c200c000000c15480c3c1101c01603900e280d0743d0b080b0000081c011400b40349000d00050701d411408480c80d9011080701ca0303400152105555a41280301f0803118182c1c0281e0b440d03000001c0c0311035181030030800503421800c5440d060519141c0301088641d048092400d0904100700703540401c99480100342070f01c2e05981c00510441d036500d180c1ca010390743c1303001412420118020086000640d8504442540d11400c4049c010308114401d400041c00c0ba5080c0078070440300c005801c030354424141c40801c003961191020341c00825058540c068060b02405050303004c0015021810718800050b00c0d5800240119011402055110344d00000001c0c0a0040c200001150401003000000e030140d014120000550003030300be4507800701c2002086440c100d040e0a0707a58000008000031b00043c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 242483543 1250 242482293 242482297
    0x150301061d1512160e01080a0b070504271802010504090b1f031512020d0303020a0e120c040b0306040b0f0c07060f0204032904061109031c02190507050402 68
    0xe00c2c0350460702d81032100b440014280070705500a0004590280384c001c0c40008040502c031002c1c040c98015110719601d48010315940e0180c000e0014140ba008002003030109028105460180560345414001140e110080d0328011042d90942200e0904000240c8142800091018515501a03448070705d002e090610003000343c400741068541082005484402280b01c1c0004043c010601d5035021440e00d009040b100c03440469030b040013141c560214103040040e9200200c00d0707902907040c10003507184c4030864400e03108001d6825a0b680c00c01e10125602548000100c0c820181d00000c030780401019002c0c109243c9d403a0310480f8000d00d101d1114001c00d84410504003c1948408450300700303403414005a4502d011b80c0d41c1e00440780328040d00850140104503004c0514102c140c6601c2c0c40110304c0040c1c1d142040e602c04080c10240980766180c12801e0280100c004a40c002c1f0405002c0710161264103040500d0612900400710050040c440120707408003520074800c8049401c1401080e0307890400381000029 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 242484793 1250 242483543 242483551
    0x60318020919090f0b0f07091401030906020d060303021908040506180a0e040b25030f0f1107020a0e0105010f1b0b34120f0e0102030c03150301061d 65
    0x2518450aa41d1070701c40c0c50f0181d182d80d1845208104002041031030200c244d142c010b0703c5400f0f50781686041010305640103100da0100e1300d8041c0540d400e618048010f80003009140c00181c0748038000188030b082c41c0b4541d0030820407a03110750300712094000804d800001c402d6986200401e002c0080100704020305d00a409007600000040c54000c0e03440c1c0d41400251104801e50041c9110350117001007206000d16006c20360341c007480700380310f05000d0048140301e03022881c9a000c409003070558498500f040c0302c0b1366038003002c18008142d0040014114042025160b5040084224403d40860001003180c0c192071f04560304a07801031311408041300307178000281d401e0420404100c18800d0b01c1c00c200404240d14081582c00f84010300d03980362118410600303001111405618000400003190550741409a10110446500c440410001649008030604801406c516452902c0319070010051040d001c02c4440110f000d90b04100340b0700b5941c1c2e0400d0915090710303494451009461991074540780840203403800c0c150702c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 242486043 1250 242484793 242484811
    0x1a060306010e0f1504080a0311030f030403032a0201021b01060303050a1b080708030a0f0603021f020307140616020c030a02040218130203060f0409050a080c070905150a0603180209 79
    0x710354904c20b030350485070050780c001c1b0415400b00000030300b495000005c1c0d0395004200c402540c038001c003483c458016448007510080c109a03440010b001d204803008c41624801400e00000c4852030b080f5030000b4040c0d000f41045c005140c0000301c03401085601442200100d9905450781030a00076506815201c46100340c1100038040845440c00001030005d00082c04007600c0f5565642d02c900708152004101d450f4580c40b00d40071440c0030790a00150303460a00b100280c1c030b0400c221300680141c480d0704a086018040005105022500d801521042c01040141c03082e00200c80283d50741c504c00c101282d4607000c11400c2c83e0140c008806000141c20150011300042c010000c5400d41c00e0302100c0400d85401180c450346000a60200c01c0c841c062a200c014060780c081c04840911043e0050303100c4a494140011004011100015a22445a409200c000d004204019040225217812020b40d85604000c2410074800c514100000c94100d00a100301450100045528046000382d80c0c24061040d1303004e80140c0c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 242487293 1250 242486043 242486059
    0x6160f021903180605090a0902030c13090905061006140904021207031a0d02060f03070e031606020106151b03090506130305070602030a080a020304020418061a060306010e0f 76
    0x48461240c8001651403031083da54148081c0c28002020002101500b08204200040003100b04580d030700703001076007500c001040041e42d030344541d140c1000b43c0c450a412002480d00120700080d2036202c0c0ea00c0810007501640c141c605aa85142c038114040311540609070100c1c040307407540e248480b00712026111400d00500700502e0112034120b4000e04250440720b240020752200e00020420010303240260040d03005445d0003000007242ea0000f2340d03074000d4038461861440d0110000f03001a01c103001c40780752404080d09a90032154024180030760350740305000300303000356081c090b00085c1d5800c580c100d03501c82d580683d19600f0040c08100d40e021311010b1304c4000e401304400e0300030101c0d2941c3e030400141003003c0c495041e074981d40c0c510318045040154a512040954000b4810312549640001703c1540c06120110010717900ea45a2001400400400c0144058098a20218010055554008490440c4400d00b544240502004000e20b501c4104d9130540025512100703000d2908010001040c02040100b00311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 242488543 1250 242487293 242487313
    0xc0607140d051f031113020c0a08031902030106050309010b01090e16030603050f1e03030106090506070c0306110a031a100302070501060803130e0c0a09050607060b03120c010b0306160f02 82
    0x100300700c41603410640e0307160901c2d80d42c5c102c2480c207401e1100c681d0700d1400e403e50a040d81064020345580ba012000b034401c01001000a5219410300400404c00c021024215120358503158010010f400403a0188441e40c6000d5140d0b541d0341c090f030420703421140208a12007041d950b0501d0300440c3e03602c003411a0241030b00d498022000900500040052207010401084548404d4600c0400400512250403158000708014040c00d40e03c07042d10410703a0713801e8032101c1d61603525192100000402d40d001034001e0703141940c0c9080845403040149684841c0d60740a00c2440742d2100120001454080031590142e40c1440c14080f41e40203402a2962500400c00056030990f07600b949411035010348000500305150b000e0a1007502c031010760043c3c000841c0c400440c28005805409003124030310b401494817480d000b090300001c200d40d9170890f803002403018060307440000c501e00b0100c40a0f080503100b038050f5401c02c51403848600300082c00c5440307540308042c104052111208150703802d0900c02c09800c21401020710807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 242489793 1250 242488543 242488591
    0x114041d0f24130201110a080a17070e040507020f06010f0305010c050c06070e0609130504021e010c0212070e01031b120807021207051201020c0607140d05 68
    0x1001148a40d03402511420004214103424580000c0310700102c20200d800d1804901920a0b074a40d000001c1011102144400e0005980c0b400c0180129a810f03c1049408000c1180380c0024002505c140e440e4003220700c404c61801d00b5500c604852510005003c2c0e9503d14a43c9000c0d0000c54001001c1d0040c0c072404580f00c01c0c840d091190981000c0401500b603602001005000d101c0d15108024625006040142c406c907290340b40c64001c0c00300420050441d281c25110f603150b000315140e03481c009000e5440099003c1a1001401046a01b40d105190340801488140c1c001400148101c105070341b0800800d0582d42000518169400352504501c06d907800031403040d00b0001c03858080e60180305404d04064004902c2d6040030010703009400941084110080000c0784481a1713400da030303812105c07821580c5a10350240d19000d2994003080c0c2c04289801601d50000042d4004c0c054203c0030415104180e8601c1400e45030310040c10300745040c0d00030803c03140a46020690001c0d8120035850502c0d90150018218 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 242491043 1250 242489793 242489831
    0x9102319080102040e1f12081b010e010f0203090307060207060f09080c060919060504060b0a0f0303080c181302040305010c03020307020f0c130f1d0106031712011404 73
    0x72031112a9400202801044d1110712610750011000114092417440345042038000003a500c174600982d080540c00d441006005020350b800d410b800c1203190000d9540c42580342c042e000c01c680d079a000794070b8080c202007142ca031130080700c0c40707074006900841c601040e030350b1203a00a5200c924141d50b41d5079184201d040e0b80d00207000380c02b40300b40120086511400e8400025040c90000b401c00149035000c9003613140c2c900e100d0380c070940c40e050b0000f00000e00c95540c0c1c00d0403c06814060b000c81d81c04912103802150700c4140c03401c0d42013078901030358500860341e443e00d95040c0c10b8420b42295243d020f403030140d401d51628201b901c25041d001c1c2098003500705613a07a520303a403c2d9541c1451300741c0820303004020812a241d04010705c001204400005062000c0910089080b81169807061201c2c0354569120900145458008044460301c224945858810341d140c100d00810440c04111404060903042030000d981c00d42c10f449011980c941e041d515646483d00c0404885500340c1c60710340107903c40c40c9801e01d911158170 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 242492293 1250 242491043 242491049
    0x20307060c091a03100608191419021315090305010504060515010302090904020f15040b03090f0f1f1805060106030506012604020f0d080909102319 65
    0x100d981032a802c210340743c4618030402c400080480307024800c2080810103440407204440c0203081041580c0c580c07192030900a1624051207621604001c501420884140140761140c2c0b1400e88203001103c40c0140030090b845080d0f8441601450640d01744440091100041b0700380002c2d081c00402e0f01c0d82c903601c580c00e450b801c0794140c80c0340e035070340080001c140e0340070440410405003441c4c01c5280a01c0e03507001501e980300140c4003174090004440000c0706916800e03041150010044a001c2d181c0d9681c4200da2602c0d17004803550200c41c00307980481c04c0d07403180010b1151492014200900010101c46039001002c4001c2081e03045095164070032032001c6d4410140e40210300d8000c44c00303004a58100070703010b420388401501041c10440540000704100c3c501c2601480104040303040d107002c0c0c2e151400080d045da4040c0114550080b25108070404200c040300040402c05c0054a0300d901d281d45501410780c00a100c0d1040b034800780a03404010107442000022401c18101c020700c103601c40c0705038424445550350590 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 242493543 1250 242492293 242492297
    0x17070314090a061104030b04030c05010216050307050c0d0807080703021006080c03070608011805130209240a0605071e15020408060a02041a0307020f030d060314060103030503070e01020307060c 85
    0x107140b1024410b8034001d0000f020500c141e860b00d010320755a42c02c032100350000d0010b030801c01101c510f6801c110b421740403201c5940220010ba015030301e0600f4201c0e101e901900742207407035115002590540b410f03ca0102021140c03c00c100c0341c00c06005031070710702c5581d0010038110118000e07200c0740402d00500e4030804000d0b0645000402d40542c066041c90700e000d10319080007042c00707a1080100101019081800903609a6110104444d01d80d0306460400005002d4000c4d44814440c007048450780c00240d40c2c0300345d1380c10209107a1443c20300500740491128580103000004101300408000701c0c120030300b076507000003521149590702882e43e103800d002940383d10104c1d0381c0240c00150400c440803042000c0f54100c0c0071400c08501d0240f5081e40103910600b1210300306240ca4011001440c42030083c081c0381052078031202581d0b52919019510401010140412291030b1a0140d11806c0003c00080c81d030305a0b603260701c95510350344680d081940d410001030542411480104a0000011214098014508565 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 242494793 1250 242493543 242493553
    0xf03020c150105242506050a0203040b0705090f100e190614090303090d020d0c0b07020405010806070f03150305070311030c100503040b0c0f16211707031409 69
    0x420100b1094040410b060052510000c00c0040e2003000134007141e000d4404001c640481c10b030007410400180c1511407015024510705000c20000d0fa0454000b148074a10400340e50b4640da0314481c00755400d00401d1000c5403c48602d604403403060410701c40301045c40b809400c00070620b07203402001540c510a210314541c2c0d014a28603040201c01d807c00344804101101417070396400c252400010031355070b002d000b5038a031007281d401060b0005d64803081c019600c0c407600104a060800e407109a59005980080340c124001c6203460000191688003181c1c0c1402954140d482009103144040210041d10a56041003581110300b04000000390041260000541c8980380204c07951185030b08040c200454140114024010449041500d56016085941c010b5021000200c0c2d5100d011401513540a00410140c0c24540041e411a5a551041081008a1140040c40c40c0c81c50b0000010a0744128450b003180468201c00060388541e0703140e0b81c81c40c0e01a080707160016210341560050074203c5004d03180d062294000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 242496043 1250 242494793 242494799
    0xd021518100c0909110f070c0509040f020316030201082a070c08011107030801031407031a0a060501030b0330040e090c0406030308130516080c01030b0f0904030f03020c1501 76
    0x1103e402d000f010304800410840011032141c0718248645c03888008600d20000740c810030040b8090000c400781c030029080d0881845d041c6040d00403e890760005038800c0c490000040492640b00c403a034815290b060f50b4454564460000799809411000c40c02c024441109800305103000c0d02d02d0150120318000c2d00787c112000d142412135030850311031410344030f0b080704200500c00200350021041c0f411680e01041d440301010440300694101103940c0c0000304541d9500d040700c04904070403007549010b84940441003107020b99900043d0102c0f168442040d802da040b80c40410280013403012000d0310256902a1a500415041e6010005920076001444881104014860554001c004ca90303048001078034204859411606c0140c61107000510040140b80703c140040300300101408540300c402d026402800c0c10035140c504041d2a540500c00c1a80000d1400000c103031145020081a461440090412441e6846603142107440c110307100840b00a1640030480e000c48800f08001070742c0d00921000c05500d444d41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 242497293 1250 242496043 242496047
    0x30e061c06080708031b0106080303070504080c011e0f03020906030108060915071e020c120309040b010212040902210403020a0605090a0302070608131407090e0d021518100c 76
    0x41e640045030305601c4602d06110000001003111420b40c2151410700381650150002405060b1070303007102555004c0401030008444d0020041c1c825180000705592541c1d100f0001114401c080e1001407201210005105080c140540d8044a90006ca46009441c002609003c28019802031748010750f11f41c070100421800c04000d20003007041030a0205400f101d403c01200c0145025402d06a0111f2090219000207550b03000b00003c60361582d000e41200d500d400301007041c980b2508103540e0a4062400c120000316158400310f1446079411091100d1b9040c40c1c01c2c001000000d40081c4072078101c4859101f03209a01c0384808010760b10691082d402030880349402d00d060010b035100078090ad142603110460000009402054020903507841c2d1400100b15600c002c00050f490b4004100076000309604446c2c481020b1001c15004196000c01c8018845501b0b490a195640d1900c0080c1c42c0040c0c00034080300c1c4400c01010080c0390400303480c840250361101a001114180400c09280c481266500d402d00c50f0019 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 242498543 1250 242497293 242497301
    0x3070c0609060503040615050306100e0606040b040b0c0717030a1701030f030809011107030c0c050904080f030a0b04022a010b0d0b0405010e0d090e0a0c0903020d030e061c 75
    0x118035807a01091251600b1405007081c000500014284c584860031280035a0380c2821a400070b10f40141181c185080514001009105a010b800c5800c038800c00010301d20309000b8221002c45200c94825481c0a2074442490119040121030011030300820800060107400c1c1d42d1340d01d907a600840f020315502c00c070089015054a101e40340904000c50443c0040020555807400c0d03e09a0703400d410a8583c40d580d07088641d004001c42c60448000300b4000c01d9010905600c01505e0000364030407182c841c0655115820400e00400c01c441c0200441410440d000c1d90412082c0a5500b06840010100304101a41c1c0002d0603a00f01034078204801c03034042e02200c48200c40b549211180c00d0084000c01421901b81c010402101174410050100c1c00d141c1d01180c03c00c0401d600100d4054031300c1e02a1843c401704060020516a02d80c4180440c01c000360020410031001440b6a4086540329242c0e40301d020310715401c0c080c2c0124010002c1d401e12000613001440ba440f804000c2418203000110303103112103803c0104008403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 242499793 1250 242498543 242498549
    0x8060601030908040905190213030203060f06030a1416180c09050f04110904050106170c040609060c02010c05011a13060b03130213020a180603231b030903070c 70
    0x541040085804180104101d505482c160031740400c0955507100b5000025104100345a0051320004104945480055040c801d480c0f00b00c003512100e44480380d0f1005181c40980e4103d0f07141e00301c1180040040c500f5182d1030100d4260100351510200124011030141200751302c82c001009004161111507440d610407111140100e042500e20789003003d0220742e15030003071841c580c0181c4e500d22041c04100b0106040d0b59031050000e000340720b02c0d0b07140e00004209400610031b001e02c585140c0c022038a00c80d03c141c29641554400c1d56072005440ca40380c02120680076045c4142e040c48075912000011a5081c0035039070226005000c5050301403090300c10b0040c800740790b48419000c03501d0300a0501c00302c4600021660040c0c5c0341039030075200c9125400010040c8403184200088035100207407400141b82c0100f4084c16446801421551403a91180207805032801c10301150f4075004034148440301d4140110000d60000360700405100c0c20711901e4120821a40181c0c0c0103c00d5a0000c2445000c000205c91940c1c05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 242501043 1250 242499793 242499797
    0x2010306080d1d010c06060902070314040b070b06010302091e2d10110d0207030204051608070c0305040f0e101d0a09050a0b0708041112030a05070507030f080408060601 74
    0x842c4024481d482a00c2e480c6034403261403c088919030701c5842060303070103a000030f4100a803d1360307080542d000f5840180b08070003140d1012918082c1c040d848041c0c41c126030102940c2450045540d039680c0c011500280094103040c2d003402407010a8030f1b41c03590f95030300245c0440d94424400e40e4000b00160501c803503811b4160402003a04411240120070032000b09050192064810019505001e80c0c10b0030501c0c0240700144101d032404400c0c2580009e241c821240251004c1001e070300d82c6008100400d100e407003108041030001d4080746959201c1c00c08403a40900900d00369090036140d2611125000c0e841c0e220440440084090210480b8020100d5000b020403c030240803070424044000b200c504d0061070000e01e40d40e1200b001c818450b089c070807070100c3c1340d001805100a01c0d00a0010b40141c0003030301c0981d4094024804185c903814455100b03905540558001c5007000b1140c0d00444a5070b000c88000c8a541c0910400040051804d5210b80d801601c0b68030a00d0301c3c0c0d8182101c2514140000f400981 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 242502293 1250 242501043 242501053
    0x706020f0714010f1b03091104090b0f09010209090402011b0204050901020a12050103051e15012301110606130b06030403020102030f070305010311040e03270a08070b12060102070b0a0c0201030608 86
    0x88203940241781c0c03602d60703112818003281d15030715030800e83c0280e400594010340150400100d00704002072804c405100d820341d01030401054499440c42e608034014454030a4200541d14007141c0550700400d02844142e03411a1009811042c550104060b2202603071081000c1e90041002298207030000e1000d074480714200c0c0e040240d589107460791580c46842c2c01190745840c10108030380030344c05d00601070300045c104462100b00701795a44140800c0b11004c5d03010010030301242c8451400b020342c031030f0780a403104a031000c5c0100310a0b111841040f070803810181e10191003654030419010765440e4580610320650090300016213070f181444400b85030400003448001050724040050000604865143ca072490040c1e800081c2d406140c50014910710030314002d08000f48146803180040ca1782c070a4a141c26140554000345060380d29802c0a6440b1034500a6040e00f881c180003804c1440c2054900079031111051048031403d96854900034416400b0010038000120201039400543d600750040c6001040d1000041c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 242503543 1250 242502293 242502311
    0x60f0c08091f11101a0f0607062c010903020601140402130306020702090105090915070c060509060603010f0c05070210180603060f060f0804110a0b04081609020c030f0706020f0714010f 81
    0x50b803107a81d0b17200218420f41c5c1c000c084803070b20788890701555041369200c0000c210015402c08061524103100000100040c09440d80032031801040c01040d5074240d1580040102da404c05920a41c4203e0303071202e954011b44d00f4041216840c1d8202c2c201c0380218000ca4006130781d0002401400300b10941600020b00403601c001c2889014000054210043c09054080d400c05444544046540040e80c50003d011340b41014180403490301c0120755580035143c21070081007031210600980066588074101c5202040b41403284030050305012400081c54081480d040c400034403690051200c440040d00f0040000b90f9983d03042c444511540555400341c54a820f2500e0022142c0400400e500707401400203010080e201040c101c41d840d20740c0303520003400054114075142d07515503814503076804425803584444034002c84005007000680c42110030103210fa1015610341024000c12048550040104903001c642c200070b040c001310b0364000500f88103442a9202d02c4045103e07641d503800c1d258078803481d4030310610300a000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 242504793 1250 242503543 242503571
    0x15050a09060e042d1d070611010207060203010e0103030e0103090c0b09130501060c03030b0d0c050607050f030304230c0906240a08040507060f0c08091f1110 69
    0x4001112810301c0c12400056950000c24090008051140d141070001c4c03641e09400402c2a050700e100040c840400c000640d0041d45007440044260501412600142010300026200328540c0d0450300114002500e000030039942e400403a070003613100c1154a40d010005108140d4040c54504802c06d003480c0c2404a0603030b82d1a0200d821070b29221709080d600340080c81da406620b41121480400c042c42608205a603501c80011f448511a95011400a4900b181d203564628103510440720071900420701060781c1d4205000d10078180d00c510019a9903100b0360386224450300d4100b0040d0300c0f862003204003059014005c1d100f40c0c01c80175000800708998018043c03410043e11000601903001004807034211215080540280d280035842c90100c0d00780200081c200d02164002c0003103400303684070b03008954070150f5a140880c2c1041c0110107650000310090088008034299102404900c2c9004103410550061810400502c00d612030b403400c0418909000d0031101741c028844030091100c205002d00c001300c4400780d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 242506043 1250 242504793 242504807
    0x801060e0d030309020a0801050105120a08090402130905070504051002030901020a1e050106030f0c0503060405030d0f2301170a02030a1e17030f13022d0d03050415050a 74
    0x940d07000340700500c8848245486904041c2445801a0030982880e0f10f4a5041e40030f484c0900515000e8541811502440740d80061b403401510f401c0b006003810903107104200000381d40000090340940c5020140130400010b68403900d40a025a5241d05039101c0c1f81c0b0060201c080503a48d070355003c0d90000d00040c0d26598000c41c40c48020341d4000700600340a07084c1100d440c816012207902030120b618055010082054841582c00683d0261350b04443c0305a5076070030150789100c2118020100d8205004100501c40f450308806032526981e0400b08035075107814000001e00f106210410300c403282c210010002d04040d560068880320b0500c2c050100c406864010036500d90362603c000b000c00103001002c0180d09400140c024003d640b004100d44132000b29552400c1c0f503002a207910b02c1c00b50070390b800b042d015040c20740740c5000168003900b07a000d0072980c9100d207200000a40c283d400361400490342d89040b030f5618100c4c1c1790060b120303445454945043c202c0110304203107000310b1141404800c20000c100746800900c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 242507293 1250 242506043 242506067
    0x31e021801080705041508090c060c1b0a0306090812060a06091a04090e0a0b0106080f01120303140901060305070b0304030206010b03090a080f030703050703060e180f070e04050d080106 81
    0x908018544880e40d0445071072003258005106d10080c4107401210703c0c1d010200703501803034120f4100c03414503101004103c1d0380d01c0f40c105901d540d9032040d583c1c204003200201000e5082c100040c80325410335501d840c0e6409444212500300c1ea03212000448000c0e444c030b0342d901c0b25040f5400740e840d02e0090b07090100c003800c058190f018410311852a20b8424181000240031200030f08070300c0006004140407807102641d185490b9804484806d41e8500100c1d0b018480e0110300c1c0306100b50030350150740744d182c54450300707403404450b2056040507240d840c1403511300185581c041c083c0404000014040785503041c0b241c20005c4c01d41106001703400402c14403010a03030000c0c078581915405130318140e8a480f00700c00c0c9840c2480d210801010b540d404242003140b00f280d10301640c0700c3e40c1c81d03882c28001d59407807002c11402c5230301038043d6a4107061000c0100f000b6000141600300c0c00e4004804413120000f501c0146841c080d00341d4403052100d4105010041008030038010321003495040d041004155040100241c01900940 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242508543 1250 242507293 242507297
    0x60b0a3609020d020d06032102151914010e180309030c040c180b0a030606020d0f26040506010f1509030201030903051b07230901090b010306030203030406031e021801 73
    0x400c900925000f00c2c1d04580c0d80701c1c1d4040040056603568a0640b03624102e882040f081c2c501c0049240c64400d00101d00010040c08641ca06201903442c850300b044c800803c1e8100300c25550b95071510000d03021340b050306d541c080c0c88030070b0b03c030601032900c0313046a51300f0100f07800c0800641e082401044a592000a01d940d00c00c0003c45001c11b6003801301d0400c81c3e20680c407801c1100100000b001c002a48880c2e00001c212400a55905000b15611500700381c1ea02c8100c60380d00c1d400142159012800244910f255650042520150310429000460001002d11050b0760580b407030b4001c400108258207071050f0200080840c59123030703503414516403000b400048652001074103042d101d0010a04242c0300c1c81c100c0701c40421380698980c4000c000042c3c40e40d60010390241004e07802c0c031090404428028925819410034008003d800c0507820480c844010303000c040d910505042d1503c0c0080016681800030708041c051b1540c0c0080c00160001e405414410080c100311900c1d0300c10400b0510103800c440a503e407001080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 242509793 1250 242508543 242508547
    0xe031009030507022106010303030207020306010512031e09041a040b04110f0a021207050f0601080712080c030705030c060412030b0d0609050a0c060f021e190303060b0a360902 77
    0x8041c0308034031303000000030005e0a4024040044109a055030240030514025400ca44050380c80303005001c0c0c4c58203001d1001001e680144299400c0c40095195482c0175a0b5070302e511414a003190004c501038130340ca0038200c0485080000440341c01e0800740301e10341403902c0071541408200d1024050002d284200d042072a403500000614003002d9000b08200c828014104018a585002a0900c01d8032550254000c103a00d01442000061031980051f0360001d407014901e240186403107503552104c841c2c2c00380074192080c1c003007801003e01040d000e1000d4000032100320042d04940c41c0c5458070301810400c3c284103400781071400795645110703158003401a414541c00032002400c0341c080d0525034a48083c0810047c13120f030403440c2c00301d041c40c0c1c4049000c4054000390200d900110700441c0b0240e92044034035032032196900c43c2841d480f41c00c14458402003040c0c02810006000381d03da1320b0165003940090314107004580b03100ca1501e4000c0107038491900d40c2d10313680c400a01000c412800c0c0c1140300c4441c4113070303030800b500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 242511043 1250 242509793 242509819
    0x103030507052505031027030219050d0f08130308041a010f06091a0a08070512160806030109051527061608041703250e03100903050702 60
    0x2c03c90100c00e502e011007081c220380041203407000003241d1401014000d0050303901c001403e620501a26041e026080d640300c1d4044200a095042a4003181042e811882290070302d140341c25440500300f1050f80140e020384a050703171841000e030840e5001030b400c508100741c1600300015120783c0240e083c141541443c025120361190704281610105084180d422460f600d8000210001c450124200302c642540724a4456903440c29169103030b074008240344960b8882002401c190380c0c852455a640710020342489070428030380242404100b0b40407034240004100380304048540680020b030896100000700c0003888010b07020741d55903495920206040005543d40c5002c40c88a180b40303510707000d120086907140c105203041045401d50f100c0b41a1501641030b40c400c0b01801d034551140201e60300ca1a00003400b500704440d850360011881d40000e00300810300202a04501c4900081070040b1fa1b2412981e5461140e2501344c0c08050412841108441c2002d1400320030400003600a802c3e2038607660125086511402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 242512293 1250 242511043 242511053
    0x3050d0c06060513140601050f07020607020307120609050c121005091c020703020a12050604151103150a050102011e1104120c090501080606011d120d0f030e060f0103030507 76
    0x46543c00c4154005851502c6041480f99948000b002010002d03060543d512140c2c0151054071914401851981c41040900c000d81028002402c000b80b01900702c41d510b6541d03502ca09803180008000311401a2141c0d001030034408100090010340100326512504001051107040c0d0713504a41c07003010841030f00c620014403015002d00c003130848120307018a007440c40aa038110083d11500c203400100e01c20f043c010b202280c41c040700d00920700055406001411780d600d40d81c0310100c030003681c2c1800b505100e45407240c00318140c400324050750080c01c007041c84100c15944101001101038a5401c00c40c1103a241c031031100e0000c00d1050038840721105000b4002110880d081c61440e540c400c9400215813100b40300410810081844d010303000303c501c0c0d02010012647c980c0c50030340d00c6a0f0191503032400140e026250343c1b41c14200441c0e200c1c5c129001000b0b00b14496883d1030045c1400012840170010800d16941881c03855018040c1e0340c0e000e00a403026102e03614181103100c0071018103010103020408003040c6281084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 242513543 1250 242512293 242512301
    0x40506032b091401021203090a150b211b0105070506070206160306152f10141b21010b032e23041b02010b090103050d0c06 54
    0x9201e403030010070011012401000500c0240d44100e0000303418600c0080c0c0820031240325622040141e01406c1c1081e6148450940c91708041c3c69a1100e0080894040000e481021142c2141c002d000020442206402c204402408210340640401e100f40307005504202e80811115200419400c80d0111402d080004880c14018820f005119101c0e0304240019a07400143d03280c450724a4a425850481c2c6005040302a240c9601c034910108048148501c0301e28020003a00d02c40e05104400c00740c400c003806043e038542c001c0c2c40d07030440d8294120020241c05803844ac0100c01b41120000080d0b46e29082004020421a41610001501c150040348120b0010211a030740c448000c03000b0001d84265840b80a1054194010b0311004d0701d11508540b001541c090106c0307241e20314402c8404206046151003010120200310460440c0d049a40c0b032000c1d0b0450380e90f40711749055100f86084040c140142080c003e4216600103248070321503000500100002036000a041c18810024900306820541070714007040030f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 242514793 1250 242513543 242513563
    0x90a0f020c060c0729040602090d0f0f030909150504050408070b04111f02062e060203071103031c020a020106090c0203030709060e031002090a030b040f1a0c030604050603 75
    0x2d0203000240018001080080d0480f180181c2d8a4030031120107041d604c016108500902010a0310000002c0103c0d0072a0b005e800940e4000d403c0b03001c904070075544d0381c8030503190500c00c980108621034000141a0300441000241403514810020440d101d0801c0c048002d19116180c8529100c90000d070401407194103a5860030350180398414107081514114180040034030581d030084200413100d404200c0900c002900c41d5140780c014010b0398889800100344111500d05880d8110920171a441800260b041000014250360707003c0d544a0303035076140c641c001c0301030034440300d03c254020311000700a024050703510301145611000040e621003240d82e00340c0c0500040d500c421348503890301065815050b008802140b0070100c60f90740c101c0a136290382041d9099130030800d45541680c09a182d0a0080d50640c1c010082804000c100449907a03595030390948003c400c4408076480d1250340c0340d400401140d003118480601c0f1b50005040d061401017141c030014080240b03079a00c216212404500c4c10f440500003c821 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 242516043 1250 242514793 242514817
    0xf040b0f060415030f1401030210020a020603100504060b090609090711010203151315360c02100c080408030c0c0d031a0901030203100c090b04140915090a0f02 70
    0x22569a180402d000c40340f0709420001290070041859034a0760b0078440e105010318a05c10a90f10750f402d58013030015410888105406602c00c3c0c60b5640056a5040081c48c810f88150301c4030f0b01043d0514081c041564201c0e0b200030000c81040c0f040e61456503508055036040001507030241881d690304403040345c1c1d43c41c10b80c021201039480007007400100d0300c5c0c41032403c0c0d00703075415a110050904c0e0207030088112000a294100c0a5141100c18407603a901109130b40d005a0440450b101c9804400c20010394080240c1014001c1540c0d480b010341a031601800000c941e0000d070310040003040b03a4060040c12403007008000030130300da130300200180000340440182e4007000041c004403103280c11a841c024000f01020440441c2c1e01c1d2142803003094070b1a041d10380c1416a98040d01034405440c000c0030310000342c5030702d8603004103000ca80076000c1860910440a40002c210540b0040140840d040c1408017000000e40301d804030700d02d2079050310141d40f00c212005420202e2090001150030420300544000c0c05485e0420417 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 242517293 1250 242516043 242516047
    0x1406040e10120b0109060b030907060f03020714010b1f020d0804020a121209050303040303020a1101050c06070c12030e032704020406110d02061e1506072009060f040b0f06 75
    0x81c08101020b0a05036592071741c0401940e5210382c0b07081103134081100d452815a000a0080c8180e41c844c843e024030ba1030040c00d01508294032a5903c01c1c00d803c00d03020030403480e03658000a024516025042560065000310b416403082c502d40d5000391142400081d6034140301c0d00401081c00c54807000f00d0007000741410491130300504168a481051141000074a40009002c01c0022a8524000c8100d90480f90b1507002032515040650314914152034507a10036040c04000e00040800d45030504c0603900c00c01056680d406c445940d8602143e0041907442c100d020117107000715410417001c0001c122040040c5032503250071044400070081a10010090b10142c20500200c0c00280150700403d407181204925000d0b6180042c9101003265140c42c1100d8051060741484007540300011400011030b046454100c0001540102102080284d80036900c12240314031000d900d4040300500940d41007000c41d003190300314450b081110000e8050544801b64a100710340d1f4890254040d0384003201200c40e140003a2081e6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 242518543 1250 242517293 242517329
    0xe030331030b060a0b040f030204050a0906110c1207030e0f030a14030c0f01051005120709230603010603030f05180a090e061f0306050a020c01050a020a091406040e10 73
    0x220301d507281a43c0c2103000c0c0008650100300c546401c070a4400b59841f1081c4615101c3c5540c00704000307040044e208001880d0340c0c090380008101d1a0040c2e14070301c040702c0381080d9140091101240340004c040402854400107001e1038002983c0030224014403001245c1542e054601000040d0405480540060440d1082c0040e010036042c007001520301100400143c510010706003407641c0c03da5400721008030007494900070503c81c0d454444841c0f144504640308560340c0c2605c8102c80e000700c070b03148265204d044420001c1c82004200050301070388e021a00780e0080c81107030718640d1302a200c0c400480800c2c0500030040b8441c60510703880c20700400121001854010030f503684402503c010411b8426031111402801d000035484040c400130a20580081c441c05502c4502c2c0d038407810020080900300411032602004080703001c0b00d090103202c1c000c031034101c401a50394941c450f01030840b1049a1010320300c441d0404007150584d5441c400e803003c8415a0640c0101c90b170712814031007400040ba800240da250a907080325 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 242519793 1250 242518543 242518553
    0x190204081f1e051e0c0a0f0908010507200a0b15061e040f1e030609020f061b07080705090a050403091e09110c03070201030f06050a17060105010e03033103 68
    0x141e80140f18101d1284c28003556001d140610f80740031101440074580810114154901c00d0803150120006407500c0e400381600c1d400c8450944000b9228000051401003040d0441c00b09225200a080142d20061601c100b0680c0d4050751031100418903000810215120f12050301c1e15011243c4041001002c1c042540c20f045540354650814020b100d80f11050500126094803050384003020140b01120000c0400c0c6980c0e1060302901090074204e0700701c01105a00d001c9038032000c0c0a0b015400ca00f101024500303442d00221494441558004031003540100070801c0284c80d22180c0a400c0300d032804010070155160304054601c48411b07403001d285020200d5040040280103480f000c140d031518171042c822142c18881100c094013903100c501d6040c0e0410030442d0010341c0603900506102000020100b0a2540c0d08002002000e1035070104032001c4512400d820f0ac2a000d0046134094682424062008840c2c60042940c900800d0301c80c0c841c04044110044000540c5001419988505a8001e1582e078072880c0c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 242521043 1250 242519793 242519801
    0x3110c0114060405040515040218010e0a0f06060f050d15030b1602010510182703020609030304080306210d03092001140f090d030206190204081f1e 65
    0x101201c600314180402d00c5890540581800b03107401c40010107000d51881003041c3c209001400403640110081540351408101c42642c0d40281b031007294400c3c4514001a40109460341c18101d01d428900d050700c00e2201a800104002138080103140c4981c40b290f0200c0268010074110f00605125052008000200041c0950300c41c80f0313a8a030101d26042090801d000d03400d030b560544403580042c8000c502800030680007503505010f0502a10040390411111104201c131103106148154002c5050120100745501000390640000085000303520b10701c1c107900d50212a004c0940028800c0045418100c0c0545481d5124549a41101c00381c2d00c0c140d881c008050001d00135054101d4112171b816a00105400422800015805040e15900d402452640c1019880c1e40107a807000350f00007003441910b14640b59103c4040290303210f5001410300d82040c41e4000000040c00c4501d20340540100401d0000701000301d495000800c0c5010744d180018468160030b005005096070010204602c2507040c1243c2141e504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 242522293 1250 242521043 242521061
    0x1110a1202040302060723010c021002070302010213082104050a05010e0102100f0501030209010e06130203060d05101409030c07030611270f100905190302060706021e09030d0305060103110c01 84
    0x780080c980006461f10500340d503040a030610242c0c00c03406201610000b80c1e0010702d5040c0c07003880018074003602d07020840500c88c0c0c00c1c0c00a98036039110b45841040d5290001d883d080a400c80341c03c1900302450310001035004c0c80c05d4054541017042c080c2c1d1400c1a130740200202d00d00c4044480e400d11420b1003500605005001c2440181d02c0740102a0000480300323022040e003400380e84080c011003d0146c03e09a028081d51001c3c00c0e064010031462181c4000c0340c800d215944071103a940c1c0c004540d800170303d0030f40700e000071000e02180f0a40d0810011002881d1001400d102203982c440008034160007140e100c008503005e51998590b40d010070340036401d0101448002c42d0070005c0e00b00c2c0c849041c03070048414000300400c0111810702088400b0310500052500b42c10762100c4903030002e85c1d040f016032a540031590b26040284105c40c443e40204407880c044401c0707110b28444511708a489400e1031038802c0082d40e41c004142001090503611804104680d120743c001030303010307860040c0403661012900300003800ac01c3c080e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 242523543 1250 242522293 242522333
    0xc05190201030f020a0c0204271a01050f0d141011190201060f0e130f12020c0303090619030b04062306090a0e13020a2601110a12020403020607 63
    0xa100034000c0c0362510030b644071a4243d1b07903401d040c170b1130302ea080c0301c0241010f60317089802940040d0078503410404512000740e07191062800b000919204000150404010307003000303104021201700000f0b40e44458810320000b41d04400355250f0061f042c0c00031401e220240c1d060005090801e4a6035903584061802030100340504510f4084030384044031300700e080360114090118502d0590200b00541031507a00744076042000500f96030001c010a655401c410b03884045c0456503400d01340c00c0415003d80600a40001c1754050700a0352a00c410100011038502c100707072050781c40f9810700107003515651196202101d1040090400c01c2119101e500003103004003205032021640c20080748100710390402e503013915214880501440c01e05800c1c44564441c0c2e15006180d40402000215204d000da607071414100700401c1650030f0805030102c001d180007c50000b010b00e807846a81419100750031142e08000301d403101d1159140030880101071483e81000303449140e101950142001c0346e440d0500c0a041c0c52141854030f44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 242524793 1250 242523543 242523551
    0x3030807090e01050f04060807030c030209071d10030902030a0b090c060906120c0d05010306050a060b03071d0f150a02010b01261302030102070303092f100c0519020103 74
    0xc42801c07144200c00d030281d0305192101d9401003200d81030185c411260440020300100d505500c0300091442d00b040c84d8000e40e40c40300740410400a41c1090b10410b80c110b5581d20b004002c40d0100d000010351400ba90840038041c0c1060b80120584611030343c4042c00041c4d00400f51040d4a400307082004100005442c0d980050107410940d020624200c001c8504c403030000341c603450410801c41c000d11070789480105000b520410801800c0442d0700144241c1d4041d621941c0d00107954240105418200d54564000c886840c2c001c0041c05205500603030801400707000c0d0100400000100700200c3d010040080101ea08822921401c40840c18260f01a000080d1668001c11050303500c1c100451385402c820f0079204003090a200c00b421142d451591180d80b21070f20341d00c2080c84012584c046822640561340950009a0301c01c5144100801540c0003808845d42c459450f880001c0440d03040082041a292644a5100890348652850143c00d0740305010307404c0000d50340d2903035032810000c103940e07606c0d00101c1c0000c0c54 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 242526043 1250 242524793 242524801
    0x4060b1e0306070c0b2e0303050a08070801050f0f150c0c040506010801030201120b041e020904060b040b0a110a082107050414040b030a0c0906031a070507021512070801030308 77
    0x104100a03481c068001480122507182c025410842c100600c000846a01c41001b04948901141e00c10000071846039444035034a2138280c01c01072103184040d181c00200400d06004018070b5443d002c10090213181158032026030949100050142c50b01403400b0001180e010610004086021880d0b048009040c6c9080c01282c0d10900111415142400000c0c0403480710003040c42c3c02582d580c400300318900040e000042c1c507014070340c130495200380e00d01080c40e20b641c0000d0010010f0030540524030007049940c181d181420705110207020b00b4012003000c0d108015441c82c454003494400c01600200310f80003841250390342d401c507500b0403080c56181400e900502402000c175003d54855000c480450340100c01c01036031101032004104c06007002c0e03841e0f650b15100d603400c0400880c000290304002810000d10014080d0310710b141803035a80318408a003080100c20b120030450a03541082c210b480c0346d23904641071a000f074421076108110380600c4003009003030003820341000042e40e00414030724140c0e40247c9402130141d071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 242527293 1250 242526043 242526047
    0x1b050c100e0d08041406010e010305010e010c050d1113030c060908030322020f031213060e0a090c12050c030105210705060c100e010902150c06010e04060b1e030607 72
    0x1412240522030b60300924410101620500d421a0001c4c4145500b2a40840440c0014078010081e08802e58043c1404010030800c58240300c1d21000350300300c0000f40051001c200000d0003900414601c0d9241d42d48418108134204003440c2151048621024a80e8040341c4038240184000900c1c052040490107010b00400d03040800810360344030701c15407104585881480202030420b01c03070502049800c602986070203106980d05010039078680e0544840d442d20340c400c2030104507201601c2c0d48150248001c1050299498030f0f1601408140d070b13000c00000c02c018501d40012500b2504040e610b04400b443d1005128800c03480000850407104201c80020642c0c1c072401c07501c00d407003400d034181c00015030005008009604194020301490795105095a1880c0c8801c41f0443c103640f1180305448290750b50740000380c114038002039007590040d03144129030300f00420307444043d55400d41801510410404c060004040000c250010181e1100c09080946822040340819100078075842c1250f02c24000c4c1c82c00108401c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 242528543 1250 242527293 242527301
    0x90c130615023004050603040b0a0b060a0206010b03060105040f060206070f090b0306090601120e010525020601060810030f061422080904061d0403030501060801060c0210031b050c10 80
    0x8100070041a4208003d10740407000d48400b42c04602c22000309101c0000c0a0742c44002442c0300728014014000f89250482070001180d5620340d503c4e100303220034860020460344c0000c05c541918202c2c0e011683c0d03901e502d4010381303140c0180d50010820f500502c90124040c0d50111300d080c02050b0030b88501d038000500d240165425601c034000c0d1109080c0030300c0080c007907160180d4031907000340d0103040246d04400d100800005850b42c521b1000e516a454100b4404014108800b5464456803809052408061010025201c54044c842e07401000280000b04a0000c2c140160400941d800000081c1181c0d442c0381140c00350030603d40a2030704208100002d015108030401d81817401103016810401c0340c25135035808805401c4500019005541d03840049240101c1601e004603043e12040440780d00d180518004043c0c40050700810200100e0f4401040380980010070f020740d0a9049904140b044104002200188442e03030340c241009403810405410b107a04640200b01130044102504d00c010181c541501c252 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 242529793 1250 242528543 242528563
    0x61d010e010507031b0b090c0a0503010c0509010c110a0e061903050304090f060807030804170309030703020108060d150c02210304030503100b0a02010c080708040b040803090c13061502 81
    0x20540403c0407400092092083d0301d80580c03040c400c4030b2600d080791600703000c0d030701d044444d0006a4800350785038040f450120f64410080c45c040b4024082445459001042230144816407070500100190490030012103008508902102400d6640310070703680d09030816400001d840d480d0061400b05422002c1e4031560742e00b2030070380390410002c0d0324151074940d204004081060208000a0355800080340c100300030720942c0011401924400e450301e0410707100450340e1103060640e60640c1d0040003c0819a00c3c0850404100c03602401c1c005032503911b071404601500c070030850003421606624030702e45420155600842c656140b0754200d91040800124118441c1a8418200c002d10030a200160000b807080c0021035001c0801003c0c4020350755251480d032102d4005045690146c1d44a9003c4064240e021050590240c81d915010703540382000d85035141441c00250029103483e10000004201c0c4004004440d0521000f6148080e8040381d071042c080108aa405042c80440004146c2c091040c40001d400c404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 242531043 1250 242529793 242529797
    0xf020303090a08090f061605010612050616030b03010905070e1b090d11030f0c1807050316090f1701050709060203030a0c09030611090306060105030c0a0c020f0307061d010e01 77
    0x4280702c252606012a0400101e441d8481c500305030240711a101c084c00740c24400c1d00820b0594480f100e62500a09580312a046202c0d80005402420045440010b1952700000030304221600d1b80f010041c01c038051b104030120160150708084c0c40e40100000010210b044880b00440000c40351185e60111025840031409000d14210500540b035503480e062629038921b9100d1800345001180081c0402e0500f40c2d4040700b006d2580024001c0f030703983d0400005804c1e6024407000c416200d4034100c0d0014106010152a0b05079581800c0d6040442c41d01900c019400b908480341c80510603960340b02d002c84000342150f5101919400d03d00401c5081c0c2c01581100e06030b4103190082c45c01e640e11a040e04009008207040041006031368480040801d0081c801d40000c0440c00c1400d5540f01c00f940c0c1410701d400405080310341045410003c0110001415081e04c0030000189030464088a250002130528550112155414010b5074070000d1103a8001c07006081c151034405001e00031121030300054400b80304c03014500340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 242532293 1250 242531043 242531053
    0x3060c200d2d08060d050a0311190b1906030605010902070615050108160c060c05030402100801181d030c0c03190804120503130306020912010207020a05091b07120f02030309 76
    0x90034600450181d6031000c0060550a5500c5440d20b541f450b04000200c01da0104204081200c40301030203125030406182400c074150b0040071a9691003412501c003c0c2400380c80040407031070030070101d11900003100850b0025410301c9196181d4a41d04000e41c0300c0b00c401c5031540e207040d280324007101d4031200880403240161030381004c5940b890524080701c42d080c1828010010711810766030010380c0e14402e0b00752002c203594629899103003502c18843d19000074030701c02042c04140401080700940c42040c5030403012002c5404151200c00b842403680b520343c000700c018183d010120395084142000980c0c68918a4204e00300c48101c18a01024101c0d0240749101034403e0300e08000070310030901c1d860300d00c6112600c40c100701c07842d0240d5007800510343c4440e80c0040325095000201d10f0b803d40b80c0410001c2409400314001c42c5801d00741d5000421030800e40c440c003800398100b8800641e529040000309900c440001080c40d903035941c0751030702150700042c00480707101203040d62a00c01759080c40041540d00c1800b1201c0104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 242533543 1250 242532293 242532377
    0x80c0301051c06020a02012309071e0302030a201504060c080712080f07021b041104120b0402090c0c06060d1b180501050603060a03060c200d 62
    0x42c60b50711103007070382000c01c01250008002400e620040081102e65400052151526503198650480c41400900903601ca04180504444c02285840480301c200d41d841c0341d0000c22500503a000c6200d03910207907150180030901c40c18030036114429200760040c2240d00c50160401c10400061901243c0c0c046000d203c140802d0141e28010a089410903000b1041c250a21050356521000d00040e10903200000755610140018402000c80c1e050700240302e0b00240c044070040340c1804451021030b01a20b4806e42e1074038040d82140000c40708039005004045941a803a0013035080030f6141c00c8050b1000c0f405007074107500140c02c0d01408401e9400742c1c825140038002d103842c0c500812011030445041920000759801420304002c5800700f141004100388100107a984a000090004440c0141d00c102d01490b01003041060540c0c2e4040c000c1c1c00d40e41d00800008103010b4050044483c503812030760b00c4411501031b50040e800f103100050680704181c251394410941003041402d44c1c24042c1020001d02c0031510555001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 242534793 1250 242533543 242533549
    0x108010e010e031804060b04060c03020c1c02090a0e012c01020702060301091a030f1006050a03110d050c0a0b25020a0b090d0210080108060c210612010e0705010f080c030105 76
    0x130440401c004001041d403503102c0d0301085859200d50b02c044003242040c40d6110030190140900c1c4400c80c811038220514034181c1582140c10070450034003d02c10b034410030000d0240210703940900307011005600200000b100c0d0075408484a0f031140346508100c4d0f51000c07503152001c81402245d0003180d0280440f03045918121491000e0190303035280c01d000d00b8040b50180020f840400112055400e10780c01820011b40b0440e8000440741141c11031809901c5401082c0007280c2c040e40c0452151100703595034594503445041090030462110505070b40506000400100f01140c0d4010703080c0e9080740440d0b5858040d1003a501c180300d84402c00c0c02500159080020044100703520f01618051a018200f00710f070b01016400100041e20303114180d0041501c600060100030b10400495500150f040002881d282e0981248644590b10f0400b2030442074001000540701d40321a80d50f0a203100805c0000d00c0404060390295071600d0450090900148441100304005481141664003031220391114030f2450b4241428 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 242536043 1250 242534793 242534827
    0x80f0a260c0a08250509040f0203090a11030717030306090a050907050f0d0606030804090e07061215080f06070f031a0d1712010f0512100c11030408060108010e010e03 73
    0x5010030890368440c00e46044007060004a0076412680d129a0f1b00c203042801c000c221030048039085ca040d441401007000391680003510b22412500081d0190010000c500081d10340b280540105580080c1c80a18103007941d000030186005000490b41c00072540e0396416104102c1d2002c84451809501c107180c10042da0030304500e52404040050800e07403c8154603154103007600d40940c411500c080e80094100049a464800e03684c43c041c010014005240c50080e0042000c60308108090400303030703610501058910300341c013000c00400b80358050340c40094804141c0b540b02da00c00c039400c80204040781c500c0041c59110f0f104007400980344e10b03000416150240140030301c400c210381080350b581c0303c00b0414115107804031010740007602c00f401d244040742d070502c0b2103e01c695040e41e00041c02075500300d0120f5070314030012820b4000e100d441240041d2003c2a444202c84078061104505a9800001404078810308040f440318103a501c03510090102306411681a1300b251743c943c6160300035800070b100b18451610b058130317 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 242537293 1250 242536043 242536051
    0x31b0210080705041703070203120c03030406050a0f0518070f080307030804060216140f01140105190e0a0204092004030305030910060609031209030b070507080f0a260c0a08 76
    0x1e04941000d1700c03410784140e0071540c0e006001d203d50000c2114030031072404000e42c01d9046000d60006007000316200031203a60b03001c040c1c4024690358684000034800d107916031066034800c0621505101d035081c8401c0c030380d05620650040c16400c2c040e0349030115440c0c06d07602c00c10045079400e00c0250301e40303d03498034201d0355980060422918540c00304a0452807d142640701881580035010440c0d43c44041a1043d00d805540030700000107906128110030350041080b00c082c1122000e0f01c021202c0031400107500a0148560080c0c1c2c40046108180007621010354043d00582d208a4000c101c00c0b01c24204000c44800c3c1d0402c0140138010400040c00080d00c6003002e15000715020b801c0342c0d008040501c14070700b5a080c0d40c02c040d000519002042003440341e00031440c80e01c001c290901221407400c649501c4c00040d0018042c034180500059490f04200c020001c0700e440d0901e00c05181d445140b442001050b0f440804e03004107829185007044003102c800520745900641c40c103119a442c03c042d0443c00d80d10500014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 242538543 1250 242537293 242537297
    0xb150307050d1404080417010e06150f0a0b09030709060b0f070218010e040c141302130e27152202041a04050709030816080f0a02010603031b02100807 66
    0x30100c8580d4030303c03110300780542e114158882d2600d00300b00b0050407441041c42c0139030080c0e0600c1400880c5140102d02e05400c0490710a000d80e203600ca007004a0421004000035a4010298800c001410403e460150018602c21402e490320103075142e02d89010380d142405480302c10001084503d0304000c0e140000c6c007542e440a040d000d09684141016488050240d00819224182d0000c0004101d154040400902007a28500e00f0440e02d8001040140411101400109600083c1301e104c4071b5910398440700504061510540900c1c0001c0f44900015044200c40b03401c01400c01a10924140030658903003501c0b006040180340c2e6500004001c0c01c04134150100e5802031513002510160302d540c02112480204500c00303810140410040c0000c55800400400070040d8090742800042c40000407280038000c0c403e00300d010382d02c1e1414101c1862080070b940c1580c54000068400318181c064000704210b0780a61a4180c84101840500c03c03000030105009502c405890070042090340950354054109000b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242539793 1250 242538543 242538551
    0x50307090e120d02030f010f21140d050903011518020f040315020c061f060305060604150f1407080a030203130c08070e06030703030f140d050a020405040b150307050d 73
    0x4419031003403940008160143d094002040040408084070440d00425042c0e480b0f1100354500150303581d1883c0c07041d0380e0341c1102060f00341400500890b40440d44590342039100340d4a054400d4080600a030748250b4082e40a542840b255401d10030840540c41c00720b508065032103c00200f481c11150007540101c156011040c810301c40030002c00c0c0d0b510b83e03416244801c04401691070170140c461034070b01381d401490004e6030032a50b0800c8240310444107030300c0e0440d0281e050204440d00c071007000030f0442c081c64010810350300b280c1c40c2014203d0ba12003100010a10745032034504040c20b040540d880103100f41107000d0b00c508400c1148001041c840d9000b503078410f0907454a1201080255102185200c90354000c40303080d404110b05109102500100c2500250210010404240345a4014250500100a003030074445247c044242c819003800c11a500074040020400503031070003506080081d081800341038000c52400c11010054100004801d2240d00080e250301d08541d074044080710a03030301284807100c1e09070326 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242541043 1250 242539793 242539813
    0x31603060f06170a09022101090212010203040b070801030c05100e310516110703050304060f0e03031204020f060c03130303030b01020303011401180b03070903060e07050307090e 78
    0x400c0030705402500460707884461241d1500300e01c4240d214040d090640c010700d001017281c0180d480d40149201d030417400c59619100c011300d0b04c01a00400020801039085802c601e4400c90f0010103500540c802c0341305030000c0030503440c5e2600c12101d0281c01d0000074469400101d051010786022441c14004591901d0700d0071000c0d4060020500c20340c0201e880400c40302c8241c400c80c04039401d910700c3c010b500820220400a62802d40100c089006400855406100c001203801800034000c0c01800061a000f0086030f41c2e50f56503250081c1282020980c40340003c000d150040707094a404011079104002110b0044019100c540170000c0200f08402c101e603110208201c00c0e24003110038405000c541c0300403003da200a03031550602a05603516100c02c07d045400070001400b541c40342c2082003003041420f01c0c0000d0601c0c031450040d0000420780d0003c019102c0c1c0402000401c07035100070741c1800d0324071546040c8400c000d007180c4540d48451030f0180d154582c00c08e900510081e03071075030303c00c283e0080c00404039141542 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242542293 1250 242541043 242541059
    0x909081c0603020a12021507030507020330070b0403080901061503020306090a06051e0409211205010803120a02070c03052107020105070201030e28060e070b03160306 73
    0x1814900894080362608800c20644c80d091203a1030041c16a0120031341070744401c0d40085d0a9146001801c5584140400c00800380362084c0300fa17896440d806000ca4040e003100d0070f118803086200c3d9401d2145a101407010300b250003840c038151510180e0141c085202a00d82d6601a150710f50020300c012007640da2041c0000f030000034204680840e4015032001a41c904002e010302c510000001c2068083c40d0410344108141d464021204a120b0100600e0b503400c03001c6200007601401005401406480006202200c04030003040110311140080e19207400001c407110304001030358824807912107140c201380702c1e590039842c070b0041c0154001c101b02d85c0107103880c40b1503482416040550b00155050b41c0003401d8540c0940049040c0f00d08039080098150a10001d07a000800300e00c00c1100081c105615452140041c4004120b00c0c04a007105111f040c50181c200c142481a180d0000070070350f0201c0c00e0401f9083c504c140440c124007640c800c0c000c901d1840c1d8841e402143c3e0443c45100100400d956400700041d550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242543543 1250 242542293 242542327
    0x504060c0308090f1c090509011a03090a0f060605040f0c080105010e03100f021e070c0605090f03010f0b150c060612070b180f0315190204030b04050309031c02030301090908 76
    0x1558400610b00145c0102a005010341940d4202500900340d450041c801400c4c035100c851040c43e82d00000c1a50380c4c0d100c0c20392a0070408a0f44000744818907040c50340080040c5504100145e81082d07034200600310710315407403501f5103c0c0c0505400c041a83c032001172090303502c5000c54802c80b1001508403458810204151b0048406e00804043c0455020030308201c4198a81d02542101020402190a0416a0700e80e8443c0344042d101f00d0701881400500750002d034441020100c4a400010020040b110451803040003400c25002424401e07604c400e40c860441d00080190742650200078024a40c660361a400e22000312610403140106104665000400348a200004c02401590070320030710000c9500003d1145003a12138240500c0781d000040042e610101246c560340e8803c0d41d5900b00354a1414444407440240302d80c0d0000340c41529504104800d02c000040206a07203031050301100e600d41c809032202480c80c02203400e2080182c0040004109000482d080103a4250041035217614002507403003181c02d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242544793 1250 242543543 242543563
    0x60c01020301060305010e0c0301060f0e0301020a080f061e1c0209090a030806041b031e090303141005030a0615050915310905070801090803090d0504060c0308090f 72
    0x90390008014008580c0c5809031070700400c0301c22150380280c24400302104460005002c0c48040040d01078501c001d451141400403621500900215074a03012280d0044c031070b02003140c5011200d003103080890b0301420b11035411442c0d4406c000302401341800076010800c031141c00741c500c00c1c9240441030b201d4000d61745002c6010300440e444d10040c01c10440301c0c60054031800c4010303c00c0d44103500e8108001c00b002c0304024103001003101440c0003d41c0300c0c00b400d0f07940e81150961440550b00c5140400080c205505030348181d10521940c1502051560303014520801c41d01ca9028090301500400c0e000d90000e8080e4001c00f000c000e00f00b01c031080d400c1c3c075035000ca004044100d540309a12800c3d00d000b120581071030080d1000d001d160b40100482201c078035138050b4441d4801328034078995a50300c000c09406d01c9428001c61015050303940003404104200d0a019080c0d400c140c0700301c0f416004141031071001e58040d1044138112555034a8840c40c0300c0241c1c909540c1c181004010b001140113940405594030800d008003560 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242546043 1250 242544793 242544817
    0x50909210309070e060a0509040302100221060a140d060b090a14160f2102030109020702180709050603130506010b0d0c02010b030c0d05070816060e0301090201140310030206 76
    0x503441c0141c4500d02e0300300541e010340c4c8100540303410b104031500c0d040031810a5620560300d00082da103032881c08a103071410b41c0880710038451010803104000d00314403100e150f4940700324001c8411500d40c41b0411010008074030030b441c020000e02e4280911400c04401d28115240605070001c3d401d0800001701e09015000c0300c040a455695000e00d0070800c03111440035070052900c8120001959070401d020740110b026411100c1800003107000380c00003400034030b2140d80840701c4030b600b55207950359520b05c03002039080080101c0c400c8401120308141d0f104052140ca1054002c2d9507200c10051401080c4441c030751010346443c200022440134000450820045a070080040015003a40c80c0b80e82c4804008483d622850101164109841010304e0ba8000071661007501d41114858030394a05031070200d00d003507055172040301c8a0280000d210001e5119032034042c00c42d0700640399080c08200c10303020142201c0220310020f020601c8810b64a00400e0400c0c013841c0d1100e05c505074901000c0e280c4d0006403003a042940d0b134141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242547293 1250 242546043 242546047
    0x312110307060c03060905041239021203070b070507080f070c03020109120b06100509100509131b03240306020705010c020c060304060b04090206030a0c090b0f0405090921 75
    0x1040f41da140c8640b0f0001c00301858108035a0525642c0c00c0b140035441d82e40401040a480c0ca0407044801d20b001800c034004088100c074012a1948003620b041d0301d6076000c142d1042010000c8190301c1980442111161503003c1c001c100e103941c0e008800e4425401404090340d5414092280c1c2000902c040000d00405018004040358035241d840010314000042d00f00510084025914000081480c98610340210013103a070b2071152014048101d541e0b01440200c40d602079014501050116004001800310001c19201c40c40351050724030400c1c013a20550070b800c030f1600039440d00801e9541d1095000c2e04000801004004040007a000010043c00b419001680c801341d00099020802c8001d10818a00c1c030514009014060720600010f40381d404005d101802c51a107690001185a8860b404503600d15402090141c482c14046030000042800c002c100340031800b0544080307140c81c07645007a2400c1c451045105482c1c2803c08003030004020003c0d00661051003220300c00020300883d940501d0204004100c1c2c6a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242548543 1250 242547293 242547311
    0xb040308090105060102190602180301061d0f071407050f0d030c1106040515040c050409032c1c06110f0c24010e090f0d12061a04031211030706 63
    0x150843d10064082419540022851071415090f40c1c40c44101d5900910010b0300c490704800c0102c0421360001c409603141d440d0100200b1107040e10540940c012410f01c40400e140e50b00c074102003070b0310b00d07042d1048404110100c04150080346802c00070207005200784242d502006070112524075211003202e404000c281c55a2540d141c260b401604090072045c80740041505040030340301d4036211180301c0400d000550b2148000b4051151310b100000080c000980300b04201d140a0074010841070740c440d0401c00480380c1c010910340100304004c001c04002401800c42800c0c07045034000c1060010840b50480d002c40e1240701c048454407224000c1d2000e420000300d0716a480800c05405070920305134003004c00941c0455907020314030404020401d419500304000200564444000092405640d082e02810603c10450780c90710040e03001c4030440c048500351000340841500e882c0f0100c101e041100c400d8902032010b03c1f08001040e240200242811524180024052a465280750841e80503220075100c040d10b4804007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242549793 1250 242548543 242548561
    0x9021531080c0307030b0106110a140c011b0309050909010b04050f0a0507090e04060c05040b03041a010902070503030c0d112107090b0702240c0709140c12130b040308 73
    0xda48466800c0f005082c08605556a140040b1410b024a204011810490050000e810000b0405070364012400c1000d05c4d200304201d42d6601180360381d050000c2c1742e071511402081c031420060080b450781502d56521a80c2230900740980880014118030b0f03199202c00c0c1414040d01c45200d03181c041c43d01c1c02c01c0f14038035140440e8000203896000e00340b501080951142000109007440ba80c90700281e1001c40807400501208003119a40a203030444a803c8000001340f0040003214458010031004408103141140e0707890006008a01451130b0150803034100708009440a03a0040041c50307200140e036400500300201004d9100c1341d4120300c100d40802c941c10ba4105000c46010366045138414454601095031900b004240311003400340d2a402402291150b8211081c0b1190540946c9401c243c0c40c443c03a11040c43d80e0105e80c0d9508603100c0c0317103041e91900d0501444074844611041c071581c10b55000500d0882486040940310400400507059020080c026600059105040c0d07801180259514210350030300c0a81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242551043 1250 242549793 242549803
    0x180402031c09060c08070b070804021f0c060e072402010e06060f0103092f1807050301121103030712080612061503100905010e100902153108 62
    0x610041d869455028044a42c007241c0d69042d40c0c40351034905490b0003a40340081007805007417030003444281e107d4204016141c0c02502c00b88254000c641c50300d8021410498011103980300d90854000450b001203090204100741c0001400f04062001c4941c46980d130281c60702220b08507000e804984142564003010030f54240601e800c407641d91005000340d42000c071300160315001d0444c0024103140c0c641000307000384103040c41c401d0901c2c3c3c3d43da80c0d482e8003080c0f8031350100313083e4117506511441000020f2518001e201c2c246c118521605164654a15503424140784240110861a00321040f10b4200d20003009a142840580304451190483c42c111320801600544446002803c00d80a41400c9895100c130a000203611604100c03c19000b44080030f856010070300f40315100c0f041e403041c0b9040a110b0401c110055000d03140c0000e03100141d40a9a807035001a0081c1e403460b90020f5440889034044c072985110000042261104000c1c041e1218400058800940104101d10025a501000c0100f10806003441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242552293 1250 242551043 242551063
    0x20a0e04150c0801050d1109010b040906080c0d06021b030706021905090108180a1e051e07141c0b0402030705030c03031e090a080c01030f020c0a0b041118040203 71
    0x20007400401c4142c20020000d400520070b45100311080e1034210180700c250103402c189130001030413180281d0307190340d02040154042c0c402ea520103460b0910000b91000085060110300c00000d081c841a4505511000c2c0a5004a41320041b881d810320001062190100300401440e445a440036888448940714502000ba0b200d0070030040c080704108101d090381e80400d03040d9214683c00d040b0140254038500881c50f106140900034026000c41c940b00480c40c05841c1c08000350f521410131a5035080302d801c07002c2c14805901801d034400d070b0f0090a003884070350b40c0e0000400c00e140003e0f21098029014864070152417051841c16038103000084e0901041d81414030038031000e00350a90040c4945540c04021075071328403c0c110302c0e2085080b80c21031a461081c02e6422184c0004006100420103a1580070107a1070b20140e100150100b480c00c0d005100204840c000c3d01c0700040c0c401701624052641da1500301c28100000c02c00c0340c103859081071106044da035540348000540100b61603a80d40d880c2c6441403602d4107007540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242553543 1250 242552293 242552333
    0x91f020304030c0b0c2712010b031f14040f020a0806150904020604031202032203020904060c02070f090b0411030903160303090605040311061305030409110403020a0e04 74
    0x10007010a4201d0010078100f98001e01c44211640c60810a4086000703000e010640007840711443d0395121703e081c800d40e2560004803040800700f94410055400c8402229000e6019007054004401d04503511185410000701144081901301d403040d00c98000b444102e44c200c031941124044802503051246c10740c4082c20600c03000301000e080612480300071600b41c0e5202d6100340f204a000408541f200f034255402150b00031080003002070b40004c040d4582d00444200f50302e40040340704040003244070b1484101241d03005002d412094856840e071a01030514002c0c200158460990001220a4060003100c0140000c0200141002e292030422080d90301c143d41041c0500c40c00e200f446900c88020046070452443d100302c02d03603c0d02141c80c098003d03121499014218514000070001030681140703030826000c2000041d01c2d0707160381e145e010b180e1a21161802824641c8140024040c202c030325400446050f041003059403e0960301d40c00200071403103540000d11103400305800c1c07008200e040100c00c60304181c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242554793 1250 242553543 242553547
    0x702070305010606111b090a020f040b0406090e07170601030903031b12240b2a011a060a02060f0c09090108010f060f061b060f0213050108090102131e0806091f02 71
    0x1403000240011405042408800d0340012b403241e2104000080740c005084110b6200e480c0c55849001030254003052007070412203455900015440c13845100c040e10b4031410420740d541c10f600d4001c0110004d00565600b01e040c1662003800c3d000f00802e0300c4104201221641c2c4a802d404d41044210301561040c1e40707081e402c01100b41c0080c00d400d5100c40110140e61044c0034154844420201c1080034011103070070b20542c4d4151081c41000301c103064100060a205003507140724079030071040901500c0e00c139800100b00142c002401103047c0307c0d883c0c122103030054880c91059081c041c04c800010703207800c0281d112042c2e0380c0d905c402a102c801c0c40c5028010050040d11410907460386000f90180c01401c000007148080720400345060200002c55000d00c443d100407200441d00c58140d444050482c60032030069a01040785040000c1080005000316054100100c40103a079140c0b420030700034803604524400f5a1646100720340030481c50404c00409121f01544801040311210f40f007102c500c000d284500ea94181c07401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242556043 1250 242554793 242554843
    0x90a03060e0d020106210803040318180b0a2105100c08011e1a0f0706060803030406110f07060e0124060809010603030e010e010210020a0309110d0b040b070207030501060611 76
    0x51000c6c5c0d042202c4d006001035580707903190b180071039074070548855140554951402c0492030302d041140700d1810303410428040080c03003000002c01c0200040e9229041d0110400384940c0019842074078209052441601140c2e0340e80c0301216181d00382e980c808841c90000724400c00405c491202c0c0b42c120b1030301d40c0c0d82842c5015000d00300320001c82000c05001e00c000900b080001c0c00f800d00c505540441c1c01c9250400800c001142d11810099126402610242c9027141404184411000034000726102780203034101b0586091040d40d2608058540c4101580b080d56a4030a840f950510580d0704888200c42646d0203582c140c103201029103542801350503000c070b5a141420601c0003a4002204c80a1a1381c2402d10342200054800100d140110780356900344900e0000c40c22a91940e0940c0050521030321801d14401d407101d80d0414072102c144000750203000b4094000c0440e0200310b541f1206a0406400c5c4180c07840300d83c90361101c9080d100a40c0c08070307000461042c0c03113150001041c040807400202000015004002d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242557293 1250 242556043 242556089
    0x3150504051302010c0f0c0303080f0a0e0d0c050703060e03120106030b091503100c020c12160b1308030708120c19050f040305010f0c1b0512090a03060e0d020106 71
    0x202220090502c2200c3c50080c0c10b104d03000203800e4003181d20580c4400c7c00b54403480d00418820050718501e000308035580c04a90500018020740341c2c040040b10023070142d04045001144c040d4002002540c15008000c03001c80030070440d008551707160005d40011595280303a10803210242d04140d110f901054508a606034007980c880f6991a00515401886104400c48800090502501ca445400b04900e400000764080c0d4000c13070106410001201c0c2307481d0b0b1450500416407241d0b0388502c400d240820040c8107100b84401000505400b6150342004040117441e107242c14919405144140c49450000c146e2020a000441409a12402140f9014202182250004a0040e10003191400d2250100d0395651440140c000c1c1c9004581200080c084440c8117203034a401803004e1002040064011054503404590000346901c11661040081c03200c02807012041031540c01c24401580d012100030703000004903020b80148228035154401811041c445c0c45000b9085075801c1d40b1451032090042241c4281c89 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242558543 1250 242557293 242557321
    0xc08190b120f0f1f0203100503030a0c05061f030602180d0f020418020609040903050c070e181f0b010302090603090d1107080a020411090307030c0602060f060901051e100315050405 79
    0xc52015000742e01c0b07880f0030881f5480064150440307a0144030202e0381030000359000104100c0e0900503c262000d507280e140c00b0201c2c0940c01341b07540c0348003804820100700142d500d03402064003464070581083c1c004000d100103107556000301c10540f005662080128250b2401d03124410031804400100b244070101d560100300140540c14080744600d544031511010305000d4021511021088820790301020b842d0301203074411000903a40c046110300b449028040c4000b0029042c00c100c00c140ca08650207041c81d40c005c1010b4500064180d040640900004505441d00805140102505000b610200cc2140c0f00140304170008c4d4009003082c0c0c04910204100103000c188082c4054060b500842c464522900f80901445841412a0140b05564000060002c25000401a42e08030f5007990010b490328011042e10200640380141d10030401c000402c058500306095400d100040048102c43c2020702c800a50543e40103802500800e40307910f08007145215001c1800003400c1c0c01c0b5410422814007803c1d405c015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242559793 1250 242558543 242558593
    0xd050d030636060513020d1b081f08120c0c010903080301150306120309080f07030201020606010f03140c0319020f1e070506070c03030608010c08190b120f0f 69
    0x511824841d001002e0410b4101001800d0050440c0d409074040b00720751802940414156018146071280041e0740054a0040509103605982c4940c2d05441d07000a030302a44c00072040e036041840050000190b8601c007400484036400007034400544891f6101c02160030b00003c2c0c2c050904004c180e100500010b03440d40141c03415281040110075200003100020340041c81141c00000741001c154090b0020591310207004c5060b540008144c030700b46407100765030a5651030305001c001d02681000c0005580ca512031160844003503c1c034540402c1c0e030308000016400d0048256501524150004200003840704066203040d10070740302c00c00441c6001c241980400443c0144820050104407450034164103d00d0b01d03054540350780d00102901c0c40e038102900c0251201035041c3c81200802e00b094400954400180b0480c041d0401a0b00e40d503d080d0384800c0e20801d41411000f000d14400c1d95214040907a840d480908584a01c404006120460920b425145403074908120004154050480c0e004c58621031600c000003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242561043 1250 242559793 242559869
    0x3030304120f03060815160c0f02010822030903050607090605030609040206090a0b120c0a0c12030e1e0f060919020303071502120f22020f0d050d0306 66
    0x382d942d603501c00f20701402c640c0d03000d110399216981065124060740324040c0e00540400748945114002000280c610031a042c0e40a40342a8a280385e21001d54020b0740450b510001200c82c0d8040700c4c40c6c80200ea2884075454030141e001521803c0c06200f00581044001e800a1040c06c01c035049034a0890020000d120040405010745d01400c0070408548580068610340f0400411a40d003003030300d400446610f600181125200e594024010401740c2ca03585080700c1c0c4907680340da0380391803030515a2180781040301640883c40415948005003a00c030181030025400e41240201118240e0340c00500340c074684030b200f1410001a4001c441813088481c00050807032001128603c9044070044035000183c20360107540c0000d8402c1c00c0f0035046d49006070703180c0d00401c01284100c1020304291140080000c80072400c50303500f4041c108148012011022001d0000219072008041c080403400010200f00007501501d0300b1074050307114140c0c018843e80c0600a42000e4040755040030f640900840004022480404800e55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242562293 1250 242561043 242561057
    0x5010e06100e270f100302100c110a12170901080f0a02040f0905070f0c120c11031207051902060a1d030d0e18010f030206250b04020f0303030412 64
    0x140580f00c00c4a500e2101806807408882c100c29022100200c820881c0c040c0c3c484500301000034540e900300241041a80d4000d4196105018144415141280801c20035030310200800c95039901e80c0c0d5034050302e2029010303001c004071510341c80c0c0c507100c1d04180301d07429500f00c4244144000d800752f9900c4040140d00c140c8001031000191100d0500d0b000a2140340c02c9001c0d04810564040307898500344c0c011038003500050f65142281560141d080712604400107008006642a40c458540b1500c81c99800d03954900030150504150540b6000910300281000540d81d4100301054100a0103014010300c9520810700c2803003242c0c00800d80c001070386d5210709040d00040c464424030500021a41d01d81109041c2006001c56020314162040a00712141c800282c0d88a5880800940006807805000c50704881b0a2002803855a0a41e0300b00b1486801c400100c0c400502c00800e4070f1001c040706207031928801d0103a07140115a05190040c8020411010a864017036441001030000285050341292500700c241c0c64842 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242563543 1250 242562293 242562317
    0xf0e060f0d02011b0c21050c130605061c0e15010e040c030605040309090f020a020624030a1b05120c01120605060408100b010309150213090204150305010e0610 70
    0x186100303011102e10b81c0b00c01a61a001800c1100e00541482035800c6c660340190320445031451220903d0b00c4400040c004d800c960601086800c0c092603a9015114a100214500c0e4607140403404075042148810049641881104510300262040706000c84410015141170450340448020102c0d040c07242185400740040020709101480c21014003441c0c0c0080140b0803401c0c1030030010a00d5520b07020b4540c03c0303881c216074900380400c140300300e82e2003003600d40181c2519078414440141c1c814010954074840e080d01c001c0c81109580038444200c4052003041c10b413421040940041e50001600d41003280100130b805036120641200042c1200750150910741001c2c1c01e4081800200504101d620058001c0c1c0e01140105101d40003103003c008010b01000c3c100030910f140d00045040e11404040980007050451200c582425540c0090903d91503220f0710303203a400d07a034480e035504982c010b6101c3d010b80000399105564840d07240c0039035401492420742c0341d181ca0500c0c50000320741203040d20300801480840c2401e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242564793 1250 242563543 242563547
    0x708070e10020c121603020111030403060c0203040305010b01051e090f03011a010e040b010903020d06022206030b0f060301090b03010603120c230a11031905070f0e060f0d0201 77
    0x10602105000e01605455a86840c002c1e55a5584016840c0b040c414802c1819004100203240641c09a00d41d086060081c41c41e00150350b07281e8550441c1100303000800c40031010801c02c0c02810014400c030350003555110b1841c06d001d8215128000114100201004941c07850b00014031b91280355032500c3c180c141e44050300c9001a105200c4c4240703583d015402c00c100b9030035882c510903101e114184281c80703050b21034010728100401c0710364561100c2d010a03402e0398240094100641c501c0c44c0c552103010014508009102d040d090f000c49040f89001000300c840f0300388240360385801b80d07191500050300c0080c0c12007041c00000d034090005010311810700d91360300810403007640c003500801c0086402808035617500108240082007440a0079065402c4032045a1a811245e0440650281c426480000d0014140300e60780f805450034103a2a000d50500c921811410510024610300c15014411030081a02618000c00080c03450440d6005400c180c200c5002c20003503407079104409207200000c0364007500940700e84c801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242566043 1250 242564793 242564807
    0x7210b13050f10051801060e01050c0a0b01051203120a0e10050a090218090a0f03030902130515040c02030f03090304180501090b0d08070f170a020c0f0a0608070807 72
    0x1a2030406400c0105110103411a080c24902465556048000031a01c0c0c0c2c040c440c20700700d0048150190100c050040142601c500c5107080c41403414034105150800300c000d0f0030f140451140060300c003094030f50010400c40c60320a1906030140f49182c00b441c2040e10362084c944000d40c0080081c5041a00c030005e2241454045c4042d04052030a048100700b181801c0e25003800401c10003100b28002c0c4000045076a00b0500f000800e480340d407610004148145032542c0c1c89481d0409110224103064540c00c0080c0141d0b20000d080c000c00d0f4100800140c03c1c601041c20140400164080074041d0346407051341c014055001c8212241c515950a000c1d030b03a91031b1070b02c1441c55842181e014035a141c80e04280100e80c011960050382c126103062105000440f0700a04011402e02d940b04011305600c0c003040002c0016548031300840000780190380b4a601590075160700a019800301903a40d0050b045548111054504a120484442e4054a03007030101c2e420203c01074402180506200140000e03d400a03090900c5120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242567293 1250 242566043 242566069
    0x10e1002010f020c0c031203010e0112020a1203121409070e092806050a02040f0504090c05120a021c171e070f060c0309051b030a0b10030b07210b 64
    0x8011583c514841c0ea1260305e0790300240445109000702c5034039203100c1c1d008030306403410386070000c1d441da03a80d9280c400140722010344802c0803030300300c42c04400008407400350400952101780252610710f5584590400b80d0115540c100c032042c0010b0084d010311284680c0040c99a054418078242414135807607051101c0e140c6178002c4602d6040c482c1c5c40c1d80010282aa15640e6000148104400e2010b521079015035002c1c1c0c003850041c203460640b180b00401141c82c20b5045181d496000d1000f5503809500c41000c1755802c08280300da0361190344100c00520131814441d007111024410070f85013000079084c3d5a9441c0f040c0440d1101c0801e41d01c808145581c8440c80d0140010200e2020555107035a50014078108903001d50003203041c1d440b1450304044010850080c01207490312036200c0054150a01100142d800300340311220540c0d0103100e00801040080d0903503001c14060790368200c038071900c03074030f146001c03010000001e00c240b04001088841c4030000c0c114031026485544d0104000c07030703202444030219440341040701f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242568543 1250 242567293 242567321
    0x60513050705011214040305070b071e030f1439090906011806020106060e100c060c210e120f0423040f0c0f030b0a0306050a110c0706020606040605010e100201 70
    0x205c00c0c0410140c10400410000303119420413820b0303540b5403505554110750900c06804d112440030721020424403035417001c3c95901c0c0c9030100041c00c5071303200c01002100d2421200400c0c00d2260b005032050b042001f21601128614284181401001724612000706000700320707140f40601480c07000308103107a0088101c03410146e00d18441d0541c4580c0c1d290028041c100d14424500494203101c0a109103041c0400000002840d50f140c41010414950f00c0c1e900503c2034008450401c0600c0b11280219074804205d070703000c503942c8440403544240403840541000c25841d6801c03943c030400c0125050004000c001d5904884011102d204131051a2403068440b040b02030510303a03c5032038030f46480422034043c0c1c01340d07481500380e5032020b400e00041d420660403a20311500590b40041d0f000e4042000030290303004554003411100000c507118079281c881e0000d6400507020140d6070340144106010140d410020075a011300100c81c1448228504030010348000211004075004031440401455003d000f50400000b0340504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242569793 1250 242568543 242568581
    0x106050d022403090a020109090c020a0f0836061201030f050c04050a021306050f0d0f060816090b0103050c03040807030c140a0507050414070c03180b070605130507050112 75
    0x90040341c0e100d40c0f0285c001c038041a442e580218944d000c610840b52030201e150018410044a91260010000104d00c01c95030504200400309942c1d07a1401c0d0105542021880610405501c0960492443d031500031a40280014040944680749201d00f440c1120f4126110186101c028108141000c1e07460300c1683d003160404083c8075144010b42c3c000e014120300704110b10900c5403105070032a05845000001c400d81a014011008402180c0d0f200026207900250001101076452060904019081d0340075820b10007100002c1222108601865100d03040034a41001146002886c022740c078000500080c2c01e1b03190200701e0300c00b018003070354041120300d400c402155a6030780e03c800d03655602c90702c44004480e18040c001000566040c107008407006c408403101032500e5591400011203603086a1242034007001110b44000700e018082002c000c02400f002060300d07035035084506003081503a001a110201100480c000c00003c900089540d01c00d840c070034030f44049000340c0c540b014005802003820071001407140c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242571043 1250 242569793 242569801
    0x1110f030f0304120804170c0f07080609070f05030703060b01031404050102040810090203060f28022701021005100f0f05030f0d080c0a201b030106050d022403 70
    0x1038000d540300d0f0788a0314a0403030104400360300f11417104007030f6001042c020b40c904025455010350300291500400320340841d43d444045400c4c01e4038200d5554000502504000f00340160183c003400064040d0000d003034583c140515100c00701e607460200d4403001e09419624644641542e109801900c5c50070400708019540d41020301b07109000350f0151081c1c0d12544100022110070345580d0240b281c0b4035030000e010f04601d03a03c8000e200040d01c40184040309100080c40f41c0300d44107044003485000060f80000058482c0e005600c0740c001e00000c080b046118180340320410f90300740c3c0c4c001010f1200c0c031010240803805840355034050800e660f0982001c1006041c9060215841118814203012200228220741220340d100c0b811036100c2100c400c112b000511a01e00040d44001210014014821289404402da01001280c4021002443c080c008150001c2c40070a2607a030382e105041c400d0143c00c60080100c6481c0c2800075840d1701511000034028541d400005c4080a03d22038040900c12050b41c02a56900d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242572293 1250 242571043 242571067
    0xa1a07090e0a0f0513020d080711130c090b040e0711010e010e060603100203060603011202010e04020a081603020a09090902030307050a03020a0b10050d020904150c0905121b01110f03 80
    0x20003114110b41c05854840010141c076040f4165042d201d4007c1c3c4107402507182d98585540f02c1d40b0025007903828a230302d100e2030390950f11900c0c16a000d0500c4040d00042120215000814410300ba5000700d1018200340b0082c014046059001078110565040c0402d201a02c4010203000d401c40300c5002100f546040c03c01c5a8408022503414882d4508030103407540b8005131900d0201320f000170748100340c100000b8801401402044844041e0703850050501e0901000004000b42c2607078800c81c11100012006024040e084102160601244c1d1803414150700303021441c1e000512846180c4548206079423115460819920148110746003d82c000c0256154002a400d01a6440065100031602902c801001035092209a20001f007a24001002850b44903515000c100740242d018209803081541c03041c03c8801500544200003090101d0344032a694203180900300b01c134240c62000c440f40c1640182800140400740d9041107800001c003424410058101d002c501c2d4900b46401c0c030790242c03070710000482204180e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242573543 1250 242572293 242572301
    0x18060c0d0e04050c0a0c240b09070201050402010522170f0f0316020423190b0103061409071e02011a100906050906070510090b07020a1a07090e0a 64
    0x11100351500d000300c50024003070204854044510b1181d424083c001700902c07600c6a0800301034203008012152540800d00c01a204441007280380904031940c07110768a015013001d02a080d4068000d000800607880c040e00068428880c200d041c0302c06c0702c0700c0d01d04420030844083d41c0384c0142001070700b0303425542007a080581d6a0794140c4100003a6108601810711440300c0001121411018081500b05194482e403e000103084804003581d40c160f050741d0340444c06131f5040011071042d907034044480400c8c800c100e0034504403020b0800482c1010305102c3d0501860390410302c1c8030041c02056801480710354038008100e0350140c042c82600610501c81c59519030b0240d05411000410400d00340d03003c801d20519080102001c4c00700c1813540410043c10041000030b00560151000c2240504a01d02e0401b0030b680c1d0034240001c00d0f100d004100e9440e0b0324402070180a60b0740380e46c080298001081d04446680ba80c459040c0c0111411200000c6040020442c91140310b2a00c003e001e052a2034840741070080d41c44001d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242574793 1250 242573543 242573563
    0x30109060506040f1512020703031506030e030306060a0309020a030b0415020703020c040b0a092412031e1715130513200628090302130218060c 63
    0x55800c02001107850301e090821a07007180e1941c0741e440d0380540360160403040074901000d000144a90340060305900f0303c1c0c500044c40c0540c840d5800090407203000404040d2202c458200c00105480c02d1504000783d04000201c0340c00a03800c80d411511018184011006003400b414000d4220301088800402c002c0d8580405001d10b110f4040352000071139002d42c0c17070701b24000c550f0040d00681c0040da540c0780030300742030b400340010781805002e111040f52074903192015141044884050401c20b0304100c20110141e02c3d82d00090900d141050101c0314040d00c0040a0340303101518100001c00396030b801502d02d8000e22171200900c1d02d41d40800c100c1d107080c10892060030b040110080c00703401400c1e99071103800d60502c50716200300c0114903040854141c2d42c40700304003502201640c0300c074084482c1c0c40401d59541c40c4081c01e8541810310003103804069404026441d4050000c440c028000c15000074801aa00e20110840305107400c07000681b00d01c14094500301e14038a40020035088080090b00f402102400f060102c02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242576043 1250 242574793 242574809
    0xf0305010c0c02061902070902040b0a020708070f1e0509040f032006130f05010501140a0b040b0906030901090c06030509071d01060f11011802040c0302030f18070e0405030301 77
    0x40300c010294280d41c03104240c42e009601500400c01084465044030350300910164520449100a4840310070601300c1c0d1180e0060012000c01141482d60203504000320409020000c014141562400b0038203030414401d40106080c02c18078030701002d08240c00a00c424020321b8001e10944490515082c00942d1135089401500051414080701135240f0000d040041e0780058200104156030f60042d4001d008052010103c031044101c040d100f012490900500b8082c20300310700e003001222104c20401081d01400e5212490390304091008120380765907801a62540002940d4090352070342c4a40044c2d004007000d24006041203412800440c84607803540c0080d1207505100104c0d010107458203055600300120351211842903d912005107c1103105140c1d00d2401c02143c10150a00c10202c1040c40c2941e00c41800700805001d4145000298039003070081134901da0f000e00301145941021061780802d510010002100c0c2407440098121b01c41c404c0000740001d00b81151060110305040c87c0c4181c886d4000c5c442c50300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242577293 1250 242576043 242576051
    0x12030c0905010503060f010311070b090d110f060c0310030b09060f1003080d020a03061d040c0608070c1101091d09011d03070b06210a05010f0e03070809040207020a0f030501 76
    0x203065003d001200d00418000b0000360380e0100318001103010701700900c0003112820082c403804000a02101056006c4e0501c500503000c43e0100e107000a0030503031044d1188650b648211320720000f480d40032038a030360032010507120603680f650380150000c4c0315041076100074100d0322a941040a041000f04000740a07261050341c08002d5110324003500445249800082c01591040044015100140d0300800940703409050220366180d54182203070302c040305c801c000342c00002d40380c042008000d1000520000703081b580c200b19056040000008003142d00c0f00f040101001c5864140002c02da00501401004101e48403040404e140f64035019800d07000d0581d0302e811558207000d80c04580450041e018004450050025414030300680c070707000000100501040d030803c050800c5202c0f00d05031030002002c41d10910000340001031051a100303003100e50a03d80f042c205460300306a00028000031003115451034020100f07075155200800041c000384504030f002035005920100000d41c2000003034521040b20701a0300204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242578543 1250 242577293 242577299
    0x3080903060c0f0406030207020a030209160216060c03050d060306110702030c3712032705010503131103060a0c0f020606220b0d03113901050712030c09 67
    0x42d42d40104410f900e00e4050a00c0107015480c400e5002c2c00c00c0c140001c0c2203112140d0b40340c0100e148040c00781e4011aa80300100501c001d8245c040021a07a00700c0e96424981b40586401c0000b00810309801d001420403100182136100c3d0402504110091500710307104120009034286020f03007130b0313102007000c900031701911154016a00e050480d0500c07150321700485004960700c64003241c500e80209070543d0b00d0a240504003040744030308106c4940707007a4860f464041c0004603a00007034010002a0701050015a90713144140041e99001d0300350b0360407504c040c0141e96079030319900e05490f14009004c4d00d5a054030541c8100903c103840c0e60484000219241c640441680c5064012a00e682d401c540e960740121b040c14540148070749a410141401002c000d0009401c480f401c0080e1405042000650004040d1202d07695284814040d50220903160403445c100daa01d14011340d15101504040e510268a82d0040411240d001c0d10842d40d14a07884112910441c08149018004105140c40480010400305002c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242579793 1250 242578543 242578561
    0x2030403030228090b030c03310501140a020a0c02060a05160f02090c0c03042601090b1b0703080c0307110a0308010905010504020403210207050a0b0306150a09090e03130308090306 79
    0x6ea0240b486111034600d10303a209030055201e80000da800c2403000e9512142c1c446c64010361891404d140b885030740007040403420561100045500900340400852042054482c0c0b150083e11039111641c2c1500c040e0780310003504506503075500490203840c00c0710882c9001c0300704101c0c4121010f01400d20031104414161500c29100381c060051554200150380100414065480207050300d0f1216890340d042090303125005030f4030f6420345243c00c0c0100c1d0880c0034041440f0102c0c2075001c0c100640b1000000c0300c0d00301503140e2401001844060040000810000040341485104030180040c9141220440707101e05000c0c5401815040309109030305025191800204c0c00d4940340c0203c5080b241c01c1181280c1605c1d103505e140744840e0608207a1030070351082c10000141030b151720040c0c00042c4085100075031280381040502c40f6080784074a80100c0c10908129507084550808140c0741940c400d10000904088104415840c5104420343c50300050038200c1f000040203090700061a01d01c0c41941601c207aa1212046 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242581043 1250 242579793 242579797
    0x1020903070b1c0e0a0606091109060f040923130308040b1e0109060e060405010b1c0b210d02070305030301140103060b0a08010806070e0901060302030403030228090b 73
    0x84a40c560091041082451015030181ca241145a00aa000740483c0482d180803100c441000d40d0040e0004103240c410720446100703035802014070b01402e018802d09120103052920440681c0380c0f01d4440480c203094030710281405d40d03001d001420401c1026191262081d015902440d440401014101c000241c41c00e08125441c0c80303181d41612880c1042d21255113810041000401481c2c0c07070350f420b102c640c1041d40050416402002d1b032090009029040018081d44001d005143c9801941410010000e8402d49001c03504c54141c01164030464060310300591000c0d0481c40715895007c40750040040c2c4d00320411800e507044240c490219414101600011b0382c0325003282c400034280cbe4005100400103484040071540103294145400500b180c1c0340e02c0e100e0103503080207080100248000005001251040208035000520340c2030a00c0f00c003001c01c0001d071607000140281401c154000c0049400c06001e5015a00c40c800c2d030340003110003095002e10281e07018a444405000258400100084407414201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242582293 1250 242581043 242581057
    0x30b090a06060c03050901020f070b0a031a03031b0a171224040e0f030c031908040f03030b0a050d1a0a0b0102060f04050a05030c07090606050f0a0f031b080609090102 73
    0x465114503041d13510b056640d07801c40c41659040d8003c0c42c9000001310740c02e000d00c2000d400320070805a01d50590700001421508510700119291248524011880d0350010a840302581c2180026840b01c4140c1c54080c2000707500c81005000d40d402d1140c65803140002d5000e0306402c11f07044514215076685000d49001c0f501d41e441079003528072604504055a041c690407851609410350121030142285444c0c45285920034000c090700c07500041008420b0401401540e540c800c1a0314280c991800e150300c822a0446040c80d00906040d40c071040350000b0384400c4c00520040c00000c200681c4034901703082140074030f01107080b842858a8000d00141007544a84124448503106074002c00081c0e442109400c00010054020f80c0c00d8402c00011740c0005008000400320030b003018001e00801403034a6911410780c0c0d03554220000707000062041090031a881e00c00d80c0c0c0d003c0702c203140c500c1c00f84c10440021381c010490440700400d00a0b0b0016140411600110058000c900c10f4503400050b5544415031404c03406041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242583543 1250 242582293 242582297
    0xf1b07080a0c170403240e0316210e0306060303181c0618030305090d0c080307210b1801080613050f030a11240c0a030615030b090a0606 60
    0x300c4002103882c451410007440601c5180042240c2000c549905529081580b044500c8441459a14030092a4201c590402c4410600a02c14003080c814101e482c0e00030091600601a0103104c81418400e07035466800312446102040516540d4211004098115041103d80607201d00ba0100e8140d080000c00ca0b49184510541c07a10700c000b603441088950002c03020b8003a11314511015000109480307116980500310083c0141b081e4401c02d00d000350550b00002c040c60302030f0304052a0b03401000d4101c00685100369001e040c0590741e5403200070a803824401e6031801c1c5494820100c01d0139151a01e03a000400b2510200d58102e00006650710142e041c12090007071400d0340e041078002c940310300503401c1000c004078802d2081e00c10181c0401000303495604260b4005000501d1503040c11002d0900b400380104480309004168910100d031b02c2a020302113000781c43e84402c40000111148160701c02e9012101a041c12004e10640404007680280074102e182d01ba90f11940c60701000c00c601001314401c4030101c441075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242584793 1250 242583543 242583547
    0x3e01150b180102010906020307050c0d090806040b1806091b09010b0d020a050f13230904170d06080714100806010c0204060905090a120203180d020a08060f1b0708 71
    0x4070784404021092010090540d07488a10076000100d141c005184544071943d640c0e5140c0750260780b10703450040701900042c1071018404040c000d158020032200c2c0e00c0394221018403056150f00c4606094024240c48890b02d9000f01801e1100030356000c550581002e280394801c0808040d101d04120a0050030305c0752400c0000100400c40090405801500d071541d070500b0410708100b1426540c000ca5401014131503441e4035009002e000c8a05110007010907000c00c4603040700505100400318502c45005000500001e8107541e00d94403009003001143c0c000310580e0070500a56650f0a011035a079403c600658092030030103280d44146042091602c03004552590320709607280c40301c0c001510301c40c901c5041a6082500c90760701041022a500880c1c0c000d10400004010740c1e045030034050b00d804021078156007103420410100b9070b03510515171180300e904030468442d08044402e10000340b007a8610340c4105130b2401001c0c100000c00b51502091886403141800100f1a001000d030154101d2041000081042c40c003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242586043 1250 242584793 242584807
    0x5100909050c09030f0f190b0f15032b0c08180409020a030807050d090b0403030305091c0804030e010906170406060305070902041805090703033e01150b 67
    0x60300107a40188460050614201d0070201180c181200192295516031000c0c0300390b02500c504003e035100149003041c40c4101e1402e039580c3d1942d0904064129589641040c01003802401050700d4020000c1c8000c1c101c030520010046812404560745071105001e5508202c0000440e018001c120042641b058200e46400f14190040380080b0700071180d150015500d00002005842d5140c0344400b860080100e41e40324030241c0351081c1703001c0f0858126020444415030402c01c002c1e010044e541a680d05050119042d43c40d00111850312820714050450141c9001342a44025008540c0d540a41d010340d07500300c1c541803110700546800c025440b40900040c035009841d101d80c0240200c040d0040e00c14000030691036501d440b030925100b19608403d080640c00941044002d03040048461480b9118100740024500a800d01c0c0d2940e085100242c24000000718541540244d03606c6000c15a00d050038440e618500c1840b0b1410608400403c08060340c41d0250505034004181c4100046070400c0302c0380c2c1c1c0b40c025 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242587293 1250 242586043 242586059
    0xc05010e010b0d02101b030909151401120906021b0607030b01020601030b04051606021b1e06090a150509010e09091c12021b070b03040506240607060c09051009 70
    0x3440700410006c02c80309000d14608061350b20107681010380240d03034040030386080c034052008852840d40c0072600c0088228007003000300721020f2038011851003400e00e0b20000c00101d4150000d846500700042001d4400110074902e00e040302c0150038040501780071074952755aa6002034048a01148049015078000b80c0100005580e03484030a50061107039040e00e040101e07101101e0005415500490090303004030307000201c491a40180000300000c2100c0c0c214a200e00303111000e00c016462000c59000d1500020b207140315454400c03109009108040c0825056042c1040041507504000303c101c0c0007a5220700303401014a0b02004240c011a4914054a40d1101c0750fa00d01c040c0310b0846140d44140400c15a4030130b200e54640c4090010070f81c256101003c04501040700c1400c00c8183e4000070b040703070014030520005c10400200076030b110002c0400d40140c2080000810030690502d624207502c807000180001c02c101d02600450007005081c2c560303030300c13454998040099168000408000140b000202081895 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242588543 1250 242587293 242587309
    0x606010507170a0306092f130b03101d0a0b010306050f040506130207032f060a0509070b03040f17040b070f02120a0804181103070509010207080601060c05010e010b0d02 74
    0x3000c0707090001c0c540703990341c0c80c1d60151f17141c2080350311544400700ca07000c507201134040c131030f0f00c8031100d0780020b81c9048520713400041c1e510b80d00d00845d10442d4010001846080c0903030000005441400f100c510b503e0b0030341c8400401004c0c1181c0c0303a0725a40c1001012030b400d5000b0b0080d00295000100429002344850b010302004010080c90185d10101d036005070311502c5058801400703018060344d118101c40462148903200d07400c2680c01c0100118415107000c190950206545030005d0207480c02243d0f50703c44401ca149010a00c3e0062886520000144000c120051501e804aa0303c280102d80c0c5070808820070303104901461180150389182000030a0000701c0c3c114000c1240c901c024030040b825484a00204e14018210404481100001a042c40240600d081c42082c101501d0300c20b001c0e10980ca40000103030f01000c1c040744207000001c00d414000ea8024001c100161a10404446042d80d4485009210354900007060b22036500c1e00b596641e8545040c001c0c1030b20a04060840c1194490315803d0144903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242589793 1250 242588543 242588557
    0x6050901090804080a02010801210f1110030b030d1706010309080c0d0807080c1603080c270a05011b110303120906060108060906010c081305040603060905060601050717 74
    0x555a6821881c0050340510160001e44030440060407040d080780b0000d0040c00b0180c0001c0364144240c00300c0d504030800b401c0050800d40d8800f203295800076051500300704ca90071440c00b40380d02503507400b148038400d81d0641c000400c110007141100c08030700b0a000c007560123140303056011841d11072000c00a40c15501070340141c54001d1060720414a009805040c0c0790600b102005140d000500c42400c1c000034079440543e440d08050340c68480d40c0f410210fa1100301c00c81048030001002d0104000c0010f009648000694210b107940502e441400b09400e07500c60044d1600548032480b80000e10300124080d449643c050003001c04450180b0900f10b529280d10034201d9980c40c94645c9807104103d5048401c481407241801840110020803030790400c1c2d0005010000c3c0241401c1c082e00c01d00081018580e813088103035000607004515181d40c1d05010f403071810704140702c2d0019504036084c003d00004009035139005000d4540100c0544520343c8401c0011203031403080e507101901c5000b2881c2103482c030482c560018a04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242591043 1250 242589793 242589811
    0x1e050a0207080715180b0a0e01050c0616091a0409090507050a030302010204091d1b01050c0a0507030c140a060f020718140105040b01050a0804050c1804030207140109030605 76
    0x82560b800c056450060b2a801400700d009010340f03007100c2180c00c500c440360f03400d6819907a0202a4140381044845010701034242c1d0800a4103c103004032640203004980005219206030392040c03400c4c0031031405001c9c1c559201c90016804030300010300e0b1400524409054464030400c04d20703151a11100340090b1582600548032409003140000d417a56900e0060401503110fa0000342e10b41d880c01000780200c80b000000c9841c69829280f20481030000418004481d203401d00b0200e500700a9070f030040b40c0c81c0c0554042d40043c0e10891b80c500040c4100003502000f2070f07201b40c0750315a06e1038039600c1c1d2600f90f004155145822440d010030601085000e1892412103500e1413044812440d5580b918103050440204203007400e56407a40c61404848480d400c95000d0481603409003e584417000000742688076030800e5008011008000c601081000d200c0c0c00c400820040406501002d10f915100010b8804d840481c003502c05c003500018444c4103c03480c0c02414005071605c1c0c210798a9501d50602400001380714180c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242592293 1250 242591043 242591053
    0x6031a190902030f090c060405010e0103020d0905060a0204080f07050d03051c050a0504050d020606010206150a05181e0f0a020c150108030a09060905060d020901050d020f090a061e050a02 82
    0x1202065440550700c5051900c034071010500b80a00040e0a006c02620707a5406404108820710450740c020302400910786080ca4016510224a550180140461500140f003030082006018803040c0c01e40180c0141c41011090340e958864212100fa540c00191140c1c0e50080241040b01d404a4012006441204069880c542d82c102e451401c084c102c607401c503500c4211690b02c20070300040c03190030030010b540b5041c01d0000b080c40b8101540040c0d40c60b5002081303003130403042411a00840303454024140d4000e20000d8400c0d0b07121007030030882c3c10424004950b020310b0014a1492034480f82e0240003034a0041c0025054040b0a03101c8100c440042e5100110070032151103034552009501c00340c0316050307000300020000742d512010b02c0e080c01040100340b030348040104980fa00c41808190380d43c008655031424802c800694960001c80141c07218040c00044501080c4040340e13900a48160b2401884c2ea0702086801c256006e4a601d02a5000742d5036102e00200e20100d881700300d102d24001c0c0001d060300715007401221 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242593543 1250 242592293 242592299
    0x405040222060e0105010216090b03010b0301140a051f050405180d02070501271e05090a020415080c03191d0304030b01050109030f11010507080c0606090106031a19 72
    0x580c0c01d0040410521103541c0c54100b0440b2003682c400d440d0241000344050036081101d6150601203c00b00c2c01340c5540c039992080c40342040d075000d502c80600154007500900c1240e036840c003150100b0300704135000c0302c1d42400c140c0003422600038510715603000d405442c0301c0440141030805120040200620f400442d0102c090180014201044a00350b080390f607a0080001034241000185035105a2602040e02c800060305450103500840c0c0f040e003641c0205210285076180c09101c0329481c0300d15070100b50007a180000348888501140c00400a9522050b414517441001d003104950a840840396402092420300c08540c0c80f800c0200da0362480c28000c0c4012407222041b0000f90203820408081c12490b502c001070820410640095081c01000242405070450780b4540302d912011400d004000d01e08807140348004241d80c041c009560b000c1ea04020641d885460b413445080c1d8611013078920a01c1959440300000d00f80e4070030f014203d01104443d070f0f544081809801440311307009001c0444244031b003100d4008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242594793 1250 242593543 242593579
    0x5130b010e0a0e07051c170406051b0303070c02010e040615020c03160311280f06020f01151404020c0f0c120c010c08090619030b0114030402030c04050402 68
    0x4540600307086640d480980c01d140022100b02c2e500f4070b604200980242c02c0c2002246d40b03e40e0a90301c2c081c041c1d02010340c16691072030711600002c2068001e20f046900441c010401d182c3c428080c142c4107042a814200f0581c002270540d40c4c0380000c4501c0b000144440d16084010b5118540300480340c0000740003c1007140c1ca0307603540d82210b568049a4001603112a031003802d10301d0100f00300701005500070745400d000b50840d12640c0d0090700c62a151800361403180c800c0d42d02156000c000001d0700d130060188000c650b4580c403204241c804248902001132042e6041c840002c1018461562201008240c9018803480c0c030b58205440b00d12841c1640d03200f81d080c0040c04400d05d05006587c24101508042c00d5030540e15420409841703d00c21030510aa4082620302c4060790b00138681643d0250010350060325080e891000a03410722071150b110b030a5072105040482c1068058100418208003601c0d44103501c1c0303024200701a1800103c5001c0c0d81507110340c20700c20050815600c401e030401d0001d0074480703803600340c2560 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242596043 1250 242594793 242594813
    0x90111010504030f1706090402040e0319020c0a0b030702060414071a03160504030b07080406090f0f060506030d02030d05041b03050c01020d030c020607080c0c0a0b0108010c030c0f030513 82
    0x2030f008a98280d0f460780341290312401101d0030500c0240c4400303050400d100410700164000308028081d40d507541880d1000c0200b0410340310f0070809008403190410403554000d403140032203005240204840c20000c906020a07609403442080703e41c1c0200019038964031861003d05619079100d04500441c000403c0b10407000c4000c3d4020590103503241c1d03890030200158070b00100a9500c01b810080d0611003400003903544044143c2111451420380c81545450900c0801410146001412420000006010043d002900000b01802503204001c55990130003031503100c540d01c3c031400d00143c100b0003010b1100c203529484030390414020840c1550501c40c0c0d01240c01c2314401500b00741c1c0c465010401c48105507904124000070746045160501102c0c602030406590791074042c00c8103050100100003c0c12254118040d40c8600d250081151f121300d081e800e00c0c4070190401e00802d0080d5082071019810540a030143c90401406a9246060320461040c11801800c025060040003000440040041508540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242597293 1250 242596043 242596051
    0xe0c101b0215130510090612020c0319020a1209050d0204020c15090a0c090b010e0d030e040c0c0212061003080a0507380603030d021e03040308070809011a04020901110105 75
    0x845190390404007005441e003042c1c0145d40c10054001c205000072a4000c46542204810101c0541c551190224a9041d800b5030410b410003200114400810b060f1300180d50203000e4001c44c1d400c003182e15076083c1151160f41d940285a080001860300c0401800c2c1503000b080da801062040c0c400914060820215445060f6180b01c650b5000700b03c10300138015410310b07400c020215050200f00d20705040d00080e24201401103614450703a1803c40078400d26002c0d007040b80903504014400c005100c95414041e10340f60b841c0300c042c0d003c0d1510701440740343e007200001c031113010700b2000d00d1014900c1d155aa03141195402805031a007040024031a100001e0324030780e40c06081011040851101c0a100308203100c0c0075400d000424015104078051081a84000c0101c40e2407a0540d1405170b42c541c07092482c500c08050310171074003d11280010800050582c0844498003070442035540702e030280c4441e0143d60907074085180001950f01540a910400d140c2540100344046040c10808082028040c0007403c540c0121 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242598543 1250 242597293 242597317
    0x60916030209030706050a020d080613090303140a1d150a09050a0b0108060f15010f0f0318080702014a04020a0315080f0303040602030406110a030e0c101b0215 70
    0x3c10585007088d01403140c401c50700c200303182c6400d403803401d040011030b02074a00b1071000450f0b5903100c2d070f44140b5120341c002d000303001d8130908108034600f00000020004c0448900c0b104001c01071a120744610309000c180a0307034588140000e0001d5482c0d0380c90820080a03c00400c50317091044284003000650100d10160007003582e5009004030740742c00100318200150003450144190b900070400c08080e81c10400a292481c004c3c07809100840780c1a100341c0040c544041030040b1060240002c10400c03108200a08941b8400e0307855640511410807180d07103a80c031075841620083d040c80842c441c0101106010103107024507110604680c941a0045000c90b0301403062103000a484600c0340501d42090007280e0003c0510783c00601e0b01c1d2003400c41140d05c0380000b4000030003154000000c20203201990308261690103604580c542d80345c4d604140500200150001d098080c0580e60580b080e5151030708015503401729580b0b03024104540068500301815501408981c0115004207070340301d000071030020b8403e0411078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242599793 1250 242598543 242598547
    0xe09071208030a0f0b060d1d01090819080415150e0c0c0606090105012c0a0f080d05070c0e04050f07150e1228021e040f0506091603020903070605 64
    0x80c20f44058401801c4c0b403004260900e0101c3c8455181c5600700c8203055820f040c000340c1262580d808103421038020706d10f50f41035820004114144101340e0014031201c1000c0b159001a162248001c2d00c080c4c0c0d00f01d038064158906d24644200c0b520464100003015215010725801e62900c072490b41d05000b0040d110075801c0302020840e1400c03a2000c1181982001c0d00311000c00880d8034100000704081d00110310100d01c040314840964642c0024807410130600b070002d0101d142551951250181c1204901c240151849101b1103170038690f010340c00700d0301040d800040009480b4113003142444181c00160080710b83c0e02c90381070540c200600a018100241c03038031a032228145080e280d4010042196401c281388548140c1c00740400001c000901c400e11005020041c10302454468205461000d0500c0040c0d005200c102d0f141d03500c40c1e1040c50384400c0003001c6904020b03200f1070400720011550111a000c2e00f180c0800c001c1100594a0700241201590614000d07107440451030220b42805030341d600c080041900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242601043 1250 242599793 242599801
    0xf0f050d0c05011a030c040b01090f0605130e090a08070503120a0f0c02030c0601030b0603030706020307020102090418020109031502130e040201110d08070c0c081f0c020304030503040e0907120803 86
    0x4280500341340c242c202e013001c80d003116503c00003075103034a0500f50343c610896503800d44501e541d000c0c08000300144221310039841043e82e54180078084c1e9000201d10044402502d00110710703182c105840034000d80340000100398280566440080325840400c0a4807607100c180a00c3c0030b114000d509280c420714000c040441c0000c81c1120610580300e0211001c41550010b00c10306030340c1840001c20504480d04540111104d40301c031000310341180710b03285c40034240c1e41c0004100b148507901500109194002a101000001102440041e07180b940c000001c1c0064920320080001c43d152122051004548842c01850a041d007100c5181c440e60a030312a211000c040f0041006643c1c00c44100415880140040c203a0003d0019000f802003800030711704c00510003008104820312101d0308041c8040c3c0344c0d51040f9041494052b036041c060b06030203041b10a01d20f091191080c0c0b0548007200380c40440e64010001c0d42054181944580c0250000344401c00300d12980c0c0c400120061000c0085100070b00440c4e0907592414 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242602293 1250 242601043 242601053
    0x12050c04090903030b040f1a1504080a050c0109140105030f0603030c1906060f0f030f060b040216120201110417030c0a0c090608010908070308090a0b190515010c0f0f050d0c 76
    0x24820501213501031800c03d102e4441044150311001a0300700300d2703e07405980da15030790034044c60140350403401c000d10404102c01c080000000703040d4509017090b26201d11481d59139600712011040b00e80094002042807010424402d00060300c190070150080c2030328100103030141c1d010f2a1441c115403071408061015007030014448940b2540c3c4c05400a40c681510090400702c0b5400307580ca043c40010301c0a900d2101039002d1114550200340308a10040081d035403043d24a0a00300b107016140300036581114030b00020780c684d03801440b801000084804255080c03d18000ad003003131404842400e4141400204070281420300d003030040c0c885071440360fa508400141840a800f04031000d541048803240e15103000c84010a4009050305c0324a613042c039000704580d4941d82c02c00d0030441c3e4401d004110399854804c0c09501200d421402040381d80c04034080101d941c580841d0381d850640c2408080c003040e603414080303000c2100c0c1c91844820a0040300c1401c3c00c89416070300e0070f00c0d01c4601c20700c5c0400117008003450780c2041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242603543 1250 242602293 242602301
    0x306160e0d0317090a0c12050c12210f0a0201060e0907060903021c020a03080421020a031e0b010e010603060803030702070605210903032512050c04090903030b04 71
    0x5009903a859960341c941e660180100ca880c01e4000303c0c101c2d00d00001450300800b04209051603602c8551035640f6981c8200103400034115041c01c580b24040c04000400c1030a1502c4e10311019a19800140b000340c4000c0325807001d00c1d0154100c49041c440400490050701c401000070250701d03903507a0000402030310702001800c15003c00303845496141c008000c204201070b0f0101e41e040c2030300d03011140078a0910100c1d00844020610502c001c1d007001840d2000028040084007a204075182e20088489040d03000c60442c11036034041d10000e5014000010500100300c2140c000c189800c401114508248501d440d603040e0104240e00100d8030450f4100188505541406100c0042c85000020f5041d4241450042d4445005005400420501054001c120301c80008080701c1c101901740b0024442c18044001a101e90048507865841050407d070740c022045444204441004603955140b40d1000041c3c117000540006032031080d42140510011602a036680714280800c3d1003600e0000f2100b41d0942400252 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242604793 1250 242603543 242603567
    0x1051801060e0f07030c030204030f0c1401050f031504020c0604061e0219030c050f0c060615090d060222060c061b050702010c0203070803041e08011b030506010e030616 74
    0x4940b801840500c84122410f40d40241c410705002c1b0348000080d404800034080d9500c090702039146400010103010720990228241c17050900c4045528158000560305131181c0c0c107500ca5444801c0001841c0081c00d0386d04020102c600500141c80d01d94004a000e141010035035003990700b5980d41380d1240c805110701c401680c5260f01100190308001042248a1900a940c940001030507114a40c1849517032103802115032030300c84175210f29110581c40380c3c9079950702801c68000d805440004c000c84850040f0205907101560018410030104085541d41c4019402507400f00408010321110f2006000b0707444400f8010b0485682d800da002480b41c204042602d541d00141144144080004543c043d40201116000e031f8080c01d00340301c0d12005101092900d405680940c1c150701020901061008141c800c4401c4840d1829030610007544a54000d422100000a0102000301c8080c411400c0d0303000e0740010345d05c00414103000d0414603400d4046403d101089072410310a003240c1d44801607a94200c00c607141c0c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242606043 1250 242604793 242604809
    0x206031608060f060421050105090f10021810050909160e01080714070c08030d061502010e0c130b090f1e01030c09051803130e0106170c1b0105180106 66
    0x20100e5801c04201305210b9405640b41e808895501d013007080c4e000b02c80050b041e41c0d05c00c00030002071a0081ba86602c17004a2034400b0028020703004540031154013402030340d4422951040709070302c25440008100c414142c0910610a0000500c202c030410b41e50920941d1084c500c2d02600604030943c120000c16214035003829a041c410082c05020040382e100c941c0800c045440380440765a0861402c0041c50314141d40d2004140b84030009501903d1043c0d90411303011a40350500010100e00310800c143c0c00c1e40c201010015096000d141a100285803000b84400034076080000020b0515000c000b0940e695000c8813250b00b8090f188051000c810078640030036152201a07840c08001d9410740d0f56241280d01e05114083e900e540b070f04003050700990061868220300c1080000c0b05d80e641c0d41c2c007a0743c400f49d003124401c0c08100c40c002800024214013540b8504042d032003075030001740507070303520340004006030000c0c0d1801c1d10340d0051310500c81c64076109201d090700845444100d01c00b0426000001e50a40e402508840c0e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242607293 1250 242606043 242606059
    0xf070c050705150c0106030507050f0a030506070302030c0f1207080108120d020a111605090a0b030d120e070f090b0607080a1d060a08090d14090d020d020603160806 72
    0x4082480422200c0940384121a540034110b03101c0018030180c000d422101520f5441c06d6030000800030009030600071520140c0311500748505190800a66050510003d0049d411039000039150510a50056030302005000e417042c00c1071a1034004500581090f10680034881245003404805500491290700501c10400180819807001003600f165001d140d104600c501c0e00411481c0c1c006001c0d43c610342c0c448080300304986014240c1e58142d0b03803c55403840381501030703000000461410708440c054040e014001030000c0c910b0b00d008180464902c4e203020201a45155a20703c00c80d8805410311580e001000410b8a0f1820340b42030000b02000c83d40112407180c4118810801540002d034004181c0d0380c61040c07424103a4003201c0c803072180010910324000305607124100280c0c80e09125009500207003c1c141c010229103407a04150016100003200c64242c1d014003006004208445c6007807003c010403a44040c20454044142d0390114046410544034a422400401c06600e140c40e4005065a1f02102c111070541d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242608543 1250 242607293 242607317
    0x215070605100506191d090705041d0709180e1f0e03090d021203040302030d0804060e070602070506070303020d0504060207201807110a050601050f180f06011e05030f07 74
    0x3a4043d640450418400c18143c4002d09410406204200303506c003602000313003454403040041495000d40108003001d80c1516810309441c403e141024407034003054441c1442d0b00d09010000c081c2d60b50310740003401069110480c00c2c11400d4140000e040a0b801f1610501070395801c00900c50503507008001808980d8401c1c044224960380c2c015000880c240c05803803551142069444440c210311407500040e40510990307a80407400ba038846045071061b40244410858928403980c0140c94842a00c11580141d01c080c00c188000d240030001005814072900300103207000c601c1904541510b074216000e0341e88560100d2840c00b40f042d050503200e8417440c83c5080e40e40000c82c8500045e03502c0b20300300c00c8031100580440020f500c0b130b000700320070303d000d41008e812541070600600e441942c138038090240030300420823074003101040c0c1424417080f1301d030840c200c00f02d65856480034845084801c0040c9001d0402190343c0c019030340703a00d540c5001001014640d8500d40d4a240c103150700d240983d0080e007000c0800164080351 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242609793 1250 242608543 242608567
    0x2071a04120c081506011106072c0406080a02030f060c032805190b030a08030c0726070605010f03083a020414010f0c030c0215070605100506 62
    0x1034058404018015160300200d06001c044410582c02c1407002c0d102c1d001d402c402c1d80070924036251092109a0320034020300d82d01103602d0f44a18060319131001280d6031303245024420070001c09044103070402501202c42c4102c0b2000040070780303065910644064100641c1d00c401e6003070900c5241c01030b030040001842182811030f90303000f241c80001d100042c10070452080842440303c5100320040c04240c004203102c00d04080740c14071904842c00030845403461a1200782c40050501084501c00e80d50000c1c041d0341503680d81410001d55502004040303942c10070b04082c50101005681403406030108905a4a0310b0380010300d4110300b00c0350180c00c40c0c0d42c0040005010400a03440310221050301c010500031001d210b00c0680110f8100503403c8404880d0b4407010b507020f4826000b83e02510403110960b20101132410040c0043d1445101040e40c1c0c000104007004810100c2e0044030020070851018000c028500740d110200005d5411211084559a071201c050269210b88450b0280181c5012214545004010844 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242611043 1250 242609793 242609797
    0x1170c0d03141306030209030f010c0c0f02030705090f0f1e1306110313110f090f0c221e06020d2019170403020f0d020f040603050d02071a 61
    0x100074100040401502094030b146415958010362211040750602c2c1c450030060060f4201c00e02d4a8002d2045c2d8000041c1004140500020464991202c1e415024a608c2d104441586e420040e41c261051400002e800c0c1c956024540c490700071000d801100b818640d0b50100310a01c040c0280c2c04103000701c04d103000509047e60545400607e1500008820540c5140888c003400030400c0c0015070300d4002c0200401c1c142807864520105102d009800c042008107410007200600d4011555003000810780025445982c005c2581e80001e0030302141c0d414002140210034044210203000115031034490810807407001d420004c00ca4055052200e90001c0e03042010007941d071409100d0700130400c00003030312548030003400414000c040b8078400c05441d14920301440104005000c10b40868141465541d100444480003040d14141d90b4000c14020401c02140d0070040f040701480000d0340c1c841a07640014619a80ba0301c95030008502c41d2010341209159650040e041407682ea01c0501390f040e0701c2400341002c01c0e600003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242612293 1250 242611043 242611069
    0x105180723031903020607030e010e06010303110f010612061d0d031d0316050f0615010e13090b090111070c03020d031701030305190e030606090a020d06030b01170c 72
    0x51156400d2580700c0000b07250050420070382c2c103820240da00e900c0a160b40415494402d40b01900c09000b582400c800782400c851b480001461160000d50042c0002441000d01140e1403140c00116054841407030342060071140c0310780c0314882402180400300304014a9008000764010303540a0700403103400490f801a02d920071340c601c400030035540321500291100302e0440012856000c100f101e8444015260440012085510070780d214800c13411910048180001d415100300310f0b9040785040c004400005560b0031810402283d4402c00b1b107544550000c0c440c0c480d001d07516000b03035903203c0541010b00f1910308660b00c0303058844089104209401c041400038000d5001c0ba903046d189031034200302d00d0a040318070407075480c0c0c40301c01c0700a00c0000205140e4018090071003a80c1d02580380c031003200c1645098400c081400c000ca6019001100003070b11926098200b540d0201101c5009072070a5001807100080300c2c815081216003041d1803005104034900300600f4107140462400418170608110b00045810400030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242613543 1250 242612293 242612339
    0x1a090f09180109050327180702010b0405090c01091401052709130606360e010612061505030a0b090c04021206012c120106030b0901051807 61
    0x21000c980c1d0302540350503420007422690020441040e0520b0702a4032036101d00f8083e01c140080e1085c90396680d4264014a5500c0c1d402000c400d20240369041c92102c6400090256095540c0c0380002c4805450358090359200701082c102810303400c1c0c0c00600140c41c1d55000d81201d44104100d07180360703010b80d80100c12903a1907040c3c101c80100c26034041c0d00503251945130301c01c026084a9040103000488140d55401c000562041c0c8090040e180c9a1200c50901400948181c075110050b00d016400355048410314505199040c0d800f041145d4200521800d49076258054600b00b50900c00785c0050203602e210301900380302902c5522108611784000207594048002c4003803c00141c00700440d0183c101000030703820aa2010b0019501c911030340c0c60302e04c1c00b5a0200c60f10f0b40822070026440042109040034092905841b6041c201c18800360300034410b0280c4042c2d006081990f03a500701001003940c04418610902c28040042464900758410703034101e0600b0a590905680a40001c3c001c0065440b1109960040c80c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242614793 1250 242613543 242613559
    0x11070f03031e090603091707060e12030705070f1b030b07020d0c08040506030c0409110403121b060b18040c090b03151b040315050403180302180408120108071a090f 72
    0x1a09154000707e030301010450700003000142000c100000d94011a0303a550341242601c6c591503401030f84d51103603c0304442e2100010702c104191000544c0f071a00124500e4051914400701c02da800d40c148900003c140c006030b450613244001c10100319030400c00d5524544a61801481031203640c1e9420088c0d0085000b17041c81424084006000948000151001000e004006000c048802c0d44006131962080c04181d510288078031802c440d1038011114504170008001010240d03817010748a4900030701d0701d001e078603500c145071890074200400c0300070400b80039030300440842000601d84031824049406107030200e8041d4100a01e5141012812180da030352140069500a081d2844d0505000661145810041c21440203041140540c612503215603c101d200345c442002409000859030246e407901d1000030750104541450914004c0142d1049030414450000c0c81d08040902e224601000c0e0700342c00c040069800300004200e00341500b2242142000b4103003082d89003c1e50007021541050b03c0c0e90f003072030203051b10f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242616043 1250 242614793 242614811
    0xa030801090f021306030c0e0a0e3105030d1401080604120309150905010c050c030a05090415061106060d0c0b09030a15060f0f06020a0b0711070f03031e090603 70
    0x10075011646414103c0c2a00d164517511140050700900500c01d640000600d07150b118259400c282a03e0402e9400ba020940c40c250b58517486c0403254410100c01640040501c1200d200890030709040012540c4940d0245883d2201901e020007124502e4461401c2c0d0381000004010082c004a080d9401a0b0440768400407400701780b5055000e014105001064030a901da811a2206d10903488010304601c00c0000b84418110100219480d00401c410007805030010090411034074050702c01008064405040031a911540c0e4a2000e0002c2d03641c1c1c452408103010b40300c10703503a40600340b2000360320100449551a0040f003544039844100003a01900345151b00015a509556a0400107500c0e401e510100c1030303074880c0717686405902405042c8a00540c1340d40d010404541d44904041c3d607002e852440c1d008200c1c9030095181c2805002d0058001400e03c10100c50005038000103000031300140c04d591595404641c5185002410201c00076041103600098141030a010741c0e02c80c8981044032024034020405903a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242617293 1250 242616043 242616071
    0x91306050d12020a020a0617060a050109061209080d0507020d0318030c02030c09090c010e04093c03030507170411060d0e03041e081f0f060b07150e0a03080109 70
    0x1400c140e0186d8070041c0000c0000b100c6500629800101c140c010002031980c80b4001030181049103805898041102200c0512282c1d115080c0c0d158050410f04001c81c1091181c0c40d16a0140c1c0070f030781c02e81645511442000301d469010000064000ba0b1031a0400c8944401120100c0d00000308100400700107110010b0000c0d954200000050118004c040d21140d00301203a07030070780d90a1040780b81d5011503513601000d6001d1416124034064240c201c2404012401c24090905209201800003030a6030307108800344180d41150300c07010781c2040c0300751400511030138a224058005205201007580008d000410040028a64150b0640704a01078562545400b00ca01560f000340c6a05880c446861001280c00656503003010705c1c2a14050111040880d02d0351070b15400358644451551101840f40c01e000118aa0032844d4000481c4000d0820b000a1113600c0d034840955960201c2401c1c0c4025010040074011300100f0710440d10140c1701030000340481241c070343d00a002e90805114210106540d4100b00010320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242618543 1250 242617293 242617303
    0xc03170d020c010605090112030909020d09120c15021c050c0d09060501030c0501050403050618071503020901030506030c100c0f0204050c0a1e210e12091306050d1202 73
    0x100ca580095442d440382c00740890081071503110301446980481d0001640700b484885c85242c1c00d4150fa5101111030a01085402950158000503c01965110210003080212001c0821102c5541d180d80301001d903400c02e92801c81100010b52100c0340704114140b5200c90103014001c0410001ca0041002c1d1744000d0300d05402c0c09501d0000d0f9072142080340740d00421002d80c0c0614141d03032042c1c0e5060402074440c8011902c9002d5808024201e51004000c5502c031440d43e114401241c0d4050102d501c0769403506454080c0140305d02c05c4401182d00490002910341e010f00407158803140030341c010610000b0800024683e0020042c1c0c3c01c003401103082d407100a2240c148003000c21560042c01c180040d0800c00c41c0030750342c0d500061076040001e20b8500ba0703117450000340c050004074010030742d240e01900b1a82d07001300030501c442e0719184000da07907a05120301c04107400784018000b600d010187e0a49070843c56040c880940890303082d01c070125190a01c20f200700d50760144040e20741e84c0c1201d1098615226000b0682c641 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242619793 1250 242618543 242618557
    0x10602010c36050402131a0f04030201180503100e061e01140d080a020f061503060f0601020a05010f1e05010e1b070803040f031e090e0903130b0703080606070c0317 72
    0x40340c00052581c0b40d0885030a00e090842e09818001c107c0001c11031800071903806596264060030108000070805581f04100380380e4548900c1030b0848015a81c0e00c0002e2418001d00303820031000d0307110360a00601c0c403001c2c0f080d41c1d40001d944d0003c20848440702034040764481c0c14011840d04283c0c0e448000c2c03081e2503146210160a03030200c04259514031000c00650b0b41c0c103c4480030310b40f5200341000208042070507050b03a140700001800a0030360b80c0b40d5000540c08600c1c0145a00d046100d070483c8500071030001d0140045051811400003181d07001a6122445442d60801030060b4505050040064403c864030650b03000884450310304400d01c0b00b410038040d41c8100040502568404024403081c030500c41d0b004601c041c42501c50950b80300300d600c1654140710226801c00b0106459038820804981301c00384660f3b0041c81c040645c0d00c1d150501740c625601203042e0300404900b07007000c206c04007010380102455400080c221881c0d0f040c60160f0303a03041c000d09014000145000a0170520098004080d0b0541d581c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242621043 1250 242619793 242619799
    0x1401020417031201060912060207060f1a0a0909031e09030c0803090a0f030506063303040215030603120f0f03131a010803091207050d0506010602010c3605 68
    0x118085100820303980c2d410020058a01184400c00010506d001d50541001c64400c0c40d40c09940c000d0030b458200003908850f505894241d143c60349007502220b5441124240c601129181d04075280b1b65060258000c2213400880301c4070b1400b5610404a50410343c503000c40300645400103026944080102d070700d075020b80c0c00200074940f40c0001003141140800030300f5142c0d005482e586802035840d0031040750b1078400c0c88040d0594000d00c0c0441c03000d080881d4207119a446d0005910002e200d0340c000314918427000e6001c803640c4140030052204520b4a070340326016490454110b03500f5401c1c0100000d46458a4200821005100040c20f820505291059811100c0341503a0a510b03454540300341d202d10201044120f502800203440b00010f82c1030102002d0581d403d1030011806d1107401c0060003130b6010000005d030400c0c4144000056141e45a00c03041c1e03039a82c400c40c0034006551610001a00307541081c2000b80501c146043d1000780a09181403401c1c64020b01c1c5a004968460384001403c2c44070181c0200d90 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242622293 1250 242621043 242621069
    0xb13120c09021306020d020102160320031c0b0a051c05100f0e010e160504020c030d060b070506070903080313150c02071a18121c090f06050a0c14010204 67
    0x3510b0982c9403c90700485003640c00b61b6001c1d0001d41c000724201d20481290040103c0c0050354980868480c40c03440300da50042000403031103088507103106491344d0099001d50304000c0810156100341c091500030f40e403914205039098dd2000c0c2c2050000f590450110301180104200131646805004041045c41514035504070304014901011403824090101c0d00d0250f190f940c00d01641d1002c06100044950900307c841d500c62580701e0401007044040e5100210b400f81d5480140140d9020242900c00d150041140d2401c0c0f95a030920392400da0700b0a1002070085050059202c01000400c43c24821242d1108600c4090003450a151502041500312090034001d102c3c07414000b02150fa80001381c000c00e41d207504401e44042800d620340c1c000740f440350307040f907085204103a404204c05040c00420280c3c0f8114260039078900c001c0341e010348039680c01006a5600090480c4800b0800d040051000310b000e41507901d0458a0007582d50800b41105480c1c6400034640c006200320b455900d9000e5054a0140174005c4c03601c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242623543 1250 242622293 242622307
    0x70b0322030801050a050915190b030f04110312090f01050d2c030a0e0f03030c03032505030105030d0e030705030a050106081612030c06060b0d0903090b13120c0902 72
    0x1071910b9002d005007400740085850124181c40c10651701c5201e07407040b28851040912101c2030191900d0404044440182407410200e001c000f81c60203035100d035104103408100b038681801c0c680100e000100302c0500941260703080d414041038103002ca840035202030b902480f844c2c1ca070f04012603861040042c055042d500e04008040b01c0070214000c064140712580e82121080010a01030752607100d0141c038040444ca002e000e0032283c0c289440c0607040c41c08002c0980b424048404041402c6600c01c130b41d1400c1580650181c885058051445c5d0707201072103139251083c115030610707000c29035548482d2000014060540d40748075081e0380400040c009080050b0550700380b00800d150050190400d03010340d403500d008007007a2144283d02c2c0a0b000341220103042c00c0c441c0074501910705582220f101041a1090364860b5800b140c0056100020124400403060005d0b10340302a0500404500d910f40151414220820820000981c00f0340401300392460b0080102c3e102e0300918201203000306581c030654440340007003034038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242624793 1250 242623543 242623547
    0x80a11240901020c101d032803090f0b03010b090f0a0b070b06091e0c09041a091303050301140109050909010e0d0c0818060c1501060e01050408070b032203 68
    0x1500c84000280c0032909840d65400c10045c04c00040360089000503c0882904000700b5a103102500c41031010b82520141e0208020b40050402060104001f41c40e40e00d58039802c059200711240014010256a1000320341090100761040c401845034800056001c584600c2603513a0001c0c02a80400003080c45c2c403002d0344c9400301c503020b421826040e148980c0440c0021024204608001d100304c5030103001c45070350710403580c005124920103020980b03800c0c001d001410741350b20f86105091f228034001c02c0c500c07080300941c02000040f000c01004421075044201104001a4210307040c1c90549018151002e54a4981001211b10b9101c075400f003a405440b00060002c1c0705410341c04860314810200603280801d80c09002a01c0c103e003550f0000386801401c0000e00703400c6030411045001d98400070003191808114456091070072008007a03145264070b402c401001244d400500906059500b030070302d075051034a081c003690349070bc040b4404d20f601701d2000070016146038412608a000354040c042c1c6609100f2641c240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242625899 1106 242624793 242624797
    0x21070608040f0501140f0c1305060a03020d1103060a050109030506240607060608010e0c0f040b0d02150307030f05090c0d0302160b0d0510080a1124 65
    0x3080b800100b0a01804032007441d0034814060364203101003e041328007009412228041400c03c82075900882100c0700000310384003112030588541038200c0503000b0340b08032240600c100e46030000040030110f242c00514041ea406485496401d600d0382c00548404226010141c000e50101e000207546900001342400720081030041140ea5100c4200400c1c550b170481e08045400a49074802132052140911825240c0181c0384010031007450b801d40814040001d14540038044c5869000411517900d039540317040c1d15035a002d0402e914003546240710b8030082e00103a0300d040029003401001400d214180c09400e0040149002070000582c08004000301e40e5000b98048040d8080c209015031481e0076964503030020555500e18079520b000034040071080f610300170155008506103079018024a00002100603a082e40081c5020030400c14000050220444800007170783c00030141b10350405c0d400340c040 = true := by decide +kernel

theorem cover : BRFrame.Cov 242446043 242625899 := by
  have h0 := BRFrame.cov_init 242446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242446043 ≤ n) (h2 : n < 242625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
