-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:33:25.366991+00:00
-- url     : https://prove2.me/submissions/37cc07cf-1ea8-4d8e-8945-0cda3064eaa2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39748206 ≤ n < 39928062 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39749456 1250 39748206 39748213
    0x30f0f06010b090904060507030e10050105040b0d0807030f0c120e01180803090f04020706050705040f1a0403080a09090614090a0b0105091311030f160804020603061002120705 77
    0x4181402050080c64090010441e00e186442990b402040c03440b071004001a02144c0d883d00032901c014400d8100d00e600d5103441c1c08540b220700111246c07100501c002e20901e4891450040100003c2c05d2110301038440c0d5800020242c04c001960310161441c1c92503a0b014020081104040d400107806442540740031010395441403255007080001410036040d6a4000c42d03e143c5c8013104202030003001007100c40840056603080c0b59441c000022134041d00580c000144011b0600d41080039003503204018000b1200346142840005680d000b03042540f26401e200402c1e0394104100920100f0b40c03a00040440151034a80315036101d981c1d00ba0b01048888a4001d0b40503802e0004554040d460030481d510b82090303d20340104914007444e40080d00314810700c10810b0041b4100b046844e51440da980c802e0704044200b00ca1180c0d02e10304658001100724044504a0b14494003c402d0740100d4807030030040d4032503603001d024a45141c0302c00e005c0103284c08110744044110310440c6400011007400740042e080091180004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39750706 1250 39749456 39749473
    0xa05090604090f140c041a070510051009020c030f0a050c010e010209030d0201150e060102070f1e06020c03151f030f0308011a040e040312020a020c09070905010c0b0a0902030f 77
    0x5201904c200e040008981c040c1c0c4000d101c0c0002000003118101c45417030807a066125070506020503c0d008910300a8154050030640300e140100a400851085000e0105054440d0319203406a04a0103030221031200341d0300501c030300443d8100701d034020440800c043c00d0481c14091840f44403402e40b070304140103401c2030350040340c07403c2207003400c02401e03140003c24002401100240000f070ba04400e0303a440f030040703101c084601003203261b4000e01c05140517080105c51100c12039280c500b5070170014101340e08402001620400001c1151001c6200c42181c20002c018001d01d60000d5a240d88a81009d04002c548000505041020030340d21b81070a4011482000020401030403414007428501c0140c0c420701c03000c03090406045050102104030f07000d480b500c803091007a989490500303c5403c40d80108045006100041c201f1500ba000183d0751445c0104503410b98080e901c1c442c040710420424071601d07010451221314000003e240d1004142c1c400b541c0180051010a9500001c2c078104041082d42040d8001c03609 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39751956 1250 39750706 39750731
    0x40903030608190510020901030e07033e190b0a030f060e010f0b03040807021008040212070f061b050604080c070906050d060b03010605120706030b0d11060a0509060409 74
    0x1076860f5400409007507200c00000d071140c1c0d480b8405603000a001c80c1d070001d07042040d42c0c026481212441c44807000c541505450745410103039988410018a00c01d000d00350044000e21040c81103410000d10003034040c0310f01008000f0b0120b102d1a01c1c641c1c2044002c0c6001c080340344080003014149940140c5e80110715901d05241c1041115406e030061340d01032604400612201c2100080442240d000c500001d03520b03500e50403c46a14029008004c1d480500140d1001e100e55110350a01e0269000301d8818260311002c80707070302d41d44405074801c1501802a0b48000c00440303024250844d02107501064800d1520141e595085c141807049808540c0150082500030071014204500d0b0003030541c00d0800c00000c2d0900c40081c1500303a840724010219602c8542440c40303601d003908100000c140161040400020401c241d9072a00554058600000d00d04100c8821500c0c12301d030401c10311a0010000d00d05100c0c0f007420720031307594003c61905c0b081c004200034829080c0c80d0440140010884508005050000c202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39753206 1250 39751956 39751963
    0x30213080a0201020a020907051c0506031912050d0207050118050d02010509030d1d0f011a010306030804090923030a030e03120a051e0a02131d010e06040902040903030608 75
    0x20400c1459501c00d00c5540700503600003a02454064048500048a0781c441404403a188501c20414020181e640250503002425410060040101b00d003520b0030003188030304000e0007000304c20003d0014541000040b00c024010001090320500040000d441e114980e107400c0e080d13610128003e035064000c0903036941807280030700c5100c001e1103a91000b8441c0c0c1c1003c001c3d41d0303908d02802040400065035038448960340035440d1803580c4410030640503150440c7e030107200940240b0300074541c840400300c6854090f0541d8400c0c0726190680b5070181126061a0406407a18010002150f00f1908807060a000f4a40503011080304040811014002c1d640c03080090780c014103a0b000300105c100c1b02e03030007408004040c5c0c08000655620500c4c00c0400507041e5510b060b0380c040944400002d40000d07041e2014411f0030700e4503400420f00c0c0e03580506154011aa10146031030100100c2011001180320300e801800301030789a00c4c2c20740d04540005d0021400e060140c001408984400c10110f0202e590b80d513081101c100c051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39754456 1250 39753206 39753209
    0x607080106110d050a030204030b16140a05030103060b0f030a08040302151206040b040b0a03060e011b08040f050c060307031b02010516050c01060b0301120b011208040608060a0e07030213 82
    0x1e00c0e08110308400d09109a940383d400318220000c2c080b010400c4000319200b6410348005507000b01468103242082400325a068520701354260000384909204981340105000321088400b440c0d41d040e02d9a841d5894940003050107454807a132000240c1d5039442e155404100085106000b020703d01c1d6030718a50301c1005402ca8401d80e1203001d48100388403111903180c05210305a800002950007007503821b070740c4000400815904a01c0342e441800c1410100134030015a02060509492100030070510b00c60b0300044204c1c0d003840b07c0c0c1360000703160500010f00081852280010681c030079070440d501000300400041054004445a200090b540e000e0302e0134840c02035070f2020058010340000c2013141800c1e01e0000c1840e5290040e0710a02c1400504c82c0f6440e8025030102c4010112a10001d4507540c543c4024101078001d98000d90709145150000319902080301d1000440703a074406071644c5802c2c9802c0301510086001000150701c0540c00d4400600700e800b40d2221841030074540d90040c0c2d1440804052200c14103203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39755706 1250 39754456 39754469
    0xc06010b12071b02060304020409120e0f0607020d02010513030b0708060907030902011e090801090f0c0803090a1202060d1b0f0203030903120c0408010c0e09070e100503060303070803010806070801 86
    0x241200d400703c1c08594910003003016015a84540d0720354a40c00480c0181c0000c1074020842c840d00b5403401281035011207000261300c1f045a100203400413120801c06117004100b0081c1d80510103902807001076024100410300c903000c2c100c08885255803520350622548080340c0000103c2c40f801e04005203490400582c59000ca110305040103242c1c40341d00020000c0d100d104441100c0e10900080754040d03805860a100140071345002440350401071b150122189080031000c50780c6002c060300205042030084250344000d074003c1c000e203640528200740000d0301c0f40314041c140d801c2802088035440c0d5148038043c80b0b030300002d0800809150001990001c3c4070040e01c45e41501150410700600044541c08000c41d2250790041a002c281500c0f41072013a035085c81541e104044962030210140c00c52600b10b1420b803500c640854100c101c5075070355407054441c1450600b40c6c80d8480688241400070a0181000c1d6400500c0902181e060014a684410b01e951080e040340341c0c3c40d88032008015035240d005103503034054600d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39756956 1250 39755706 39755717
    0x507150801030204050f24040608010e0c030708190303110f031806060607150203040c05060c1b0915040c12090b04020f0f030316020d0b04110901050f06040603050a020c06010b1207 79
    0x100b800c59501c20000d03d0b03225400d48100d0b8840d40c00b169848d40c0014006d0000c1c0320080210105200520f40c0c0c0c1e04260181c14001c2c017a6480010326000e0116008288004072110700c0950102c2d03a0303080340140310361450240d12030010300c0060381c15040440950b00c1848290550300032030640000391450210005c003090300c508010019100000d840d008070340d0081e0500100540c4a4855140820f65125150410ae82000c4081000802c40d800001d0b5180195960b010f900c60381c0d00300f1014040340540485070841000d42c840f00250540c00e1541c09600001010704d010300400c00032842d030100740e800000301620414801c1061009520b083c0c1081d032000541203c01e111004201e40c0800d449000d441410010801e664040348159290706600e00800c0f64014a0042145841d00e05200907a46000f845070207030710200e0003c40c0d1030400d03500d40541c40f80700400d9541010300c4d00104038060a002030054130899024071039020b100c01c0c10010f072030103454075074007154a80c0d0b0800700c00011407100402c0ca204011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39758206 1250 39756956 39756961
    0x30a0615080a0f110a0503090a1a07080105040b0108010501050c15070201090b010e040c0302100c0206070312140c030115050c0f010603021003060b04030f02040e16060207080105040803070302070507150801030204050f 95
    0x130305500c2100c0c142d000b039040c015265a10310076014100885104007030104500c2007208180c0002c02c030750461180c0e00310340740d6484a0362508103000840b801012081c0c0440e1501d001400150700400c05800ba14410100710b0316480368001d035480f0b1000099400d18051b0b03440e10211400c00400e00c80e0b050140c40380e414001c0312481e00740c40d2080c40c020316100c064040c400701d08508140c0b921488804149540140c0007942e00c2e54189070040c403100c1032a00001e403652401d007d0105510960003071900403a1700742c40c003070f0441c2d003007040d00182400340d6402c02e41800420080c00280c4007041c84148040b0f40c0030070001034110f28500512160a00024600b020546452010300083c02100152001e603a005160110380e0b44061000c100142500c011200c29031050400307055a80340c140d540442a907103150309403504a030396466028283c071402e6a00a110394014400541c109200390701030900540104e0031038071141d0740d40c044c1442c1003001750f045a00003100d000050040d400c05d40111500209110155103062 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39759456 1250 39758206 39758231
    0x2030306041a0d02040b030307080a0503150102010c021c090f0e010305150c0a0f030209040207060507090605070807020904020118030308060a06170402040504170c0a0510090b0c030a0615080a0f 85
    0x6601918001703100b0395031001c81034800c0c0c40c2002600d10b03103540701d03500955410b003280c00504580c004548103c42500400c0c14001954818024ac0c4162803c81e0014080c2000e082011720800070450b4003442003083e0035000203519105164072000130041c001207862954114280765003411440f0614211502220040c41802001c600840e500e882c014a40660f80d0916002c040307010744103550241d9401800420258140451a803200707003c0e02c100c2d11050305c001d40d181410b81c0d05010344032010340a22030074041000541090540190f005205140014202000d01c82c03410403402c0d1500b0581c0000c41d1182009a40c4c00c0000b151005421242400341ca00751400e4103608941c5401403000b8000e60b1100701060801020010003103591104052603a1140c155504107580c440440d034041c0c40d03c0c45007082021404006202c4c80d0b01403030f000181c400060303641c112901032991014000c0700c0e60070760342c4100042046140c00c120750480904e54030802207050088405003035500342140401c01038541800184030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39760706 1250 39759456 39759469
    0xa0f2003030406050c16031202060a05100504020c2107110f09010b0c010912050c010b04060521120d06080d080907050103090305070b0403051b0601030f06020306040b040c02030306041a 81
    0x115012813509590710240400c0030381c200b0300c001c0c610700100c494100022081100403801503e6000c0140c1c21204655543e205c003c3c290344060303031034201400e50554140482e08254004280345004103048508292090301c16002440302c040140348800170118000c030402504600d01440000c0495210040c40d005000051003a076061042d0b1180d00e000003020403010000b0b405c82035103590450110303910b03050f5620010340741e030380020103018140d484c0c011910503e10b440d200c4c000076a074028252024041620300315091803107440c1c40340c00162003204c3d00151000c403803400801c541c0452080c0490030900c1c0241182c5031042c030000c0b034420320002c08100603003550300080030707401c4030b00900c5e000c5944103090900b641e06205510707000d45000c0e0345104010034950000d00501d1424061160390903040001203203103880c0c0b2400e01004040410259600700812029005103400c05001030001451b40d602c040010100c070f00801000005d60404000c1005624051140310740d082d02c8441003001452510000408 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39761956 1250 39760706 39760709
    0x20403020f0405130c03050f010e030f090409081308010b04050106030207050a3f020d020a0b0a1509020a0309020f01030b0306160903080a02100c05120711010e0a0f20030304 76
    0x55a03502c0001e02c0b40d460340c4131442e500e0b030741000c2c1c061262034a0f0304066469506070304800d5200c0d820100e05540d43d07100081200d102c0c0c0758942c6000e080c60f032400d0400014144582c0251103c00c814850307803010b04c0c0811050801801c4650000850103401c1d000d01c01901c00507400001498410f124460100e08046103414440350300c04101034544c070800b1901c41810500032107615000c0011309201140c0442c40043c00d424000030303022607062200d0610100d9450540d0034000300f044841d42c0c042002e250301c0350001034041341107441c03581c900307900c3e0780c001c00880c0c11048212001a0f120000301c070540c1003c000c0c40420300021320b0f01340b1410041401095640300003074002038480c0c54424160301c00c148146048009107501c041019510504100e00965900c28540701e0518a868101c0300d108890088048601240480d55a10380c1982c5441c8103840c0710f403046075030300103954070344a42e0340d0f201006008490400d442080c0e03410b0045410304224901220030000d2500340d60b1b05410080281e640002541c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39763206 1250 39761956 39761959
    0xd1104060c0f022407020a0b0702010c030f030f1b0801090b06070b180105040c080d0305010f180b040516090801020405030309090a0902040c0806010f0306061d041103071809020403020f 81
    0x24603040d101d202144945665004d0010306600c1480ba0011a040c10401050381074000c131440c4002948645452801e0301c14000000c2c041806c2c5044200024042c0510f1091001d00341000501011683d800e0010742c2c07042c8544501500707601c405207280d1504914224054503034404204180c180c1c0101003003042c85220360207042c0c01c90403000508131402103a850440b409402e4001e104500b4540760404081e80d41c0c0c011110103001b0700c001034401d1031003441aa0f040381d40e202c0e004000301d0310306861210741ca11440945040e803911007000303030307a162524010207004103036090a504070301801902c000c09112054100b1041640104020000f954000098600d9440100c030b901181c1d0303c892030340d00014440c100c4000c2d00075040c05806014150410802840b031082a252242c0070034001c0381c22000c65001d8002c00001c00c80d464040e507d440720104441a01440240001804003c1d480d1054020740080b12010006120ba03244248150341005500c0001e05141d0f0040d42410b0450707000402441e0001d4665 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39764456 1250 39763206 39763223
    0x1005010614090a050d0b090d02060c030402040c1209030503090705010518043c0515030d0806060c0f0309041b050d09060b040f0c02070501180e0405031e0d1104060c 72
    0xb0120b584030700b01d0348000c003002004002100d41c5c500c2c0200030340004076241c12890040c3c20f480140d0500107d086482540c0e0a0724141c034568581e403c010045c105881c1e86401c10070340d40114041c402241c071072a4841c60003038590a0300ca15000b60343d6454600c80f900a24100801071102003219901c03140ca00d401404100e40100d90382448a240381320001c200c901d4484040318a0a140500c0b00c0c00042e5080b600c0c82c902d60a210315501c481c00805034010046000e03402d07070321151080d4806882900c1054201c54010001403030160668241450940b40319a10b05c10b60300002180e03d001c0ca010b120300c580d4460b40241288103207041202c041d01c14020001050781d000e03240c140039010080560700c003a0302a03030020001c01c5140228190310008000388510400503120307100004c03d466000c2c01514079202031818070040560306121800300d80c2c00010300215414481804104400c60b021010f4101c4081e0302c808a07611201ca401040d425130b003403a5102d0726005000c00082c0301c2950b114451201da00e42120b0320303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39765706 1250 39764456 39764467
    0x1a0f0a031112070b0304030e040203010305060a050405030f0a02070e060a0e0a0203090a060e0c01030b0906030307060e150708190c050304030c1502030723160201121413051005010614 80
    0x305110100b914903075482805608000301c1e551070980003950056020395503c02400a070360301030004070f01c0b080c04040d240d940724000080c50031070150400c1b90711911500c140da05110386682175041d9900000780b80e50140e04164000d0103014111541e40e6400641256900703c2245441c280c858200d0380501038640d110340010004001400402003c0c201c10f074421010440e102e91600c06a40703500d003000c18180002d040010052a80c54540c01050050790001c02039494507240703994160040c1400118a05580154200d080c582c0781d07025030a5103d0b0b2019110341da41c914003840794440c2041c514503031030301700c510342494204032581c0481500d03031241d030506002c46000110300b002030404440805900085000008100030326a00c890642803003c81c00d1090002e10950102c2410a4088c00c0811603c210100b0004000f41d84609414140c400c090700c00083c2884182e0003151600000b25501c64005112121110070480100440c0c00ea91002d0b15080049504003000102811559466070402d80c0e0041007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39766956 1250 39765706 39765709
    0x709060c080c07030c0e06101b06060b0403030806010206090a320601090204060e0a030503250b01230d020f09070302040e04110901080303070905130b03101a0f0a0311 73
    0x4680114641d03104440f2a16503070f05e0403554000c00c034082c0038010000000030880c01e0074a580c0300c1c0205442c54998140d880585100e410182d903280304140d0b05e00d03864a4001415503054401480598000d0b03444800a103041c50000e4985000582458050382c0450b5000c0046002042130100049007001d503c4140100c40b141d054104200801c1c2200c103004840001420340f440358002c200312040754440c6980d005410003048800282c521024105070820000c0740090300c1e019145512810007020044d40482d100c3c0c482c400064000d07000300c0f2184844924140c41d00c0c003460381480e046402200c031070400020700d501081403440141e50250141c00100041511203000703405032005040c10642440c0503142c9070030705016100050450b28090a803020006c90010004030880e4440e00c0640c880312462403030001031048104500445c2d40031030703a59546804855070b0522050311141d5514201048e0f9015500d10450480e082091042c440c0001050310310213600d03102500f03012681c10a4484100411290 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39768206 1250 39766956 39766973
    0x408030703020d020a0306030c050301020f0f03180d020c1f020d03050c0408010c0c02090c2d130b09090903160204090f1b0801060509010605070b060a0b0d020a0210050709060c 77
    0x2c1c00c0f03080b12070010684c036102c3c0364582c1c011001c9902a640802c01c1680e65024103080388644110080700784002c100900d84075191000458110b2900c0070809088a14180440d00f07109000c020040180c0003d24210b04500d03201071a046074250700840a1192091440c020f0f603200e00c902c140100b4140c0b030302e00144c00d541c1b00d034041c1c0e002802d4410082c000030012440090144c1030380c0e00c1c1244102c1140010810f09904c41b0141ca9524031581d1200e905000c0f1841280140c000412022404640c10450320131101d0908014100a2240c3c07030350b5644aa41490811519280c0100702e20306550051003015401c5141d0203640c01425019280021111b403107007001c1c1c031014034a041c050728035452681c3c001150394a1148a4003201c03549002000340c80d84601c04c12a65030400c1c484c4c0e1001a10034841c1801007129150701c0c42d001640101200c10040c1da4036540d02254000e1043d078085140d02041c90090300380c061044c046c0d107c20b12a000c02c400c1c0342510010700b11041c0c83c010b070030030802004c07081001c011280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39769456 1250 39768206 39768217
    0x12030103021e1002010b0102060f010311060304060f110d0c2a06060504110309060a050702060f07020c030f010204050a0603020f251b060e010509090106031107020d0b070201060f0b03040803070302 86
    0x1625400310f030112a80301901a00d840b403405130040c03081d203000030485003180310054181d1368801104140d02d058442003000e1034202a00a0310320560703d01c80d59000f08445c2c403d0600c40281891004d80b1104071140c0a01101d8842201c5801e01050f110110381c402980141d000704103048012004a501c5181090001815a0b8002542003403402c0281a80c400e910000365200f55080300c103c40c100c0c0d8a82c2c6004003540c1d02940c0350707009a486907020070211640b44280c507504c14410310440b0828906000000e242c00191500031549941c0000c062101e03091920007000603140c5810154503180444074460051f124000c0800b00404c01c000c1c0601201807200e42d10100160031103546512a40c08001400e2050711610402c1d011411048a81409502a00030345003000c0004104c0d00c0c01e40e1911505a018011101000060308810040301c00181d0715100c45210403030080d0300c8450b0700d00d082c540180c2107a070203401281010500c01c20400c03549201c0700881c0e5109500c19032080c1c80b51602001a0043e0260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39770706 1250 39769456 39769459
    0x20f010f02030d061d0109140c0d180812010807030b06010e1305040b0403120b0303030606070501060f06030506030601050d2003010e0d020f0d110714040b040603060e0706050313020d050a0b07170912030103021e 92
    0x9061480043c083c482c8050020b840d18968a4dc6090740d892209680d50381c0c0601c801040c0300804000180d00b5800b800304da15184c0710180c6815a0350445141101c11a00203c03001c8030f040c40894140000c1c103520070031403100030700b29000c10051000c8100000f82e41e40802040307980304080000e1340b201041000e4211000804040d1010340c28a5101c07000600540700842c1c4050080c41100700000d0303145420030103684003540122498612815500a450340d000340c80c0303003980d01592201e490040b0000101705a402900d001e6002d0401101891041d0b4102a50300035100100315600441415603403002c201101100c101c03d402d004000c12070408500581200240d0301c0d44580341200000a00200b5000311018000c20f00a41d40e507540c5402040c0c4642c007082e243d08060314401114900141410701c1d6003000d01d809041217412100c0590b0780c2000c0308000300c4410000807030448240d400080c10300b081c1d80e00070100314060042c002c01103c0c000083c3c00144000384c030031000700103c0c0e0040c1801e020140d1020a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39771956 1250 39770706 39770741
    0x60307120f0506090a0512310b0f071a01060503011502160f060f020114060f01020f060408130e010810020306010e040906060501090f03020f010f02030d061d0109140c0d 74
    0x13002e0706899118081c10005032406e00500020600100402084030220032003402d450000c421346480720802a1580b410700383c1d01000c01c50000c20103d0f41030001c0d14030a003544450590313544080c0350090001d10780d40c520340c0e02d101207200140901ea82040a903419580440071f51144c1c01d440c40703412441cbc030000c50389220520f02c56000c0030031681e640800500960b01151201000f41e104207408908849284107512010b588601c04254140760814000c501c1c00c00510407951403404e50301c0210700f0300c0030a80342114640c070000780c1026201d0803004017200400c010320820f202507140000080d181e10307900c8980c1004580c0000080e10341c0c0c2c06100e081d058880040c0041024035481e03d40725004040720301419001c00c0e6017580008139080f41a41d071405a99002c0c08403429086204015182c40c004007a8400550005120041c070441961155100808800080030081c0b01d84440040000710107811014070a81060381c001041c03481a904507401051a28441c1d40d501d4400c00003100400603255070141180d0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39773206 1250 39771956 39771961
    0x5090112150c050306040c0f1d040902090a050411010516020f0103090b0a0e071215021614100b06070503120402030309120102030a0501050307050108010b070303110408031b0303060307120f0506 85
    0x26400380145101d42130a0701c04000c1f20070140c005a40d85801045864000b82301d44624000403a208000800b040f0800340c0042000c2c00143e00080c032411080341d108200542d544104418068480b0055600070801e081140c6441100b82c3c5103044001030107400b0340244985480e46a0b9a4440c4c0c3c0701c40c0d9802c3d00000c1da0f1703d05080003000c2801915120540c9010f510030040701041c40040801080351003903100891400441112044401070b40010174100307010080f0081c0000071807041c1c101c80201010a00251020746030000200e421103410014450003010305000e0600004c00000c02c4032880f14141710791130f489984a1001a2842c803404107815001003050190404c6010b05401660042204e004113102c0c0f44e0b00e034401e16070380300f600344102400942010300411118420350018400c2600914002c1900d40740b488400040c3c0e8031680c00f00e0581c2d400080c2c503c00e40358034103448162240100000d5491402d02d40c4c0000e540e10070500449a60360001c05540d010826014a034040059200b004d45a0b0352 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39774456 1250 39773206 39773231
    0x4050108060402090603012309010f0e03070b0705040b0306040504140d02010204061b260412110102010518030a0f030e060112031107030b01060305090a0f0c050a0f0509011215 77
    0x941d001d80301240220301c03e00114005140c103020380d116046081401e60381840420030f0b0303c80f60038405032605030503541e0384403c040c120402d4010b0402e40350410000b0f690761090b174035040800c0c210091000c0304015003804140321040055044a0b01b103001103030302080310b40b00c5040c4094014900c02100c109880b5040f00c8076030150701074008d84111070301034841e0f14107400e01c0305400080240400c802860164001c603501c003807039408501d20411800c0a0243e038141615600380b00d02904203802c090301c003450075011036034441d0703824002c1c5540000300c0619000030340da21040050b03480c042d2984060501001d01e4030001010700c40c4e840b0703030b0305c0c1e4800034120f03002380d65902103c41100104000680000e0000f0402a5407014005242030403250300c0145901e80b80e180440c00c400510019083d0801406940158800710300000c550b84004c0c1c0c0542528010103140c10100800082c140d4004c112103007103001c0c100841d59581410f14111040780400c864070703403032900e0410904d003d101800300119280c0300d00402d45c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39775706 1250 39774456 39774463
    0x50f1c060e0114010801030825141605010302090a03060b0f0901031103010b010203031003110d080d0c0905040b0105031b0405060f0405100804050c0d02130c12060e010509040809060904050108 84
    0x40310042d01c40c010000f06107000450790f41d5400d00001e000d0a80c200301801e47c800755190310300044031206900108461059807110480304401c44409290307402050f07541c010408007805680141000d0808615141c492000b0038601d900d81c1c80003621950351546000c00755140d10f440240c0340d41e4005c1119040e503851380b074030b0380005102c184a03a029600c0c00312450095400041281c0c011121403140302c0c151841e42e51036030407194511a0345c58200800050700000030704448060800741100480110724644005801081c03142d56a00071031060b030501c01110042e1343c101c0c0844c2d4004142d400d51101041d4252070148141c8243d030700050f0000e8001032110303d2480c0b5440a031040d144c00311085000c00b040c81c1d00c1104d0a4809890280068001c04074107000391400d075a00e0200244007412300401d1441e8070750078204071020700f045240480c110030b403403221450040c451075018002c6008894419410304001c14a00c40d8001c1000300b0020340080c660340c01d644e032042601c01461005206000c070350b84134051983c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39776956 1250 39775706 39775709
    0x6100e060a03090c09150e060418050309030f0303070c080310050d050d080601050301140d060f020a18050306010b09010c0501090c032306060105090d0606080105130b0f07050f1c060e01 81
    0x44058685802260b1070119000d082002d02054130307103111b498200149403002030005000076502565a1114030160303880b182403800118014806075840e04540000d060a21000404050300c03a00108108041c181d04910794a008a4100310b2054403940c8207920f42c83c01414503048250300083c0021844108500061403402c402841c0d55a008aa10744030015945400700b8002c284405d20388051150060601a5240360218060a008507006400300e541d00c00f241d011600c00000107031a05001c2040d10790414114004040136001410380b98174002c00001c083c0a4080b0f000e0404c400c01c1c0080c02888000d400081c1807a03003000480e6070b0300c1c0d500d14194048081a0b588810700c10034003460312110380b1000c11250321524068527541e151400c50f4080110340f0380c080038101c5500c1e42d11407004c100050f09100e03442c0f1500180c084400440710070706103560054401800c4503c003d05071010801010351040030350b01d0001e491448261900c22445e030325200f1103070f580b01e0340111900d44a800610345817040c102c1070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39778206 1250 39776956 39776963
    0x50306040807120c030e0105090301090606080606010207050d1a0402030307050f030405090a0e0d08180106090204030303110304050c0112060b0a020607140903060f060a0803041215090b06100e060a0309 88
    0x1540c20a201c3c261458130038208040c0103d950b0001c1e04206500176070040c060024000e000080101055880c44102d90341504121402e0744400104002540c0401140f80030b004225481c0207011000d41ea19000394009960603a03000303100d00b02190841d242081520300d142e40c0502590184160301c40c102d541e0790024030459109807204c0c4082004c01d6807030320496801c402003d01411036160301e414142c94000001e000c05144801c0811500304600007881007030050301d00b065015079a20b00c0c40c00c0c024182c42c1e0900340d11420b40e4042040c000011b1000a010f40114004e0800106035981e000050340107296540c002c04013400c0008207105040d40c00715016102c0c0030309031141c00c091031015400030154003e02c0512a0035500c40e1021071301100c402040950720500043c01c02001d02e407144080c03401c5400ca51f020714a8074207040502c4041003a034101213810080803041c100812589610303401c000c190b009c2c25041c01403964510042c0480d00c909007035007080c1c001415003656402c0c91540200101094030058 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39779456 1250 39778206 39778223
    0xc0903070305151005121c11030a080108060c091f0c02040905010504020102060c0c0c15040f0303050d0b0f06040605090109050306070c0b0a020901020604170403060504060207020f031c05070c050306040807 90
    0x4205860003500402180140c0700050588045071070b07c0c2c002481c04c588401d4148004034001d40d1441c1400c100400001c1c070700e42e40f8140d29514120415151000c0501003541409050010301003907200e5a0700c444803c06c595a42e20144100d4640c103680d2800340850103034007c1e040c400903c090100541119002e18800e900f216490350344c1ca00350545501030303c8a8408160840a070781790b0680f030700321211140c40c48100c1159280c13503910114503100c0da2450b403089001c500046003c4407180ea00e031180e82c000c00303801e17210003c0410041d0002a194403660003000c0030b1100101d810307407150340300e000c44002400b409000c494243c18503401c060440c10059030101c90842c03221000030341204160080d03442e01441a00104000e0310b030340c0d65980038083c1c034501e442d100c1e21040c00000085119805900c0c01240a0300c001a60383c22140148020b410354919064003d5000c0200c1c0341c1c5040f60410400140c050a1a24644848503494011092051603110b184d041c410348040c4014407191100415440303100341d140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39780706 1250 39779456 39779459
    0x3053f04120e03030d0c050405030307060501081207020d030c081308010f150f0302010f0c1a100e06030a02040f0b060304082206020d0305040303020c01020711040609060b030c09030703051510 84
    0x1c84140b00042c4469030140c00502c401c0c03003050b115400070404c1901c10308001c4d0401d40c0302c402091840d0010901607440c9504e5074010401408240801108400400d800c9468820a5004215071003980c40c1c00400700021a07480c3d134140201e040036517040c440000407a2603803aa9408003507018104c40180c00c0b680034503000c0c10182c0424294511002c5642c01c0c203440e0541c1c0d03d150010f496410100180f5401c0c0003c01140100081d40c800d5503ca00c107408080321621418003c030640000141038000b0416a07095400f030000a680004441d00c549904031001b04008c400403c282c0080d10002038915004903010003032104214155001d4000c004140b8884401401101c104e001112803034880d0202503040300f40352040f0a0f1294000544c058068180540750903400452182241c1c00200251980c45030407402c1030071894580105001088002c030103016007805c00c02c00c401144406003c0400c0ca44000882c0c6102c2e4900344403103402903412030300f90b81c881212a0011076803044116000100071052140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39781956 1250 39780706 39780743
    0x30810050111190203150a0e0d1110050403050c0304091e05010506040905090a0c060c0210030e0c061b0601180e0a03080c070c0b0408150603010903053f04 68
    0x446151008421004007000740c0415480f600507966981c00f40c0c3c1601410149919142829407174074010611403c0004108020083c66414005940380741410020b00780700440d1a03542c0010703800c0b0540614080012151600c8c50144d441d403203005441441d41c00b010a0001d04803080703600c42403490b4032080f40c680e04c00c0c101070071007400c8440901440e036101d40c0501c02841a0b00381540117640c4449901c00300d91101c1411389450307551b1102c9910500000703620b044e540045040100d000d6400c070740c035404d0a0244480780c03200f168481704846041402400085040700030081005d024070942c0750450190b0ba400d50f100c0b1051144082c00701000c5600909101d10709a000d0000180352900e19010340e030f40c40b62615901010750095001900a55105c0c1ca12140400c40d0b444d14402400200740300d4000f844c5e0b0041c641480e079050f04000b40501c0c420b915041c003400209401104031000d2842094070280412aa44c5c4414990781d007083d1202d88040c165a40b0503120b505421003140618060300c0481084080485c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39783206 1250 39781956 39781967
    0xf01030518121818042009041212050106090501050a02070906090204030c080d0504030209150301050a0b0a1410050309031605070e0115090902030a140901050a051e010303080705090402070308100501 87
    0x183c621a5070107104000780111b03200c0a1284100d022942d0034445180f03104001924510007585d0039204c0307050761a84100c0c1c054211000f541c0f181c008900500c429032420f80c01424004891003914103104000441043c030920a00c0003038060a03600714104682c1d511040f458000f50050b00040b03482c801c1c99000410419400201810300f05170725510540381604545c2405004074001d0a441e58048a07131000c114240d400380030b403038820f282d0b501d800a8880302440c2005083e01150344404101d940c55018111191140b40d86403150181c242865a035a03100c07440f6442c0b45104400780c50441a04c000c0601c0b04001c0081031305000c858070808820420b0340c80e0001a04110407500040b80421170030f000c10448105580c016680c410000c12000616031660a04206201022100d0b024103946d6102009071036420391180c15000f0b04092508040520604c0388140c03251018080074050201c2c80c0001084141300b1400c85017210b80290081d51a20072601d0041c00b680e030305030354040c031600d00311340041295407142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39784456 1250 39783206 39783229
    0xe040210050f0d11070b07021623060a020304080a05060105130204060c030c17070809130b011403090a08040303020303040501050105100c02060d0914030309070503030304020f010305181218 83
    0xc41c41d503454105000004402080c102d400604132400070300040001c5040d0b441d034144100b91f56000340500400c4c0a800c6c2da20303c8001c3e044000c52100151000b00202d9002da40c0d046075100c01d175241c0340e5403d006a8280d1440c059644401c0403485864251001c208011400604948080d00e0404803000e09141c0682a40590300030100050304208542c0042403081e11403004540c020149112407003211080c00c1c10700d91084100f07032680c200c0000e458840e030500608188000b08006402c112807c03010300000c01444810510042c02c450200205180380700a0000301c80307a56205e41e07695078480d6a40b4019449400845054840b54030b800300001e22400c06180312000c04540b96628408410070780d081103184d03001018401b1505036241080000551000300d04121001028001c5840c1e241180419141030301036002140260014001c0c4001a15180d84d850301440090a020440381d035420388006641a48941c1c0b045c0a02c1141c5010060302ca002c4001c184103140d502c1c41c020b00c80441e501344121000c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39785706 1250 39784456 39784477
    0x6060304030e010c0f0506070507020a09060302010e06030c0f0304060e151006210204060504053c040209040f060906060215010b090303070c03050c0405060f13110d02040e04021005 79
    0x89100d90b150544c8a0380300096000d210303622203002000c4540b500f030b242901c1201c0c0d030404110000b07040815460140d1001c1e0040c120420203200b980d0459000030304428964215030700842c0c0120100c0c0e25802c07180182c0e81e9006050120a8903480c103404e091001d0040084a90a5405860088031088568008061289800c45400500c01e86440c804950320040251030190060942149810f407140c50b00052008120300d40e1074135203884c1080100300790104021510300710b0710010202806808000f000c9600802c013000c8040103500c040e0000f04010744109000740b58894640040751250700995801402990b02001c0300700400b585809050b0390702c410281c155480000d04a004008030480d10009001503003014041d071f82041c03040d5452031203d00154000f1a0960003000c4014402d081c20b1107001d611403002c954403500c0d540200d0100c0c01c44020103801b00306071174541c038580e010200104115a075012140380215541c955441521104030400d84040b0b1283d0100e540f599240d511075009e86011564 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39786956 1250 39785706 39785717
    0x130c020706050a02070801052a120a0c051c060f08030705190302011e06030b2d07032c010b01020309060a030903020c0607050f160f0612020405030303040f0303050606030403 76
    0x41003402d55150708041c00c103030f04500c903522020440c0c800c00c3c02000d0159448000d40441821181200e8040c00d10118941941040620100389501c150030009078000c143c055000400c03080c0140c0c1124248110840445002441103d0404101c3e199010b8801c40d446885010f01c056228101591244030321403024015510076003450a880901d00d0081400610900002403001c1200010b403000710b07103651407442e046035106010001c1c001c40040f115400712804175500394940d0321105d4044010b091110344c5003010810000110158042d40c44410000f0715440581e1911001c46860043c014491420701c406508202016920354000070035600c82c0c140040100d401c1005d051022030051921034030503021071045020f02c03000380e11030100501c08035004002800f8102c03402d0381000d20b0300d5a54a9140340840419008010341542641031030184c4201d860070500c00d19003041c0c90000390140c0c1e000250302d0b010001c1448100b00b20000042c40d1140b103500c060040740e46100800006010888000d8046a0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39788206 1250 39786956 39786959
    0x20d050f041701090209010e0421080106080a0f1b02160605031303050d050c0702040515010203030c0901030902100e010207090b0a0308030601030f0c030e0c04270c0306050a0605130c0207 82
    0x1c6800b403401d019060070400000d00c1103194000907203900081c0c0c07203074220026170001d0000f40b0015006504260050b55074005110f42940d20050005005105103410451414081380e0b41e1400c58000d100340c005041030500c4102e9003105000910329005083d140584581c0600c0c0c8400c040440c481c40803503001d522400d065940d00f01715450b40c580304d00001c40401400708001e00c0c0340c01181c031170b0300c3c05812410000c1d030b01d84040e44144421218080c0000c81820000203421101c0c0e0390010403241d00613a0b140707800b61140004001603001e0031041c1030003503000d02651591107205d5070102071500000001d0342200c2c80c00d50b42e018020b0841e41c0454103581c02001c200c0080c400305000e10300440e0090418540011340c0046541c2c0c5004031000070075088000703a00d588050480250800000101d101d040360100820710910f02514001c2c05a5840c070740c5e00d06000d425520a0041d00380d80d8400030f50300903070240582c2c42c04e9030560340101040d019140c0704a4107241501c3c411089403003041100c045a40007007004a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39789456 1250 39788206 39788219
    0xe0709060609120f05070803160b0108060402030606011b02150721050f0307090e0f04050105010b120426040314190f110f030708100c02030a0f081003060501080607020d050f04 77
    0x691310002692203125110380010320403000c20041c201d0314042282110a41018640203000f00d9041c1d108801d41da104c9800e21016960100384243c10800c00d082c4414a098159640001402c8410020358031165480034001882c00041c0200039952040c0400c00509803901082194038103d03030326001c001a0103201200307007426154011a00141142801d012840c0d80d4190510310040032a450740b0030744020b40c244010000c003405003a001d800110221800c104c07072901c0015040303800038405007501c02032480c1c24102100d0340c6281d5024a804800441d40d460702c0b410000141c080000594082d84503030700010303564100e101325800c0d61940c010b1000710800401d03117903402250343c02000780e940004070b400c501c0c5103035a0400c0218010402d0602901145030710808130803c0b11552207003001950010042c0581883d80040c88400d00300d200d060400441d16207400030101c020064000818003803a10001094440300012154800d152682c2250b80c981c1c0e04402c1150540a40001580210001e020a2190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39790706 1250 39789456 39789473
    0x1091a131b05060706020703110102030613050a02040905040f0308011203050a050d0f1a010305060402041a0a02150f15010306080303061e040c051b030c0d030506060d0e070906060912 80
    0x4600c075040c10481e80a0311840082c3c03055100a800b240c0050340003450108064221824008584898008508516152021401641c80110010f010650318000102c9440701c0da41601c0181c0342c2e1020800c1545040e191210340d10800c0002031740442c1641d03000040007103881c908a61301b654103580d41c80c1844640030090703a040c0c0080040149558564417403141116103032180884103041e040802c451110200d002508690010744598060740c0100006e12800d190400c081c443d00c0100c01420340c0ea211100400c90030060b014694103103003080ca01c248a2089030341c458481c021243c0224124404c000800190100e0310302d80700704481740c0c0081c8005411481c002c062228451000c806800081007050b000a0440c1c44c0f45041d10302141c0e000c11a108044004000100031400c040b00071450105c3c180707035a81c1d0f1307200e4458040d401c0503114400113180c0c0c7c5605050b21888454500140161310920305840d407182d000d40195888149040c50029505204004000850b04480480c2181c46910b803141c62030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39791956 1250 39790706 39790733
    0x110a03050402013b0405090309270112020a0501030b130e0304080703050105161b0209060d0203010f0501090b0a0f030807080f0409020c10050103110f03010612030201091a13 76
    0x620052050204d02d01e00c0d042c07101044007014000a880c4c50341d107031040a00c00000107003000d00a601e01002c000009900208403000c09004464030700c42056078001c0f80403100c2011421040701500300b400080c028500b24070390180c1c40d00c00c8400031012501d0f08011411a601c00325865031040521030302114400c80f07540940c103000700707140503030f4a02510780c41564681802d07a801140c141e9034880402400001802c0d207032200008925144c1d0b0b100d151900c040d0300344509000301030310404109021036843c2e80c0303100c030031081541d01400a2210300c5a04421000074542480388040701410a885640755192400c5a0001c0d1800d0801a031841d40c00c6854500c21a04a0b07041150703507110401c0300040382c81e1441d0240c4001c00e10414007603641c500c03035114035040c220814904080141000c00600009040a610703410700681035840d0a480c440002c0024094052540111860720b00b00d848441403540c1034215214460003402201100d08255103803040c0100111506400c800b1144107050000308211480078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39793206 1250 39791956 39791959
    0x1c0303110c0309040c0905090f060102031b1c0311040b0903010b06070b04050d0903030e13060e01060f0e0303030f040b0712050f0403110c0a05010513080d03020c10110a03050402 78
    0x640d984503151910556020962a00c0305a001080072041c03880e0500440d80040300030314210f000b2510309030101d100064054803841e005039180d0000f0f90140d200700242e950f85100303031440080c907034405802c0c69100c0002004c0040d42e900a0403402801034024028600061a000c40043c41c051a003555045190000e0f840b566265484444101099503003c0161402c40d00502d40004a8201440c040f454041c444d000c0700284a12201b0030000300340c20541e200d03001c00f015204002003604c0c44c00150024010340e00940440c01e00c2400100317055520645482c00206662034450800c3d41c500101a40c07800126010450154014001000509507000464101b146801c2c580c084a054208410566104a900807030b404402002c000c00d0550101ea040c02c3c10b84d03a00c001d4a600e04c02000400d0408a80c0d0142d2418084c000545012181107221000000c00005080c0d03210b4100888009001c0c0d40540240b60341489a22401e07850300789644181030109440d01e0141d8070741494600705034090300c8000c1040c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39794456 1250 39793206 39793211
    0x1030203250b03010b031006020a0201050409050402060702030a03030b0a060c080409090309080613020f0414060f031e0d0e01020601080a060b0609100f08010f06091a0906070f060513021c0303 84
    0x240803101001640c0038116917008a9180d15100401011356070031540900e00b1503120542150140c0d800030200c074250b848040c0003084a650720b0001c20b400f440b0b8884002d406105c2d2038500410325a15910926440b40b044403040d02c001e0750703094100e40c0510030300d1010f054640208010008288070394059010f0511a04003d40a107a03030b05841428458200e48a950303201d03085403648110701e4030b0b030070150140034210340c10445d1140114000c3c05200008001d82d0050b000c5191826203079030704002c0a5050716440105d169803884911000392034a02e15030051010400001c40058250300101e084c506031400c00005090780380841c0c850601800c441c000345178201004000c3c1030759503241c1c6001c41c1c000e1b94042d12a01b0200005400c01090000141c7c00400c00303036480c81060191031740c40710f1841d048a240780118410014584181505c5200395000729611080005d0030314100b0409000441742103006e0801040155108445400408560300b0000d602030140d00031800022035090001c19032034041d2400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39795706 1250 39794456 39794459
    0x303051b070807080304060e01030e100504020f030703030207080c040905061f09050106030212060402040b040902030612010509060405070e07120c140d0204080c101b03030905070b0c0607080103020325 88
    0x2d80c0d09050550300244001d400001d024000e8a803c146810f0f01102c0a280030400c142c8049005034841030100700c0c13080b1481c0c4a001040955a038018500074400c070041c00e4070485556460080d40d240c5891040754400c1c054484032071068500ba1140480c01c40d00080076041d0f5546d180d90140706d6024542004011214401000c101c5040c5842014040c005035200141d507030040720104076144000134006889240100400c2c050000044140c50444403580d00140c1c50f0384546d8001005902000c0c2450b84a40c6001c040014071040004c00a01032801074044d210080d8486480d410440360441d28240426001ca080c02e0aa80c0958803000700e4010a00c0e1501c0140d0300390481b10303441d500101e032040030180c0116040c020707013109100d103450070341003142c200c065000c0d04d62002d004010162042400d0076580c2d0b00030004e0500940280c00c40503030140c1525036540e1900103030750a54000064039401c62041d0400112207a020780b5800741640d800500404880e916101500c502198610403186915040b650 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39796956 1250 39795706 39795719
    0x90f1b05071b0b070c050111070b0f090f040e0a0b391209010e1203040b0105010c15060b07060e060415020c01020c06241903080901140304060c0206100303051b07 71
    0x140c40b2a9202c4c290005180303152600041c404c23452903201142c0743d00300361410001c85c01071204031a406c0e41302d10000fa0312207010303070001010a030b2003458882e0400e0508407107160307040010508131142482000741e0071450301d4100e00481c0f0248051101c00022107a110400204460626030021103e081d41c0854074056060520f1600f13600c090302c0030700d090383d11540c00760024a030078042d0000304002818000e08518290710b6079031240c01c040c4203031414490030307103040011310490700800c3d5000c00715000d0500006903500b03251521039000040c2901d0652a0600c000840b03400891950300894000040140385100c0c1c007403e10081d48800028003817594204048070040000303201ea24411707002d550720041c0710403c40d1040348040510300f00191065800e1400d80e80303249040c090410680c0d0304485c0303150300e035a074100040c3c0d0040000303041c504004001004000030019150010034692810340e0030f0750030030307101c1c0c004856500c0142d00000300030981c08c2c040300c1c0040031203580c1c800d030541490b021144036964842 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39798206 1250 39796956 39796979
    0xe130c0305090f0a1a04050a020a030f0b060906060306190f030c09060614031326071401020901051c06030209040c06030e0601210201090e01090f1b05071b 68
    0x8010001207500c560402c05411401c2c8418544602c448001d040c4400003584c4076154040c1070b0300c1c596800040e210106007844800c010951509a0280817039030526106c0c01c04680300c041740300c0b04848114102c0d000490b5401e1a40986010700c03405440c03242992516020400c14440c0c03c104440100c542034030005003030780e084020034019802002e42a070418100314880e17050b9000c5030820818040c490400d000704015080481c3e0f4006800014403080043d1803602d0100d8060340321111311100e80c4c5100610007108103900600c1c000348a440080c3c08901a45c07a41c6090b401001c1c100c2c0d020407024800e9a8500510350881c104400c2050350005000c0e8484d400038000755070a45064928011038071040c80742c16014403c07150401c0e020801001390350302d4407248285491042c0ca0884030451100c0000c000c40e40101083c1001d08002703900c01c001c039a1500d440100510f1140c0114088a04000080d0318100310074403c9814000700c2c1d6a0ad500d0314207035442d100420848a111f029900810490001d03c9c090340b131 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39799456 1250 39798206 39798221
    0xc0b090d170406020105090a0201080106050a05071a0a0b030109080f070f0b040b0711060408040605070501020910110d0e0a0e0c0706050406090b071106040605090a020301020c0f061803030105010e13 87
    0x194801e507280c0d414007000a0031100010030310388a96000b0351031040541e030401e5a55044451502d81196a0042d44008503031500494070004c09000001030003141075002c220a6a1142400340c208102c562125810542640c8181c400600309805c20085040300d0b50b03041c001024454050311140b607042c00560355031200010304031410f41d0f1403a1540c0900c40400d80c810358084a9043d80c1c40201894105502d941000784241d11035801031000029003802040703402e40545502d600d0081180c4808026107102502c2601c0b907481a1025000d00804413450301c1c0101903485442170080c004e4002c8604007807803000c2c0c42c5030103442541e40303031070500211000a5003401a10710803440340c440841c80480516003425025000ba22140611080030401c63b524080003503040e502c41d821807408145070b100c07240c2c054148003d002010350103500025848141c0c180029882944132001d80403581d4940c0e5000c002c1041080c5000e41745210f400400040000d90f10511542581c03160040c140814240203041c100c04032000c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39800706 1250 39799456 39799493
    0x6060903070807080601030c0506040803120a0906090302060403020609190809010207050d060e0111031306150f060201150902030c0a03052809020a1e050411040e09070e01050604030c0b090d 83
    0x2034014020080d80c108c0d002d000300001c1e0f034041c0c04c203070038204000d85900510f00e0910007804240c00140301e195003030b000307130780d505800c0300081001c207000d400e0007521007004a4041c3c000d4840e03103011803022503000840a600008000c604002031215540303200e01035110714035090452042000200c1c440c1c0e0380e1903140c0d100503c40c1c072001030901000c0c09540d0030b680030b102e00c059046d842801008400c0240c954a909483d0340007200180c00007a143c286c83c10400250010741d2038981c41c10740400c4180d0154070040d0400074440c5480b850550740c0c0959400d0344012640350080040510038900100c0c0690442904054880c00f0718035101c04008035002d141c440340c0744409a15880d82d2410b01581420150413010f00540469440448204c3ea03281e500895a4440d26005d207a071075005e0343e418000041514003038502520750b102682490458260b035031505d801440900002d04000041501c3c0c01011130781286d9000046008180c0f40c2801003100740c04c285e4241d5003104d02001d820000404010750941256131 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39801956 1250 39800706 39800713
    0x303070c0f0f0b120f0a110c0c0301050f01050607021e03011e0c03050103080306190b0a0c021008011802030901090501110a0f0306030506060f0312040801091502120606090307080708 80
    0x90b0030800c520090481d8080c3c450b00e0b078104540798503903008130041e55126078180c42403022601c070403410800800100c1044c80303031102c02282e5511041804501000303007902c120001d020540301c518844551541c00e1103040c1e8400820020200182440709980d03510b0f580c55600c49010b0000c103804039095401c50004940545040c1030401009034083c424100d003a8540d1a0822140d811a0b03602d480c10300c400342c2a284a0154401e9202150081c8503000000d0280d40b005641c0790307c1e0b9404040c00b510fa01d444102d01c0f4001c02c46100300954441c2c6d1f41d00741264200102030000d26021442e0400a50001d85048255502c0b074000ca0003040090060700090140c41074090750b038400e001d0004007900400c626080406003015002c20129030001420b030741106c0700b01d510500b40380d40000064038207410038514506c0404080b030000780300e0350190320800e0b07540e004421480300b80c10b103410208200d101d10211181c55175404c00101d40e5034106036000d841c00c0703000039045421043c0c440510502c2e01c0d00e01c0d444104581e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39803206 1250 39801956 39801959
    0x10c0c03090806060306070e0f15070b090312152701081c02031e071703010510050a05070f050c1905030c01050a090603150306090807020f0108071b020303070c0f 71
    0x41e80002050010a041c2000d0000f13414800006501c41c000604aa410455440b030b590b01e1654548468619144005000e041404403510300140c0982103000e082e2001d0a1140000740008800b00c1110001440c1030103000c680c0d41c540902420b00c5030080102170308201d455450291403c0c42c130050240420301c00c02140820743c501210036241102e00345482c50030f04607146c4061259030f00041a1410310424003010000092100c0182c0150f014480380548181c400d10342c11400340010100441c160741e4140c510b8050600c01c0a03041e41c00780300700a81c050018104100120100340c207054801103080c45841940e902080c4003001881001c0d102050141414140108011f94075040003c000c62150030300303241e230403d660b60501610500c010b201700d200b03140e120315448107030720606075800c0050740c2c0c8000704115421072814180701a401c00003040b03001da102c1001006107580541700c2180304002d250f64814041565092000039052550b4040f80c251000b0301a00001400d0494141c000d000c00f11410790308103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39804456 1250 39803206 39803213
    0x20a030f0b16050702041e1b03061d0604050603010e010c05040503070512120c070b0703090608181e030c03040303080f0c0307080a0903020c10080105150c07060c0311010c0c 76
    0x7104040d10b01c8070003191a110420301d15030030a06a90003107030110b4000903125001c3e141804082200c5010680b518549202e10340c07022100750ba4075170b5603429603030308020352619a40a5208000003c0c040810f5074150750008806180a070440c640c000d1001e0700110b50340d4540040c242c01e603005010060080742021a0034816410300b040540e0041c1070840e503924400303000c940841e44800301481e01030030f013840014214003003401c100700c0131004202d0100d11550320302c01400d0051080129010300e03000030b950300740841c60b40741e11a1139101c14403042102030264003c0b501d1070319802286045c0001d003e40000d1006104c601014809480154000e441d0020240352814500803150001059584001003c3c0240500c0d41d42c0002d50651054045800280540c041c0c101645440f0360f01030a162310616030031403a107250b68800d006a0403204103441041100c40c072010b07207640c1e60041c1c42c440c140540c040c1d0320820445114803000c078826806405c0c2070390940500200e95007580d920403050301c00705041141d42004c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39805706 1250 39804456 39804473
    0x603060614010305060609010305070c0804030501050f0a020705070603021e12010609080f03180d06050a1a03010603080f030c07080a020a02010f05030103030f121506090503010b04050c070311030403020a030f 91
    0x450109283c03c0004c3c0c0340c0480050030500078409014105a980d400103079800c0d0050314048106504451078603203659403032620901a00048442c148002c0d00300b40401d6111600e4002d0760f4001e5072140103020401c1c03e103d01240250410040300d03110440c51569580001c40140c010b000c4840d40c1614200305605001c0064120030031a030241401e5407006201d0380c42c1d80f0010054801c1c0313034212008424030020510000e1900c0c1d200080181c0f403140b400d001d00050840c3d9a102450303c443c024882c104940e171540c2014201c9400c0c0c132015044640400c030f4160004e03c03010044d03a0005506e035100d81020565282e04500b034000e143c0210140c0c0c0805001030a541c0c011001e251414143c2c40c280389550304542c1c00418400c5150440814810800440c115889268000c20544454071a203000c12640d10980203240d00c006d44907640c0203503c0c10f45810400d040ca8001c50784101000c00080e071910302107503821a00d5800000c258511804107010110044c2d80304d41c40c02008500070021402c04040a0400c240e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39806956 1250 39805706 39805739
    0x90c03060e010f060c0f03031d010209030607050c070b160804060908070b13050103020a2714030a0b070f0c120e01030509160b093d02160302060d020d06030606 70
    0x70b04210707a01041300c994403101045245134851203403c0b141e01a4507095016041d4503030281610502141500c11a400560240445420840803548551a155003e0342c0b00d10825450700d40036040302806000f1102420300600d02c86440342c0800c180815261980b81031038002c0d80108000031035550041012340300410070030740074018041000b481c00c0d1a071040c01e1150012841060305040d0042000786000d4040e03115a206185502d860030b5160510955040032403c0303078042e002e160501010b5a9455080c000303201c010321940440314102a4031070000594011007100e4442e000c010705000f10000045141010914041031741d1141c3c0c518900c408005415038000030310350355196021406030806405d80c9404c800c2240c0b05003400c540d81e08192804600012414202c14490070128491019850100d140540d05403d49085c0301d9915035118000300d0b02d80b080001c080c294440f8224040c009032806130b00a005081030203400600d0701c841d844050081e24000cae441a00d5141da20001000000361503211400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39808206 1250 39806956 39806969
    0x303010806010b0408030a0c02010c02040905030a09090203090618120c01061809030e0906010c0b091b0306090606130e0d0e010f0509010801090e010905070306050a0f090201020a0308040309090c03060e01 89
    0x2810241000030345c5544c0c2c0a0f1008a108000e02d018800d410742e4000c5c14880442900500284490f2040b81840340e620f9002c1c40303480c00003501d001c10000e074059032071003524040d1081074050b122640781d441b002d030f010411400006825001d81042d035201001840c0050001c1c09903000041442d51a00211108940b0046404c0e1111070505141400090388100007562644046031401000e448940040b2140300c1d00440040c03016060b901440040440080c0d500e501010900c0014076100504045c1526480141e80480c61540071802040b482d1802c4000c20030709524889000a1091054507110315000340d004900300419203d8460410381c4d64040c144003420007842c10722074545058200000e050841c148903000b1550745c0d83e480d201400c182908840d007484d41090499800315180d08009000b013006545010300c1616100280e4a0124180204207040c0e030140c019040d00e0305543c8080e66002c2008000f10704000310003c000c103014215114900c044a9196400280c0c43d0030003042e12604a81138205a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39809456 1250 39808206 39808229
    0x30c0d030e010305070e060a030f061a030f01090e07140d1a0f01050103200705030409090302061e0f180c09090313090b03070b0d09122706020c040207050703080c030301080601 77
    0x45032507210823501174450070310740080d0300111800c04200420940c1c1002c202c0e1048020410200008640610b02039240c514820302180d988200c46401c0b1410060115102e4000201c01c102c03507980b003000804079036806400c1e1403844100c0e945441801c000200030751030701d101e40d400323021020320707403104803800751a0a00741007103900501074880102c0c5215101c0b50b0503a0800049240c02c0003400c5c81510020121301030140000001450065142c90080311000807081c0c004000c0e11000400031001c5000c0c61900c000605079488000c8285043c01240765071040c6071103040c1c0c01545507120700351a944034400100c060340c0c48501c442002100d0a01c1d0f0f5001c0304196062681c41041640d0100b001011903490108441d80c2d0420684072401800782a4800341100800b440400c21060f04400b04a5120500f42240e100154030300e01c1c50020003613103004410050340300050710078650400781c2c01050709074081d004640000d640e035950a2078039403242c03c1c1075420382c1021004022105040050078094400035415 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39810706 1250 39809456 39809477
    0x2901030f03080f0613110f030f01081006030201170402040e0a1202120405030606010e010224040c050402160b0c0405040f02090108060109080604020603041a0a0c020c0f0d11030c0d030e01030507 85
    0x11728145550581003119075440e610000f103040140101c54501000300380040d03d91a04008400d4100000d104040060081c100d01d10400103c512405d4241c980c16105c14280600703410380b2690202004000302d800654901c0b000e440540100480107042d40300d200340b8203691386405402820b12412120000302ca403014041888039503808141164403400030b02e0310440c2888000d0040b450b002d8802448002d41c0105041800ba146441a1443c40381d4020400c06140566440c2480b0403480340101906010600c455100001407200090907041580d00c1c00a909094072740001a003103400c50703c24004010350004039158a0b50b001100b140c1c2c03201090800c40b0580d403510414a44902004000900c9100700000080c204907280314221040072a5000750003030380c80d28010240041c0a1948403101510907146000b001d440c01c03001564940102a007080d507a500c042d030b80c0c0e9850f0400500c5440d03060044401c4440e05450f2604080c075050f000782c0d01d8108440d003003000503044803000340000040000042c0f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39811956 1250 39810706 39810709
    0x3060605040e162601030b0c0414010c150e0304170102040501050715060f0b03100b0313031103040806070815010201020f07030c0f08040f03060b0604050d2901030f03080f06 76
    0x85a44410f0060344250606489882104c2e005000707010101490405416101030482c0883c002d4183e92141c000c442e8030361590060700c200c078000c03441313540c81c00c5280c000400500c1d44a80900001184034900b201c0c0c042a4442610096807800d0040e01640d5101081c1044050302d0b001214008100c81c1d002145050f0410340000d100b407042e480040c0400e070070340900b5031000e5401d031304c07000080807a00c001c6405a900d030b00c9a60499403066810180041060101140f811248012a4020003c0c800b090441d0400f564056030003054004140c04d00c0d0000340000907054006000f1603110304030540c3c0708400c901c0c1401c18403210b400749150560440e0b00c107120382c00050341c808040722143c0350142030128441806117890000c03441c03010801444064081400141e5402900000041da44030300003e2150f84003401c24020f080c0a23901c6080d5201d0486440300002c85e141c0b844441c0100000710102621a0b100794980d8002602a48100c8170260340c840c1c40020f1590002c2e40300d030070075042406035016007082c90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39813206 1250 39811956 39811979
    0x11d030306090c0d060603020d05150f01140409020408010605100207080601140f1206060307061d01030e0f060114040c03090b010314070305011103070801080d0207150c02040e0106060306060504 85
    0x20560390003500c8032004108a001410240d070a41d0b01c02135024400c2a0311072900401a402c180711800c0d02d5410b01001c1215203140c1d01107030548030000f41c852403005e5400c4004466001103078030080354500c030400000c83c081c5010b00003800682000700021450914250030b01c010000b4031200c100843d08942c2040c0050640030840c1c070f045420a01440c0c4c0451919400600c5101c500342c403003540f085015641d040d41e0310000c03c600d4800c0000310252000e060303540d081610351030381400b444041d41718212840f417440d42c000e40c4091021110041210070f40741d034800c161864000e0a030419480501482d0003462145424000e0804110562030180071180144c3d991a00c0c121040c003000b0200000306c03001c41800352040144000a6404c10000e00c8040e080071007105603648181d844900051440c1c0021aa0301400525580403000302e50080c600c00c0e140c4150040c00f006407138560001c21448554440c0503a460380500768000b40000000210985007203005022201d0700e6110805020007808204480e68110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39814456 1250 39813206 39813211
    0x26060109051005061303020109050d02011403090a0b25030b0d0201110309030a0803060a0b040501120e0c0a2c010b070308060415030c060e1c03030e160b0c011d0303 72
    0x1080301180c00d8961010552240d01e6907000250413580c045420781d03a554051312440100d0b8002c2c1c1303445841035120028400003008000010380480c44c034403919126010f00e14000c6900104090a580100e00310f6551008c00003c02e03611017006a01d03880c440c170048000760a4540100c61141010000d154030360012403071040c507c0401070b0601c4103c0c02c607608582000d001322440304c03c0041c00d80d0810a050300e0b2102a940054602d24000c1c13511400200c0c08a038110103d03026148142c542022005541c004803001e80764050381c40c2c0c01d5000c0d20b5803146180e01c5016607400a80030400b4071941801640f6006402c10404800c0c0826408103000100841d0441d081200c1043e6018a442490b540d120004200074101504080740183e5010400105109204c1c40d5241a110f59a0320002c5154151040042400c0303086e000e00b21001c4000300031b00000340240d100b9410209a007042e01c40e14107180d0300100010301141d000900d00b00740060219040d0100b8030034414503c1d51803d818402c0d00f40101d80590740d0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39815706 1250 39814456 39814469
    0x140114090402120102030c07030e10170a060312080a0b0f010f0f020102090d06060609080a080301091d0f060117030309030a030c0203041a0729040201120f0501030c260601 75
    0x2940302080c10340d11048400b20011090600942d0f07241000130f030391149540260360590005a1105504210780392000354509010441d40e0340820401c0905910009040050071144409690b54000400980d06208129801816860f210401d10300280504103a40e000c80b4a544240d84424001895030f170814641c610403110391800341944450146c1c00c0e0300904c6014000ca0744001404041400c0000d070750440419203085995100e24641d680400507541c40e1a244018001d0a052005200b04000d5502241050080d08802225a88100c18040c100b01650020010036040000140904009218281d08014403403000358950310f800c0381c00584a02524031580101078542c032140f80340794820003c1d038020301224219002103ca611122803850742c07100d00e04444031007000390084a04580b1039983c43c40343c40c080c185820690f549500455000750144e800b6042c00e81d403028140d80c0b2804a1040314061441030f1035082569081040780c00300c0c82a04500c0c0400e60106204076818003101203813203411100c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39816956 1250 39815706 39815719
    0x51e070206150a0515090321090105071104021b07050a030512090103060312030c08070906020307020f0411070602030a1109010210090c030605070f0906182601021b01140114 76
    0xb038100203480c0100540c4425402480c104603002e2080094006084196046007207a9400d400820642840b500401d2035a8040c00180b0901407a5402000280700e000d100705554285000c0d0500040d0407600079100284e4880e01454004000354410450400075200442c0c080d59120700d5a0740c1c00f80e69021000c20a60500c3d070110341c10441c0c2e4080d4000c100510360240800000490039640200208054464a00002e1206010401c45401003544105591403607014500e080d038a6028000800002140140c00583d2805070340707034903641034000d0a50644598805a40c0f4100700c18104161141075224001044042041d2421a0380010f485403d09144110200d0341003200d00305050080b5280c5d101a20403402c10080010f0b00c0c1d4043c0034480e02420766226810314603103602c1d0803034106107070010300c0102084401c801e10030031008900c205500b03503224032841c0403a440c3c41009801d81c4c100d441c041c0c40780c0c0c070403000d02c07040490280541c001c3c0c03468594504c2e44a61400b040c85102404184c9414011107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39818206 1250 39816956 39816991
    0x31305010c0501020c0604150605010f080123090a09031d0904021c05010203070908010e0f0717100606030605010f05090a0308280f0e030a0812070507050f01051e070206 74
    0x40c0c01e4054039804130403017041c0c4046103010308210100e10700d110801ea040e181f0f00a40803607550701400c0358203407042c055a54103100ea82405120040304a00c80c000e504004034078205002d039640e40c40d01c028400c0f400c0c1c1d007002c550070003586006445038001e10600380c641444240085d01c540c6039400724952054049840707904c03800601c0c024071003156480c0006002c6500000801ca2419007000d425400c5840350b6000304401d000140c1c200e80c036040409810200ea41188a040014600c00001d0102d100409001c0d21825a04140c00108035441544120003003030700c030b13881081030303680180810b04c20141c3c40c00c004e40303040c909500007020f208550100070907644011a100171050395080d81c281d120420047e07180501056040040d0080f200eaa102c18000b07003202400001c01c1c100464042607166201c00c540d410540c2030103e40e45080d4000700b244080020500091010a50800076041c4017806c1030000100c5007052503c01c01c0c0240742d0914002c1000c03180c0c090256450f400107490364090451154400c455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39819456 1250 39818206 39818213
    0x121908010b07241a0a0e0601120c030b060313051203010f090c09170a020405061008180f0703080a0e06070503030a0f0609060602060a050a05010f0312210b030f031305010c 75
    0xf20504040c2010b0601d030000c3c0f100004013136121001000022654100b01c20b9031811402c0983d00221483c0307000448a0071400036031442394000303c0f110032050601098a04d6000b01240c0140c108075044052884040786c0e4000b401014841500c5003c003c1445a00d1581000b01e8209001040e11429103040d5907540300564041c440d0040501618071041000804940c1102030395884603c400140e00c12490540490464078104644001d0a030181e183d0900c0e5945030f4580010080941061000900a05242c81c410240510960000d107209442090315000418001080d040107510124000c0d1000c0108101040e8000140ca50051340c40c0008070300c0c0503903000700d12301071304403580300a098a00342407002c07604980110388240704500c045010040c5a48031841441552002c0c801c0c10343c49414220140f0201c0d400c210102121042c50920342c03039445004582c0d2800070382c683d028070106540da15289a6a140034030841042802c203400a60404070581e810f482c181040d8441c60341031103c40d0a490b02007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 39820706 1250 39819456 39819503
    0xd050a0c1e080c010606020d09090510080f0a05160f0e190e01020a03150b03040803070c050303071e1403060d0201020703020409050c18040c0e06040905121908010b07 73
    0x152003880c4107540008910701d05001250003a00385280c0d42d500307101010503500e1001814131a040099915001c1a62400c2e400000400020707114126080181c1000308501d0b004000000440d92410010b1105400c1410140d08007580044045526001d8580401600307100d141842e09403000e20700240030030744481411025184000500c003c00d281081e110080c0400190f02030314000714960bd051003c840c00d00b001059001650048401c03411042c8003060118288001550380410f09052181144110303444561558108540d00000198141c49540c2c124407a01c40030843c1d01058241b5403040c0700701841c80d503001d00000709514002c10300f050702e000640e03100300b01040056401510030441030302a82019030302c40c44d11000d070070f0159807010320a030244e5030409043c034815500580e04e041800d041181c000d504038005401d681d0b001d07880b80410400f182e802e0080417400d000040401e03541d203146002d480c2c0c3d9660303420b06000601039464010090340f02d02000700c840080d401000300c4142c150f0940079161 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 39821956 1250 39820706 39820733
    0x506031603200a11060105030a03031512111f0f080714031005010e030d140f2b0b01020f1b0a080708060106030b10120504020616050309120d050a0c 65
    0x700d80d04007800908020b900b0002465440f180740da9005080d122100350035a500700078400d864041d03020035115030200e44254042c80c44843d070740130b211b110180c1d41c041022649460030000da804480c003450300d04c080d1400394070b910039802184031070040720707080c21502500d00c5010842032020f000a40000651941c070808500a00715206a90f00c0c0e200d0070a11164405075401d0300806000c40e032022aa820a8500000e540040010f0b81e80c50604180c1c4406548409030002400581d83d00c0c0d06020045080c0d14105a991980700d10203401c0f03120700d41840b999001d0300d955003102030640d0000d034001d141004011548801c040b40c0400c013041074400703c0300800d0a0189660210a05010700d40d00400c0d021000704000b412200507590034407003400900308201a5801302016140425102c0101184081454001641c400d0004000c5800c28200401c08005002429000c070b643c0e03000044c080c0201e10b4042d6400c2c01085110707000340340c25003602030050164411802403d091001004004e0104400c910100380c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 39823206 1250 39821956 39821981
    0xb010504081b120c0d24020d02090102071703040306020711040501080a03020c041401051309140309190303050a080a06050a0b030106030c030e2e050106081e010506031603 75
    0x18150908821440650394510440901c15451a810980c5412000071030040900000b0004c40070744e03205596925280c0419403076011050070404800c2801e2407584040c1c00309423030b40800941c1c1c0d200c51500080c20a07080f5004061400703101422140612800000c2c0c509403503000000503500c800c0c5060400c50b002e00d4030000f5500c642020004103040c1d8000c140b40809a00c81d400700c0e0795601103141080305a8184081d035442c83d40d804c10040140303107040c0b001ca52140407a50343c000740c440314507101c1800c5d01c011840c030911745520001d0507840604015a03c015501a00c0c4040d030481802c40e0b900625034030804241204004070038001c100030342010392018004080040c06400c0840da40c00312000550000d00c55800071914006560607424040c0c01030242e0a040140503000c0e140c10b40009103912001c02c06600f400d03489210154003000c102d0710881c1d01074582916039000524041e10302c4800c0386e14039442c83d0314025108004002540750001501c0cac02048000080c40f0001c42441d00300c00500a996400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 39824456 1250 39823206 39823213
    0x1050d02030108011e020703080609060f15040f050105040305070303030207080c0714040c0e010f180b0f0c0115060507031412040b07090503010b0904020d051c050c0d030606120b01050408 82
    0x1883c0c9405501800181604500f80c0c901540c40604036812402110b4025001c81c40f0030000520a181207003400d540080000d1112072051440404103200380d900c03140a01a14000040038840038485d188658020b000900e0302c1d500d0729045a491079210102071000074103040c2c000ca0f400040003400b00c03c4d1840d42c8403440072100f90319550040e0000d8030f2041030f0218029860710042c80e003124030804500000c0366041e10780e6440c10800c00c50407124420814600e60028012000104d08141c0740001404800c0c40e0a0a01791030b01030500f0303800c2c211101042a603502144c0050100011130300481030302c0d103e9030907040451a000148907010203504c0b80520080d14000300310100002c012800e1145c034010b10300c0d9612149800e0b242d10902d4200d810072039000f81c0c8030699600240051a00740e014452940c0702c1c0742a11150400d02880b1aa412001c0d10018081036003c20031040075001000710303105840ca00c0c5010b00006140c1100a40b0b00e40540070b000c80310b16111100d00e01943d0040301103900802209045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 39825706 1250 39824456 39824459
    0x100b0604150f18030f0f0501020904090506010512160603020309010b130906050c09061206030307020307080f06070e0d02040f0917040806010803040b0901050307030608060c0d140412030b01050d020301 88
    0x300000e2088102d10080782c1c0551402000d0001c0046842c25203600031108070f0900d1a0391110003080380048000c440f559020070034504e0303a48450198000c4644910001c20407941031004110b42c82d100c2c1c280d1030030300d41d10070b828215507841c00f41a10012101941001070f540d40f145d001b2a400760400300e400ea9040103412840344c0c0c2e0030341182c4c80740b1700490054008003d50348883e1205142c80c0f0500c502a0f030300c10700500c01c0c0c041c4065074011250300710750f008080f680380004950120341450340590041616400840310701c40c81c0c02d400d00081c0d0303104a140c60420040200701d400030f108081c200601074051680c50250340386184440d400107036604c1d0059040742c181110305030b05a50f01e50260080c443c080c0624800014440030000c10307a0140d1f4050b8000500300740b0301c41700466258100170031200c1010f84440d400290340390140580d034040d901007003005030340c2e40e8485810029101d421101080b15440c004c00c110100d0045462142142c1061401140e1204648012a0903006460340e9500300c0340b00000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 39826956 1250 39825706 39825749
    0x702040c080906280c0504050a080706110604030206010b0703030f05160f03090203030301140604170109060c020a121103040504240602060103080702040c1202030f010311030c03100b0604 82
    0x1c0144101c034203204a0760555150156071042c401c1843c82c003405882805503021020700b01390006000d610301e9207030490a0a0359440000c403000c145610141240d00070207400d004040d4007100c401a28000503006086904241d540250f8401c41446050043c100100c0d034079080510070381103400502005a001d100a0504455414040302c1030759402021079424040f00e4200350080c01100e1407075400034051030031a803800007070411849482c0851680585c0401002c00c000165007010611070154400010f200d14541c49c2c030404450350750030b0b003038155800344206c04001001554500301e100980d26000c90301da078028241074a54000ca41241c2e034018103190b00b0003030310b042c14203c203401407900b8003035030540075541c2e20140d80740c500a00010b815200d04112400143c01c10390091504640c00e40342245c05400559100d40480e08240c0b50b0024141645c0010000e00c6404103600c40011011030140500310100000241d50302c6110500c00c10003525444495020f50301d083c00c2d50002c0c40c5516010b944041d80e0b20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 39828206 1250 39826956 39826967
    0x102030a06080d020d02100e031306020703020a05041802010e1c030203031603020a020304151205070c060e07120b0405190308070305010803070f110d1e0201021b01050307080c0702040c 81
    0xb54008070f1243e0000c000f029803002940340e9104190f50042c000103a0961014070140001640241c1c00e480108a030007407441a0480c41401003a140d07001d804400e00318810840c0009555004c03501c01d60414501d41814541410000840c7d41d0900703141408144640210b0440c85403941c81000756030914600000380754011005610414009070106a001c03440e9505038100e0244100381801688141700500c010000620307200502042070170104045a85070440c202a52411039020000038039012100080081c103000340018003174004050247c0343e040c054a60500c0a280a01812180303d10012400303001080c080000c0c20502402c1214a0440a060141a0800a95191001070300c0d04d00001404176010080c0d40a089d4460000c0504428a450b0090031200c128a0554020684120100094103881c1e4142e00072000b1890000f52003114000641450208145071950385018480310a2581e030290441e580700e5440d00304154103803105640b07001e46009041f00290080d1505050050454021 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 39829456 1250 39828206 39828209
    0x5010e010e130e21030403020a12030e030316020c040e06060d060b1002010e0f01050105030c1302090d05070801060e0f0112080f030403080406051302010f05030705070f06060303030b01080c040b0a110102030a06 92
    0x51003100c00140d0f603508804c50520080710060016045100803900140035040101d40c2400d040c83c0100310620a880700a0a43d4800d40d410524018941d0403049100c4c0c05020780e004001c0200c80400610b40b40d0010b054840383e000f0074844c841c0c03840d0103c440800455512020300d2060150401070500b01b0400044e000b4002c1c041165113510444240d000007a605000350343c1030b10b0f03000c0e000c0d269000c0c0704400d010203008000c909000d042d8003808402e0036a01c48214031200c180c007500003000d00c240340c024010300b10303030158000d0081002c0c810100101540c80783c403403604484030030241c0c5050b22403504021089008100527616012800020f2105065101aa06000e1070080b601000301c1d0300d4400c4020102d05a100e0000e012544107460100300c540560059a0300508508146142800558a01c880001d000e00308442d9550784040031301c03d25a02d80b0511340c0b808001e00b02101903050501820310b083c00740c2d02c101e4041f0303140058580040e070300c6043d05a0180714043d00940d201c4c200381e80e124000c2c2905 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 39830706 1250 39829456 39829483
    0x901051c060e06120307030507140609070510030216080a020a02131410030b06010c020301151e080309011403060406030803010e06131e0509120a09080c060405010e010e130e 76
    0x802c00421900d181004011081059810046103014034640d41a1010b0700842000d0b5800c040710110703000e068034117104445c8101c0d89507010300035182c244000c0107182c01c6440805810544103210742c0000c0100101840b003910b80040b1119110129460101d2030102c072040c0094210003805940090314500d50000e400781c603070b90300141c1c5196480070402d451000041c8400341552881c440030411a5000301001c0755820f00240020400c031303900a900c0c10410707105a1200706a00350500708094078140c2c0c07540c0000038028840c059464103225074002080386450007202581c1794400400700e130b0300d6607490307010000556004c0c10b01e681f0707580d441c200d4852031130703044991600900312000c07800f010305901c3c0710b00320307801c1d1081d03000e00541c6902c1203014000701801407d503a400d02c00c8800181c00008240040d012880d51a99098545800d010318142068095241d450041d4002d10061000360303004000041001e0080c0303804800c400100340000c01100b0145032041c0594909030451a0070701c0e0104039844000007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 39831956 1250 39830706 39830729
    0xc0605040603061a1204050705091e061e090915010b0a02190b0c0a1b11030d0503040b0a050601120603030806031203060a03031b080a0f1b050706050901051c06 70
    0x1600c6106031003d020480b0344001e8942e0422940c1c601725440310400381c1182c024002c680035a5181c4001c110314001c203980c81c0304d843c0300000030ba0015070038060000398412420b481b503c0f043c03002c60044103007004032140010300c150542c5001990101041180000030407a0300740780041565215642105580400c00d400018020794101d002e03400c454000c2d0811244c0c1c040d81c00190341d500c1c0070300451035401071100202084201e02c20002e050a00660000b401070041d0351103481d2402e01c0d801c00d89440e0042c0402400d0040c1841000045144c0c125942d605c40c0c010f620114955840d60012a0a0200f40f0780d81c000d00c6180120110601d0f5209400c5881a80180c080342c0c0b4205484148e42d03200c0c041111840e0f40701c00a1030080c80024803400c4247d800c007504034a0094400c60179554004141c20601032100020f01000855407060381c8151a03110690b1032a4036902143b00b00d441d095142e00300d80c0600c401340702001a071865541d2240c1c00701c038052003076858114142e062000504c0080e000034820016500c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 39833206 1250 39831956 39831959
    0xc090108010b0c1c0210051e01051002030d09020a0302060c010f0b010306030507120201170414010506040203040203030a0f2709110a080703050a060f030f03031a030c0603060d0c060504060306 84
    0x50b45812554242e400350001c202e0202c114481001d12000c080380700045000e0080602000700a5015030b074050301e040b0410080d003101d14821200405016402544506000c40c01d0300d42494011003183e80c40d22000f880420b0f184035034000b2465003800c5a00c001e4029000042250ba030010641c442000080000d505001b91420030b0011800d075081404041c2c10342d00300100030070082ca06020364201051043c1406c2d00d06884601120200710f40456050320001010705510407503020038890302d07610100031036003103055040940120741c2d0f9000d020140360601c45900c85009241e802a618555901c08219442011104a5072225400041ca200f441082414401c8074050b40513510b00b613070039400065a41194070341d1902d408070098130000d8600303a10341d0741d11180420450103201c1c0c500b02a600071a00340c084840181f400400310340055a040040150072840c010303442e54045140c09140c01c0c11a0407503240d45624000070255042100020301140781400c0010b91f242c0c10074090030440d0303c0c40c1c40400060307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 39834456 1250 39833206 39833219
    0x14030a03150602070504020319050c070b0109090312090204060801052d0c0703140f12010509180309060702041d0c1305091507050c0708030d0f0e0303061c0b0c09010801 74
    0x507820341c0a0280507070840401448a42001e41c090340c0c0c48110340c81d0400c4201080c0c01c400c02101d10648101c1c2c0c01010000b1040700788022440d80e90700400b80c07d00c081012501ca500c000b40792060206150190f15150841d180655445401400140c20f0002c020002418103107407004181e61482071030000001452012541529049a6584503e100040072481c14406540c225000d103202444004049001e010b41905c5080c038001500f400407004000d42d031194100740030044007640050002000400d800c80c4013160007000301c1541c454144c02c0d030742185c0355034880c80001c3c003902c2d80d982100d07030900040740c40844d100c20025031031201140a0380e0300814038a01c82140380075a00101d03807080c916800880700700c0300001c030388041590240c1c03a4641030707090908145074581003100e42d0340803483e40d5101240f89003070020390340300d01c0b506c42c02004400c203d04881c1c880d8040d181c1c000100194414030071b03848010000e041054102ca04103038001400329841c43c0c4140343c01c100d504501985c500054000c070011655 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 39835706 1250 39834456 39834491
    0x10612020306070e0a080a1203060b07030207090c050d021305010f020a0b01060e0d0602071101021015030b1003050f06010801110301121106190320070803010e0402040914030a03 78
    0x10103401a0241500b43d48810341581c403039244440307440d00100901070014841c0400e02107452100c0c4035030784450f4140c0c0403c0000701650502d40100b405000f0410004002a800141800031107124400128248031120000d444601036203a004407014000503510b04404c1c50302074543d00365402622081b03032070b90706540b049a41c4d4410600082c00340b90800010310100d40503d0780c1040050300240041d140f250513665031001c0c0d03001a00d0854040e46041c50002407586c0502c89801c0255541000b006241410750011111030000d01c00074240c00049000304401e1040d601400015603042021201c03161081444c0a84e5407400344200c0709113510b425041d04a00d903420701224100e41c2c2800c40d41040a44c141c503016400b480100d00507034040030420025811244a207103510901840703860001c0c41c0c0702c1a1140a001ba0790154a03110340386e4040210400242d254002d6034191802d08040d1042d5603101d01c081802460203003006444425140101743c4651400002840a8040c0c0e950a003c89062485000070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 39836956 1250 39835706 39835739
    0x106050a1a030c0f0405040216061b02030a0806060706110711040b0d0222060801060e0f07051605150c300c130504050709030c0b04050607030c0203010b030d0306080106 74
    0xa00e01d04002103851521454041c060078410110020314156039140001e040307a0050602084604195120905000041c8240b4000c8403050860840300750f04104025103a00c6541810424004030001107261522400151000c04c0e512070300421250740051960f54482d0000300044800c0d444040b624500740c142800340c5103d40101601d40c40f00b5030780d01d41c20000108102da03040100300e1700061040d0510f90f400c0c01840010310901000045803410300611500c0382c0c03001804103400364103513424001201d900808481010584120401a0051520300a801c280c100d003201c0a200380c0d440c083c4100d100190004243c0980c1181c3c17244502429991540a07194911040b1140718110b607001403109180040103121032264540040704181d103410005084800544110780003d545c000300741700702301e01c04c007030720025200c03c003500ca003414a0140042e1480c07150300001001c01055082c2901151030035000382049460040035034400c0d031980400140248120321402e000d035801d00e4400140d00c00140301070b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 39838206 1250 39836956 39836999
    0x106050f061804060b0a090b130501030b011202030103060c1d010e0906061b0a02031501080a0f060212070806010f030c0c1e020307060f12050903031321020106050a 72
    0x40199044010002142c204000d007001030015039288000d680e5035445200003809010540d25240c1a2010000b801003038590440c01d80c031902000a001070044150714103040310024a408208903100ca00100c650645001080c40d03118000f10011040012541041c0080d4030b142e5241d200940700c002c810313180190404405030100d00d600d03079841e200b42040c0b15525800b94010780a189044c0812402015142d04990454610340100708500d08515061205480e407201c070201d40c81165040010254444030702203001090a000f2003880410400b040d0141c0c2c0502060400c055043c3c40d02c00006050f0131000c030303200703400581c0281c0c00a1102e802031007803078840c401e541da6040c007051a6079501c403100310f00e486401d05511070040c84440142d50400101703001d010155114240a502e49401810702100c05800c00741c5a804c0104011920790008140c80d4406a00500007250314054103000c440d19072490f03000ca5000500f841c5802415405400040848605840204c5801d40c1d805844166458003201c14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 39839456 1250 39838206 39838219
    0x160503041709030d031406040207050d0c02040902040906150504020a0210021308030c030711090105010c020105070303141006020601090c0801050d060209030d0804050609070e0703021303140601030b0702010605 92
    0x940419006010319001c0010905031610340b49038840020316080440d03900398001380d00c40d80a400044180b0703640036000003080d40d040d811318285658058640c1841e444000c00c00402d031113180191354403600b28011854018004020043c1d4a0038042c002e0700e00311700d407a074610590510005950525108880c3e035142c031075001e4030010443d980d40e01c0195100d40c005c03969520341710345c02092081003800202000d0207842d004540c8c4080e285000035401c654186d02e0b91154001600400460340c0292222240c03d84c240b1300641c2e94030fa00e00d001da0003005e610f002d20340082d00800c108040700b100450007105451141c0c0031035040d03a9a542c00030040c5d0314201c82030b10015100d0001003009081c11070114201c14803c450260810499601007481d00b61401e08110026100605120500c403080c0031070340d048a0708001038011641041c8031481c2c1282e001c1c050b8001c042d40041c00c0c1030f118a1910008000d1607004811803202a0103491540c0c4d140804e00050741d1264440000c216103034014801d5500310b40024158 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 39840706 1250 39839456 39839461
    0x906010f1e0c020a0f05100507021f2601060212030103050c150c01020d050103030e0303090321070506090a0302151302100306120c060e01090e0f0c07080a0e0108160503 74
    0x1c41034500c410120320340502100d55640c0700143d540c040700764041d22144085500d0701d032801c0c0c20030605013202c11615050000070026203015858441d4003080c8081c01d00c90403003400303422140c1221100d21440000050035109500c00843d4540c6440c0241200c461354221040c0f0303200518940b034130744000e100081440e40301d440d0190441c107240d030504030481e004002c11414510180d140c1d60a9074005540f035005180d803040107004268111004501c0c4c10000c0e0f004608004000700800c0e0b88200c0c24118092082c0c803011841030001c1c40b0b4080740e102d640d000080d0ba1207414800b2042d5034a1103c880d00720054011140450000007005070b01500c2004420180180103016409001d41903100600e04030401d5243c0001060f072006403e5412060f0740300352201d0b04e03402d29101c80180300c000701d920100d0401490343c60802c0310079800007001b500508883c0f600800da40300c4081d006990310030080010090b01c004110144e4158201c80198110314080e06e030f4405680d50031251440707c030102402c140204005002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 39841956 1250 39840706 39840737
    0x4060e01090c110a0b160903030f230c0a0204110c0601060e030a0b010e04141b12190309091a06030403080403020c09010803041e0308160302100203010902090906010f 73
    0x125140081d0b2509104840f1030401d0035032804e00c120003405861404258003442084407044107002410213417403500034442c600390780d0000c01020740d5180c076808000c2141048803a08812229000365540d01d8112941d464513188080740c3c07600e80c00700b400d078070507440c0180d500d11241944049802d0110b500c4041d20300c82e070801c4c8090310080c00d8140c00b6609445612007550000e0013a180c030901a11a808084680f441c00c3d160070001c8101140480402c4d412101042d1007407500c005a401150a048400e098003520031400b581c503200b0082110840b0003503800d00c6005040d009100c00080d540c0e031644c10300001458507424081018888140390f0000001c000080c0402c1c45510100d0b0840c1c403d01c15504100101000610150300a810501081d00b002508200d40c9464601da04100c003442c8010400c060f00e15110b0240300e00030754214029440e94042030008040c828401000c2c4140c001200310340344d5031500403150080d04a049490f00030800900800c030507600030744444031580c0e0075079070b0420754210015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 39843206 1250 39841956 39841961
    0xb0a0509070908030301060504091a0907051b060a050402030f010c020c011101140106030203070207090902060403081c0c03060515070b010302120c04050f0601030b0a030305030a110c010c0f020c04060e0109 90
    0x1d0010040050070b91012880282c00d0000310300804c0e650b5038141c1c58a0404144400b01e54900e03034442c0c90741c6070b034428000d419101d0045040d8810401d04041e07449100440500e240e080c4003400d541c0280c0030b26401c0120000c16503002034000e030700036411110840c8400c0b0805003243c0001103908050f134003011100007103610582031030007000c1c450300010903c0b200441102c030112000781c22680100c0e03008001c112200340c1c10002d400c01804600c6040c80001e205801050306440b441c0400b82842900181c0c112441181d0140c1038810355440d5010400709050510050083c0001d00819124101e141c44200c840503044042d1203200e9000760a00744203900e15401c00081242d80203018845004007442154140c2d528450940b050041c041c00c04014070b4581e0005003101c03070380f024040c4176020303020313085c80071940c40b000340c0b540225454000144041d0fa500c10062902400c10400250360038807007803071750a90b44070094008801081d001c03940306540641c2004103a85d01c42c0603d100005c0303440010002e111968 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 39844456 1250 39843206 39843211
    0x3030103050715020f120d06030515040201080c070201080c03040201030603050703080a0f0f121d0102070f170f03182b030606030605150d02040b0f03070801140d0b0613020a0e040b040b0a0509 84
    0x1081f0001d210743c0e41e603039070604000c1509605203601310380008100a650f08618a07943c40412030186030324208966001030b05a00000c0c00301c14540c0404800101164001d500c4040613680080456034403580d0b03441d02d0a100e07071200404100141003007000c40a403a0084d40c4505210405072a0002280c822080d03101c02440c983d0041c0243e4403100c030103140c08060a01c02408d99500600402280741c0c564240080c103940f8003021070075100300811000903a01d8814090343d0b00107100c8111030002c403044402d450310f085050852004603001585251620580740e101416050358191801c0c400207586a0082d0111181e0344181500135032100c03010740703502c45007100402c0c0411040d6030050500d6101c0800c0107060b0002c20000c04400700c00824800350340e4000480e14010704a84503010345400c07440c8080782444484134001400c1040010102d001d075aa0b809001c910f030780340d2a10440d104c0316000e0000349040d40e402d070268002d6281c4010b298003800c207070050988000d006070800e0091803419081c0070095000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 39845706 1250 39844456 39844477
    0x804030507020415060905040b0613051c02040609020910030b0906010c080418020c12090d11040e0d030b01110c09040b07051b0a0c05010507051c0c0503030103050715020f12 76
    0x101c21104214980c0134480c030003d000c0c80d40c1d40b000085c0c1854244011109000c1c203441c85050140301c5000070f22090070b100c4050340c800350f590140a540c0c500c101900c03690b090307000035403140c204400860a0001680035207030420303048841c1445440194000c0c2c04965030b980e0b419811031505c0f4005401c3e075028070185a40a1b00c1313101e080c0e141c41d541ea01403005212000601c01d400640000b50065043d0040054940d424110a2460301d00074003040003848034a0005030007070800381110110201580c660303000003482004501952140c0c54010402001003080c800890b000c1032103599010303d500b400141c5031300b0009001c0c001155586464441c000030307084c01802e20341006000c0001044a484101540040e808000024590183d0a00d442a0071110741e0700460b04000e01880401d0121f100001c00c49021411440d0503164610000c4003110302c18184070303000c0c146e440000000010404005241c0003111081e0182078440003000748200c0e114003142e046140b06600c0200703020400d42a51004081c022134 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 39846956 1250 39845706 39845711
    0x60b060403060513062405040b040b030d110601090c14091507030f02010609020306180603071208040302090a0b010203041703041701050a0b100c0f060902060f0301170601050108040305070204 84
    0x1d6030b65615054034821565101e0342421210000c0400c0650b01403042d03080c03200c071181e0303640312650121042002002c0c440c4a11880d2a6503444190792182c1d131080c3d208410190644011a05141024100035882c1e030465045200380d0b800003822440610400ba4603c141c0d5542603050001034950300c032103400c043c0c101540005299261205040c11500421040303100c0d41701c441d01d004c441c1c507000e8210361807580107200481c0101300304000c0740e0313604a10388500d004020945000d0307242c04001c00d00d04102b030b400021005a02080903424003d400d0043c0085a2080f40c2800140d0303144201e000c00d46074644602400343e40240014003014142900081c1107151880899003072658031180811403030303084880c1002c41d0755204180615600785024204a000c002d40d4280207044070504000c2400049a0020b001001000c00344c0c4e040040c680c1150020940080c25252100c0c414600f0320803950083c41080701100c2410403c00354000d02241d40350486105840d440c4250351640c80985541d402520120313400396 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 39848206 1250 39846956 39846959
    0x8030c04090e06071701050607080304030909020a030b03010b030705010806090a0e1204030618020108070f0306030606141008040503030c0a031d1f02071707080c010216030816020a060b0604 83
    0xc1c03510035403654140d26002030007181050303280540081c164109820701c200d0321000500043d10385404448220750b00c01109650380e510381c101103c0340ca945030883e40b004c0e8000030703500106580c10740042c11910001c80003005002d968a0425907100c5070ba109450118608200207103051038450794250b171008045201040f081d80f40340d011420300d07200355400c07140b454000c5001e006201261058200c4203d07019012511172045030006042038500611610070880c007550402401d80c80780c0c002c1e10007540e0045051013441d864116440d14150006044d030b026040d6050300c1402240319101090046800901440ca10380390070160758031950140c03286605154031a1841e0f41000b03d10ba0340c141210300183e01610540c941e00840ca10410070b1900c1140031180140820380200794801e004000e07001c1c2ca080080d0b9550444e20f40400c4030701503140400344035480440d02459044034480741400491003541c0b2044207070b40304a409012004400400d00060341300c0c140000000d440c7d68404031a6540040c0a50700b0603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 39849456 1250 39848206 39848219
    0x140705010c0507060f0b150d090f0602030a11030103120c030e090f0114030d081305071502030316050703020c010f030e0307080c060901090302120904060f17210708030c04 75
    0x550900c070352240010000500101889103502c02d207080f2aa050806010060321031000407241c02d407060344c0d1194500001145450003003580d102041d501d07840700d6048806030b810304141e0000e4004880b140d028504044218248140c0981100c1c16a640f01019481501c500d80301118a4140c02c88120144200c80320001d500307596074074240784246101c0321a000c0942c10008050340c810440203030680250300410074141c079950021000d0b903205040140c081c00c1c401e010704006140182560045141c0e03e2a112141c5100c1da020000f144254143c01d02c04814403890754040714184a56840580182c001e0121520b5a6108880300406881e00b0300c1d001c611100b100d504a402c540c80640c00f25841e401c005269000c1040a214180d4407a5040d0000c003d014402d0b01d001c1d48401c01c100340e0486001c000a600b44866659a01078400b811580c1080814140c880001020004000b800c04030345124203d0341100b03405d1940e00c0d0010103003492403da400e004080c0d41d64023030340c4c00103441000000814080403c92 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 39850706 1250 39849456 39849461
    0x4020a0303030c12050c1b1f1104120305030702010606050316050901020c03100207030206011706131a15090610091202010504050301050c030f0108060601020c0f0415060e01031401050306060114070501 88
    0x1d00a1090700c6c0e60740e500c000c45944200361041242044c140c006503a02120010804411803500520b580040382174007002c0c550403514810340d003001c4246030441022005060740324001e50711804c442c0e00200b20f15611403000751410b00084882c04020552810901780052003100604107070a41801165501c41ea0360002a0900300020845078440740e012034038005041d4100500d0b0300500c2c000c85a50102843d002e11a600c44000401d0401000c03004400041001540201c0340c805c014105001e003a141880f10b13100c41c41800a908440c400e07030b91000815018034103010410b04808840d21400380151070400505c0c5104100501641401070078000094141c4081c06068411020510119500d00e0007403404c080000040c2c11548042c0d10170401c014903a40c00041702c21901408681280414a000e0300040140404007888000d000e05410002002c940100d00d0048640d800d8030244401c000074000540f600009114455042d4044408245254055048401c0564005900758641091522031a0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 39851956 1250 39850706 39850711
    0xb03070801020d0b0103050903190c0807060b0a06030c02070323010516030c0c030203221205010501050102010b10140c03130b031504020c0a060b030c0d0b150904020a0303030c1205 79
    0x31650000782d4404490761a114240000001b420704105074241440d102d6902d0281c00404800591000c440c0e00c035140c014106041e006911000c5150b03030b51030600e410006403166281181c043e0310300300e80100310f040c024010ba04ca0070140e54010b11009107940c407411010340f0702091a01d40300c400d94102c107995440a0007517510404202041c901d8400484200400b00c442c03019488080001c0a01c851b00066030110031a10100d601c0d08000520310800020200c050405074440f00004c280700c090803040000641144d41291401d8000b0460b10404c0f02c140030072100314440200000384c125014288582d000c40181003c1c4132107100316801e05480d00c0394503000e9030309500702e0f101134540030082140c202e901002050a120003514150300303020180030035030f03580e2502120043c40c258458440c3c1075242c4040245010b405070081107010001c859007003c48034450103603011a004851100b840b80d890622403c1030b0300450b8007411b038030710242c0b8545084005115031507442c070800592810a07070499081d03005050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 39853206 1250 39851956 39851969
    0x14091b0d050108070803120a0c02031b0105040b0a061a03130f0b040c15080c16050106060c0b0f0c09060d09060614120f070504020a0203130303050c060f010302030d120b0307 76
    0x280c40d5040c10801c610703103130003503102c200250f104109080030100a44642c6c0d801000d00361001c524503064150607400d500a160040c1c0700e0b85842c0f11303480c0250030305400003030040d401410a41c0d041d0312000d01403001e0b9001703801081a48440c100d9a00d04c40c55080000316840301d6005d0390485a4a02e565034007214120440b020345000c50b80c0000e04c402c3c4441c1038000c0e0000c01440b02280000611010701401c0e6017001000311500700c1c40403c00303401840c201c032401e006140e48030b0000c121250321210080c0110354a81b03000d0710690f00da0800102001002c0380590300580c13510ba400313802c09640c0010008e40c1c0d40460010400d480d00c944640b00002d1342c03402400084c0036044d00e03409000e500d050a2140c0720002400d00c520308c1e800b000d4a809684408a130420680d40140c0c0c001daa42e29580409030300e9445910314030385030b40c02900800001e040d800707070182010702e117483c09840072510b54810015095100f070001a40c903400200271070000340d008070359603010b5030403055001c07890b4001000001d0800055a1049 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 39854456 1250 39853206 39853211
    0x90105091f090806060a030f08090909031c0209090a0b010507060c051209030304110114040b0c0a12080c04060c1707030c03080105030111070209041110050a031514091b0d 75
    0x19124182c202e56940080e040e000700400903860020001040080342d880040c00c218400312400d42030144907400c80750000d00140c10b1070620300b80328a0007556680003a80b024010901c605150400c95105d008494180200401c1180540c484410b19002080a51100c81c1404020018400000c035180582c0700210025207540351560a0420710f101e113810010514011900b0070000c000004074040e0011844460a181202d58003240c128a100035100d203070003060003480c001c921041070b000e0010b4501400780c807840001c0c11044031444260780180041e2000c040710b100c00d1009004030340c4240c100c010218060401440305058500c0d01d00700d1540031440c154001140b1061150605800c41c403000d00420b020380080004001400c1005c04901400728021f110f400c030540440d003809101c01e82d9986a90004081850300c261184024003907a00803580c0d01c0200c0d041c0501024088a00750842040359045a41500d061404d41704101e03121000512081204102e516010221580807025191201018000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 39855706 1250 39854456 39854509
    0xf0e06120a08090307050a081507030f14060a0f03030215040501060b040e0609180a020609030c0301180b090115090209150406031a04020304050309060c01110a1d01030b100509010509 80
    0x9050801d07580e90070050198030501f03000c111010b070020343d120030000d14141c0c0f0803403511000c20440281031f81300080803c050820141e8400210006207240c000c0c1c0c0101c41c4ac0c3c2226546545d0007030211407522003e800b5070800c07000c2c2d41c014140e0f003890a0384148258000140e05450f88040c144503005074020301094800d030810440c072418002049900081c2c8000e1110766951800401a550020803000074011000852548525181007200b07080c05100100240189480d1180a0b094071503407407400d8800c40c014030042810500c0c103100f45440103001e083c03444102406d10b00550302035403003008050f402525498489800300902d00c0608080d08407544c010903000401c400c0100010b0f0b008070814440c034410014070000035000821202c60840644a003500c0f028543c054a00402c20711420b010900d4000482c04116680701001c00d66482002d801c4211031814640114115540303820115007006880312040b84090181d00a0b0160310f40505d060b904e00304030480840e0000101d811460100d8106444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 39856956 1250 39855706 39855709
    0x303070806010e040902060f070809040c080912030708010303081f060801050a0b160b0c07060903031b0807020a0b0c0408010f1b080c030408070c0b1603180f0e06120a0809 75
    0x20507090610125000e000c1a00700fa00002d400e407240a0000780310008c0003890308100002841581c40301500180304000004800d48040c0904c4001c40741410107015001e00485400c1d4400280c034028007240e03461800c2a82566811389201c0c030040c01c024030b00320720b5882c0c6801201420308107034041c09880e5100d00003540741030248401c030380e4503400020940c03c0a111601224104c206e1a4501c642c002480f21040c0d126811820b149100303000b40600014100303d106814943c1640080c1ca10f030a0009401c049181401d02c1121204010341e045001a084040c1090101c0d140d21411a00f01d044005010300e0555a8000345086604611401c18159220603444910744d8500c021440f464040b42045402440d1805109060f488001c10050055401040c103006010540000501810303040910725a00d1491907044000d82140241c120300044064109803113501c516105941240c03401d0704100c0b80d541c14807601d4605420f001300750640100e40c4c503800ba04070315400c20540d00c805001c2c08540b55100d10000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 39858206 1250 39856956 39856967
    0x3031d150c0c1504060204050d0501020304020118030201081302010201060510090312020601080706030e01090204021b0601060302040503030d0b040e0a03120627020c010b130f180b06090408040305030307080601 92
    0x1807030307601c0820091000600c064800700300d00c005412041c40c2c0d020140d0300c9103081e0b030080c02260030050708402101c05890030003605500940c007540c000d8072040742200200d44082c0380140c40d800001d00090340e14010403c5881030038442080e00b441400041503941e203031008600402c42d04090385000800c061410003d001010000700c4034143c081c8041c005540c14901c0c00d0781d540b10603100301300425558240f0680000c1083d80417a002c40d500030425541c0381c030324079140829810b017201c4460ba2401030320000600036010b84210b404864019002d942428070b5208000024004820800c1e005030300d81c11403e00ba441e017848891680da02c80d0310761901d0001d0841484040310460f41199150b01103501e0748410400240c801501d514001c05e001584d945a94480c0c1809010480314142c0c20460362040c0340038405003a00300d1004542e80390020007405a06a10401c00c202c03c810000e0988194503000c1661800c06d440250741c040e00694030b42d0b15255a0303035034943c42e6500c22982400003071254001d02140790ba211 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 39859456 1250 39858206 39858211
    0xa060b0a020d0318022101020f0a0302041518090207020607020301020d05040c09090b0a020a050c010c05040501030f050606040b0705070e0f06040c0c150203130804030b042f01080403031d15 83
    0xd00010710f1511a408034124811204020414441d540e06d40d07000d1030317825011a582c01041700308817030302d480c42d00d100940a0341050041c281e6007030810182d10840d600c1800c85c9003406480d2501212081d1900d00660002c2d881030100fa6000113040242c07070090707102400108201441110005118601402d1441802180d070300f0054101e801c081d03081001c2841e40c10103540100341ca0100687d2055851400d441c18402d80030190301e03650170039492420454100c80036208844003a2000c3c02855142c1c0c0c0182c081f144115a4176500080c03c2c081404840e00400140001c5c41c45101220851a2603903800040c0a10454080d070a0004c4041003095034201070080b40c0501d400d9003030102074039210340d5602000e44100384030440000d90201c00141e01c44209002100202c0c0c00210302c5d41d0340e03500e90400300080042110295001140110303001040c0000c11109503c585c4440c00b54200035000307030011100d811020704194205a100d2a00f500e40703048440b08680c010b00303060000c24001140000100044100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 39860706 1250 39859456 39859481
    0x30126150103031206081506030f03090303072a0909021c151a0607051e06010510030b030703080c0607020c010f0207060c051e0d031503080906030a060b0a020d03 71
    0x80000c00c000c40c06188810381540e60604143c00041d01c5107401d000100003560040c80c43c5e224040542e1414561341c4c6110780a00816003c1c0e0b0303a004001c0b040755031783c0e106d442c0000c0d402d0307442000303604041041c01580c805030302c021001050280c0401c4c0d400140c0c209445d080039124070b0340e4840d1002140381640e140103001a01400a01d0b0310f14040d214082c0f1071540011010507551122205020060f0f01c00c0020f01088008010545030001800c0c0190f4a6286020310141641d01c480c0a050340400001c0d42d504a880c01004c030391094800c40030850140070300032142e581611400c0001301c0080d8210b00a008901e51030802803407a40381580c002481d0a260500303881c14400001d1001031069800329003001900c4082c140407c500815180207468240d034510384d120b1415001c55031003030070701000c80c5039002840550345c20b020003c0c0003015804045070a01c00104007050800030048035052240144d03a21a41c85100060f003c0ea5a03580301c411640420703201d02c0185c0020a902c01020380501c192981e0b8240d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 39861956 1250 39860706 39860713
    0x801030201050d091a07020d02070807120807080405030307060b0415050603241314010609080a06050a0902030a03020708071a0a051b030d0605122109010311030126 72
    0x15503000644640b04039040d146400351994075110611211098500d40000b6100c1311905a1a001500944804625004000500540d00c2c0041e001e80c1c000380a00960702c10348440300c48210b90b81d1380c14103030b03520410080380c00311028040061180c0d0309101401c0198065100440d4801d080300c00c001c2100d0f1404802d00d54001961001c4c0301641b0781d00160381d80441c1003040401102107100300c2c21a124a400728030340d8824801240041c0043d110740004a0440c0304805445107039898880c03e4840f00154000c40c0095804021440042015500b00c5134000f40703540c1c400201080c042e00482d08040e0201420350140e8414901003280401c01c02c214401000d200303950000030080c4482c0d50a051103400e00000030801d001c2000d04c0e01d00b240a441f44500c40700407048a81e40c090260040d005007900b48102c0303216144a640442c5200b0b0003084015071780d4082500740400c01e41038116520103030010101ca03030405070399040507441403c50900444c06800d011481e404000740003101c0500c6032100081e400781540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 39863206 1250 39861956 39861959
    0x7080702060921090d08070506010b0f0703030b0a150305091c1409030c090405070302040f0e0303040204091103011a0a060e0901030b0a0f020d020703020f0102090f0d08070b01080d0f0801 82
    0x20300114000700d1982203000003d40320742d600800c08802d80205503490303a02200a404107402c02460f0002008a0781c411030a60321941e0ba01c81e28280140075441c0b166050301c07020441c44000074884d6216032072032000145402421902c48a81d041e41d512400c074030a011a40d60424400020010490100507010315a0302c0c40201c400c03c0c80040c042507203000c40b2082810080355003409a542030040421058020b0105150340ca001d0925a50312107171480264000c07840e103145107082c450203000e18140f1100b050000d41ca0743d01d542e405e000040030050015540001d62540d18074080e034003801900c810000b0014a01001d500d0ba0b010803061456507400a41031200058112103682c1781c106807035045170b0700a01c46941c00d036502141c000181c11001c4241c0c0300c151000030300705441314681c2c1c0603001a074042e41c200d400c04080600d500b4201d104520589034040c0f08210071030964030780b40c1e00e8888a90711988600f814003089694a600c143d0382a008948150000c03c400b410707040c0c1c00b0810340c234035000c00c1c5002581075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 39864456 1250 39863206 39863221
    0x90a0c0203071b050306070c031112040e070c0501110403050106080f07030305030a0204051306090c080603070b0702040b03010f0c140301060525050703030503070e060c1207020a031202060708070206 87
    0x20b1142840040000949202c6400010305400e14a4000c00010341510740900e0b0000303005041f8428418102d010031002000b15002101c0018034440c01201504054605402c054540d5110f04c4000c2c519402c110610341302c00005882802000c03500d0385032409142e250742c1075241140c2903c940744c010708101d52004200240000f000507101d02280d0f090301b0200e580e515146c2111010b07110381d81189800c084a10591385400c0141d6005034100d07100d6060401840c8c040c2007007103400401c1a214a0340c56440b91100740040c0aa03100208104c91000340000389908101c00441c0c2903569404800d0229556640c43c2c100d1207401048402d00460442071280c130303560401801030454014100b00da41c49050391030300480380d0740079201c3d2a4082e503084030407107038100da4078a8010065842107829a0010b0b1200074480460b05010044d940905c4203e0064207050f0400110159a5041580d0603a40101107541c00004286e001d0013800d08019581d001e030070303180340400c0c010700540c002406000440d400b00c800c02011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 39865706 1250 39864456 39864463
    0xe1509090a0f020a0e07090f060c230a06060305030405100c05060a050c0c0a050c0a05030a08160602040e0a0204091503110108060a0b0a05090a0e090a0f0819030209090a0c02 76
    0x35449103000644102c20b0020900c244880c1c0c00014120001c1420f00c184107804c5000c5804640a01400740211511681c080341d100304012401048520002e0340d0101c0c180103140001182c1d60b905c0300f09c07504600103450307003400d403501a4815681c1e80c20002e001c0c4510704265503403188105d0b00d4101000c80c8021542c0c0d444d0355600c000c00b0061007075558130200740017208030070494200381903a00481e881c0d0b0045041c42521403042e08102c43c441c0d504030000207040e081c040780f818031003030308440a039040011122401941171407901d01101c60075030810000c00ca40034900e403110f0007411a0500140c59900b00012201215840c2d8100320f400000c41c03500304009102200e040101c51004c0c0f03403400c3c050302d400010960040c9030350400710b400c40001c02e9210f0129417010280070890070440d15030800c541e035110345041a04098814240540241480001156170307149081d40c2a032042a07001e02c1c22605c0186800c1c5030310351648440000742c0000d581e135440c0c6450001e00e50480f5880304100300031100e46601175079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 39866956 1250 39865706 39865723
    0xa090c0308030405031207031d0607020307031d10050a020106060c0804091e0c0e09100609260a0c05040506040605061b010e0a050c180709030f0f0c0e150909 69
    0x400e00c1c004000b8003000350600982e13005030ba4000b0582d10f513051510024019012079411084158240ca0001a1005000484501901154000d5407920f580c0d500c08643c5000030f02900b100b000402200203505481c1e01c61041491006076680d103031202481a002800d4805580c4241c04100c21666041c1c04102d50008035011610070748000078000e400c2401074014154000740c4c00d0055071419001c101d213150401d1400000010844805c0700707507641c54070301c2d02c020b0307035940101400646a11410311000e610b00f0300c1804190310054001015080b0101d400d403410500205c00c40f1210100d1000700b14074149801043d4000c8070864040c4040d5045c040428500d020303144401d60701c0111001240c00c0c0f07010a501490f03c1c4040e50040c0c4042c0783d9035061099032a4802140c0600902114442200845400008900814181d41c0344817040345192602810030301a207809681038814429200d001420a1189074000d0018008828483c03401d80d600c0ca41514140314040c2c00b0300c0c000003c000d1200b001162a84 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 39868206 1250 39866956 39866963
    0x90703020a0902070201020c04050a0c03140f01031211030a030b010f030c02060402060d0e12040e07050a0c020f01120507180f030b0402060706020c0d120b0d03080402040905010209030709090501050a090c03 90
    0x41e114004c42c00102d10b0100c9403c405a04946000c061044000303054102007024074842c3c1342408034034001d030542d80b80c82c0bd00b03d60500c0c81109500051000032140800c0009601c07072454000c10025400b03860a003594445141c80c3c011a0b40c5480448bc0d0707507080032070550080b074142020001c440c801e02c1d02944034640244001d02c9504000b90710001c0c1d240310790101c0030008014040740c400d8071241180c0c0c5031799400790103500405c0a03503034005030010340300c0c0040301d1901041e85e030303103a58200140c0d09004140c9100d104050503c0304001c6100904d000c40c0c4103081c403030130080d9900a03928000c0c110003a4907103a9a0007a0a030110214414404560811070941c0c0042c3e0540d0000d0f503e07600f03030800320024025221000b01130301484480404041c2d202007840c5a030103110350100b003500e180d10100720324090a03550040c085a49800000e0151405074030200d11240961b001610f40700b00400020300704407041d00300f209041e80e1403041c6420f2240c01d00c5116442485502e00300006556901c460f4100850b81c071004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 39869456 1250 39868206 39868211
    0x160201111911160801050604061707030b0408090d0308070e04061406160501020408061905010e071206051c0308100b1608070204140f07031a01030b030a0503071a090703020a09 77
    0x6042c1c80c2c1082203250100d550015604040d01d0301c402c11240648000c2d0354452080c3d0602d440800e22103149103080c03986008250080403141c0c034564900300200c0c0300600949090030305000e51348481d11400c0c10558000d00c80e946041e000e181a0401810000840c250240a1840c02c0000e0007403d042070b02e84252083c0854041d41c8550300b260912052406408005046500200e40090b0340100083d10900400c0c404a0f07070b01240500c5042403080394024899001100304210210f42480d000313102440b40804440c20100364640c451010903041c0f00d1080ba0441c2214081b001002030541c031004103904184013190314100701d86802c40821490051944040742e001a180d0302800300400304c01141c1c0c0b895809041030255480c0d903045546809402c4031514860100c00c0d00040016100b03200e04240c14510405104000a00c80c0045000f4180313045000d41610800700c1000124504001400910f0301c03039120b42c042d06404101b100030045c0d020340708050b182e10248050005955240d0904117403500301a00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 39870706 1250 39869456 39869477
    0x4020f0d0213090506090609030c0604030323071211070c031704091113090b100806040e06010816120c0605030a020f030717061005030117010902091602011119 70
    0xb07000201408040c46549103400b14100030482c001c01c00c1e51040c40302c101601c15991b5841c860f1034403413140c41d190664a402071800100080c0c000d0340456a110043c45400c80300404801030340c607610a0568080c00803600084107c0c0c00d010503405401c203070b4104140d1003801d2648503640c0052740480c1d800004c00c080020441e0388400b40142007030310000e200f500d2040c02250f50301d0784511040d03440303003201e03030100d5034501c60205a4075000c0c000e00b90f8004000c0c0008140340c8024000b11070100e4060812640943c44005850100d6010041c181c0030300000405009030960040003e03000018070b030302c1407081d030038151090301c041001d0060100817507400b07040c190703942d50702c02c030707000c8003e200f1401d03400d8405602100340240207030700000c20681d44800030f040e04000c2d12a08200703c560060500c952000030010001072140c000940455141c46400303000100b0506083c0d4005807500b02d0840d0260031450803841384148032642401494000d02c142011a0300d000034a2800c402d400c8600e00e4000140520850b8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 39871956 1250 39870706 39870709
    0xb1602060f070309031104020c06150a05060c0304090f06080604030302031e0414010606140706090204180b0901110a1205070908060a0204090b0a051f0e06030103120201050f04020f0d02 81
    0x4880d0030200716000c05903a01c1c168603000d46420305900040d40e000b040c401924a56003054803c840c0e200e1600d000a003aa42da40340011003080790740c1c150464029902e104000b44a40f02c0a01a00c0d801070281d000d55150342c00c01e0b801c1d00440340884481c210307280c03c0c0030b01084074880c045003554200c1e40500e00541d4076a9800c82c1d9803084d5075150310082e11145508104030500c07842d0310700100c01003440c0700240440341d9203410455821034224102075650008001900c0010b415500610b08a44081d10105502105d900703042011400701d101941c80700754400400c04001d000307106045440c286100154144074032078100a0507401a5205541001e07611404540c1a0b40a40e40c440c0040010600300c0c1d16529181107481c01a401a01c25043c1080c108003942c140340c039000d24000d0a403240548018144001811034182e011800b003042010700540c10301001c0d107601c0d000d0080d800b9501401090b4100340525030000e084400040270440000c080000388001a075a01480400c2c03a007044a40d031100c80010700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 39873206 1250 39871956 39871969
    0x402060703110312060415050a050f011106070509031618020304080706050703020c070501020111191106040302070302090f130602030711060a0f05090304030c0603020f0910090305010c05040b1602 86
    0x10380c9450500c408510070107200102c1380050301c0b070001a9000d10408181020304401d1700000e000d00c42e880031751481d042c000c42c140a4509a80c0c00d10515000c0c2078800750544035800c05030141c407032000003540054206402e003410070480d130208003600c4005040614080c03038800403042e450b0500c100305030000040360a0002c1c0006403106a0380000c4200b00504021034003030020b600a41c0c11009602031040e0006444d8010b1084201510b5086d03003080c6002841d1a074240d01101599230300c401c0c0844080c55034a80c08041007101d100f54402d4006103202801c5004100400c01c0041c0310b0902d043d116400c002442000300341e000360785a4000d00260312a10b95500582e01240e8080d0030b40118800c200420044a01c08c1d00a610409407181702040384c0c0d2146080c2a450b4820f1303010240c070b01c03c4c8500c41000580e111764000c2042c1c400010000e07040410704000500344d00c10402214001a404001c14010301c5000c0c4100b10842030300d410018a0145000000c83d030314051980d0941d2014440030b182c030155240c40b07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 39874456 1250 39873206 39873227
    0x5041d011406121209090903130b130929060c0109080304020f040204030f0807020a03080703050703020d03021603080a0609110408060f070801032a06020102041a040605030402060703 80
    0x100240060601c01210503098241281c94503c51072604181c061403020100d0550220b03584488202d01c0d00041409220035000080c04c901d20611040009004101d95558130002922080c81550340d5240444410b42501c04541c1012040034030303008048800f50032524082c0401c0d00c0045415121101d0480003a004d4043c0700301a51042d42010082c0e07081084100c000e6210b0340c800c60301d0055144a02062004900840c00010a452051008a804101d844c1d01030030b01244014141c1031000d44035a2880c443d0740003a00100c01041c2d010407400105601031101020700002440e04500781040c03030301d40c0315508036610005070500c130000011495981d40c503007140e0041c00c1100400d0102c0140302d030310030b07205610500c2010070501230400810445281566000d010301c0d02035072445526400d43e01c405903d50040c44882059059504d0743c1e02c2c0b200c0880c03608200038400c2e5000142c4807403524040d20b004404501c1e81112940042009000303060b005020380380c100381c06681d41038898105250a03a102c8210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 39875706 1250 39874456 39874511
    0x18010906021318050708040f050109051504050d170a0e010f020a180b0406080a050606070b0403081602030c12090325030312090f0212011409160509100504 68
    0x5411203041240110b1001240c540f44100c9240740d40300c01c03042045510989507440018406804a00891910601958014058030001600690aa41d16450b01c4002c92600758002e000d281000103002c0e0621480b0103010580c1407122400d200301078104040c45000704203e44807030390364903040c5820b0400d40c0305a064072a1580704542e1080710641c06040001d0308910100c20368400600803540c4140d0070195400c981080c3c44142668658010100140c20000c3c80140c0103801404198041011001c0381c4e4000c2e40a5214900c0a040c404061240c42402640d00700540d442044220b403080400140146803c00c41401b043e154500a8002820112908000004094000c050381d04160000000ea012240703e5120404007090750061401520320403a0094240901550b551002d0706040351501000c440720000020070803001440062080810b50719248650b02034240b142542218140c2c0002800d012148654036281c00f200501c0c4203101406810b00580c1c4a14500384502800b94048800191 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 39876956 1250 39875706 39875711
    0x70305070f0816080604110d24050c04060e090615210703090f061509021605010b0405090601060c03200d0305060609010c02090408220311031518010906 67
    0x1d884901101031105030003034810038020f242c200b02c9518283e02e0854221200300010b03110342c0d0b6564440c5240c11810032803154201001000e560009141c2030010041c500403511130518211003d03d400c0c04980004048120141c010402800000d801038901c11b6030f2034007114080ba280d0b0303c1d040450b0103410300d401584090030740400c408021550701c051400c28414407007000c0c8a80e03038480400303d0941d0081400504880403140601b0082003035900801c407615102100d00842d1656800d503102268802940125003500c90a07111041040a000da021802c80440e42403100e814106001621502c041c0b0890040c025207520680c2010302400d41c03520400e203a120108800003810300b09a441c0d0750846200d0700003900d040005481858620155580c030350069442c9440c0d016241c0c00c1c4140040007500a813280001404500f6260300700380a0030303c45d0851021040b10080c5903117443c03601406c42c4179040348650040f00000541c03103403510683c1c0d88906070b48140380d0740d9454100e403e8011305e02c0d080040d003402d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 39878206 1250 39876956 39876959
    0x40204080a080a030b0102071401110f06010801090b06030d1e090b1308160f170307021504150302040305030703120f051f05030a05070504020a02030c030c1b030c030703060e07030507 80
    0x40c102003e002180d07642d48041c020014030700300482e00c80083d4094198a80155008003515501c122200024404103074100c03a4031039000d9010601e49a4241e01c01011b681d183c174200380820020306080c9030044000c3d0010004812400c00c05031901480118802010a038407640800360f51049072201e00900710000815a12680758440801900c45401104183c2c452002040041c0c0c0002d0f007c0b604642c0310610400415080000701650b01105650705201c500c001c0c0051070150340c0302a45548003001e00e5540790b603624541080c00290204146002040c1032060000b000810800b20859848580c1490595008501c1580b060001c0c4145041c115051789404c1c100310158030f181469506003d1980e0005031410756031310406a80c5d601041005002c1d4201c030100f0001d90400f60060602030b18240140c90521f000b00341203504d503170410b01c1d5141c10741c1d00c151a4141030160500d0011701182043d0003412030340e2892000f1982d40d008600c802022036503a90998401144140004400f85078010103840110b07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 39879456 1250 39878206 39878213
    0xc05150106090608090a030f09120c0302040605090415020d0b03030c030a020d080103030921060906090b150a0e06010207081f0b1813060618050915060901060c020109030812180102040f03060902040204080a 90
    0x2f500a80006ca00842c90020042400d1600341401c920a42e03100100690300c00c042e0711000c000e0740002808103045a20307943d034034140e07075400d0002e0b0034041444402180c6131100b80c40024074010103803984000b03020380400181b000c40d40c080038180a4408002107405000d80130484000c11340701e41600900b42501d052102c1e403c001d0b07907400640d00c05e8001e5041c81600e8840100d407000071510800085d501000c0b031642008071200c0c000041ea40000305005449000e95200001e03810030f49041032018103541c80302c00d942c5086d402449242070800d019208021031031600d5a049001400c0913002c0c1c9001d15043d00c4050410409402c400090448502034006c01c03d00d00108001500c410f0b50450082d00070114001030a01007442b44601c50b0000400d2040680d00c0c0041c290384599420100360304000f461103010022404280007080855003101c100d208610307004e00080b40c0455001c0103248564010032041020120060010301940c1d00b02100155603411403001800a2003998080402e6004200d061b4051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 39880706 1250 39879456 39879473
    0x50d1413060509010909180f05030910080f010b03060105040b13080f010b041103040203030f030a0e070e09060702060705030105040b19030b0105150408060a05070c05150106090608090a030f0912 85
    0x210b405e8803607104240c0c0b105040c105071a40000080ca1040703c0940410118504041c0680c0c0380c2c1c081d109a0f40342809140100300362152044181022600f903800b8408840b44003001c06005100c4400360074114204030000134654421407042c03898220300440c200b0140010400824005d02100e01100d0031002c0c5000d209000e0211054018420ba00c2c00c010040c1c06507a41d01100d1046a009001d9450000502d0100e036841e04050540b0158580d541020144042d04000410180044400700081454a541003501d410001844441150840c60074409041c4d0410281c9064503022540440d00c0d590140c00304058401e0490340c5944001c440e14000705002540e0140760603200c041c1d44040004000801c803141350f00c104e1058159940c07002d000100c3c00000e81d80a5500403800d85440f450305500f1f80c482c0e611b0244140c0c402440d62080c14010010306030408001d0005240c581400801446c181e80c219460b002807600280501a1071030900b080d01d80f02d2844800546215001011510001d092800c1c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 39881956 1250 39880706 39880717
    0x7050c2b0906140a0807050d09050303040b01050d02010f03180f08090109080d080109090215070302060609060a0602070312200303041109161d1011060112050d14130605 74
    0x20890446010540700d11034507a54680c3d4004095451400201c03000803600200014030501c10840d0502000410759980c0c0038481d003050003400216202d04050400e10080c01040c3e004510030080303080640c3c010303600300e030030100d241c210781c05d002881c10704a84190801417000c2034002d200d00d001d2280202000101406041351031b0081e0380b1112016100ca65a580d00e0780c0d91504030303011854020040116072405e821100d541e602c0500410014082c8901d0020303240c0221008502680081d002c000040c2081e00c3c0860344030380708403031200e202490184080d480e03600703c1c000500112a14440d81112034041c000c9130080c564400c080784440140e00c1e8905445c0d40090340c6c02c5410011a603210328003072411000c4240140030205040b443c40c0e20840003a1480c480c0005010903c00d1100e14140056035070101c8030340818019140d2401401300c0c004150305000301604405401c01d440740d8880081200007842218824503814601c0d01c6041e501803440a900480d202181c40c110100c03008142e05612202502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 39883206 1250 39881956 39882043
    0x1b0804091e0c0804050a06050c04050a09020703030f11071415010f03050f06010f090902041409030d0f0908090d030908120415020f120904090f2301021207050c 70
    0x16450b010070202d41030039054a0141207548480d40410104100d0f40c84145c005203080711051426540368081220601154042c100499002c240310701815014000d00340605c0781c0c0d00d020800d003072110b40c542d031044c0109800900036001e4119040100f9008100d4560b4001c410003000d00c207581c4d500261134041c02c07540002c0b40c8501a54264000890b0001520782c140c8102e498070001d1141440240d80041c054044140e0b40952503032401c0d12250400c0a0050060711004081d43c2d49030b942100c0041a940d04090f410310403498281b0440100d41e103078040c2e810095044074035444405e107030705046448882540042c0072a00802410302c070f81600c0c03040204112401125440d00a0048240c20b98031141010b59051700340d0402c4500c4815034401c04000e011b9920001c000041d4034825887c1c228900c203682104403061400300341078010f00c41c1c030200c0c9d4405404449000390321704044001502a4130001a198006000c0301080710039800d602030200c60002c903003005403084e2044002d90780031130117500456200c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 39884456 1250 39883206 39883211
    0x61b060902130b03100c0507020f06070b040b01051002160b03071206290a020a030503070210060f05010201110301141915080f060103090206030402060703171302041505011b0804091e 80
    0x105c0050241c01440710818140c1c49039418a00709400384a8030906011521341c0c841020001d07540050106400c06001300d00400355403030f20f90304040521aa03a816188600709541c4401303001c6410312008030402c0195441c06000d01c2c1c59461391041644c0c200c10f404500400301341802408200c5064007160404403501c0c2e0400746c2c00324402d50340c01072014450f000f18080160420145100400c2c001c100541d00800380c1c0c811500d110f138100915030115201d035086452114180002000903680c24050940c83d000c00300501c6185514043d4180348184200c0e07043c502840034856841044140490f024000344001c540c0c001c168195800000c0c00c0745021120303804a10992008190154400d10400c810160302500b901d01e96182c5808000442d08030307031300440400801c0081c80c0002d4401c0f00d03a21740141480080e0031040807491042200713541200d071440d5031b401c004205c10407482e80d100f4208481c1041c515401150045107051103182407040703030080d074041c81c1480c000c0c554802e40144a041c080c142603008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 39885706 1250 39884456 39884473
    0x902030f011a01080402030a020f22060503060a0203010807120201050f0a020c0415080a03050d1b0c0506010801051302010c0606030c0b04090b03010903020303220f0606090510061b060902130b03 85
    0x190780341541900c0107901030f0302240850005050981d03602b15207500081c00341481c1105080191040c003140b20550182c01c1e2182010011030404004050704005404000e40c1558102840255202050b128000b0000c2e841c00ca00002e590180f01103c5401440706507403665005081c601a60f5503c0c14841540240d1800e030070040700304072103001c6800396009d890181252078031549040750760f0740101103000d24003644c407034200401201c1c8410a01600c0e03c0e503101e104145000c0e003003403810b1a00503440311140764144002c000b40c4144034400d00f580f090742400d2406441605042400084c0065000202014181070011440080c00006001181d08030b2205104034280b050500d0b00340ca2040c800200980e0003030002c907034a4070f03400d101000c80c09a0803802c11412000c80e00d0b15100c2a90702141610f00c00d60b200001c0c00540300d103005103680305001e00300800103149031000083c00c032401e40311500009403501c2651010409039030042444a5001442444207501010188000300b02d0440380e14401e1007903550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 39886956 1250 39885706 39885709
    0x40303111011030c07080d05010303090806090a1e050f010509010b0f04091106070f0501020f0310061806030c05090402030c040f05030a0804140a031e0605010501140712030902030f011a 81
    0x1003000b54000c0d0b81802d400c5440304640030510313400200003224a00000e00200c8214402442803c0c0218040c0da90140b50a1809820904100026001c801036820015090000c1820a40750403111001705086045140d0b6908040c2d08080040e8407100a9500380001e20452080540200c5081e0070111101c02ca00403401040ac0101d8000280003040c0c03001842c0250162310b0440064440e00f170007512030385840c00095840700c1c2268400c401201280c00c021050206e0865410038000280c086410103060001d211002d690400720144108000c00d0b489082e120360381c0c1d105c2c400382c0d070703061a024200b5500d85c100b0210481072070700305000d0000010307044240001c09203800a52102000d40100704a031500b030030903070042204580380122a4120f541e6100020002e525100c050400242051040400c0300c01450184166041079004904024a84065032a00240f010441d280ba950083c85105082407804059003d4802404045d52602406218000038178041d0049503005110302001c5140820f08030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 39888206 1250 39886956 39886961
    0x4020906040e071202150a0503040c050a0302060d0b030106120b090d02010c08150a050d080705010501170c190e0403051207050310050f04060b0408010e07140d1707080403031110 78
    0x22107111142c2c2c8043c03010000c08100070b102600c410300290005841c0035100c0d03c0940240e10054100380040d50020401c414008000c0b1840d014040440740000c440c3e10310380016445004106000e543c3e02c0c2d54800303a00e000e0b9030035400398004001c40070113441e407601d050502c05a20340c412034140d003080c0524660050010320610500300407011549400a0070385480742c0c0481404100d181450708a0592140800c190340c605d2900c0b61801c1c4180e506c19540c0b0140d01d006030030b40d003041c0d016000030420b040540300080e001088416041005898481c4012100d00c100e4980300c03003e0380701c07400107000207040c80103041d840401811000041100c15a01e6101c880084030b05110442d21401c0e50b4101c03400900c1039103045030a0505000d0014004902e5648802200c1c02540c0a07606c0301300e00c1d80d5500c0c000154184248030020040c204050b00c103003540c4158000c91501059880000c19460900d0300010000c0203e00c281c1d100d40c3c1d00214507585a40e01ca01d40505032051000300b04115100780040120001000e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 39889456 1250 39888206 39888221
    0x3070b0c0f070501090608040305130f050111010915090507030c0b03040201020624150c07090608070e06090a020306010c060e0304060318031d010309020d05010b191401081305150402090604 83
    0x40e5119017425240c0501283c1003c8060000c90421200300214180107188040541c00b42075008880b40b5020b24010000d844049035045040b0b00e6418824440085460b2001da0034404403685008145c03c081d80c07078810b003030051a40009111a031812008103408425102452145100303070202c8200351106106508081c4891003109a422006100c0035914200020505284c4071121141e50400400d01d1102d407d140b5103401140a5a50380c01080000540c02c000d518014001029041418100000442c9803040011b00960717006400201041543c3d20a1090204a64128804010712003081c141c140d282d902500c0b800300080d04141e5200080403039410740202d0180d040d26050031203080620301c4860b002c0c2d5481c2050500d55104020005a10348902c040d600724840c000002e0071419440410000c89003038403c50300500c10810061012040d804c108205085c42420720325203580c0c03174210040f0001c46140e001445c50042800c0c00740e00131807c0d07034928041c5200300c415841c240c0d02c401c00c1c002110706a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 39890706 1250 39889456 39889459
    0x507090218030316061a030604030f0f030b0901090c05090315041502040803030703050a0e1f0c0207030c1806030c0e070905010206160c080405040507050a09060201110a1b0203070b0c0f0705 83
    0x268511302d00007125075222880072030222005003603103060580001d007000d03800c441c142c0128003455503040c420395101d40c01d0545100181410000816002d0200d09205014018000080c0c6e071614a150703900c0c018825142810030050440344047e03d0302048030402041590110b400d240c20600300b2101d60054000e43d802c0d0740d8140c00950035582c4440c41240604005804018000ea40780c0e4034175a035a070103100044604900c104840b6085003024400030454103070b19111700840d08452018400076040c00c2695085038400140380074504c0090310360340024420f40c1c0c001081010118030001b2545450309003d44500001d440d4240b106585500580e200c0b5000c07194140422001c4030900341c0b09000f05a03501400e0b019032159814280c07038034082801c482054482202140001c20481174140c0e10111400240a0b070303100a004180700c00c24810b00e54011840348500707015144001290798052218600c04180c0c00608035082d0a40e58007010142d907105070105620f13402240035010050400080c010101c400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 39891956 1250 39890706 39890737
    0x4b0215040b040204090c0512010c11060610180918020310110904020a120c05071b050303040902030a02090a030309090b01030203011505071e0b0105010909091a100305070902180303 79
    0x2c0c2c540c00c01c0003c24a170441102c00b29040300e40481d0585070307005407400300610030300001081c0302d81d00341c040c00000c0b504405510030b07445601000780940307a0b80c0d400746050445050040c06601240d00005100c441500030300b101c3c034a01140c100e0041a80c00300c0c40c0c942da00039020780d8212550300c8014426180b54103103510361204200321009041c10954020a42d60700c50b40341c00714140901c0940b030419038a03030000d008000741d03002c601141403000700800d05601011059400c50850714002c08203441c3c0c0250b114440e0720a60120004100c00a02c5c3c0445c4c411080080510613031588034540038005071503071b002d00110949031161480680d4002d2089030b05135030800705928002e850503903084406920096041340c46071130361031124501c8144100b1111000d44100442e103042e60400000600302c003010746c480c0030b202d41040400030100c0c00c01d91103d50101412859082c07a581c1c1c00080307800000b44e03984001d00d42e12451100203802d4000d0f50251003034108020140c60791101c40d90030103035203005140340800c5e0081e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 39893206 1250 39891956 39891961
    0x30406032403080c0c0a1d090708060403030929090c01020a0312090204020708030c0301050102060601050a0e0d0314041d0c0a09151202040311120d4b0215040b 70
    0x10200f00141c000b02c2d40d80d100321112003031441d010030303003207880c4c3e80c0681c0401d4201e28920315000048070255074040321070700052044a19000400d5913420700500080d05040d603071943c0105000c0c5a051010715260504828112541d2407035111041907400c40c0c0c1040c0038000e610101480e58400301c1e1030707010150596104c0100040310b0008000034458003000300c2e0700075820020340d8006550303000594811403403800b100740c03250b143c0000a820141d008001a040000c100301e0498416000005815070391815188490450030318607041c0e85140e061043d003814420041000205402c29007031050341040100380031106500c5190710a071480c020b6802312400309600e44030520003c0421341080403d600d0500c1c11100090348650208120790185d042035902d0b803400b13201125141051034603c0f2488103104014500365540140017000d100304080301d08428403130419080c0c04a2031480b005100280c91942c171210185103d0088580700440c41801000b6019250b503c084121104007458410f6801010041113903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 39894456 1250 39893206 39893213
    0x9120105061018171005070503010b16020d05030f0403020114070203071a13030803070201181104020706090602040e0601090b0301140d020301020c1609060b0c07090b03100e030406032403 82
    0x10400391220b10303110340009100281c103000c3c1c401003c4480c0c031303144098103045400591480030340b4401401841480703000c01c01007103800c054204417a41740800c400400c0d0b000303007940700180c14040e0307206010303103944808924501404200c0f0010b100301da100341c840450503c40e0384200c50701d034011380c0e0010f50b0603082100100b03c20984100b048000c91800c82444d40f403c80207005050080c0190307001640c401c800482007120050b024850810b05882d2070f03080e1244454542c0c0d80040c1942e54801080c001c80d0013140070000c00a26030011a0300c154042019501d55480d0a5103c1420304101c03020b90009604040c00590003400d10112416600c40e0f40400c00e0840c031100c00e2008180303032300c0001c9030550360801035500085018400c604050704400170002c0c0081c94040200b090300c1c01138020b041c522204000d0720f041c200b8000340c0c0700c085a0b41a44041481380c85500000c0c10840058610b6900a05010b04036050203400300040090301c02d561410000d00c800d1054603000041a90410b0045c610448424400b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 39895706 1250 39894456 39894467
    0xf0509010e010513031803120c062a0f0c301b02040506060702040f0b031c02060f060a0308041502100501080615060d0609020301090f020a0207031520091201050610 72
    0x6c00303c0e0301d82c000b0303415603413981c40c100e00a800c03450600005030301c91002402c20405001c0d1414001010108200c030310080a070702e240740e05441450340b0074010303100c00709580c05010300c641c0f0074101d42041d151070a620780c041d5100c50b100d016841c0460b0355428501c4180303c1030b001d039400000313500320010b50500c601001e0b42484010320700030f4889580080c0c1400300200599560081c9210381c1403080010810364080300c01d01d0325060740784680c81d1408001249940b03550b40e0004415520690400e0b040c1010703114040414020000c1340c00180c42210300080100318484506125200d1002c00c0c1d00316107841000d00d0800f8100d41081c0203810041d081a80800c03040c0a0003542c0c5a11901c00500d1140380c910310050640c22140c4552101c40d0a035004001040003020718414800101c9448406601e132100340c000080d21580140002490703481e14040c1d0ba888113a031540195050f0790711403010100045200054800e60b0800300c1070030700c103c054401801e0140340602440740510005084e88501d002504402d442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 39896956 1250 39895706 39895727
    0xb09070f030609230307060e0c1003110904110a080106080f010e0403030e03130f0e090c10050405030105042a060504061d04060b0309060c03010503060403050d09060f0509010e01051303 81
    0x6894002c1c104601e0945403021904c0703035648150f00110740e90380640c58071009951800413004070a070080c01c0ba501150b12180071082103459540303000102442041c03440364150144204450b0002c1c900b01900d803000130200028440408503440c1d0000c160b0f80c4074001c40c2c0400c0d040300c894112415950042000042e80004590803c0c42814003142c804c9a1103005440e6400408403030030710071610403040101c501044000303030182502203072140107894418081c59880140c45a01c5020b264460020f100003840b0f4020f80e03001c0d26004000f07110604141c1041c2c40d85212016962810010b5160700116617006003034848104d03034441d01c40b28240740c5071400580300c40d14440c204c050200c8000c650810780f9541d521a40018004200b07896480c0d0600c1151a440d00500a10364083d40008000500150340c00103a916445a0f051420700d60311031441141801900309214010905814507003109031a035030603005039200710380b01402089035401c007d003941c0c20780308141c600f00c86820700083c0b8640420301c00d011441c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 39898206 1250 39896956 39896963
    0x50402221e0605010f0201090209010501080405070f060f030e0a0201080604180605040507080d050304050606090c07080c071502010903050904050c090303041805010e192f04030b09070f030609 84
    0x61200105105554030300d04501080c1c1280d5071048144195a0032810030704940301144003c0007441001d0340803615075103060182030f0502820500040402c8130400000b005000c1c0c9509150700c250b80d55102a140c1c0c0c400040c518046400e00c01608949400082c90702076041c0c05944920441d19101d0034000100440c86138620781c9401c22002a0114041e1f0141c94000d503c0b501c018000981781c100c07414101080030490758100681001032101003000081c08940252003100d4030fa11980b120250b4200501c50404014072284010074422045003010480408452110b80000ba1079480381d4012400c95200060040101e441888583d0080c1060b620980d03020701941c1199141030112400a45180c009a005e002015030002c0d9813440d20001c2e000301801072040300c0b80178a07542805d5044802c05410034403110080356847da1040d440782c0400c0d00c106002140304036080484080301461500c0e550180c007050312020500404110707061b1001804008481844502c05804c2d801d55503171768083e04402c002035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39899456 1250 39898206 39898211
    0xb0f0601110d0815040207020901140607020a06020f060105030303070f0311040305010501030c170706090e090a0c06050403020108011e0303050a02030f120414010e030d0b011103030906040c0905040222 88
    0x10300701c22801c0008070040e4081c0d40303440d0070b03a00d0f00d50800002d00351070349501130140780140095001601d0706032406045d540c02a111601c243c91031004a0311a01540002075400608442c00203401038003c60314000c103200c0354084e0b0781640e80b03c1c0140741d9244015524000052800c84103983d446200e548100c0c00d1509800c03070945040ea590710f03100d003550307000e030810340304c100d2150b40404c10801e0701071428464069407400340100c1468050090003000701131041c101350f8540c840003d030615070b0502050341025444007503e45550b4070b80000078039a40040c04100e020822000c004a550100031540c070001d040d410000d140032604540e03040b14160400000b0703c1c00d61000303009101e06010044d02500030b032041c01c1c86180061401d404e000c241c030070703000e00c0c0320619034500f0f01c042852050109c200c40e9104064080230649001c0b460040b10040182c040488484c00040280240041c0120b1a103010354019500300f10450b031203603900700488034207030b03002580490003c0c0036030302d01c54004441300c80030a3b502400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39900706 1250 39899456 39899477
    0x5090d020a090c0807020601060309030206040f020f15090f042c03040b16020f010807021e0f07030b1015020304030f2d02031b0d06020304170703020307020102010c0c0b0f0601 77
    0x1006640c2c3c1e0000d00c00104000310100243e1590412001d401030035285428402403903140c0f4060b49581001d03001a1084420f41e05400c15915401001480003401038100101e140340741d80c40c2025030300f11030500c610501c1108190103461030140128401002807009110618404440301c4500224100b84050180410303c4001a114051307409000400c250108502d8081114410040b1034803071034180c14144440d07c801d0100d000e5001962122401a0001e046200c4a4041a69241124007181242c242c0718511010040201c00040e0b80e020b070b03030a801200b0501d602d80401c101d0581c0c001c40824016030042c4020001720f140914414401401103c3c00c010140c00f0203916a6840f0a150201148910b004071030811806c0810510041030b4901e850341141118103c0020a014042031001d802150040701203418010740d1b030018014061000513541e55100d803850040e450740c0000d41b059000d54604110000100c0c064800d50400d1603012a400d07680d5a5403004241c1c02420140040d8100410b581c40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39901956 1250 39900706 39900719
    0x909080910110d02060405070e010b09090406020d1a0a080c060a050702130501060c020a060302030108030d0908090301020406120b03061b0705070f0b1c0b03120c010b09010905040308060d020105090d020a 89
    0x81c400903c1d56a003c2c000c42d03d080d041161504038554084a2a00c0131000100b00e01d030a40d1043c0e5030381500485100b005600c2d41c0c2048000390203003d81c5068414942680b400c0708030402a00030801841c2a00c1420f640b41e960f583c00c0b5243d400c44101d040d002041080452070251150005010462000340340b05506000d0b82d031100101c44090b04040c021902d00300a49043d45026625480100501d00e4254615814014925268011040344050b91511083c6d03500030001d503c401e441407240b001d0002c40d142d55550400805104e00358400352041443c00da24443c0760700300466418801c403d0b000b400d452010f80c450200101d640b14820a80b95070044a401041c00c41e06505154000c103480580d490310303041c24204c9842d075140300480c120102850114001c00586011030128070b410401004252a40400b1070001d016060b089081540034072084004074154440d98040341c0105e000780e540440c26038521051040c02019440007a0110b0000e002500711454682c1422203190b03c058280c001c5c2039560103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39903206 1250 39901956 39901963
    0x50304050904080d0903120506090103120507021203030a021e070305040308030903130305010e0c09101a04120f12020d090902130e09010506010f02070303081b071a070801090908091011 81
    0x1700c110002074920b4a0310080030014012180c12860403680990316526545d038440703a5034a89480c1c2c02c01e00801103408810766881400070903800c40600d007642d03540c2ca045081e1400075800b6074008160f444401c0b203003050b03401c1e40200741d810141e4543c898606e0241075890b004015000245141c0c19031008210054840400c0b10410700110b00c10000800c0e06d4043c0c2e0f00c040d083c050780c0401203014104601c100000c1440f605256800c58000b818040c400702c2d040403401d1020702c01e580080740303456080c144c528208014034881c5c4582d2030145130015041501d90a00b245c5074008070b800f140000d106501c090114900e140d005203d485014640303008865502c42070050030b1202204c3d800300c0c07a551030003000350355600440d001364100c0b018406818003e0941d64090309074000070305410441070081020540382c165180031215440e800140059942201c00003c04d1100d00445400001440600002540100501070300142903401204982000c0040051080003880c0201e40400c004070303d480050103190030b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39904456 1250 39903206 39903221
    0xc06110d050402040b0409020a05040228090914010b22051804050c03150f0a09141c030c0212030a11030f010303080c12010303110a0506010f090501080109050304050904080d 76
    0x4000201ea280380600400c0704503898285030034015400c200040005958054400e01a250222401a11b400c1d40849a85840c1c1100d40e5a82034030840c0da50b104010703070700042c0352003c55800d1401884814280580707007021307210a104080900710140321002898a100000c054080c12a0300f00310a50350707031040054904001e80711500b41c200c0f02070b000d01c0b0030b000017888034140681c0c0079801050000b034450105040690002c00000100300440c002c030b100b82d01250410380d82e194002c4607a01408a0744420b03682c42e0300440c50800a044030038907048030000c0c000d004601c8034035801e8001d0311312090280503243d1560f00c01411203400654942a1040c156a0607019502418404200804070341c103514020b03004840c06456110805028003035111020a40d01c0b08030706503a4035280015810000c510420300c0c1c9413500400418a002d01800450540780c41c0101100b120389a003400e0242d40d0b6030300c1125003280d8490a0107801031f003042006200c5818159107203a0064070425802d480c2c072411242d01001c8034543c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39905706 1250 39904456 39904477
    0x21010612020f0a0503070303080a020c0703060e100509070501030e120a051b061302060c0c0907020102130605070c0905070c1505010f05040b09220b01030f020316060503070c0611 78
    0x880c0e00a06604085a003800480d1055074081003031410080020384c1c0740118131001f4100605140051604121a019200c001080608552200d9128034002014101c2c0a480d000184a00c45000b403a002150150354042c17448403000d41403e034204001180a40000841d003401480755020240b09440e082008161180755035882c5601c4101108030342e400802c1d081d2034500d09a0100c0d0501c001c100005201115196040341c61503a10300c1d5031034000d41806640400581e00c0301c8040100400d2903019002089042c4041030034401e4036403645000e4400d8010403030050102d03014040306101c0d05103d98070240c1c024030b450402c449075900582c0c0340740c03065402d841c2901c0c00319154001040242142e1902034003404c000ca03001d0003e079200e007022a0003408003e200342c2000c020703da0340c2c0900030303004030314106550f820103000704407903840c1c1c28034201c104a448000c074042e01c41c9454110301d100382035050b44103032071080c0c0d80c00f031440d00d81d1101100c3e03210011209440c110b5503684030341d981808203001041a842d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39906956 1250 39905706 39905729
    0xc15010e0406050c0c12130803030403080421140a0e06041211150a081005040609090c06020604080d0b01051b06160e0a1208130305030304060f0218210106 68
    0x420b46010010340394041c107009a032100902c01c1459061011400c5605984580a4141c440c00b0800d2441c0c3c0e00703000703680150124040081803009066000da40244034900a40d8028000c5031103c146075108480010490001010405101041011100244108895132a1075081c3e114031400103200d0b64840e900c01c0b00b415103c202a14200700074290110040d1000f01c55081000c0880000c4280d0f81c40f60004680c10000000c0000b8010b8500c0007980d0094500900200002520740c807076003000740642042034520b00c0300c1c0303240010210f100007002e52003960701c800842e00b131480c00000b02c0043e107414a20310381404414410402030203118010078852901074001007900d400d0103010880558861440d034010801e03583c00c0708000d074075004038082c21500c040004090180d81824500c1060040e04066458188d07549000000d01c080000a940614000d103400c0110415040c3c0840881c46440c9078004070711400318800c0b00030716040b41e0400e0b42d801d6206d01c440340c01040710304681c2140c220380c0240043d06c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39908206 1250 39906956 39906961
    0xf0516030b0d02060910020708060108030406031104050105271005180a05030303071101060b0708040501020d050301030b010303080718171002030108060a020702150d0b0103230103080c15010e 84
    0x99140c02a01440701060301e424504072816000b24445109502da928025901c116005c0d680c80c0c0308009090080030b00006980055842e844419201d1707105115100000e42401d1084d0700762072070b4104440447e14161215441c10800020340c401082c0301c0f550310081d030b06651042411710345a400b84007446c0c18056440300da490150900f004646103c4142c0140074540c0e48a081c0406d80b0000101d0780c2103281e604209008120100301640500219040f1851200d03005c01e0080c1003000050141c82a22006d800350b40d42002c6503082220706010910000d03008000c000e004201081c054280b039030700b000e031501c1c1400f00c0f50320307408030b09150700095800f91036040c14030b170707020004400140a600001030030b0200541ca1940340410700356903458050840801a41d001444204541d5903104a410740300683d42c18540b14204220600010213030350350880c1c00300382440020b143d40740250181c4045e8454100c0720754100e9007103031106a05a00079040c40d420390300c0361541e0807108000944809000b44a5902e00c0082d52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39909456 1250 39908206 39908251
    0xa0302040f060f02060601080901091a1008120405010c0303022109100b0d1202030903070f08010513030503070e0109120f120305070c0803040c15110106060206070f050d0f05 76
    0x402540420204010b451981c849544e000c140f0b250082c1c0709191440840e181c5403600c07030041a19800040041e4000c018020200d075041c450030317100b561031000280c0c80b99a40c0e148962240501500310040c0c01c000c02c8140710540c01042e50303001417402440c005041a120107110303418098021413610b410b100d0300007000660f00b420040c071803001441203000e1050551100215103403c0480100130300310b050881041010178400c000784c4808420080c102c0c0e2140c2e40c0c50356004600c448602685019500f440c002503012000c82071b083d000da40e8195590340ca07541c1e400c03100325004d03440340c24258100201071a0008450301806000190749005180b07519000d0351500d8010340d000351601041003032508010420bd50135800c1030069803241e801c1181c642c0e07030780d480d450101d414442c250010309802018840e51103c10b079020702250f124620303d85c020401542c5650050b6030350344d0300f160040c0c0050308064445140c02e12403000707000540d4034060042403400031200d0b544213940007101c0250110b2240742100c03021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39910706 1250 39909456 39909479
    0xe1e0a090b0109120501020d05100303030b0603040807060203060f031e06010f0302030a0305030712020301030c0302030c150306040209030705030d020102220308040e07020a050f250503060105040b03120a030204 92
    0xd280c80d000400c40c000846001900501c8a80302d0001020700b2286001e007801400e40450ba64100e17060020801854072440800512071103010a40003c1e02e058580581802c054080b20301071500f00c0b200b2404d1010b140d4607a03000e07600c0141610740042c44024070f028651410404440e14001d10301f40d20034070004680c00d4601c0c00340b059104403812000d0560400150b200400d2000790180c041c030342181d4a9a880d00c0986034405481c0c3d600190a100000010601180440c804256032080701600c804c3e00c6410100084080982100c80380300304d040000c9015440c10303600810020348050705564080e980c0e18000f034200007c103091040542d40000d404050b80c00660308452a01064210540e00b1b642541c45000441c007981c02150b087e66060000329541c2c1d0b0080100102c281c1d4800c003218405061100340944642d1602503c00c0401c01f1661116000d1090031801c0c0165000640104400e80c42c0c0350800c8003a01c14622807580600403031400001c00c0081400034500e41c0e43c80e460169540d443e24a080b1503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39911956 1250 39910706 39910709
    0x40b01090c0206150105030c160503030a06090b0f01030b01111006090c0903050a0204020f0403080a021005090c03190303020408100e0c0901081009061803110f06010b0a030504030e1e0a 81
    0xc42d0000800c000e80046041003030040304d402840e0071a02c90f580e140c0040c54a01c14040c0d42d041180718150070b07804100001004600ca040c0c00700c401c0c08050390360802081500c042c4082194041040840078540e94420350141e0080300052410360003004010400a041c82c042d41003010100b902c80f0b03424401d04600d4040c0b401030210300d2821039149491500e51a8444541c070400a12454001404100801030361042e43c3c0030b182c01c4000c003079403140719000182d41e501d050340c01e0040a605100001e000c0d101d003c101486101d00141c00340ca0b070500c3d6824102c04148405030110280b5034240320104030400204a03001240304400700c001045811442c01301e02d025608101c180c820030038803006001200d40850b0291140c01541004103c00442d443c066025001d0129903c031034030844d5046005060b4041c3e4000c0c1c80b5503513801601d003032a90300ca20554507400d0901a500154208000e8400c11038401d500159102e03009140040c0e500700e51000041e01240000f40504403501d0744d008550300e501c0c200c44c4620 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39913206 1250 39911956 39911981
    0xd0e011a150307080c09120d0807030615030203090102071b14030d0509010f0e09070c02040b0603010f0308030c040806010b0c0115050f0f0a0e070819020a020604020f0f09040b0109 79
    0x100c4000750581203140c0c80014028000c000b02070340843c031281441000e48104420040c580401210b07109041940c03070610300512030001d0400030100f40c40034000c0c4500019a910342140034000512000c06401075407000c0c01c000300b99035081264001041e0070721201101c900300000d0181103103244c49615044400d0080c403403032003074000341505110690090222985030000307003807084100e103100d41c4c16984050300034100c035008407200c0c0401c040c00368003103004054203100f01c50030400940d03203506201c882e00090186038004400d040082c004140c0d104003031548203260070142803030301d612980c0050501800380d1041402c4000450202440748081c0121040c1d20130078011f151405191500042c82c610240319064003410f06c010748012f00b612030a8400c006065202d240c000582029000201000e00407110b00c5202403050440e08441e407854000ca4000e40d020fa03004105c0794440b80c0070091503104950010b1f07070206400701000125201d950910307101e00c0c05882d45070751662403c0c0481c7e046d12005840300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39914456 1250 39913206 39913219
    0x4050103050c1f0507030804081204060501170a0804060c0804031712060f150a02010f05090606010306050a0608010302061c14070801090603020105070803100f03080a02010609061202040509030d0e011a 88
    0x480f129a10005441038107030076250071160340c0c40e03504100d4003500c07401c03900781e94050b041d03410041400001c0c0c0006040302c209d074644024482007039203503d071130342d1204200405566080200300071652143c0c1c1c82201e024007500d01c881c40d065880c0e07612144981030300400c03440382d400851040130101c100100c0e1640041c05940103da80e03900750002905026940102c04c182510214190700d03c0e61003580a0300340102c2108040040d401d00c0c01d005550f0380011694180000d013020400b003941c0c1030198511040f2682ca031a118190317400d513801c00500740c102c2d0a041d00281c0c8442403285a01405004841c0804001030300d20703030b05082080004103003010507003058540d2814900100011b0341c0c01000c581025030801815601c0f52036400c014401042142c0c45022011041c02d40803040c861000010300001f051341e0020044556180300305400d581480c45000241d5402c8003074000941400e0700060b5100900d5030640e490003841d640040103c4800030203002c9140e55419119410b41c04c1141b42072451541100c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39915706 1250 39914456 39914509
    0x307060f1706060d0c1209031806230a021c05070201080901060815040206090a0b040905100e04030c021201110409050906040f140c1003020307021006140f0a0504050103050c 76
    0x70036028820202c0358000e4685c0d40524404d02c070700c40ca040c20301410a07801e050062140d503040c01400c0c080300082098840445040c0007942c1c40c05501b500c104034140c0c11007203158000d480c2e1001c00507040410130740150700598524501d0070090030080c3c140d50b00903072074903911030b0f0071400014940c4100600c00c4c500e0343c3c500802809006c20004180c100000003054211440c0d80c1c901c007041141c0240615240c01039202100412b40c6119a0301a0080d80c1501000300980d41d50a8515840c850440c81070510040c030b682d01040104c0d128140050a05001419403110b42000c407601600310f8007500c0300d0804e8460081000c0c0181c4943d0f0083c0e03904403507001c00916180c01e1985a80c601648204001410400d0400c4080c1007050207014520341c520006000b000b0129941c00d0142c082c0d072046408e80e00500403900d401d0903a482a20950b810344e1400e014050700c100d0440c061101d010520009150302c00d1000d040000c480d03a5600403a80070703603c56406081c00070105c03400d00c5403051600500085004600e6207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39916956 1250 39915706 39915709
    0x80a06030c05040902190b030105010807020d0f0503040812010602101808121f03050c120f0705061305040906090b0606030114040906090203160e070507050a12030b0307060f1706 78
    0x100e040d07a10444000500c4900c81c0700103040b1002007201c491000d0381800780040c045147c00090350403104203803941a55650340b03803000c070307146c0d180c00203020040781000d8054a62203110744050f551162040c040685081740d9a03940381004e15090303000c440141c0c07040e07601d1144a00740f40107000985024140174040c034149940c0303404140c00f89000c14034604001c00001800d5940c02c2c20b04441200d0304400c5103407030984070b080c0140c840740b46003d86405122000d07207080222100007559004009564041d20801f8100002c00c881030703000b981c0c03150071546c5140011440b03540d540304a00041c2c1c81400006060322843c40c00b20104036004000344e00c1030340c00b0700040004e00710000c91342d0103404085900060081407894110b00800c00e048010b03406104200c0b03050b0300d03a11944820020740300900c8512000b55500c0001725041e208851004000340c200c40f0000e0300142c3e0f415162300c0e02c941107040c0802d9600040300400e140542650240c000100507030102d0a056800c01204a21180b0152004490f440c2150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39918206 1250 39916956 39916973
    0xf12030218060a02070506031603062705040c0f06020c0a0e0f01060e01050f03010608190b060a0503220812060a060e0d02030c040f020909220b1506040f06080a0603 72
    0xc0c03075940941070000d000c984051007480703030790003800000300039945030f08000c02801d07096206022401e0100c2d19119010880b601111404101040f10414100c0451001e0b0311440c0074240141040303801040180005ca42010b1000c480c074080c10056004000c41007146007086100500740c0d0010504110700810b12002c2c0c8801c140c141d0649a441c00d0040c0c400303400d000125a0b41c400d0340504140e8801c04000814555440740d2450b01642451980b107600c107407030171002e004407a004a03502d680322000700700316420769010302c003c1d540c80340d01380010401806901444080c003500000040314416000a41c1d10f0280300d0601d40160001404d4030200c1d41c003401c00c080542410285140f15101e00c840c40203031710855400308070000f080e0102070424800c02d948100a46e020b50071421203544038045100014540c089640c500c17003601844021012140b07200781d1606d01812502903e0303560070510070f4143c114035442e9070f402080206000e0140d10300c994035210000301010805000030002e182400b504002040118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39919456 1250 39918206 39918247
    0xa02130308070507090624020d0203030a0b12030403060b010f0c05071205030d06060e0f0114030a2022050d0c031b05040f0614010c050d08070507050a0f120302 70
    0x8041d0703a80c00380d070070f2152515007590f1000c1d50310b03420f00c074010403401104c108081e1440b241241c884010156141c041ea2212413047d0230a00503441070000560000c1e40e6003041e014001c000d01821300c00c51300c01c4501411030740300e80c02c240d42c042c0d01d80c40780d1a615680960b45640c0301c242450450350b5000c0035580c03da185c1046210b84c0c4407075200c00c0c000d8001e00c601801101c880d211221750802000c0d50390a409001d42400103a02e40c815545c1020781040c950150113800304000110110720f20b5a624820714600828012190010348110301482220034861203000b0502280700b810026045c11451600c0d450550740ca80005000b0107920f10340c41300207280410b102084d60b6000c1c1c020758426440980540c3d580d4002e501803580325003020b140c0c40700a041d980c0702400341d51920140c00903041004005441040f000c0d4070040581c0d11040d0000d00e6144241003950308480203180182c5401500d0300c5043c9465105c038000e41e01d80842d0f1344010104965102101c01541060405504009000c12201c0c3c041c2c042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39920706 1250 39919456 39919463
    0x709081507080402011209030206010303090f0609151b0609061a06072006070b0108010e0c03030a0f02120d02130510020c040509030409020301060801090b04020f16030903060f140a021303 82
    0x2d05010400316802109910958000300070200960206410003c0d56034400784000e0f000300390116404102c113030718a003000054892903160a000c0c83e00d81280e004005103580b080342e041250303010000b40704100e826610442180074000104501d11a410004125210540d0884c0c50020f070304a04030340e0752100c030181e0782519000a07101c195010626084040c4810600d40c0681c00600001c59a00b040200d010180c16940e07450000c02c00352465104a40d51014038058480e81940140071021180d80700d80103505d5425104c0c41510043c0401840b03c0c1600d030000da420040050b00401c0781d45002c403110b80c51310014003085502002810507460040d44540c08105203c1c015615000001e83d5008100308035402010035100031940e0350313529000101104002e00440c02005d003400d220060342e150074000d844d130742000020480d00c0c0410041d02c44c428140008002c03000c0c44a04480000410001e01c980001c0d10004030021804a00c10100c6400c07141d00100030200d480d105120703083d80ba0100300540e4082d01da2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39921956 1250 39920706 39920717
    0x60806010c0203100f090c0920070501020903030301090b01020d02070e010902070203070302030a0f050d0824040b0a0b0a03140910020a0212030106030c0f02030309060609130203030d050709081507 86
    0x34000300b41440c01e0000c1072001c0c5420001004070511172903100050711030160728540d0f44d5903201c080000540c0c072103410800281d2102c605083c58100440c0040254500c114001880c0812107004079042d50400da1181160340d40cac42c0c55030165075806001038060892988080c000c80f0303003004000c00d0000810b000f109400e660100f103800454400708408400b55070000e040341c0401202d40341c41280c1c0f2072400c10480c1c440c0500008240103a0240700920b0040d00b003100a5042c07482c482c2045a5605503201096a100740c44410059558580c554444040e00d00c03265699650f020070b41c4090261010240c2c1d03614100345203010404560404500f16250740f030b081070301603552002e02c0001c03840c114600c681116850000400040d01c0da402d94406000150f150305d031030f035a9840d0280e087c1d0300c034081100c1c1c1c0038003a04654002042d0745000c805407503200071030341c03008803000c9181d8020030b01c0c6800c40d600d04841d541c2d40c1c005010900c0e820121003002012018002c05030018031000350710310300d440034100300103222 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39923206 1250 39921956 39921977
    0x120a020901121107150b2d0105070606030b0406091407060207090504082101031725080c0304030305030105030601150c060b0a031e03030510050109060c08121305070f06080601 77
    0x1040801100d404e190845400d4580444d40861100180043e22005114a89085c4203541c0400d0071002c0c507000d083c2d104a6040140340c3c80c070041d2015403064800300c91043da5554007000003140e80e00c0403400749014620000e052421458544c8103100c014007682e00d103500c182c00400100d07500003203030403e644c060703900411b45403a0391524035000d0081c04001c00121903001c0584184144152905040b80d00074030b10180500d111208041251049008040e500b000290415100310203102c807091000d840703500c046180214841030b20f4110340064200f04d0004400200401052a0401c034260240680c001d41e00c1f0b60810401024000340d195107001004203494800202007981e80004040046410850845241e203450007840000d4907214402c8010070b1030000426418501050f01c0e1040c0d40c4103844201c2c03002d04120060b18641800202200c5d6070344200700101c2c05a02c9043c040b070140324580e150000d059a545005810800c0300d41146a10680350b003c10041c49500072601034100782c080c00c3c44400c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39924456 1250 39923206 39923231
    0x703050f1b0f0f0403031d040506060403060b010e1e150a080412020f150103030807170105010302090301020706060e190e0706050d0f09051b0409050a030807180b120a02090112 77
    0x81c090f640350540062008940001410740029816860f0600b4640002c1065200340800003151000d071242c80d00000c05000901c0059007a81c08001e80010506001c0710032030b81d5000080014181c22082c210308100d690907065603040c240444401e00310700041140c00d01c00d010034000c040ca40028006001e8601d950160201140248000c008003c40036094484071107030324a011a5400c4203100c1140041d0030000042c00c507034483e1400312000c0308003101030200c50746000011406500720b04940c583c555030810003500091880d00c1814000c00c10860300510600c0d14405102c090480041c0c9924010304140810300303404404a80320040e00e103d0f09001d9150756803806482d00034117070450860b00c2d1f1481c000c000750500000040a4110343c01c1c4240e4001030000d0b24040c031094811008009240390700846003200001c0c00f448505510014515190190043d0300a900001444030351040040f1900001c03541c0c80e400f01900038550040300e0000540c680341000c80001c02c0c940100d8054020141e844420207402d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39925706 1250 39924456 39924487
    0x910030c0c0b0109060608010506030402010905040f020d05130203010c08090c09040317091005070302090a15030e0607090303020607031803080903130f30030e03010f020a02060703050f1b 82
    0x101c6401560302030340c0e5a1580c104c000107240e0f6001e0f04001c50742c460000034041c5020000c13a0301c05e80c0d040c0c0d1a41c02c500d10b008140000382660b03509201c0415000c0c401c400b00c02e035151160ba4404d002145c06403031019200d0042c0340c2168109544081040610020451800310000e01c161060105a0710219a40d0725402c0440e1110f241082c07440010440030b003130100003600011071282c007121045081200d0384640505604070b00c544042075410170220402001b49007000e00c0300c103d8020b03560070040344030b40e41c0400190408400300d80120100340880000d200b0701d941001210b40c802400e040c10054558061410413282d4a100001020409400c000550740c031030178001c1d10804500a0829100241c90f0103990031030341c41502840407050207405604410811070244110004417007004221242d00c00d4800300d410160081e0000e404d0b40d22221900da221119100401805900e41d0240000b4201072900406540010307100c002528081c0080c0204410701d0048000d0015104444030f5884a00b03400fa101e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39926956 1250 39925706 39925727
    0xb070501060306090b06040c1b0602160f03020708010f1107140115090b01020f060c1c0204050307090504210206060d0f060603050a03080c1c02090301090213021309020910030c 77
    0xb503e800c2a1100d800c01211010150059804607010b2044c10720301e032000c80d1850700c2c06550701070310f8a0a004481c082000f40e402040c62190714414666280000c2d2507103402144455000c50060f4021213082000310380c280306201d00f08103070310750a00030444507002c503080500800d0005004410690701c140c0005400354820301c44039030411072081c18141d0303a540b0380c0d000700005000715001d80150040c0d0000042c0101c0c480d40b04141c5000b041d41041d0031000c1820740c040700310f00100d041680c00c10003ca03003540d007040704600800409001240383d20b42407401400c1400f0882c0c210f420b19130f4501d80d01c8a40d54000c00c2c2c1a5001c5000c1c4e41026004095007060f07100d16004039006040c280c9410b9020007442008030b60307a603c907030085d20b4500044d22402c418011910410307400e60144d44aa202d5152040d0041d00180500e220003000070840002d190000340d83d84460340102146c8030740c0018500d0030300620b4090075000b00110b04007181040c6c03c04010a9114103006000e10406540703a02003000c40d40211010003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39928062 1106 39926956 39926963
    0xf030a021204200910141311030a061203090501030f020d0f02040302010f020d020604021009080d0207061806080408160b0c030906060f031507030219021c0804020a0b0705010603 78
    0x1844c0c090030003240d80d4000b4519007e0700b81d40c00305004081c2c1c9075010508095032414104009800c5a00540c06403100036810f035040e40101c0d03041a400740c100e980a0a01040c840c1c2c440142c00300034410344030300f0322200d450030320324184640d1158042c000307a034400c0c0c07500680f6000c140c0302079070355000c00304031440140c0c8004001001420424010312108000d414280c1405480b81c00340350502000c55074560050340200410006a030f070003105424410900310009800a0074a0402030045400400140000500040c0b40c0501c1d016400070715502600203040c1c034210700300040031010350f900603a540d00652158034003240c0540307401400c2078030010009000b02442120307000c81c508034180007003041082c03580c2804804210b40300c000740f41418070003d9003c1e02c40d845440280301030190328404500e040140d02420000180ca50749020b800796807441c1c108039100d20551611901600d0b09402c004d = true := by decide +kernel

theorem cover : BRFrame.Cov 39748206 39928062 := by
  have h0 := BRFrame.cov_init 39748206
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39748206 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39748206 ≤ n) (h2 : n < 39928062) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
