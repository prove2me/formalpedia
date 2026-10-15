-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:59.448534+00:00
-- url     : https://prove2.me/submissions/e9db3e97-e396-460f-a368-87fb08a61e4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 749640287 ≤ n < 749820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 749641537 1250 749640287 749640293
    0x103020609010819051501030c030e0c0103020d02090a090207170a05120622060f1a0a0309051f0b091302010906031d0303041401050c0a0e101b1202100c0804 69
    0x1200201002125483d0034048516101075105c0d05000b990040304504001c1804c400240641d10741a9855041520380f40a07403901075408242006603000c2443c015907103001054840c80a800340700d0381603902103084000040e54110640c010915075200700c5401480d81021503030052030340210405203005c140d0820100b50700824a221a030b41c0704000404480b030b545c198100e00e51014609800c0411540c1d030342e040503c00120413403d018010564950300520b10246081501441c0c0034400d0300350700f07050300c680c0c6003804c0007000d00175440034401c03142c0480c12418400a0440140017000344280c0941c00050100d4452010501d40803600c64042e160f10090902c2d000045008111008186c0300a441308038084001041c00d000860140c2c2c000d45880701c0101d001c42c215400c490b00030b429020254802c1000c17408090f00840e00301083c1400321350068681004000070b8a010030700511030b203402181d1000c020708100c45000c100150798116421a61a0b0354552071942c100c0c2c40d4148c0c3e030780c00b181001e000a000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 749642787 1250 749641537 749641547
    0x15050f0d1d100b0a1502070e092109010f0c0201051903020c10050402040b220509100c120c141819030b010612060e01050d0c03051f0e06010302060901 66
    0x340404070003944468000c034042810b24149242240c0800d0b141c805500d10340c03828088000c0600030328007800311071403190040a543d9542c2403043e0782c00035081c4c100081192205010101c9251040c0341c81d172880301c40e0030450b500d450303001e0065940410500030701c01d540180724082800c8442e13410703100c036442d02482c42c8940840c51f8414460008040e0204a1b00c54070303040074415500c520100c0040810a41098410801901c024440f201d001c2c040700d8800c1c5084042d6084040072038915180700060700c0e12400e40c0d10741400074a00e44070300344a0405130b02405465206031b641c400008105001c001880207038101302c41c001e4004010b605081d4003442905c000c500d005400c1350402800502491903035140c2c1c6a801d00400650380150f0340c484504004001203600310115040c281c1d0740c0c034000c2052505000c2c400e42c1100f01802070070301036902d0507040d40411410042d03030720145800c101100c0741c040c21172101034030323001134884511420340c10804002c1c282c280000741e2506980e070003010682002903000045035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 749644037 1250 749642787 749642801
    0x306131e06060e03070803120606070303060b12040b0f07050406033308100203160e21060627011a120a09030e0d0201140309160803030115050f0d 64
    0x1100c401110030380558216140706030380050295403608095605100e04240c24003583d94400c4846070410040303659611080324900360302000407901141c4400c040c2c14100c00402c0f445c0c00c051400b41c0d0024032141403100c2c0c8282184518030690300c4c0101642c503c0b1aa00b02c2960548100340417403414042407100d14042c0d0411800d0101d038040642c900301c140a42e40394801007081c1401c80385064a01c1c20701c40d070342081c010710f04200e40014082d85141401e0707101c003680841800d0008200b045240500c40c8503641d0068062100e414840728208441c107004140351111406d8820b0352203020083c008a40918401d80401c00701c4021340740e0f2800c80d071b282ca00000a2142480d0a00010200402c141e441300c140d0304508030b004805440000410781950b00e00070305280032840c039482c0300b17614680c075040060b03074000c8200c210444500c1280e522500c490300010b10301600c08403070010360b000030000854406000400782d8100e0340c04031708803a14207001ca8426696403084220003c07000d60100100c0f1444425070b0040c3c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 749645287 1250 749644037 749644061
    0x20109030903060f0b0306180c03030304031b06020714070510020708072112020a03031d030315120d0e0a0b1c02030606190f032901320403050111030613 67
    0x1107030000c1d445d00004d042c04801c41e55414040f440c00091084480c0c01c0110046158056000b5455403c1c40e0728064035983d10340580b0108880345a100404108454054900e403a0f07001c6c10304018140c1c20040161140d0607402042d0092000c498281007192002901c0d10803034185c1006041c00904148840300991100b45425403049072044040c00010903121095801e01210350207485040000e2030014213860791070361900340201625156a400440101c203d0382c00c90300b9140b900c6418509103001c1840c03c3c0495444c85003074080c20100e60b001030f1b0814100c2c503041d20700b2142d1408140d00c440c64001d05014035404e40010307a25040104200402950003190441d900038010350805010702d04038241e084126100200050080070503108040c0c140c0540551848028420301c03c10400465100c2701c1e0044000d058108121001c40c403121000e148246030303c0c1e0b10350411400b0181820000700c3c1640d8014031048895610f0709002c00e468200358000d0340e00a200c01462840000360308035a80000c3e100d00c00000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 749646537 1250 749645287 749645291
    0x903151303081b0f040f0608060609100e150c0708010203151030051501020613061401060503160216050108090319110d020102030402062203060207050a060c020109030903060f 77
    0xc0c903000c4040b5024140c4c1900000003241d80701c5c10708042c20b203080c0d00d075803100d070a005c00e507814400e055a4a90594844c000c00340c1e4240c045a46e0b0040c100c0300d800b50350701070340d0700004003080518980f905d8600514261401c0c2080f5100300d543c45102c507080344000c442e81d128a1038250700840c11407500f510f200c003042060b80380198051300e20b0910803802c0c0f880f000388400000e025025069103001280606a0703c17500781d01011000401000001c4c1d102d01c3c00a25070380e208000d408120042040507030001c4d001d401140312000240d80c507000c01170141d0b4802d440700321000c022601c4080da01480094be0840710382040d60306008107840c000065501400c040d040414034041407006400c11200014100800e88260b950b02c0d41114440d02007a051580c05000d800859004000304405a15400c0845800314001c4a03401440310310403001a600c2ca005400081101d400080d00c003080c41400a4000002401000c081000c4140f0f074005070300320b440302c07035001b0b0118441c200f0400115030035501c500d844036421440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 749647787 1250 749646537 749646571
    0x504230c060d020901140309030403140d02120d09140105101a0909060d0818010905010c0305030112050c030601140f0d11010c080d0c110706050a020303191b0302090315130308 77
    0x48000347d0300f0480d01d0100540c00890304006100e01c01d80d10706018101c01c0c0140c2000c43c6405002520340c25a145102091007001070304111440b4150303c010300043d08160219a01482180281c0c00790100780c4620049088880d0b0206100d02200b8940c9007040d812000c241c686885a0244201081b00400d400d6000b525001c2040c00720300301e003000b4682c4408a1540603a5207400b0750001d0701c02d5119821450420100071b91040010390010101c034195140903039455040c410b5458014606111001c820b03030907029540001843c48150302d1a2003200b142220051642900c030420721980c0c000c025809000760b560f0400c0040194061150342000034010f40d40d0034603004218010000703442e918130300780000800d011102c190750320051040001802c101e180c000e103801110740c40256680805094070210752140d5800e2090264140c0c44114003009030f4040c2408903031900d001400a400c01086140a0b01501c0709204082c3d140021030361241e46d00181d10005000030b030324220f8041e4801003084011403d8080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 749649037 1250 749647787 749647817
    0x51602040f0504080310081603260a0f0813030f03051009050702100b030c03250807090b011701051e06040e0a0b0a0e07050706021c0504230c060d020901 67
    0x41c0b070312035409600250354a0400c0098050340d403c480c0c3c4030b5643c40c0c01150071070604000c03000c08001207035080031a06503600f40180908041034840f42c6a504010030001d030304441240c000e0400c405403086601c0d1480c039580c5211150031141007030b14008001603103861030b004165000364030242d000f410040c43d0903002610303404c0000448009481002c00744c0c2c09150550344900ca58014190303000000d50141c10300d180300d0b5011a58a50420007400c0c0c401c0d00b01d03c8051341001c0130071010001008080100d481065441c030109008241650020340001d64501244404404050925040300e01c082d210040c05004c041e0741c01c80003e0b11100f0143d0105003000b000948403c1280868060441a45c002941030480380c00c020403e0856841007014649010820083c01c4d004415100801e07000200075079922403a0680851000e5011500c3e0401898038040c04148040b140090710300d0102416912001d80307441d502a50b480350748106e1558040340800440c10781140356009030400c0700c810305141540c051018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 749650287 1250 749649037 749649041
    0xa050f0c2104140109031203090203030c1005101d07080c04030b0f0109150e01030b040c0312020c03070609050f040b01030608151e0105031507020f070303090e01060906051602040f 79
    0x1d210200080012405000d2180c0c4144103642c0d0200c00d08041d1066880d55907001910070400e1858024140d549005c84290b48080c0101c0381c81198150a80313640c010385c002090028141607038800400d0520120110319107490303c8861601c0048254031070115600c06008641c0300e4002030140404d00428880000000c542c0c42c0ca807801408203803007002da10341c10719152134110b0b20100b45000c00c50403030308410400e40817203001c1d050640c1d804c1101c0050300e0740c0d00d040a100c0340c0c00e03075800280403081d01c0d0300c4240a00c0d40841d8641003400e044090b01c0d4120783c0d600044030135128034040da07070b401030120400b182030f45000e5210035030780360042c1404102d143d52401c21130300380500d190140300700071300c150100003408000310610b400a0722040705030201541000f010070750b100c0580002e21780b090341c24404038240c580200a00580da0880350101d44074aa140e24008200c5607803842801c4862000c0400422198080d496038016aa40c6544181c1007041004080700c400f410a4016070304184d030b4543c1c002c4200340303074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 749651537 1250 749650287 749650333
    0x120705090307091d07031203051005130f0e1605060c241503061501080a0b0301230108060708132a080f06040b0a0902030102120703060501080c0a050f0c 67
    0x850707800101400c42105005040548060013001c0750072481050001400c00344d1100108100c1d807400003199520003e81040604032a0000b550108a05102100c9101540c11400e142d02c2c0b24041030107000000e01480b81da466030781341c41030034014055400b4003060800030060582c0905c0b803421120300b01c601d0200902c003401411942069030000600b0003a01d10801d2000029400d01a4000c240905c1c169840b03448646a405c96541000b01e00c0d00400c20345101500240c1c044031006008101000c54640004003502c220700d0909802001c80b0000644042c0220300c151091880d91203c02a9a0301e280030080c40107404c070400c903054000701c109801071104042d003a60808185501121402e420591694540088106000215400304e410880014480b483d911781007084500c002c14124400d02c000790183c05104500480d14080a013040200c55260300600d00b21002a220041c4980311002c9131039152081003010301c0491003c00292580310503020040c26501e601c2d4047c0d400603404499480044c3d500c3c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 749652787 1250 749651537 749651549
    0xa0212070c1a071205090118180b0609030a020409020303190503010906150903020f030a150204030209060108010312050304020a0308070c14040b0a030f05070f0f0806070f05120705090307 82
    0xc40c0c40902c02c802e0364849000b690181015010308040c107503a02d0300d00e54000700030524104180460390310984e0340118015401d056100c4814031b0025102c050716006580d40000100b10380742840403001203401d00404070340414030701801500d03006074541c003803001411201e6001c80e014801000115003050080e1a106496107250b940d117542d95260225036410742c2c00d0b1341c00c601c0d00000300d00000030110fa00500300d84d003144e5055400794032001e02100040e0030144000720250810224200803408041d0580c000c0081e24401c807442d002686403240110391050090100030240500d50505951060050024603480f5100905003086652281e80d0581660014203049802e0900250300b801008520016041450801e807000c20023440c0300c0d40040c2c1d514070b00b44400380920b50f0380c2c90014103001c0d060102c40040d0003022481309400d030381c072118405d0054043c480d034030f003500800002c6016207109a1516030300b41c240381d40c1d960414210705405d540c100d00190000003804410800700c901910103002e8200101a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 749654037 1250 749652787 749652803
    0x301350a0506480408071e0605040608090709060e0a0b01080c0702060c03090d12080901180209101a071b0803030c0f070c09050103030f03110405060a021207 69
    0xa4501c1c04030315020000e8146409143d102503044004403a07428071044041c2c819100141030701c0058607460942c42c20ba0040c80e5404000580400c031290001009030071940c1891002c0c07010540d03440200c04804203405203e0000b10104002c12402d4842c5110369081aa40006d840809031b03038410540884400c0d0344070030b5400d0410010002445800d1007031620464081c03c0401c5540781c500b212641034860710000910030030740400c0300842690304001752406c41c00c1c003401e49040c446050508202c2052141314400000751858001110307902c060150398016012010582403421a136420800c44c044000d10b40410006a080300145c1c0344400142c0074824200742d481c41c3d1760303440b49007401d84000c01c00004508807001c1300e40d0100459030000040782e43c452541800f03591200c060700082c0095216040000c2c0040b0310788580498001d0b11980a1412a403007526035050174801004180c0a442c0d507400d48450254080c0b000300040c0c14083c005040e0f811551059030013458069000842c2a08a0300090311249 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 749655287 1250 749654037 749654053
    0x50a08070329090a15060c032307020310020f0a0f0e090c04051507120305060d0507060f03240501080603030714010203100b03131b180e0105100b030135 67
    0x820f0400300d0b5900300014220a0040005030b4280e1507142c0305610500b020840001c2c002e10900d44110075510505101100910588404000719101c80d00b100406a100380501c103041d0341560010320842310010368161303d450411480c0e03e000d82c1c00808100c3c008050100941c00c480107039580d298038511a444821805407141e091600f4009289641001102007800030003014000c12159540f5110042c2c00e49404181503a64502043c51003a400100810a204888021813a02d070070201c80c01d9180c1407954200b01d69029159041c03850200120620056185800280210752103845503592201c03016003184d1070320003240d40c1e0100702c00d91010310211a95000c010f0012401c6000b11110003401c140b05881c0c1982032020008011594443d402841c00040d0907940f0340c000f8015000030020040c20403007881400b8068041e0003c0d10a10394101541d502e03140010b45241240a01901603401c000321a905607030a05c80042d4880e44900b940041801d00c480181a0403185e5101c1000041001d0b00603010031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 749656537 1250 749655287 749655289
    0x609100e030c06010b0d020c07080d0201050709050d030f0201240302040c020304061e0e06031801110301270b0607030908150c070b071205100305100507050a08070329 73
    0x4501800c0031126035042003001d070030011000640030b4151035810507259030799050700062200078031500103c0b2205008903407002854600201c3c0e00ca54038140384c3c000317100e15603e01004450160b601c1c01500d07440700902b155000824071600110941c03026a000004013801c0802844950b900c07903002c1d58400b800c1d4680240300314107103409050080d1503680000c505190034010301038064054030b08500746041484071561341e113074132450410b110048007600c850f9490810740c0001540c0c40300c048071002c9170760800b00f1044076505800102d034100d0360b03414102e6801101c035900307000c032107121071100001c040d403201d1800103281d40781001005a2072090722040301d002e2420181c03504105283d00c82d14848800c02c4100b00304160f502c011503010a0b132004a902c0c565564000a0700e014400c0e204802900e46400c04200d040f00004c012501640d00560440351003107250300300031041d544100c45600000da0305005001400b4000d0302d155800043c20f080104112000c140201d501d2042030340035003040b82c84a80c62002c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 749657787 1250 749656537 749656541
    0x10080a0e210702033c0106090203040b040b16020c060d06080d08040b07020106050a090b1306030503041d0c0d15090e030316051e030a0605040f021e0c0a08030612060910 74
    0x4150a1017900310540a07900684450101c504c02c03150000c20840ca1003031440800a61100024000c1c0c40c000f1501c0c0d00f81400c092102d40000c603400c503104401c103000b140e0701001c82220051851394a500070302c400762420702070000c03940041c040888500c1d1151804211001f003481481091841681d42d00c500b450907040c40040c140b40030b454542036916141040c000d0307484030000701c42544d100140124a075000c00b0301144205c0b00182e01040e40f01d00e03246002c42001408402482105c1170080f08099441702e010b41007408200c19541c40d40c0e1513208010101e56030701d4603001078451404849018666a40c1c82405006407045101e034040c582e0400010441c6488014004802c0b9109a1a0082c200b00c80c1c1d5170005106109003000d501598400300c0016807201c1e10344c02030000380c80b019000b44022903d40d050700c4040e403c01c040c8444107928034050050500a940140d4625401c104001c2c01040f51507180c10049030301c00381503503801c003204500c091610318003040f48a00402c105801890b4800c040000141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 749659037 1250 749657787 749657803
    0xf0f140601181a040b0304120207091815090b0c07051207030c061a06040b030f010b360603011205060604051501080901090c0e011410080a0e21070203 66
    0x2051000e08100d040b290955a0440e00c142c030743c424030211034402c6000e1000d50382d005a40c40032846000002c10041008154030440c00401019021035176010380360f2035500c003034441e16844101c4000480000c60081290210100240d08c5050000640b400043e00d0712400724070111541c20b042d5400154201c200f1108006500e0b6401c041c9501605054040e40c009119510004020b400030751281c4c6403800120b40d900550859500081002d5070703c1c3d035a40720a11690304216403807484400200000140f45c00040102e8020b50042d60805886000003c01c03c0b080182d03040b1001c44c00b00b031008207010036445040c021806004074040118940050b0310703101e841d1045c000d000c02d0045041138244040c0401880503055100e4003400c2569003640c0f03a050701d43c010401460301601455160b040000d13100c01548100d416500c000d078010a500c90a41c091107495a0419031590024000da000a4007008403544104102c046170400e0b200300c41f645824501c00410f5000004211403030000740c1600714502041480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 749660287 1250 749659037 749659039
    0x240031a15010c02061e04060903060b04060803040b07080702060310050f04110d0902030c0d0b01050a170c0112020c06090106180e07050111030f0c0c010e0301090b01180f0f1406 78
    0x1c4070a84044000818502003800000d02072030703000c2166000110a1341a140c0792001c021500303921290b8030400189008004c3c07205a502915014913081241418028541501c00481c0210328103403800016000f00d501c034002c20b82e03060300309200442c016034480c8025800781c000c5482c40302e1034034100010404045802c0b86094411482c0212001c29a40d848095444508092400240084c8a4000310341405c614004082d886017a4842d20780400080d0785080b0705950082e55140c0c4059100e200d82919294000c80405a5500501480d5060740c440c180714441110002e00141c104084041c5140c941003007038442c40740d680d459400c1800302d54580800b41c1c45e8180c01e10018800a00c0c01c0c2da40903210000e038001c0302d040204801d54010507074805c10443d030410100e10f0710185d0380d06003521015101c501d0b40d00305500180d0502c0f6804014941406003400990300131046a142d40d18280b04600801940501e441c0400e4507001040f004000b00d21501d1294034003014045848000305008281240c401401a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 749661537 1250 749660287 749660311
    0xd151409100e060102190f05060f0f0408030c0f1c0c090302090a110c0f0703110103111605120c100b0604150f03090f05100e010240031a 60
    0x301070790303280040d0012036000312941c0c4030540300c0100403414031002401d00b06403420512400e50400052406d42e07500d083c015016034441303440d26980074541c12010749503082038100490105010800e690001c40c1c03c8034458101e145459451604d031a055000180122010b08181e41740324414030850186070441400c2c3d140c500c207628115400105040c03c0644540c4105a4400c0c0c4059500386000032101c01c0d03544d000840342e1401880c55103982d0351060b804101d4504945011154855010307025006260000d4404075003044c0c45104601d184404844069450b4403036120410b5601000700c0c01014011000000f0307003000c4507030307420b1401924584c40c800390150104201c10080c001c22951500b1140501e0f2500d07005100310300c0070480c0a005588009028584a09002e20401200061403071031a0110f84003170080c01100c0345460700302d000310501202c1c3c407010044002c1001c81010b103c55109904540b00000611008090008410b01030304102c07003d50040490283d400c40504015074402421088 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 749662787 1250 749661537 749661541
    0xd120305100b0c0312060402090405090d02071401050a030b180a141e0105010c030512071e09050a142106091504030210020309150403120f090f0b040302030d151409 72
    0x5102c0e035034171a40c01200c01760080704020036510f40c3c681e0100c07841d03000700400074000303030420400303a5442e08404084d032409403103001400204400c1c840c032401d0340c8070300507101c081c1802c3d00d154064010b040550029a800041089a100c000c440d401810b0b000e01c040d01400145990a0460494210340240c61038131240422440e04c0d91051209040d03d054030002c0c0b07415254511740745000e880300d001e1103015640d060240801c1100c6182c1c06400c41024012260094180402c3c040003075071000054000d07543c00c8202c050040c0070038513120009009514000c0e0141200f8007207420f00407800f212001c045265500b1440c01e02000300b0041000b241c15182040b540c1c8454103081d607000e9901e8200703012031080541c000c00020100d520500c03200e41c041c0060f00c1d102c895843c161800511080d212011040003610b008a031107a600e07810701c61620307142c2e070082403030804c0f012585803001c41c49070050084086100410904208802c140503203405c0064019038400780c0703414103500c40c0d034030412800340c41d02880604007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 749664037 1250 749662787 749662807
    0x506042909030301060e0109090608010506010e040b0a09270605040201022b08040314070b100812090d0c120b0402100311030a0e010b1804060e03041d060d120305100b 73
    0x40f241190210f040642440784803c00582d40d003c096402400c00c20f1400000003a80c51041d04000c0c8035a800741c0e903c080104040e810031003140d40c9000d6440e00110a19000d200d03010055000c40f090070003044c00d850320112014020700414001e070200300c55550301c841c00e010855804110310f104103440640842140880d003c2e01d0100ca00b4101141c200300b04030f0740f000c101894050350f0120082d11400038030955601c2c0c1410041c098010584642000c111640b90000c0d020740f021564500d07941044040030300d405003243c208441c204001409450040c5c02003000610a01c6407007148003d54821200080c0034500707401005890250314800c40c2c14941420060406841840c01300c03988125608400103521420186c4c050040910400050b003084484140340740c0410b4820760188958403c15042c042241540c490b81c1e26402940301e5810200714091118074418602100141c1c4810040c14081081505840d152100d0094402032400709a0711820f000341001c0124296018040500409162500c010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 749665287 1250 749664037 749664043
    0x1201150c06241d09030a0518011b031d030d1407080d06081b06030717040f0b090c1c030e13020d2d0603030203090415050301020706020c060a06061b020d0506042909 72
    0x180c4516140235181b80350040503801418664042030440e41707002a0890640380280211504e00305901d088503044907001d070180360009880e5814082683e441040c0740d101a0b41c0c558036080018119421304042c090035502c59811b102da280100118001480c1281d42c4038007000030f010280308941d0040c03004000300704405822200c46002c80c180c11f107030801355654a041c00111042c0c03950b00100880644003e04c5403000c4001880000000c0448102c004858100440201285071840040c00714520414900c81c0785480402d203c10740841480261418501d801980c0440314240c0c1c844080900c0f9200561113204012406c030118a802e0034200b0019045403000781d924041d4200c110312490b29480c8242c40410788210b0395000300000340c0250f4aa0708585004c001942040608205a10074000050101540d41c000c403c02c03280d6a4603608020709905411800c070411450302a60031104c090940300c0022010010140700c0c03801440100b941c4020201001030010021001e026120450f4042c409811008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 749666537 1250 749665287 749665297
    0x1a0301030807020d0f020306070816020105010305060c07031701030303060906270b040e06011715221a0f01050f04110f09030705151201150c06241d09030a05 69
    0x450714071602d40d604d4034111052402139000250035015507002e10030300b01d41000c1d00500a85858040400c40b05040711b089080b66024403010745940c2c03103440401c02c00e0020340001c1205c00c0c0a0b00e4035042c90192216255042802a403080703000036600d4608000e84603051040c200607180c03051040f52000c01d1043c0407032070000321054111505503150802406039940303911001000b510342059035203542c0d56040040d001d005481040d000b600400354900c1e20a902c1401c40d40c07107914500711a155048001c1d1108500c24200c02c000c0b00c40b403c0526090031742c00c1111001030310581c443c8240540d00c0d03040c074090001e44e43c0c600790741c1400340d030410400612000e052829100e0382585454000d407105c900c500002d140140d65400280c01030b080ca002200914184002030100d81003581c0d09492a903a1002c00030b002180d405818070000301414803520001c0c000c7d0f000b46510013200f106c129a0041100c1c01440350b01182e911480b900102c800c100c50880700d82c081c610750700251100c040c5082c01d103d140054014424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 749667787 1250 749666537 749666539
    0xc05090618062b0b0a0f0507321911010e0a0206030a02090d0b04050d1701061d0a060c020102011a0f12070b0d05150d080f0903071a041a030103080702 66
    0xb0050700f1010484078865010154004200d00b601d1000300d04050588280c256100001c850a10451025948035030050500403100c1da070758007952a040c844000300382515102e0b650107401030780c8958460882880007800212035150b041c11041e10800d000500710004411040c03842da4108903410b8030340303c8041190081250117030f5025689580d1820120001d20424002581c010502c00e0300e0005c4c4180030203410f01c510301c00c0c2e04480241c044450140c4020142610210300902044014080a80724071800340900c4003104002401c80000d50026161410540201d00001c1112981505642c1e0901030084d5400012203400c2c00f060881d404104104051068507024040030740019864030000c1100340300900f40014035648940d0b0800030b800141005880c96805840c0c80c044500c022315241c1e180343c614540c020480352800f10644140021500158029a0706010745900014000103410540640089030450079030360b281800d040481c28014480c01a4486005100601c0002c000d40100c503501b9070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 749669037 1250 749667787 749667799
    0x316060206131e06020c0d03150b03010b03011205010b150a03150b1e070f0c14010f02100b030109140d08091c210f050f06100203070b0c04080a0c0509061806 69
    0xc60510721302900c02c102c04416144100d0748250682e5606600c0300245600711100c00451981d0b8148002d000e02083c0144911a1010001008400c460002c0820080d108034004140181c02d88001070380a06848050940c040700064050445503140c07040a1803c001603c2e113019143c20400846020f01686d8031804140c11541e00601f02c4403404000d96000c954000140c0c1701c85c2450f03261001c20b611080c418a041c4499001102e0641e40c09007a000c5901d6255038001c00d0b4ae843e4049210025000242805815550f5a9001d03004111450081c00100c4d0b1084003c20400e022404014030120700105680440d401c500b6404031030701c910230345070b0b0104040d0740b070300420b8020800d4a22861075080d1201801d2180341c025120b01d0b002e40b0340c00003842803e001e1000c900d80da4440e020311049403034060307107000103800801c01e10000035800c80f182500860009806410513448030001843c0032514002035031a450040c0e420003d03482d084400135408102681c2d000464021429070403a049070107880244603070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749670287 1250 749669037 749669093
    0x20114040f0c08070603020a0f03021206090c09100324030206220b03090c0916090e15030a0f0605070203092b05030d0b01081003020a12030e031606020613 68
    0x3001c5860310b0000790440744243d8680d243c1d03640d00030700250700c40c21039600898003502c000705802d4000c0c0709580074001ba201c01100d96640c0c075400c0081c1810000c0100340340040610801480d03803100d0503020551040750f2400500300d86159010815211aa0392840280720440024801178461005484803c03010040c0100161745952301110903400a400c00140c181c0c0100c20000b450070001922050b44005540a0400d61203075000750403800540c11f24000440d10144040042c00c42150000368060107031940905c410164000080c01d0800c6403070240c40200882a403941448003510841d908030340319000031850201c0d0b0102040340021860030b0003400c000d030035080072a08054250300010301a03000003501c0d52880840c441c0001022441d501c3c600041510b00021659041c5405072416650000c00483c0317464600f820600c0c40c3e481d00c0ca011401c02ca1100c12801107620100640100648990307140c400807810050000d280140040152031a040c10026038004110f00701151074071034001c0f444000b500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 749671537 1250 749670287 749670293
    0xb0913020d020114120c030105091e1303020c040f06150203190e030c150d241e0b041202130507090e130503031f1215050a1107050a060507020114040f 66
    0x10780103841890f04400d01d81010002c40b1400d6000440c1a6903086800cac41e0a40c954a80c0f80d100c0303140c085030782c3c0c01e0800c0d0b03100440e5081681e2429041698840e01c12603041111100106094032a20483d424819440790407d129403c2508069907050f8414401141401e0011b01c5117040b14003c410348006200b908450340d886a14203100900c100000540041d4100824005829140d48000d01c10461140381000c1891580441042d6000142221850300c203000d0801680400014404032207180148003d100042d14500c07100c05480280f001d0610004815034900601035800d81140500b4100f81c507120800103c140c00c0310711101a80c044030541d4096070340c0c81400d04070040ea80740e00984940f001008020441d48010585415081c1016a0007407090303441c81c107201c0b034091086006001004503401d09811004640c00707190702424010000c149c05210340a02d0b40640d01500c030a541503000303d140ca0050010a0185c1a006031480c80204025600c4101588039540080d0004011900001c002c0d424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 749672787 1250 749671537 749671577
    0x403140a0e270403020c03010623090903130b0d0b0a12110102010e10050603070816090c0c120e01080f0615030c07020402042d380408010b0913020d0201 67
    0x20b074081804000741014140a540d545001c0c0d01a8484c0d824000d02182000941a8a1485420360040041e41e41451020081e0f4180004d01030146031200707001c1da00b00000280d40702c400504080c3d0b1056501c140c2140d45d80d00391201d42103614091421204108900207141c4000c600302600000c07241071000c4010300403030240c2800040004036210b500503105200038158030031401501d0031821142100d9036603140f280c44241200c20546000960b041c1048044500d80000300d50002c40d160441d2444002e6840904041d1500b4039940000c10201d003520165802030780a54000303074001c4002c60103140020003d1284a050010680390041c0880440c40d00c000c088c00741d0396450340c000c0080d07444980701c85048400d45a00b01c4e29030a0030000380c803440301c540c1804440307900365000c00c601c1018046018025094280c98028189103495400741c100918002030805030000d01510300000c076174241000c0401c0042c1c0400b8002c4880c1c0c2a0b0407080c0f03001a0f40d8030030411000b590a0078404004888105901c00f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 749674037 1250 749672787 749672839
    0x905091c03021602062b0e190501061d090d03290f0612060315040f1e0c08012c03040303080711100906050f060f0112020715050403140a0e 61
    0x1d0014070220710060807080c0040da1503c0400c00d0402c040024000d031002001f6241c102ca665502038200503884d048200303078030084520031405500081841951201e401c05480321440380f43c00c0d400301c0c08080c88081e2800744403442c01e8400515040c011a5001001400101082d50001400303140100303a206003a15031850710f0045c3c000081690f600d4207032000343d5000d03030141200d11620078011062561000000c800400b40107541005080b024100c80d592120902c101d03040c6602505aa106440300000e1000c0c0c5c1031b840a03001020020030715030300078501080d00240365011183e8107150240482c0c09150300105490490350540340c190060307100c81106480c81e40100648a00c20300505040d22074410b8a5004403940503c2143e04101d0755030390340020b0144c1841543d18682c445a070f101c0d003d03050b40c45811200300c08004528010b180100b1903403003542d050b080c01c0620100c19100c400300310605d5001000c400c480584a0103151811591a0b0010921407440385600c0c45058540c070010b5000c4a8904410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 749675287 1250 749674037 749674039
    0x1005091b01081e10060e0307140603070504090c020f010516120b04060b0a0e030601060c0206120405100c0e0f100813060b04061e080d0921020306040c0905091c03021602 74
    0x2aa908240000f04d0f1020010700603d80410b000b032180c0b0a0b1070034009020070803140f210000c4807106103400708224159101400c0d10b002c015040c08045045c044500c5803010204040e0014600400511505400e40e98020318880355003044400d010840c0c1c8e00300410020102140301c00080c10180840000c000f005d681d0440461400003060702e00d1030607003242d40c5001090048084a00580e039402c0c0c2140c04400c40e26000350000418132440500615812130035800621580907070f00202c11031000d050444001c0c00902001808150341c1c1505400c2c0f00d5000390642c02d0541d09400e01d02054070004e080d02001a0174030524244103104c4109000c0564010140024010000d0101e40d540b61040e02c441500041c11010070450101c00048800000400c010580c41c5610340807201454007460801c450b480100203100541108002001a17406001082c41181310f0503c0031a0a0309100c4c2070780865000030b000d452164061400d11b1b12482c0884500f8181c2115882c0c0943d8540ca8800d07180440c0b1780d115402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 749676537 1250 749675287 749675341
    0x130305030304081b030406051207020106180204060e0306060102070608090c0a0303030203250815060705030c070303020610120807081b011e230c16051005091b0108 72
    0x102c030401c05010000c242c00038505400320100c08101161503100d00c5603204402c0422001c000000c0f062890366503069000500e4000000e004c4d50701c0b8a0000396a071f10a089034a480c1e0b00007030520500e0303005800d01b14017120030b4004280c3c5281200010756202544d000e06414042142c00003034401c1c0e0704112080d003d040c050070340061309030f5914002e0080e400507114080c81d50041c0303d2040203600099070b507100070781c0540d0b94100c00362910182d105d000f602c0e0034a80c5401850412095001c140104010160340300080024104186507040003800e10002400c503600183c005001000810011003c1043c0c59800c000255581c001a04d48903206204100c8401c00c0080195808041c0000650040c400e6006d18007603004100200c05008084a20709804036002c0c41e50071001c014590141e0469035800103a4054030740c54610141c8100700611502001115154881c100451800b0080c2c040c254010540b040240030300700c1003a107144040c5210b489101e041002c0940008e004039a070a012041c4da40c0c40d0920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 749677787 1250 749676537 749676541
    0x1409120a0f0f14030a1d0d061104051503040c050616021003200a120f060b0c0d0306120b07030506130c0905030d080702032502061c0f1a0103021303050303 68
    0x40804400c540d85000e442d621612400440003e2000c41100d003101582d81d146050703c610300404032500501030180da608171040e9821000001c01921500303c2e110544864151281d00c2c0c42c0401200624001c580c200100c2c1c00d2080c0400510b1940402098607003c8502c1611108034040702c0c0c05544c064503001e9803040700c01c05480103e640541c4403000d071881c0b83c2074543d007203075464001101c244200d00074400041e64490080e0f0762000d9a41c001580701100780004500581e80c0c42c1c00b254940c00101920449422180e0395a407226090300c140c0c0000c1014a601e12098a010340703440c0c243c06401420390050680b10400903c180d9034072030300290304000311481000340b84909400180640c41a014480c001d209281c03440c43d0441c014600d02c0e1260070140c0c0154038003850554588000c2002d00059808074848284440045c2d5030200600710822a803860300764511560074004007954090b00184601c42d2500f01200074003c20b80c2e00c0b0080090080c03c01607035903401c030012324850704c416500c0036240e4000803007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 749679037 1250 749677787 749677793
    0x903010207150203191a0111030d14090601060c0c2112030f1107021c08072001120e0606060c0a05060106020a02120c2d0901080c0102010c1409120a0f 66
    0x40070310300400000e17044c82209003086413014111126640000380c4044a0036403540c80e588281c0240c009082420242da0808090040d040107459568031050304c030500640c108003d451080001a0040059180c904890aa552102e1800307030018007544031401032181507200c050040c0b0b034001c03100303a602404900b07241480d84801001000175401c0e0316442420700004400103101d103415505a01d400a08090803903907401780290020000d5041142c680006200d030001150103c1c02d5420900088082c0f459030720740ba40c00040221050702500004140780050482e00b03518000b070903d520844c00c0c0c511580e00c800d00030a16240001040d00100b85d4842d880000c203103241d000c94034103000c0d8803d07a02d00c1c03a19024141c4040d101c260000b000c1390000760920310700380c1c0450042183c0b14250244006054100c41c82804106051030903004a0880d601102088115590902c1141d03070700d1981349090440c901845154207500e200304100580b180d404081a41900034007441044505a4801d050001c070358100d103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 749680287 1250 749679037 749679041
    0x1106071a0a0605040e0d27060e13050405100b010e04090501091e03080402130e010c080612010b0618010504120303060305060c3910090b070306030314090301020715 72
    0x44200d81001e0402c000001c03141050700581c0c054514200190003080b0b0400700468050080c50109817042181d40b42d1220248002015100540b60590321118a1000c5c94103102c0050003105440d90030700d1500080201041c0045034080d041e45440001049801d00c410040391610018102e19501070b140210a00802605510a20420340b0980d001d40100c810250444c114044401018001c6070001000500619001c0c603042c0080342c00240009111105103c0542101d03641601c65001c02d070240180b00c424500941c241c80000040c00081c006600d484001c40e4042c016818141c2410100c0500b84e515a030060090710051b1400400c0700030044001d040c000c0141ca406d20080d0350500440c40070039000701484040f90100b604400c503644e400f10180200008003c5001d0308036581001c0c1a80610b049681400380307840b4045510008281100c540c10117a90200e0b011f003400050602d001070400000750441c260206036100c2c1e000e80c546524803600482c0c060f21440d20001d1101032850043c03c00c4054035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 749681537 1250 749680287 749680291
    0x4050f010201020a020d030c03140405101d0c0d3e06040b030c09030709020a0302070510141614070606140a051c0c080111041d060d1106071a 62
    0x85451609611081005a00b00e1196121010058000f00c501a510034042e8200c0b84050100d4500001c900182800e4403d98a00a0b01c0440e1141c0260583c0d400d444440c0c0112510854803400c4032099441c295210b0b41d4880308540c03110301810003440170f4000e0000501601009101c5601070128064045116202841c0a01101d5090801c0c3c2041d2f03081c070341072600a50b03040e07480803c1d98900d16181c401c00c51069030480700d0300316854881e40c100450340b007070b982c005811a5001c5880258032a00c5902d020f5050541c00d80000031080c0c50031101c09045290426441c2c0c002a01040e400a4281481001c90f954020403c8485024100203001c03c10441e043d4001070880d910208501c40051801007000b020b515507118880c1e05c01001d003211313441d6080400c40c400840d803041d41a45401c036607803103c0e079094078070a002402a111001c40c00b000b08490f68060440d440d01c001c24001000c0c6041000102d104007141e0000d80100040c002403900e544801c1d088910064201c1e408580701001d4000d602100401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 749682787 1250 749681537 749681539
    0x5040c05300f0720010b100504050a0530030c0a0308010609080d02060a0c050c06040b0402030705150a08070c1b0f091a09073506060c0c091009060603020405 69
    0x20100020341800c0e400b00030203004403415a600301440c0d484121002541400d1351081800755078a40704181c00d0b54507503114106c040d140d40c60b01038a6500c1d01041102407080c0d0f901090060300e0000c9080c440700c4052a1000c0c0700804507a00046c1d42c6040700320f05241d4050400400c2c190f10079020700c40103054100303402c0c1e0304852059841c0c1401a4840c0d4100f522125600c07403580c05030b481034001c150340302201d401025812030146003003414480010781c07007407030b1001c2510309860480010049c407080d81002d00804014040035140040c0c4021000810302c3d691040600072020030051102141003c1c0c841c00d80010501e8000780c3c07a003102c180301c10784092444028408c5258070065039200080c4004d860050102883e00c01d080518041889010b0040485000344844204075041c81030300d210040c04074103e025140000d4008541180e0310126641c8100060f0541e03100c0c1c0c03024003400c030080394000f9028902080030b0b240f0003255286e0500724080340712150440907003141803000c0400c64a034145d01420407104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 749684037 1250 749682787 749682877
    0x60903230408330702030f0d150b09090415060b0403060507030c0f0e090c041707060201050c090d060207020d050f152a0307020705180610090e0105040c05 68
    0x8211070343c0c5243d40c080c243d400851041118280e285100d03441800d0f9071000d0700c0d0056a240480005460311558400745007050010780e100c03920405060700b01041000307403030310000b6180380c04420000541711400c010b200400b01c01d40310390b800400030003030b802100c018901e48000c207440d5501c80c0340000281c00c044516400007481c0c840714104542c0f06041004100385103840740940407001d4001d1101503400104011111002044001404100002010440c03207115000d0180a03003071000003401e60350080d01c1d4502d000003d01c005a01680c9010100c00c40c180d1140b00141c0e0b408040c4041818400d031088007400c135000d07059544110b00008900751000081070070b01c82c07240d0760311000c4003442000b0352041540c00510342100c0404c0301d402d041c002c0d904140180104d40c91281c0d01e6000401407414142c1c03403140e0800b90401d00c101030a101c0c10401c1d11a54505065416a0138028503040300201445030754480c944980d00d0043d82070140b0210354820060780885440002c03428142c002d541454061011208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 749685287 1250 749684037 749684053
    0x6011101050105010e0609060403020307030f05070602030901051b1908030924070503070c080f12060d030210020a031418061e06040911030d0206160504080703060903230408 76
    0x8180300d59810790b941615482d00c100a014280115038008103172403078100804000200148e0713400c11511008510414407405c0342c100034608103003042c0c0f0f19803003103066500074010322201b0386c0c01006403817192101c2c50b20001c8404030780090b141340000e2003102c0d030018140c01d43d8030410b00c900310700250f1040d041c041c1124061811100029034100c01c0580702c914000f401400324038014411030007503800052a282012429080d52901071855110b401b100104a034001044c80d100301000c1c20044e8001d60403599070390550b02d80d4501030344035a01072410b440260b0740042c95180003030003980b140c600484010310400d801e2030092845d03884820785e82c1740388042d4403603000010383e903414880140c10512007420152400361201414003001e020f600404403404075140e5000d91707050b01c00300b02c0d882c1d40031005d900070000e504100d455501c580d9568900d100c1045800c110a0190401c00101101280d501480001d005c050038242181c940d031900c031005074980c4681c551340405900c000082d10943d411142620515 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 749686537 1250 749685287 749685317
    0x2406030204061a0d0b0f0907020309010815030d11071806091503081b0109060e0c0a0f051e270f0a180f061401060306081005090c060c0f0303040303050601 68
    0x1882c0010307000032980d0f100300064000441a508591141e020140c03041b044029108001002e909040b01c840005074008a43d0382001c0d84e10417960347d000703240c6a000300540c10310580482c0d120301ea0001000c4c00e11099a081d10f24400c0100300800007424041c007040e0350040700b1480381014004900c02c5610315403d2000c0d202e185e07032400d101d140840e64040300c01c5141ca4078140100640c001d905241175219580c6100e0320010811074003c20b84a07603982c9002c1c01c0101255002c0000f43ca5040d041040c590440310300600c001e48404003a080000f40d255051b00f010004040010002c000008910950684070b9500c1c81c18502c450b400180074200750b0500141c10b0380c0b082c050034212080744003001c02003680d0803800c1011a190482c03004120f40142c1001c611407a1f0070f0701810282001b82e1002000a99a4600308010f05017806446201034078070606010328105000200d990b01c2508001d94820724002601b0345880c0e0042005184034a80345054986a107086e040140060901b16240c502060107403a184a40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 749687787 1250 749686537 749686559
    0x10e0d0908121e04091a130b01050a0c1103030d06030b010608060f0f0607021503060a05121024181b0804060507030e01050405031b031303020607240603020406 70
    0x4049104407103d05019060800b000d01d100007603140b0b0b03480c1108000200f10f81d05640582c0945102c0d0f240890003503504603050111505090305089002454501c051490380c0e40001200c94042080c90500c445410350309046800c4614010381940c03500c400030341707a4620802034209404072802141c0b00030260307a079000251004401100c65552048020640348130707a1030060500460840d001c3c08060600e1306550208551642d444403404403400c01008004091078000b04400c0074182c00d4625055818100710441e0b80c50300031581502481d5200d55240032010034a45420800b008403c1c0f8002c0703401e40d90141a590b46810800502d03c0e1401d1007035066811010080280d5152a00d95580103a940d07151a008014400a80b0001c1010303140c11008421000034003809000f00e014601035a915056481240320324591110300d05250703003040c40b10080016100d01500c00300c9030151038203075945072586002c00c0010743c03001001c1c42d80c101082d0071441804050344801c0a07203100b40c808000b01515281c2d5a11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 749689037 1250 749687787 749687803
    0x50910080c040521010c110705190504090501092001050910110a0b01030210050403053a0801090c030506090a0b030111070b070e01020723041401120611041203030c020708010e0d0908 80
    0xc47c0da03021420070070490a0496540801a00880c07013600010349500c0001c00756004034400782d800c1d0391030705001414083e0340d10400c0b100c00b503030717a07207090745600c2150010f0443d0182d507884c90f104409001464180600880384401100c000d00140c0314070b10224a4041c000400c01c0c00b09138010802030304000081c40c069000c840541390098014405414100f5040c040e00004e208140015001c0071004103513590038492a160095640e16402419030400d68244225600c11076801c0415080c03601340b08464481c410080d41003d0410808210080c0c49000b00303016184076038034121802c40001d414030520091500003809140345a84040010340200300483c0e4800907030003165440c0074840d245000e0b0140c0b0b5030b403000d200d081c05080031480f07060380c420f022100d135026440381a040c4410140c0004108507442001520361380c03030700c99500301801c01c05020b40e034840d0f138071005084c55034508a01017000c0c020001c1c8402800301000a0100071030404403240c68031000700b0b0640100d40c018001003407207880825090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 749690287 1250 749689037 749689067
    0x316230601050d14011b09031509080901110a020a0f0303080609070f032a0806011101060b0a05091f021b2e1709061501050910080c040521010c 63
    0x50003c2c0d516152445004102d0454030f5240d0350f1910181c0d54001c25010196554000b900e84043d44c514500b8206881000c019856144034a090240d00014402a06403002c0c82c1003842c01e00c0c4048007681226141c2403280c0c10107580010154400102180e81e407010030180c074440e030707a03c8605403034078024402c1424043e65401d010866031560505030a101ba4807a540303400d5000f6865014003040500c09071041460200c01303002514031400c11956503080781700240d45019400081000c10300d4041d90381001d0040600140400100090341d091980d01c4403003604400c40142c0d1111070705a2040d02c040d43d141c8040c1c4c0081c4440d000380c0c196505c03900c2d0100c081510601c1c5021082d140e503c4c0346c4003240c0e911040340f22203805e00282c0d684c003407032a04140340070900c1041400010582d41c01d01c00c000c00002040034000310f0400038100501005e544402e241c04107048410f04201000303407a481d00d185124029900041c0d003290081e41c080c00c0d080d192002010b0038010540c000c014075120860212901c8206642c26 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 749691537 1250 749690287 749690299
    0xa09060c081003020907030609050a0b0a060503040b01060305190f0902090a0b0315040f0f05061009050403120b0109050d0803040b0a060503460203120406021b03031623060105 77
    0x80000d0b0034203200705c0d43e020509180009040d6111b03034070042107510503104007001c3e07540c1c0c04001d4911305042015a019041a0605500310b2400c0e9650198900d01402060101619880801d901c1e401c05110521407816000c0107101c1c0340c2c3c5c024240707801048009000d9100c1d2442d1030101e00016264464042e02d1b0340050050880c0008095214611410141044480c050b0800710f8601150000c0160035155100360b0203084141442c0707101328180d840e1504212030f85d038035203814040000c0c4c12540840000503810030116224204a0060320620059880182c00240d041040b6007004510740040d40314602c210b83c1800f1360344821101404648090240c2a0035500c95409000c528159003550040c4048400e481c08014442d074a844001e04085031181e900080c450b2410741c2145802e01c04035800d100e80d080e500e4146850550000d544100102202c0303501100c00741440307102d444c00c1c0100d4040580c24440e07a45503c40b289404445032030340301c031040c502602c0141544003071000402c0b101c2c121a001071030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 749692787 1250 749691537 749691539
    0x50d051303021e0904050f25061808120d06120203151b0a0e132706020409140405070605030c0a0e060702030616030e16061110050a09060c0810 63
    0x80c4011200c00c1c2e1600f0b150f12000c012404601d0381c8940c1c080d842144600042c060001c0d01654240c0381486445200310154403800000c202c610140d105001120410324041803520f109650710b804044044d08603840358012040d160860240d000d0050003402d84e84401000401d42e25581000144e0800c81d00030b6141c0c2200d410401f82e1080e4000072904030300351082c084154003031140014040e0340b01e0240b0401046003100e080f00c480c07528084403400c1081001e0140b00f000003d6201c068031202034807040f1070f10b002006801d4107015060703040e54094a0b9400e810410500130140041c6243c0c02201d04079210710840b4400b2800a02c0b0f10242d034040c41c04280c02c02d0a00070340b0281614285202c980280e00641705106410142c2c0e0100501d0f030080c001750401c6451260485001004c0c1d80f210310346c0e81d03c9644405844045513818081420440d03d1a1a00989543c3e68910b100c0c2004061503944094604100500c4103401242d808000c403644030380810021166818000c1d10300080881d186c0003940b1028070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 749694037 1250 749692787 749692789
    0xa0501051207080d080c0c100609050f04120305070c0204140402030705120c010521040b0402041a01020a14030702090403080a150e040201030c11071d060904020907050901200a050d05130302 83
    0x21107140c0050360021b420341010450840c1a01c3d01904400140200b42c46080c200181841032060b00c0d00480072000750001c0b8130742a00c034143c1000104c0042c2e01003565840c0014a6148907164082885600900c140300e48031402e0300c640940d050581e01070f1702c42e01034070400144504c0d0480300007040559000141c600030340c000b001583c0304e40011207010b0188500c00540c1f4144030303042c801c441c82541b0a50810751982882c0c014441110507560010307588550000d0402916038002074890461948030090246076004104401e04501542d48025086040b07031081c0020950040320701c91113282c1c0380e0030420039801c1d1441c960034032486d5031160000d0102c1140115000d54440e401c0842c3d1209070703091880000c0d9070a03542a141250382d0b882106843e0780400d5010b02d00501c11105500712030216000c0700f030b9003041e07000102143d101800c0b00050200014131690264090a06502c02c40c502d001401c0506104003881611082143d90850740c0f806004442e900c028040c50607900030f0030450710301a140c40d055034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 749695287 1250 749694037 749694047
    0x30804060c052107080601030b180c0403020d030816051e0306011713110a150c0615060e10020d21020904020304030c0309060801061209060b090a0501051207080d 71
    0x14910318200070080091041d400c0003400d00b040d00c41124030010301c03e0b260211004113280c0016103060304242c144150042c2556501307465403424404e0203218002500e911603500c0c0107201d5640000e4000806a0000080c5500000d140d0320800c0581c2101841c40364461046905208540102d41da01240d4400716909035403403c00745038041410304144c031240884607548610040202e4816104000d05c944210402c003006540c8a21000207540d0640c5290812445500c458401180760040002000091003401100e8101d03c0000c6126440101256114032004025910b0b02c0b11a074052081c5264400310b0318070000d505440701c181e82d50390000a03900d0700c00b800c1d91840008075031040c3c00d80074480003019070b0f2a48000d41c0240c3c440d454140c0000c442e4500a0040d03207040d801082444500c42c0100003154108130601d04001514100180d07103030b0744e49030a00c01400a081c2d85500f03c003025003000408155507018070706a038002c450038a0440c8400348451303502c0403140241245a04081c1003d1940d500131 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 749696537 1250 749695287 749695301
    0x60a020a020124150302040305030f0f0f180103051609030809010c0b011805010b030108030d09140a0c0f05150d090620030a0b0409111e0409050313080a03080406 71
    0xd01c00880c3d00d1001c5507080f198070b80501c50280d00c20b148070000f000405281812010945041d003015401d0920756101d80d40c90340a4109880302460300080d0500011905d40200c807140308a01d1030b803a45403d0030400382050f03c00094509800710f8030f40004a0100c4191007580b903007003001590313210f4103541956290a07190b04555000e5041c0700700c3d80100350020720012012030280c4002c284d00c04104d403440d2517210035988103a10900131000200018403000c03e0210482d403600b0042a07011804103414030b03000c2e0040940c0ca540821390300800220004000c0080886000c94861001984900342c95208118003002d00c00099a2414000c001140c000d01c815000560012302907640040d4500706440c00d80e208241c0902e11b0003a4003000020000746442c1032050289620081d10104901080e60b0303204956000400c181f01d100e51032441d07919800d401080e919a045e040040c00c02e000b510743c9813800c0d42e600d40245121401c0d1b0804e101002c0746806000409aa816400d695100320740c1c1c455803140c070b000707001d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 749697787 1250 749696537 749696557
    0x605010f1e0c030318080c010c110601031e0b012310050d05060307030503120f16090302010309050f070f0303080c1206060f04090911030d020c0a300501061d0603060a02 74
    0x25801e003c9110017440c000104014000c40b0070b15520501c401e00d842c211483c0501c1101032081400b0130380704010000404c03030306684c3d10040d1007590a0011122002502c11000c0050441001200201d0180e02c0e40f12004100c1c00c010402500300c070152000c00180d04d409110300c000003407041c8008580c05206403c1250018005800e41c0c041680700c5d120b0908503804000e40070564000c1d0010b100c80c80c40030300b241c01da1000d8141100c2d0944044501d000380000400d00c0060304041c1c903a036070034090150500c603c0c55010b10b580111520141e650900c018110701621064000c10805030016149103064011900b6000c103400200103555540c00800c0b54a030861154810908010b000c042240c855620480244600a00710805455000b100f014941401b42c500030003190007440c200a8161100c201c504240d44070100f400000d4560450f040424540680c442d5010340c1d260725101c024400103602110030784503040342084640d0035048018254520070781d9034940586c0083e000809110080d0b01800359200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 749699037 1250 749697787 749697791
    0x10050a030b0418060209120a0206030106030b060c0105010e010623070326100f05301501150305011509030611070212010b040617030d1a03100605010f1e0c0303 70
    0x1029010066040300c4401d003c407a039175070004806d180b0f49084840241d4452060303005002a44850303000c01c0c03103400113210340414141c4800920703100346e4400050721401c2502c00003c1003950fa480c40300b10506c05003803055001041103600c040f440c414050710420031140ca1003112900d0301160741e0f0120f40041c052110360b1101d000040c42600d09403542c0c0222402144a01c00d05078545041441308403440e10346510540c071a1810401d00000440d85280c001e08081d5449440007401c000940845e0402034200e1540252804240000c600c8814a0400140180366590b041056a1302d400c40b03522880011100b010101d0790002003000021a6500140d000c036550505103410409541c7c08a8007404003107440c41b00994640c010b616150815110b07002c010410460300c01c0c03841d64445234403a2240b150140c600300031a00c03205094080c00140620740142a40070702281c2c19912a201e000c8014043d0b40901c60014507040c501400d60341c0303d01c1d500d042c0c40600864004200c180c18105542d80040000c086080c95 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 749700287 1250 749699037 749699051
    0x604020f0f0f280b13170a030309020a0902070818180a1a0a09020c10020a05041202030c030a080703030b0904030504090c030b040e030903120f16060e161410050a030b04 74
    0x43c10300303042008000ba860943d489480428102100740303c5a00602d0303a03201c1025205500240c0019010503654160500160f4503480c0d0000c00d1095189801c20300000e40002005001c0040990082141c2040c0c1104c507203042c1c2840040040802c2c0c0b401c1403840301e07418413020a10000199100405080d8840310000d101c220075030115044941e191b0000e400968003041a0b0440f42c014000c14041d040700300c1e0110315181c1c82c5c080142c03a80c0518045d43c3c2c00c40d036445061104640342040880d00180c001170890b0000f5940b460440070a501c11038048000a00b001c81503d540e040036081c0f03501490345a01c1d101d041c0b6041c40160f81c000c1100040d00c100b01074681f62240002d807218850b9090448005018603501c4900c1030a0515103011840d080780d0402c1d0801683c1e64a0b811300064603100349004000e0a0a10600d00f0564083d004017808202c250003070300340c03a0010111030740c1c85200311052040b070415145c0c088001c100c101c00201041034049a0100422041d8601c240d010003a50280240001058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 749701537 1250 749700287 749700349
    0x31c0905011103040b1008070b090f03031b2a040c170406052a070602030c070606180c02010e0a020405060a090e060615130e0a18050604020f0f0f 64
    0x90b07207050407540c1d4150742c00000d00041c0f04030346180641c4241c15004003010146801c0300140e440e022842001900040450514115515070b0440201d401c4010102d945855408c000034a4416158010710414032030225098210744200e02a0481c0e00e4407044011b00d44540d4074180000342c950008204200652081d948645a60242416000d903010300c0002445240c0300d912050031030b20120f4280403140c1c00c449030346410a1000122241103500101c09600ca0711a0307540074040b40950540202280d00f404804907548050301642007035802c09403028001400030040907400c90307c01c55402d81003904102080c00150416412007500b202010b4544450395561301014411030703203940c0c10300c0ca242e08030005100c21442c0042602c201c101c03008829034070382900d5000304440c50500341304005001c1c0815000030b0b4a40c406a00955180b11506603686800b6403619003191141c0c8116400c078400c02002d00488a541400b12500e140c1d000041c01d14461040c8100402504c2500c000406004003481d8080c1002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 749702787 1250 749701537 749701541
    0x10b18010b030c21190e0a021509091e0a1a04090302030d1103160908030406080c071401021903061d0a02090301020a0908210a0e0102010b0a060216080f031c090501 72
    0x48551024484d1201d41040720b900000241ca940c0780340d0800d41070804031802c10070301145a0403400d904403428403249d2500b09160320207000e03502c40301e940484408100700e0421340704020846504555134010710b455850280201c200d41a01c2d0401c030200700440050303441e6041a900c1443c10300d00038011a07040000c101135182c260744d1480c11030310405001000740072050003880345400c14030b03a060a100800d00d0800c4520340d9039020340d10a01c020480799001040c1440354410854031202d4002c50b280300b00d03076003d241c01d50207036010a00d50000e040041c006100401c0c420700c5510195001d540301501140360004020848003030150550725029420005d203407640c2c0c5c091000740f201d001e26884000d000c0703152001080c1000c002400c82c14503031010005101c41c01460108a98141c0403e040030440442d05500403401491445c0160f80c12400c031040c04a0403a40004800390000341d1b2075680c60b030307035074032641495190600c9002c4011194001d0010039900318200701400c58050001e0b1001a410b87d00e6206c2c01c2c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 749704037 1250 749702787 749702827
    0x40f0902072a031704051f0c15020a020f0111160302010f0906060f06030506090621060106120c110304030f03120204090207061a010806060a11011a03010b18010b030c 73
    0x450b020b141000c008106621800b41000f510000b001403c0500c0d003030100f03411060313038461140160b265242c41c4108900450705e42040c690440009180c00030f80191104c029404101a48058800c0c6c4c81800d01508050054210301c0700040640342c2440644551030a0428004504500f59501c03405942c2e074401e11072048140441c0075160100d8501e01d440005095600f09410010405003840700308541c0303841e101c000c690000000d49601c4090034079080420843c2e1484a00122079024007000011442d0340503120042c05070001c0010043c203402004103680151007414908540c0c1c1050104002044240c8031903c1102d0103810b1281c0c041500703030040001c03644650001800035074041500018040c07980b085500c2c2d403442002403001e424003100060070001c8014801c0d48a0340c00000c0d0310020f184034120700c00d04c031000100280100c2c980040400304a4064400c0c4602941c03904200035080d19100c500c40c40403444821070b03691982d0034952136031541d503c01040311014040800400c0420150318035a0b117 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 749705287 1250 749704037 749704103
    0x12050a02091c0212060c030402130e03030a060e0106052b02040f121106090d020436110613090e0a0c080c04051b0d0e0a05010903050d11040f090207 65
    0x81d464503094410401d0101c05030100515070703801002040b1071030140f1b10440b034005030101d401002004400d59100040c14210403070280307071301010041c4842280150480d90a85c0c5545000c0c0440740c0c0c880e9821111070080100c22a0500c0c00ba40010108011519103440c0e5009000e8001d4a440d446017250f8502c051603500481520803800e020006100c050f9034416660002110020319021071362001603e0b0a1110801a106a6540708000c04100481e9408600c14400d203e00c25034000711a451545450140c000075141d003076041300070304668075016017107400307000c2d640600c0030016062400c4400101403946110a0724031407010301c0c60105203110000c03001407200c83c00400c0714260308030030b103c2a510040e1a4031010301540503201c0d6000d056205490111040d1640010305420322081c080c9069103040c03001d8865403a00501c9030078558080010200302c4091401405803000c10100380740c051040d8400c560303501030321050a1000150315001411624040c005064100104404038810b4180000d05a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 749706537 1250 749705287 749705329
    0x90418020607050a0c0b03072025030b01080105130318050604030b010501030b03161203031d06071701030b1503100e06010501090608040c0302150417010b0906040c12050a0209 77
    0x110200400c5d0340d024006000854101c0d030460501080280141e69928004541c3e41440c21707100c91015020400c00495000c04c520300c4030507602400084800210b1400181c4441050800104005405000b03160180060004180003209181c50031074111400340b100b020342e500c6903170000a0135503403080500055030203024114803070b500d484005022200c2d041c0c2d0141c000d0b00705c00c40000740700d007201c070f00b101c2158201030101e84041581c0c5000c80c018502001008039507100c448508620040002d81a44900c0481d111121003200642e802c01c80e1500903c0020084807880c00020b262010300705100011a80150442d131005078a02441d40a440c0d4100d120f2a050748481c00401c101d681c0600c041c002025242821205400d00780c680d40003142072800007a02030031004000c11010103411003120002c181404188002013680c42030903010b068100c1c0c0d403522545030740300494054039061143c503001e0708154032103d1000031500180c0c0301900005205269040e42880003850540740c0c00c0240c20500311035030f11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 749707787 1250 749706537 749706553
    0x8040918172b0609180b071107050a08100b0d0f030f0c120804050601090606080c0f04031703101a1207030b040603030203130b040b0a0516060c0507050c0102010e0309041802060705 79
    0x4000220350090b0100d4a00d0140190f41750007040c90042032a805c0b00c0c09152070646003408280d01c500c0c01c81d07030740d0120b50002c03c04034000030f40d040041490680c51140a6062101c101c9903010011900720f1070380e014006190b8000b00d100028040c0d00c84130030060581c10400025200ca403a042454a619850304012610410800080200512080340034007040d8104018050502400801c11a4001d1041400580000340540c91100302401c0d01c000b03503400783c6540307603075900d1040384400c0b0f4006961585040b5807210010804c1000460f1704020f040d0068541403c1c04641c428071400490042d00c080e041c540d0ba910b09040300c1c1ca80d40a1a03001e107010343c000f155030b50021002c00c030030202e003a0310041045070b0500090003d40340b17020850301c01c10b1407032501586403000c1c01a6144c41c031190407002081d47e450b00c00020725051b0810054880c203401041501c050030741e10f0005a00f81c0f45034180e5a07115820400c00c40280b46003640c010389000b20400700d130b171600c600e06501207011a8088403040d201a80700d648 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 749709037 1250 749707787 749707799
    0x309050607200102030a0203041205030c0a14011b05070308060a081902090609010303020a030804080c3408120c0109020a32010e0d061808040918172b06 67
    0x101544030b440d0a1000758a03100c2c04810007501c0380a80e00a01314010a41c0b0301500c14040c04200343c502d10740c654400c0c3c40c8085014a8100080d100e400b011161650905c681c070b5400d0104441c08000c0c980103600c0d806e00d07150407503030210b5160400820a99200c0092a23010540311010081411039108443c16108000750741d004000445400402c02c038440d00740e820043c40001c0d07001c1440400941d060a1807601526031745481581c1d0b0007081c000000034810151183d000509510b4410440c04004001c1e00307481012005034007800b0b0b418000e5040551105044040c2d402e08000100004d030b5001d800001c54010310f50018421f00d0040d800f1982c0b1084001e00082603c0051038150280e4050f8032403680081c00c540000381002c03440341d00e66403081801651540510249402c60403060001300c245e42180105480c4c550483c2d0410300548102d1464103800c40c40802101c08542c0b0080e800102c11040326400325900011745e401400c2000c0d070f5021118805084280903e103559089044a50100b4030b1384c1024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 749710287 1250 749709037 749709083
    0xf1101090b0718210807050d031d010207170a090b0f03040c0f0e0a0c03061d010303031b051b01020702180411013006051009170f12070309050607 64
    0xd07410403980000b0240400016480700d4800500603828500415100020700b820b17002401840c01c050010300a184540708910b074143d000c502502020038101540f104003102250803400380e003030020030f440e2111149401101c052009828800b11a2410f00c90b2151141d01c42c4542d500001c071149800000030043c0010800d41044040c06060400c4a503e01c4900d0200c0e100c058560280c1400040c076a5052075042e5035100c0d401100c05804145801c0d40d400340361941072180c03007809101c26000207242c1505612001e0060020351400c1307a4503950503007081c06240034185080f00c0b5007110000b0359804c00c0b9034801615160043d5440c0364800404801c17a01c0c040c10700301100e0701ea00a04904120303610210b500c880c004842100c0c0131854240d50140c01c042c9441c4810010070964204c264844521a0002900c90740320803008160f0340804100d58030388900d007220599a4801011114240e080081116a80326448000d402414042e02d803864000350f581c0003040303003030348003d90541b03e0141c01c600100707259580d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 749711537 1250 749710287 749710307
    0x9060b040c0c1703130c0b0a140405030a0b0903130f090b061c050a09050709090c0f0b0304020603040c0b0706020c190309090b0402040902030c09010908070503030a0f1101090b07 78
    0x9050191002c58182e0329a2800041c65008800c491004008184045520300d159040103070b00a40000303220391500146030356600b142d03484100251004c081c1402c0710002c00159400c0b600d000d00100580d0350b480d0380c0c0d2114280c008141142920080c81213460307020074041818010000e41d1159600141082c4101040d2469140744500800040000c0c40c1c50501c0140080c0c1741c08800500040c080d11100540009400e40480141071845004c0c4082038100740c0d907014424107031140c83c043c00445e0782e60340f0b4000c0040c654482d0300c40b060004d00016015040400056620604c2a250380c40e803940c82e0781c04008207801000055501940c0840c414080700c0080154520410120b0041c101402d040c0d0b40052500411b400340003100760b164099030401c2d46903501030390003809440c2c405540701c0c0b91400155000c0c0d008102128000b807441c2c40c00154210021503138409540024018600e0561440810f50b4400c2e07050700c245003044042c4000c2c0b00203d1086c0718492000d41325001b050058100444018020a05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 749712787 1250 749711537 749711561
    0x8060a0816060309151506120b060304030f02070e130b0c2a0f030441060a0e060a110106050a2301200109020a0b0f0915040909060b04 59
    0x10300c0c101070a644070392655034100d41031841c0200f8001002c1c944404091080b0000d66030385c608204040706001350800c0d14609071161a940d08941200084400c2c2c103035407402d8405030704520200003050100340b00315041904445540116200c031a40c2c4c18240d43d001c0740841303802281c0080380101100300f0062402d00d94120800d0102c5078200030070310005040060550803202c09103541c03011100800c8070103015080a03503804000b5251559903400940743c0900050310f5080b024524191607049030807007240c0d0120304901d40082180e001c00b1070000e1001642c006030583c0180f00c011002e80303040e55203c4006161202103070391030b4020125214401429120180c000b03a114024110701030000920388a4100c01e41103c90f200c040d03000350202d00503030303901c1c55002c5809102940111482a0140c05422817003410344281c070b84400c201d81d6288421200d020318100c0640750f24080040a015207802c140d03241044040c840c21625107076031100114212030a00c2d86c206c550540b2020903903e10f00e824840c0b040d074026 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 749714037 1250 749712787 749712793
    0xa020304120e0a0803040b0316030e120d02040314030901110127140102070f0c0603020405060d020c120c01230f0106050c030409060902030405010c14031501020c040c08060a08 77
    0x50640d81c154594400080000400c038042c1c0400d00155162901c0c207004116080c141d03075480307490390200b0700c03c1d0780200e0360b0079410051060074000341486841001d148440c4607018240c0724240d00501049036100a211458583d001c1c440030020a001c0c0303029250081e801001075984281980c0054206400243c3ca00c07083c0c0d24040d411110015204504983c1c0c0d42884012003802c0e186103003001d47c08010b0483d952042d80301040b0001049640c00680191900660780640036956550b4200c0aa20031809100d402c01030902c165242e00455030054110300708144240c40581d840012030703214a420580d40f00c0d145039181e8903c44800d044450441702d410b0740041e80750745036190122042090140610031074003080000541c0c540c882800b80150b41c0649110380007445155640e04010020390003e03a000d0302c6139407030a402e82d624640502e05c4481c600810b412418103551b292003d82e043d06480342c2026065016090b0a1212a41c0b24411065207a085403075144150601c0010711100c14020341200c12a0740c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 749715287 1250 749714037 749714041
    0xa020a120c0f05131e030c270c050c0a060518030f0a08060d170304030e010c3908030a0f1b060911090415050c0f030a0218030703110102060a0203 64
    0x1a0321480c0b51002d00c0e640e0400b02c1d5110510303201c4180d441030941c45900451010031030300c0405180342c88140101c0340070300781108950780c5401c4120303070b43c92683d1001d902e04182c0c55002e001038510f80e0482c00c24070949041950030040049a014108020356108070b900791769510400034040d14100c65030040985180046040082c01d080921041c8030301c6484400340702000780000c055682d2451003c2c18590f110300c60751500c1c0320031284400c8681003502c003140498003070000e2018552003540303007014458001004031200c0310740c01e07607030400c0c42c0881e80c40114000a0b0540481d02c45120007034800100006001940d0f24110107100410107000c1010b820204080301d5065030716005886110000d10340c20003400101c0d03100614000000c50004c580f92a000f1150303804000c1405400080810081d80080c4203001a9550001410091090f5464981080024000305404600716405444851900c004074003041440c140020b240c401503a008a803410724507420f004c03203568148806500140c2e4a4400c0d0700b14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 749716537 1250 749715287 749715311
    0x31425030c0e0906120f0d030c1103030412090f080c090601090f031b0302210105060906100305090708031209100504080f21090d0207050d05060601050d140a020a12 72
    0x386502002c4544101107001c0810403d50394180c030240c8001d10101212420901c0c280e415855005000320030000c0391508041c145158002c0d100f8000d095503600c085c61442d03071203680340100c031610300d0842c1c420814503c4000c521701440048200c040e0050b107000703104241200b01000310b1658010402d504102ea0444100300400d1449040e00640740d008144405204021810000d610450f5002a6202d19030384c000183e2600c41e41c0e0001c0c10200040000d10883e6510700c2070114840040d5402034105450111404c07031107200ba40038a402a00700c4065070141a661808980b45402800000e0000340e114000e001c84030808111000c1ea5650700c400a20003071402c0d86a0300d065026a540385000e0303400006440945e103401c0070010002406042d1640413605000c851031343c1c3e402c411614a0094800d03200c010415240003a81415120790110044c00540d5410004541607002080035422154a440c2c2e51800d4184880f04544940c0b40d032600103856211040c0020092100c41d280003406518001c3c8a03010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 749717787 1250 749716537 749716547
    0x50c0a08032d1b01020706020406030b0907032028051b01111c1514040b06090a0909030504030f031d100c03030c0e06030109020a170106020d0c03031425030c 69
    0x120b801d41c10b02c1031010f20f16030b01d299029129085009200314030004010602c96019804a02c00305400d8400c66070036500c2c15800d80403201008801c10f8450742600381103131180c0341c55000382050034000c070610711020a1481122100c50058040101103000030038811048001e5480034501402c10030001d00801c00c41c1c0c4d5000c0c1c0d4a2003580d4124803d03c442446108001000c2d401c04c0c404c00020312084011142c3d84c0034000c51444084071002d200340d04142c0c82c807800789031101c15a0343c13074100100441c3c80d00d071501d41c0200041148460890a101e024400000841e00c07180d808269640030740c035081e00c3c184264407850b100c26520b4648910a010707009114504660240c020880c0507410b040c00030310000d400c5003d407044212545251384c0608008004943c650258001d0702e0583c0080c0c0704c40703882500300800650094000d01070040103030b0044481c848010b100b01e064501c0305000342000580c041c030301590410780000489040b04a284c10b00d50030f60b91540d128500d00c060701540d150410000e1641100203107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 749719037 1250 749717787 749717797
    0x20111150604050403170901090203100c0905100309080a020a02010813030507031404080f01020d140105030303040b15090901150f060909020f0f13300b04050c0a08032d 74
    0xb010b00da581c0d002800701030141c18118816244910a1480340c5803c00d0801c0c040c010480e0101e0090181c50175045c04000320340650041180d46444d01d16880741082c1c01e01c5405002e80d11700c8001c064075540d58201080c0b103c4000c3c44d03651040e40c06040c003011640005401c80c40d014002c0400d203540d1720942004130740e214054501050b0b040c41c1604160b58440ea02081c28021a007100c0d03100d01030001c3c9011300745030541c010706210300715a00911106040707020244800b8000d02c180703a0581c00030400140001c04c44c2007415070000d51402207414030901200455442e120441d801c080d00ea640e01e032100e540c1440d0040c070b036005000741d1602e40d165505010000382110080d00c03802c601c3c03e8000ca400c04850303d42006854074200750480558561006921119850045101d813019082454042e400c810b41e901407a0b0703102c40b0400a110802e4682583c0315258280001d200b81d50b14000e00c03100310003d68400780040c0c014000b1000458503078903031485c2c0c2c1e001c280650820001d00c001e9054030044a00c524004d43c5d07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749720287 1250 749719037 749719039
    0x81224040e01110f0406020c0406050109060c06020423040b030a02100309030516030504230a0b0703051605100c030209150714010513030f050c07050415050a0905040201111506 77
    0x101e60142030481203405050028112000c200002c2828011040030030b000d04100e1340d941d82250201d00700003051100b01e9024bc0940d40c0055484202801202d010701d0540307000a2040c2e03001860550b84011201c6035200900256081d602901040800381c5064080c640340640c1c02c4003d031032340c0390a40d40054403200c480101d0700d052544900c940d5003418020b20503162202849891203c03000040d14000340140d02c1401251242c03040d8030441c500071a00d01ca005e0300c4012002e405100398601741501c065658000c0c6001b1010000c003006007441d80d192091030740394401d03c00c0c4010103000c800030340124103441c42c44c1c405604051041c03192210965880031030101c030702074942009940301403505084480104423215815a9804c04003030051404140182e814054000d030f0314000c46840a0500300d80c14840c900d0001043c3e0710400040c0b005141a92082c00144105030300700741256038500200d40140f11661017464184d55440820042d540c00050081481703201c030019004180c1d074902140030209003c1d00c16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749721537 1250 749720287 749720291
    0xc092803020f01020c09090f12040602070303080c0d0903120c17011202010311041e0e0c0306150910050d0b100f050706181b06080106050d09021c08122404 68
    0x11142c50b4000e1001c04007001c0e015201c0e00403442c1c03941070103a5810b010f210980551040d00c040b180c1450000056400b551515030240c9803141c03454400706d070f0729640500320940ba0700c0704000d1403421107410302c00c407a00300c1d1080d00c1c1c00a1a85205020b5011140240184014006c03003c032000904200007c0382c074192400560341151560460004800425001d15011411407001402190b80c138411170302260326100688450405070340703030031140b44110416550112190030501c082821032a040c0303502c0311102403d8000358140410380300042c04200356588804007003080014002458120740c0280015000d0036550b8015a0354400780c001c080c048442909410003034081688010810143c00069414244031317104000d25501d406d04989842003400e640c00b101014090000b07019025181c410b0480e460b03501c8a5081141900b4240040c0c01060b104a0b0b100e80e0110052128900311301d004040316004450741c0c1c0e1a005258210041c1503006000b0f40c0920781071540e2002c3d40750b507081da280858182a140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749722787 1250 749721537 749721559
    0x60c0d050a02041703360108061201020a030b01030b04020f03070c03030b0a0609210308220b0907080d020a080304061a040e030c011505030a0b09150c09280302 70
    0x80000a000c3d541160384200c0c191000500c0d4150f000020300503800701c5515030440040714030740c5d00f4001c0b81c102900700c8411085000d031907815802501c0c1954400005090740d800b03940c030008a50700720381c402404071020a54965404aa0756894401c8504a2a05980c11454184d2445c0e45201501008203c9000c00c1814034408040600ca42c2041406410107401100140d486102c00380c45600940201580008910303001c010007085812400c1d002030705510360b001291921500e540110341c07546c4064074030b80300342245407001a001e50019071103001c00348080d00301d450620f031020f0f05265421102004543c80841e12801007005c0508803034100f51b0040b40050103643c3d0501a40944181e50310302503109191504c08116440e01200a1002144600c02044804240001c1305201042e86c09401d03015400b002c499800907000c1164143c00c14000c0c0c3c2141e0a100c4a0a800d00281c0743c02c031891805a0408180c0500509006405107070f600d5600600e540b0f100ac0041c514a400f82c03407444007900c9014040301c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749724037 1250 749722787 749722801
    0x4080c070f0e060906060306090c0c0a140106210305160c1508010e011a040306090f020306010605040f0f080d030b1903060501080f010209100f09050a03140f060c0d05 73
    0x100c480000c04400d00321009066a8524426141100b02c5505000300020000100c60303140000031a44a004004c0046107a9202ca09285038150420301e081c2485108003c0d0368800b040c1d0008102000482c10000801c8460130320340484480e003000e64001445400000c03030740700002c0e04074056070891814291102221301c05030603d0150a084d075441180340022042d00c452000b54440d201c00e0585500b000700c1c0b9080c0e41e90300d08051030090414231699007801c05000030b05c00181c40340c00900e0f0080c01075007100804802e50300002e003050401e920020118000040403c65402c090460000030910b4141291015250044a40e100c2031854a42e03001c065461040521076030f654000f0200101110350f004900c3c644030301d012002001c0a014103050b138801c0c05000940503005000b240c6c16250b02800c02464600140819220702e074000f04400c1c04d00c0508080460325444110b0721900071401581d5002904217400039643c00c016107002c040011340c0007801000b81103001141216003160031f40ca030000d940c0da5449 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749725287 1250 749724037 749724043
    0xa03081b04091b0905060702010c06020408010c0903050111031003030e0102160605040609080735030d020304120306030203060105061c05011e06090303080a02030702031b03180904020904080c 84
    0x365001a042000c9804102112543e10110743c1c079902d054400103c5101c0d20b8140d45144c014070486601c9a03003080742c07200651140f160703940d42c1881924094103058481d0f0116080d01d2082c10040c0c0014403124082040c4282401206202401d95a01c2d03444c605007a00800c03005010780c00003400b400400e440e6102140d20030050002e00c48200100e00c0c5400e034032600010416071043c4600c200041c003905022400e4080482c0d0082150380c030102283c403054252102050b01c882c0045840e8201441c1d05402404610900083c2140c60b01c0241c01030b62880c0c03d292244201e90a0030001b420180f030018140b00507100022681d0544070100c1b0f00544a03684602c10105001816009001c600e00307020000494004442e5030850b0504a51044a800d81c0c54031400c039540b0110340310141c001001030b40400e40305421540156040889403054920309407949048904810003010304200ca6400024100c1d01d0401902c0001e42441085510440e942010b1300050443e03a4040d00181290700d00092100842a0070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749726537 1250 749725287 749725321
    0x70e1f2c03150903070611161110030510050f130c17090f0c04020c0102090a0e06012a03030209011115011401091a03090c091003050c041b1d04020c0a110301020a020a0308 75
    0x160142400103402031400c80000c10409c04090700440b803010300f07011124000d0051354422000f040b80403409514000410040d29800301c2d04035002900e00048806a03d00e90040d200d8910700398940c00c3c02000c0a80b034030b903d8403d0050010030a60400c20309041401408685104503580444002d038807003800d81c421a009204004407154000305400001880e90344001400e8410182600c400b02d4bc400d4a019000805248100348001c9100140503880028000d40c09084c4810062401020301d8500d01e40491410801c240b88100d0002e90000400081c180107100700c9843c0020701c0d142022a103400c0400c451405490714880031508040b000a400a03405c00c2481500d01d4010440d14840c01c050740244440d4500703000c29240c0380605004241a800c01c5c0c0180719102000d01c070a42d00281100100f281d900c020a0f40030406034a442558000790313501d1340060040603103c000a49030002c298502804a2805d4080850080e4010711403c40c610743c012038030b1441c06c0d4040c100480260b6500301d01c2c50161107c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749727787 1250 749726537 749726557
    0x11e0e0607150b0d051f140a15231c0203010518010c02190f031205151215190207050d030207030305070e1f2c03150903070611 56
    0x800c12005101421818a10b0001000010040041c840c4107102071303440090b00141c6039034040e00040f86d00e028a941d2803100405003100000380f415140c0044210707003030155003d4034036544030403629611520f40320175035006007401115000d4251102000e580e8034160070703003004d00ca107405030044503000c0c0c4078030b41120143c0d5000700200914039000540d06105030035049411540d42ca813400c1c4e03690b06800001c1901e66580440c50059121103d507440c00003224100408400700182c4a400e0405000107000e0640124188001c041144039800b0074005042c550a5000c0c200da0301c80c2d80842c1d0740c4031100340c50310b4004a034902c03940301013182144010064400d1410040c0688103d07586014242c0c3d041d4050811070740309640a10085d1a1035404840502c0c2c007581c601e6000413065a43d8417120310314400110480260b0400c100d000d01040500036503162003850020702450f003940300113801d10b824080c111074144d0103a05032a1030f040080103103a4a010b000d4008150a07503c640309014002c482c1c0c2580d0309084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749729037 1250 749727787 749727799
    0xf0402090d0609031803020604150507060908040503100b0901120c0e0a0203060a0504091110180806090105090d020c06030a110705010e1e061614030109020a180302011e0e 75
    0x101d40e2070003200800320030000b60002094801480301e0400d10018400440340c0003003449041c5802c1c5030200f40307000f140c107103d402444400c104080000d030082c0210b0080c9401500c609403620b1401d002d160030010999144c1911516110040c02290f0703075048001d06555600206003148ad600d0302c1e00d03050103143c1d80c2122b004c4010381810040040416002584604c0058030036030f41040e41c2e40c05110079100c4ad500001d0211905a1021280c3c0c2401043d44943c4042480c01030060031100300000300d4159035411042d200e8000d50708010300b0745000d00031290096000e0700146102924000000d445c0d200750728074240b181e10004081800d201050300f0900c0c541407a004041e81d00d40c000e01d0481d000b04911191489680111044600e00d82c041c00b0900c00e14400d42e01c05400690313160a10f2083e2446100109424400c008501402a00200340a58081c121a0100603513400303201c4005000c142100f07034101000b840b07200c018030040c2d0340164210603403101605001d0070f000401c10140d031200f100018143d0898 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749730287 1250 749729037 749729059
    0x1050c0312060a0605030705031911180a050f0d060f020f04060507110a12020f031e15010503160b030a0e0d0c350a0c0b040605070e010207030b060f040209 68
    0x71010146034001c1e0403c5880303000a079aa0704041d6001e000c2110345e140030a006000107a8a441d1311800303610b161220490010fa03d444080d20144190002c5c80d43c002c0056155000403064249001c04101070141128080c03c590851000940024140b60005021644449150344006413a0701038030134481124401981f601d072a113400a00c207400c03942d02610f813803207081800300d06410303c0c524100980d8100303039424807505415001e00000d207a0030b206030b0360107100701103860950303450228111038005043c0e0003800c022105032032000154201070700254482e4020300c649180d58258051007508070751110400e2604c0e607903103204100050003d050ba001440c0a110103000086a01074a04158144122403462098201e4403540d007040084900510030300e83d5034404007005001e4403000d8412000149061040300181d0381e20011024070540e0704480c910f840382c0034006419041003040c030b501d40e13080c03000340107151035521111640007001c0d0095000e08642c2102180310b4845030102c50032008090000c900b05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749731537 1250 749730287 749730307
    0x640150b0d061203050c011b0807260403170a051909020f0d051606031a0111100e16090203060d02040c020f0111090907020a1106090a09090609050c0301020918040201050c03 76
    0x180d0112591b900c0b40c3d46000031440714543c40c074003083e15000c0303541c0c2c414010f80d95215081c0c6d105040c201c8025a1b5404845840c102c2060329002144503502c2541c0b42003031040902c025030090200a04111000ea050004120382c40b00782c103078020b01482c030024000c1a548483c1c00401c007012280141c0d550400c1c0c8180d001d00500000040505051b602c821500000b1907841c4000c41c1210540f050b54804a0030b407840d01c08140d03104200800360080100240d40301d007030300041c2104c12644914011515a0070651a910b03011a03010402d00051500460951851920b100040c60384400e401c0e0082c412561a01c100305014401c014000b40c40c90751200800c4504006034850032a50003441c80c00c1e103c1c030000000117103042d1021945500d00f43e0f0103000960714203030000400c4900d400080d40107070014220301c4006110422406660000c0b03000c1c030303400500c0500301d00b051030900f4240c40240e40240e0041240394840e8440c0300c8a9096007800c0d00c1d800c0496111880121007030301c2120b0f8200054400800d4030885 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749732787 1250 749731537 749731547
    0x120c100e1f111b0105180f060c0c12070f02040b040209010c0b10080d020c0901060e090a0509120a03020c070e1923100f15080f0640150b0d061203 64
    0x9030384045011200a070b800d001c1947d40d14000d42c407400654006801188401103214060705204080c14160350100f12030102031000350b0022503054850046a1354000b096003040e00c14403800c40b0f010380e4190316109150300040e12240768a14000c01b19251100007445800681e4400390203020100c05071600e05c200d01798003d503034282429120344078800d003200001380b05004401d80822002c010f41244616642c0550030700040100038401040c5000700c107200d141501104005103c004456180140c03201d420b00007151800c145a007010001d0383c600d40a0240002c4109904400c102d8000303008940c0c07044070840c2010350014a503e85280840e02003d00000280260206055031682d030542c541c1c1c1540d03500400c640680c00500c3c440800c86103800301d181030103404a0b040c1e004201070040e400700b821146103000340603080104000418410281194200481d000810860a0055051001200d000031031242c40c20386200d4120b01c040700088021340090941c01c1000180021040c2c6040c2081906020f8a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749734037 1250 749732787 749732791
    0x1200c010f0e0d080a061d0a0506010c08090402070c0306150317070804030b07051303030e150c07140d120305040b06060a080414120c100e1f111b0105 66
    0x1025424144031a107600524421100c2c00340c1180028010030441d41001e8810000c081e1194141d5074031644042001440040703002400d581884080c801481d14500100494001801083c10810042e2800006c11502c109030ba114600444006075074205600c2c1995170468981e000030b003154100006001600c0c40919014202c030b00402075072803400d00814440003a486414401401024140424030214844084650348440e16080040c50440c4212070010743c119070342e0040b170000b0700200041d0041e061404000d0401401c00c4601400c007000d1415098464641d03004000300515401440040d80c0e88116100c808240c0101100108054015004001d004103c3d001d8070003100c40404514503003010ba003150401c010a940d5415161903070ba8802500c030749100342002941c0306400840d4032910503240280000d000d00e000606004204040ca00e081da00c048003205601e13080112954180018600075010b43d4a03a241d00280c64000c6280d0700301c0c03c1c01480c4448840301c000d045008180d00301507002c0340c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749735287 1250 749734037 749734057
    0x12007030f02040e1219030f0212060a1a1c06050d1a0112081c0e0f0105060a080a03020d11030f04080d03061a041701020d0c05041d1b0c0120 62
    0x1200d034a4500318015a1004130a0543e5174405040100c1a4119504240e000700600f003850042070800e0107000140c217030313044418a08c40300c3d20701a0600c0402e01c0c2410802c0c00402281c540710380d00c40c044540b05e440301d004001d41ca51461040c801140310004603a480030b0003801008145030781100082c14003000b02001c0d543c5015010b016840040b454800c22540c1070401c42c2d0004455190684041e06581007085418088224540310070041810100c24062201580c038138000004061030140f04101c9500c4042d8000c5607990020514000072a60106a002c1440d5003820807140064010f407040749507100b00000d80c0080c05000c10301003012034010510700d0239640c0c65601880071070723100c0403801545000d0761008040f408042104000b0108509170b40e041e07503549000014140401d075a150307025545a542903200040d0002400c0c080c04c0010311180440f104120480c2c440f03498014540c0c0140c88103e007640c0c02d0007801052918074040250001d07404821140030b03003d95081c282c1541e200301d8100d80c4000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749736537 1250 749735287 749735291
    0x150c0a060b04020319090f06112a070512190303021207020c0f10090308040609080f01060f031403190207052b02010302091f020d0306150e012007030f0204 68
    0x503000a20300350090364080d280e00901c0440c0000c0b109018801091b500100310341d03122030060440049103040c8145903010740c005644540d0703092036052085a0b200031208921842030300540c0c1c06600600001d800041c0d6400ba10712807e400b0046462904d84410307a0f600345c40103680d18000108055050b00607043c90881c032590703115181c9903a98240e07100e51600321015007001030b40720003204518080e90940e00c0c040f003600303201c0642a00c81d11018020751168004c079000c2015403d08208003001081000c4401c050000200700307079400d2a03d0740c444038682d48400b51507982242c0080c00c0e144401e0045072244d03a0444d503404082c1e4200c910194960300984101489000c14407020010225003910024031411040903180040c05140d00540094101c1000300c4e4002001c0340c00400f81c48080d13102c420151025030028001400d8041c0d004003504c0c4142c021a58084d01211441c1000b038200c8840f08a001090030051060648880030404020140405154070710072417030000309000c1925452101c9900907201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749737787 1250 749736537 749736551
    0x10207210c21030e060424080606040803030708071103031003020f0d05120c1c09090b060901171f0e041b0f03080c010906021803010e01050601051602150c0a06 70
    0x184035030070300003808107011090190b100d242c00030340b0407003043c8035096005002c0c6090135107503940040142001e800700d000d480403034001c8000c4260000c9038503610400171920149071504000030280ca0340400307080d003401c0c0701507400811980c078012040c8400340504801203e407245440203640900320054801a4011b410888081d030340c030304000155107429900301000b002c030380d00c5c01035800002d0b40c49420b11410070b010b0440f924500e01d1415415040c2d21103503036200400a42001d001000b140c01005a042c86400c08000b0003a09907041010352040c8082d00f002c041541d61540c514440c00c0c601030702800d001c500390000c01308003484140340181c003603030103103580c2004000b954010684000c150f00401800c0c0d0058042080001d0340c04009100001c0c00c0310000c01d41d05034907901d03001680c1004d03500306041000003841401d681003d2082810b141d1003d0000e0185040030760010300700e84100070494480f004020094800c3d51507256941420200e05402c0c1c50b0784440c8541510b480d072203035140803940c590800c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749739037 1250 749737787 749737799
    0x204050a0c110102180d15060303020313060e0a120201090503060a090311060106021e03070b010b1b0607050d0902040e07030807031704050d1d030d091401051303020f010207210c 78
    0x403e54501510320040c02507800085c400300008500c4141003110801a84501390030420f03064002c403402188250020340d02c80d08000e02e800200d003459001400ac01016068140c51540c0d840310040407221509940680c960940c00100c0d2901b50a40019405200b044c0510034107600507406003403282e0003913650480c110141d58880f6112142846850010390280b5042c0740c141c41c2c03400e60007040185c0002280d241c16003a03030380c500c5a454242d1280d100c0034008a61001000440030700a0104140c00c0040c00780c500e48040c0c094100e000ea0aa03901c02159106020811500d0300c0c1d0091500110791011151160b41e24603100401d80e0080100b140007428008642d401c0003401c0c1da60740d0045030700c1009800106440300f000c0b00c0401d0081980a8400409803d8000e551401e00042d90603402540e503444100d81005458040300c500303002f115040240030032500740e00d1440d07911410152541183d10801c3d0380700010040b490b00c400c0360003c401c8031014040388840f420300c086141901c1880303000421549a5105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749740287 1250 749739037 749739041
    0x110103180b071b17220303020c01090803070b1f051818120d0504021f0801030302070b040612020c2103010311040b06030402090402011b0305030109271b030204050a0c1101 75
    0x1c041c4a100800400d00d80c00d440b014122170140000721a42120b5003000407000810b245d401030b805600003c04e100341550b8800f48040152000000840c5050b0301562039a140403c024210895040900c008004a002c051405c0004240c010b1079229140c0d007a13107070004289819a04107203002c080b01b5003407148a20205414048400c01d00c0d585041083c0040c0810140800174030407640481750941500000b641034031450007810840d50703151010b604615010386444003680004032000010700c41000215440304180c4544c0c6c0c5566405a242d01080100324901004000320840308186901e4400c000e4190001543c101c03805418245459004503040c0710440d078210100d0340c0c0144007040044d004d418024001c80d00b1910600d40310100411040b03803190300c0c5800117003c80020b20000010400c03480c450064134941030325031246016481194044483d480c47c070b130000901c0800c0140400e407004540c02d000a005540181050120b490b007410180000d09007084100c01003105c0340000c02c00e2417014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749741537 1250 749740287 749740337
    0xd110d0e2503031e090302040e0c030105090102182e0f0212132c190509150f1b0d020415020705010509040b030106181b0c050604110103180b07 63
    0x180c9400138020816072201020a03105808402486043d100010042e03e41c4c1c49002c1c040c2055901030320b880041c031002c040c01d4500c00740400c0d80a03030040c0940c6070345851101c00713010481800c4666001000300000d00d03080c25010804114072750342504030849010754100002c11f0700a0803e43c240d414a480c040f072034074440d0103418030b002c43c0d51034040c2003440084107026060b83c502800c000c0102e000900c0c11000704401c0b41c1220328031100070550900161100c998080c0036080b07501c040107030184850700c00803414034250041c003e00c8548006000318040c4130003102c2e00d1407100d81e80c0e08903c0c0e40e8030320502000040d602501c0f40200300c8a8075a100c501151010411505036981650340c04d140c00d00e10410440540780c500c8100d68555603580700041c0100741d100403c500001c0306000491b2091815004400c0c1944d079482c0602800702c4034113468002000800c9641c0e200d075000003e01c40a541070342c0120004c2c100795070004100c0c894441840144255111901d20800040e41c920f940b946803450501c1c0405c004d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749742787 1250 749741537 749741543
    0x1109010e0115110f0708010c1407020303030705031906060c0c060302090102060636100e190515060304140d03021804020901180b030403030c030b03030d110d0e2503 72
    0x80c800034419201c0c090060078205404100c81c81c0d00c138082521414608290702c913600380e030756a41c1000303146c40d0840340500e40c19007154a15424000b15401094581c0b000406c40d40c100030000000480b08070400c09040c500c01c01c50482001420f48a46014010040504081da107905180c1c0700061024072900032a400903070180d010b00442d031500c00a0200a010041f160002d944640c6c016484c5401c00c51000405405400480403860400d0740a49010300e0079500042c1c41c0c9590103041200c43e48000f035040021607010a0f00040503078518510240e42031514424607400f8100000303010a0005150a13404c14011480913640c900e0003940d801d07012403040c1d80c40020600c640e1944e11b40c2c00d14103a030140c41d4004c07041c10108450100d285031401029059000390340f0266000c0b041c803042c1680762042002e8042d10703050802c003140002c400030381e480c082d814400711140e0b01c8804c11910302c094842610b020502d851824007041042d40e90003500e441000707030f000c0a400f40344c0c048400c451184180e03140840350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749744037 1250 749742787 749742809
    0x109050c030106020c2211130b07080f070c050418030801080f0d1d0907020703171204060504150c020c041a0d1203090516080c0a152106031109010e01 66
    0x2480007400940c641009280007105a0306d21400c0e0a103020740a40034070186000c01c3c1903950000e0b080ca52410301e14581052220381814040d150000d01c90904844541d003606401648424040c90144c0c07048082e5085181c00c00c4c10010301040d801c0c001000b104900f44203490b240003c0c1e880e44c04d0140c0d2000c02c2200369a103540158181100d150117090306540311440582c094800d189000045000c04e001034a0707400050303100040410078042d01c001c0650384012150282c40c6000034014600488543c040e1000d450f030707035448001c94208880c202440c4485080700000748803e040d0003402039100c020000d0003138000d074142030141f4023556200c10041c0030807100418807131590b19a0384410244903052040441415070311028a00803940402c01d01e080c501107001e55440c0349003800e11141c242021280c0050003600035030011f02c00985124a0348400e000a8503180e440b17602c1543d10b00f8101405035005046c0c3c280350810220500603039104c7d401c54990151a01040c03039030394290501c440b00e4248a1811491 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749745287 1250 749744037 749744053
    0x2041b050a03021b010c0818031309270c080d08010302060a08040f05030301121a07120b0301060b031006081605030604110d1401080c0102031e070819080109050c03010602 75
    0x1d8060341c0900b040552400c210b01903120180c800d42c0c01c65214502c8040881d4903078080214044a60102c010342e0750340d400240d41058046449400f00c1801c40c01841c500a0712a030303004d012503c01c01c44240c40554030452076003078608203040c080fa60303562601a600786405014140407030342e070080f41c0c0203040b294041d1010349030400b140401c540015020300215007130302c40c40b90010301041c0c3c1040550301821041c05056400b411501c0d052850000100805e1403c81c5100c0400c408260001c0c4903081e00c1c40c9510003c1208000e0100290041c980303038100d041c41c0b507408420b001c444041468a0f0081d24000d0f07e030b600c41500c0e000540143c480b01100d0700b800091041002130070310309242d046100080b0001040a092020125690090f01d21203064514444040d000400424000f00955a0307441400c0c0080d500e44002c0001224444030403104411441000240003410030521404544400444002f0b2140903841000000c242c0795080c801c0340007560400c0c01092400005070100c0c0d04903115900101a24 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749746537 1250 749745287 749745307
    0x80109080315030a12031a04060e060d03140a0e12030301030209013005010b01030522080310050312030106020d030527121812030406080f0a09050703080702041b05 72
    0x240002d01c401d400d4060074a0890000e41300c0d040a43e408081c1c0d0318081100e4152034000c0c0e000c40c500d041a180f06505020b400c01480500002d102d0b0024000c0d107098500545604040d1401c180c0b1200301c60385072400260540c4400d030300001c03001440034119078110354a070100100965a01083c00007944c001e00e504010041d28151100007044059695504016060083c91144200c001d1840c02d403940d9441d0820004151b07410b10955030b0200c0720107070f000100343d8044007030003140119140091613003200101056035407034035050305001054020204c2d0006a007000800c080c0c3d8100707115250241c41800c50920301c050081c000e0620517240011211a00e00b8400706ca03d944180d2014009014000c0c08510801c2e4511040203143c0c0355000c45410203511248803d000c880f40815460030041d82041c041445510350184840d03410841002601d81c0c1601c4039150780000b03200c00c01c8001c1031380c4103115000007084a034a02a00006000304d5081044035008015a01030600c031404030400580c0800c002011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749747787 1250 749746537 749746561
    0x6080102032211060301031515150e031c030204030506010b0901170402010c061b0207080115090c090e090607081503062d0411040b031915022208070801090803 70
    0x1580340140510400c40c0f040c0004510954400e030416113550710f003a4202c41e00061280180c1019542c5000151000c0f840c089103011800005c0c4107a008010544604080e00d079030030002c5411503040c07021039080d1400b4807000a4029406840105d445002c0c00d0000605035400000761240d80310180c584a01500e080c072843c1042c004014022410311411002038004030701300c0d100c2c03020410002c2c018041d8249400304064585141c51b4811229a81000d09443c51011148500801c5414014001c541005900d00948407071619030090503100340b48004102c06104000f030320718040c15042d152802c50303071611011080003040c100c050b250564031a02c0458000f26401000c0c42c6008903406240301041e18000900410340c1003514280c411107800030780c0c0c0740a813601d8483c5c0704400c00110020541c9020040054118411400c1c0c00b6000456640c0180b0940d1001d804440c1e9644000d100300200d0001307541e0710b03454800f060140140310700c00c80102250009052140442081d00024003a0850f500d407808810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749749037 1250 749747787 749747851
    0xc02060a050c0f07091b09030809040605090c0a0e15030711100906050f0a15150c140a11010807140d090210090e0603010207171b120a02010608010203 66
    0x800c0080030451040445803e01c51240c140250340041d110f42da10b4182e111007030f40e50b040c4800e80002c0c003141e141080503800983c01e00840b540410860740360744070340303001500800b902c0e801180c02402e000104600c28a0341e00003080c4042c081c3c0c0701d40141440203000c0c08001d9003660200076102e1000c0000c1020075000b0301114899600300012220f511401147e040c050341d45042d401c4413a1034640b003e02c4412030300f40502c0390740b25251800421505000450031f51088006200300404903010406984451f031103851809101034202803815081c00c14612420754a2042ca1016600020840e1103404032b0361244800394000c0b10725540300d50300c5605124400c9400e0340007144180c4040c1e501c1400d8030043c0c44408840480603141d465200c4010700c0c0610540349803074010031040c440e0348104041d80004040940c0c4c050040305250380c5a886266025a180038060b00c0c25240300b584c41040b468030400d100010003032114021a45c002d1012695500c038150030303400240c17808400c20120002d204200440000c1c0b40e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749750287 1250 749749037 749749057
    0x70507021e0411040b070b0f0411010c2a0302180603061b070506010b040e090d020616032c010c021b100c080a080610211d03120403020c0108070c0206 66
    0x616058590701124544c0d00980c00380b002d0b11300220303228090165000c00280d00c51103a4540c04034502e0181e0f58030401d00d04048041d030510100c1c61102d03080c01011189a8080c50b0f40c000d09000b080c040400d1401034042c6440100d02c00c1070942612400004103024860107010301a0051001d41c5034541031034118800e060030752441110034001d540202d00b00300b1045000704104642941c2d50b908241441400c10001003c41c0a1035000000c2d0018882d8005007036944404c800b825031220b140b004408401070048001c05024001e400075115000e01c1e88120955045942603000300042c2c01100d000340c5e1034004104070b00c2c40d0100c0b2115140d200d414180c144200043e2103181c038020000b07503540e414001c0e4211011410000b00910308101590802c400400001076180c1000303000342c40c1d18603034111281c40040e0307080036240d12003e0340286000741881e034003410410744003969140d18010a0b410404142107600f40c005103e801c0c6149569400b64049601440b0560f0f148003030401d0540034881d2951200710b00c2b13 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749751537 1250 749750287 749750291
    0x31e0a0212030c03010501080601020607120b0103061203030c02010c0c110d03030e1b030601091a0112020913050609100e0a020f07120221131806030b0c0c0105070507021e04 76
    0x40200c07000040d0040d4811503c2c0305070552654142000100504c03001005541954001d078103011195411580700244811400c4000c41c42040348801200a0240c0350b1001958001110282c0101074041d0810000b0f11001d41c000c208079171400808803869094070710041c09a040844d4590b6a90420004400006002c0e00700440c0485080740301a143c1104800200c0006006040104942c5004e000090051442c00400d000c0000c000d1000e1074511b200a038414140700340d1b10101400800c098064598480380149030307000340b0702007a03c1076014000c101d4000744034001100005003a03000c00001e4074141c070844401c1e81816078134890400029848915004207580091080070001402e0700d218402400445c1e010f040c5141d1000d142100d21202000c0c0882140d40a00246a095018021a104031504010b5080500741c00d58201c500504542d000130b013080701280100410024034000400c6040403041c000c1090303030f81c1c014045a8a00078060f000358050614400e64401c4040c0700c03c015405c1d4001040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749752787 1250 749751537 749751553
    0x360d0602281d011b030c0b09011e090b070f120203071d0109080606211b0a06020705030604020d080d0c030c121407050307110703060b12031e0a02 64
    0x140103201c071240812107980c010041c440900140d01c00b0407001410050200ca10a186520002800554040409a001524070202003061602c10407226803000d410010001d0a820a850054040c0c40240c0d6a21511010840e003086180c100c3d2064000e007d03000031207411513484190085036048840e03070042c030802051540400f8902c8052004600405098941100300070080c0000309007010b00c0380c17580f4180320f00d811041080d0400440c81e580e10100840d0140e010340701c8008545201c6d01d0500e80b50741b0522070240402e070100e080030b88d1420044030843c1c17a08401565184d04030303941d41843c000e41d83c25402000c04500181405030b20341113514030400c0030604113184489003000300d91090000c88000b980300c9046511860b08542030303114a105240082c071495203c0d030a00d0760f0318a0050004000c0040000002c0da469100c2d800f8815000c0516040d00e0301190f680c200000900800740c20a0320640c080c0c1d90000d0780310340010844010740115460602d601d401c0c031503151404d400145032507080d4000c50107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749754037 1250 749752787 749752807
    0x100302210f04141c0824030d0e0d0602030112051903020c09060a0e0709030605180304030f060e0a0c0e36010b041422030c1509080d02360d0602 63
    0x207044805040740e40d100e083e03191440030030751b4000313500f03401d002c82c000b5141450446440100b0a06905085801d0955a8200302c20205511441c1020090b11880c40071001080201841120031031903401a0308030361071189071042e000386481001d0710040141c0d00c003070f500c20001c1c10481940d030b52000c001490041c20356561070140405800403140c820000320310010601c2040680e20941e41c206c009a201001142181c95620b503503031180d8000076000851a03c41c0c0d0041001c16080207114011350360668201c036000e0b18026508443c54001d1090045a40c800980c0ca0750410144032800d40c44412250402d140208140600701e40c0c690a600d01952200c4007542152154010001030310a21005104146803070203a2948107000e0899900300080007410314004213170700600c01d01c0035a8004200e0725125500c0300c0d5440003458444002041480082260080b3703c0c40c960150498800c4c00e000c40704003440c1400c4a1700805415603d0211001404140f249a03003031140644246a209040c010703d041c240740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749755287 1250 749754037 749754073
    0x31303090f06020105070f031112040f0f0f060507020307171309060b211b0f090d0b061804080f180a03050102090312070c150509100302210f0414 64
    0x142000b000350f034540c401c3c403050580c000041c0d01d50b90300341d150800c4103240c0d050700071105100c0d00800e05050a1030b0781c00304060181105100010740d602442d003807031304400c518065071206102001078170014500700c0082e0441d4004001c131080c596020803800e07140413040c008030809402c141040810207524100110724081c552140c0c07800380c41d401c200ca60700c4107a00b4218100034080d240009140c3c880079400d000b140c200c01514040c4018035007001684440c481d42040300c06000303c1524a901c04e20f89421031090007820001240101030603102240c03030302c4080300c01c0703124444103442c01000443c08001011100700c004000e440080c000404444c1d029001000080e00b03d1801d81041c0c80a13540051050150302e4100100040103036080441c50074900c05444020503ca103c1c410345070000c2c2080e40c0d004107030b13118000311101d5200007000d1000e00d401c903d00c010000c4d08000c01c101100010500d00740c0b446c1407181a040c0c42224041c010a00030760382c5980711440c5458000951180307110b0800104501c802031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749756537 1250 749755287 749755289
    0x180a09060c02070f12081e070b010b040906050306062409030f030901090f080a110406081906060f03051b180903030411060c030a140d0f020702040507050f031303090f 73
    0xa42c0c0242580d42c18251008040ba100b0b5000c8150003100e6070140d80084d0303800c0107540189001d02000c4044501e0002441000d02c100c0350010504200300c000032580c1c84101002d081a01c1580c801041002e45030800d241d615403041d5100c56000e007020000e444a801c1c0085030340d075001901804141041e0340500800c0c6040d01d020320707030411500007152910465038001d40580c001d1440c0041840b01c0c920b4803004644500100c40e0140c405d0f4110800041e194a40c0c0c1c006400034244007040300c1c0340600d2540641e04006e0707110012204075003001d000040092030003043c8016139070010007400c1c0000c20320010aa507010b4945115402c00408900400b5032196001d40d10301c2049054003450362882c141c038008a13a40000d040d460700c9840f060041e0710320103800105817116070405003410400c460300028481031380c0c0254524002d00505180c10880d4440b025009051032038400d841c11b000c04e45a45030151681d004105250800c00c40610020304c000704940500c809080c040c0c20aa86920f4544801a40e44001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749757787 1250 749756537 749756561
    0x315130609020c1506010804152705120f09010e130203010b03161d040510050a0609050f0d030507120504050306071e0206061e040b0301020705010e0714180a0906 71
    0x400320b814090f038082402100c511a2000c96030500c03610340700001030b100d01e20240000e040300c0d40401c01c0099240155203e19440c407094040c589203009402d40c641d0044140740002c40d06806544a16240440c101d01514180c0d030303243d00842d0600c036100c0d00444100e10700507440c5070b2101c505a100381c011610707440214060b00708038240d9662803401180070407109880d1655802080046010020740300b50616a4101484044501044a8681402c103110384c4035140c00c000c0c0d100c0486100068104c0e0809d00e0041141e1055815035504c11012080000c40030039904080d0101d40c00300800b04c001004078410164491146c200030741060b8899000c07030700e0700e0012038032032020aa0120801345941c00c280540d03021036007540300a20311441c104011a0b410410850000c00d0990076083c1000682d0700c68000d26510715000d0003c5407956a60304285001c4d021104040405000b003140c082502000c01e400403404076000340c0600303d0403000b034441c011802c01c014180104256664007210002d001ca000d030984c1c0902c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749759037 1250 749757787 749757791
    0x50d08040515040f060e010203072a1d070c02010c083417031b0304050d030605121f1103040b060109050409020f040e0703150c230315130609 62
    0x10a040901c01180b080105048210b50300707100810036242d482c04883c0640340b252801010401c64000140e1941c080c25400510815111b001d4015201003a00c40c2040310a1041d0030349040c1d0341e91030b481c0c00b01c80d00c0c0c4041d066031a001308001500e00c60003061481c07a618030602d0510400e080316103030f06810f03030482242b64525042008000c9031050840481d1421800c0c81030840e442c440540e40c6615080d01d054050084440c07000c40041c062071504c200b02441d980031280032523600c0c9040d2804035220b075070b110801700100b490504040349504080c032601010303040034402000d411820492032131a105201880d950104c0e00d40715241c0d216081c0101a500480c46625420b4050a2010014003040040d0300883e0046180904820250760b035004000d005a1040d83c0001c1c42c4960360a40c6402d00e5907a8001030001e503c0d0780c1d515503c1f581d55034061951070788259034500161220000f82c11129100c10080c45040000348007050104181c3c1c00c1241681c5401031500d1100d00158103401e06843c0305030300c0415070f25 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749760287 1250 749759037 749759039
    0x307030c0b090411180915040222061707030e1915110306131a27010b04050105191e030c090e0f041707020402031006020f1203010915050d0804 63
    0x82444d000790003c04803880211402c1c5048456041800304068000c0d511440c0c0000c0469248a43d05004149290000d0000d5644c3c084000700c1c250807560703141e400a0802c4035000e00049451007050b5280400c89100090610354841e0702045014141c112040c0c1058091814812500c9445031f40c0004010312074841034070311b03038518001d0400b101d488075140440c1500030401c01026559407002c404140d1500180020076400392155110f031102071100300e6801541040601000350030ba88012028030068090070080d980c0c03214569401802688505404110184001143da0b240e120805e00c460030b180c641154109046440d05a8275094112104046661414050303a516480b41d418005440b118141541d54141911800d0094034020701c007a200c90303029480642441c900e40d085640c03540d0028029902c0342828120021309a40b2071060308050300c165250358850201c0030541030510480440d85900310307840c203104031020740190303010721031850003540010800c1e50f251100c5482170350141001585903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749761537 1250 749760287 749760289
    0x1005100816080106080112030513060320070f0303051e0a0e0f0304030c06030e10090b0130030806060702060714070506041203050723060603010c0516020607020307030c0b09 76
    0x342507800008010480005002403600041040d04454448065480008103400c0c11074050141c0011b15600740d042c1440094450b80c550442c0c4500802084594210090640115203600c1444001040d20014a44040c00f1a01136802194419107a103014403c00200c00800d000303050045803103500d01961115103126100c010001d8444200ca403000071032415007552111800b03440b15100c1c017810180c441c0d60f07107441c40300148180d050f22107100806201030306040c5413504d400e207000d00803140c882c54421920000140c83c2109503159143d031140182d6a401359441c21110f8510062508e500a00108000c60050f00c0750001001440c0c0201c3c801251036000c995a9410006551f014030b21400d02400240140518510800801a81410304503500e104034946000d2030150144009a10544410804860600030070558401c0d94210020441e580f40f50f8030542d2070f8003500c2406544c0020002000005017401b00041c600140010101d440956a035a0fa00789480029004404d02c0440447d0f14106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749762787 1250 749761537 749761561
    0x1b16060c150f1e1a0402030c12010f030b061c1106040b07030e040606020c0a14130c050703140c03040e0c0c030304050a050609063d0f1403210310051008 67
    0x190180490f001e104462800599040c504c09902980307100d0fa40c0000802c0140f09241d04998002c552644030300310540c2e4803c80e944600301d5030304c0140c4241002d5000594541f80400720609107505030804640601d1a98444c0804d080491070140e8011908110200d1391402000250401d18803980e00e10b041918107005000940d44258403c41c10365100071040100341c3c1e07031460310000f50340c013800684c071001c110b000003c1d44c8240f0700c01c205000e4514000d00603060b00d41c000000c05205000f501c4443ca5441081d0703503540c0e02d10448801d0042900f040c401030024210006009800212034440d490034180920072190460b401a282102e20398882004101004014011182e200c420400940003d01d40900740054421810130710100c0400d110340840c1402a445607080c038508000b2051518140d02c8203100c00d10309202d40110007683c0100c041004283c50005016802040700c0d440d5241030802c0c0a07003c01e0b8541010303010b122921170044002c102900c44030787c5a003459420340d4030840507040201c401c8813 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749764037 1250 749762787 749762831
    0x9040609150f080307020906190b03010b070b0718140d0b0f04020a090c020c010c150c08060f1c02010327050a0204050a0e06070e0103140a021b16060c150f 68
    0x100d500144001c5d40540d07038401c1d2a80d44008152010000454003461400d20102c0d903401040a0320700c0440080b45120700e00c009003c0c280e200c0c0700703108400d0702ca0340e00075224400c01c0d01d420076040c450f020044c8240500030092018500000d010132149021641c0d5000300fa8000304d07940511000480100004d62516034507400041400031003c01c0040c0c5032140080d1100100c0310352906210f00c0200174070030070060718482103005012907401c128400780840020f14070303002902e4080c801d0a8000c4280c2d02c1cbd140a0041c8804c40501c0d04000c0c05000c0780e540150082c00c800c2000f200d0359039003080b26880800039410805002c40c8181c1c0540842c0c41288100401c0f42c034007a00504080e80380c038650841280f000588513401c130070b5504201000c801006d004070042c4c000324603080c95005120061003aa405503030050140101c1840728201c003100071040c1c160380c4081c841105000c42103104020480e00c0d018a0b048000395010300c034a48461000e021b690b1054071000044000b00c030303940f4005940190701c000c070300705 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749765287 1250 749764037 749764049
    0x625121e1503030504050f0f04090302010603231507020a150501090c0e0f0d02031006080c24040b0a030f0c020a1a090a03050d090b282009040609150f 66
    0x14445402e50714010580d0003680159030141040170030341b07015582d0710164000c2c5614018428841007040c0d1070000d0182107144000c07100c0788402c440c1e90421400b0908524034030f2078104001c004103500f030b410304d0400310f10180c51441036005d0300480c000070900103070740e50750240c1c240c54001c074030f0f5458200104112038400b4410400c000c516501940c85640d00711042401e03090442c0c50461240305800040d00b80b801048181800510f40840000c51703800115407148240c5003256241d481c1c0700380d144032043c00405c800802d00800c0040000f4070072410140c3c0604514009807030000b401c244041c200b00112101d07004540d0150b48010f507003030100a0208c0c80000550400707203001c0c0207801d00c54212076031403032041802014884042081e5003c2042980000035207038200c140301509041c038a006a03420300c012804906100e11f0454034444200c0c00e030080c0c8054402e002001c102515004080e070300b03150001138000741c4c45900c03090b0000c2c00601c0c500030603440800d043c05075035242c0c1c41c2107600141d15000f580700d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749766537 1250 749765287 749765321
    0x22e0806060f0a08091513020a0b070c0e040f05060a14100f09200a0e130b150901020307060c031d0a050d03050402180705070c080625121e 61
    0xc0d0980b454064252541c80303005007031100c4952114100141803901e650320400041079828108254440307592004000d050080d6000c41e166034503618980311611a030200505000d0440323101700180b140c41e203a1180d003d4003400c0104109101a55481c4c102103060780c25094450f22851040c9202410810032604400d8040c40407802525002c20f01b14804003610900031074507900c00920f0781001da040b4121811000c0d542c0d809607103040341c40c00642141076803600c507402040034841c0c000400d0650b22900343d0000700180800748a00c082261000303d940583c200c9270450206001d007100084650049154030340140d10007045030091540a00b0b0b02294003003a000c015801407951201243c0c021594240c903103611b103000700b455995030001c5500d0f000c54080180604012504100e0b0455010000e400340511900b8245c138440d964050a55031807501391881d14124141c402c5002d152054a4407083d09000c2d18108090484d03046180c400c100d4044002d2854000c4102c103c3c2c00c55801540f1441600c480f2010038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749767787 1250 749766537 749766547
    0x312030227031209130608030406020613050613030e040914121e0d060302060c060601092301110f1510060f050f1602042d0507050f07022e080606 64
    0x2a61181c00408000002c2d100003079984042d142c68084510317451400006000f010b582c5c80c5025074a83c024400c20005004481c0411411400344180440080e04600100038a4603020f94807101d0454a90045091020603441000e0700d44960040801c0749010700440c2a501d40710a030701600b0414010111a08017130200000d402d559469000c1c89034502010328416201c00807481008010102070708003a500c003001060745001d0440020300d5502c82c12082c0d0302c171400c85079500c1010066052419004441d0440044030401652080840310384030380c0814111000d0034280c0c4812404c0c00c089020303c544040e2440200214044100200c100625540c600443c0410349140010170034003c91460300c82e9500d000482403c4465500d081301607041e0010020021080307100d10b02001c0810b42d00c60850305160908440b1078641043c89810700c5101d00e41c07180f0749020141401c441803680311010480c1d00c004406480609a0b100c1c00425029007210380a0a045088a410252126100400041c0300b0003007000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749769037 1250 749767787 749767789
    0xa0c0509011b021903050d03110405010e09062b140d02071502071a03041a01030336060804031806020a02092e060e09010e04080a090312030227 63
    0x814281d60241c07280c2c80d128030b121907100154403c00310141314010f4240103031011084c8500440e501010504585080245614032148034440e400f441c070907980440c44000141c0040e003849004079a001d04014151505004c1e000700405198142882d034201104045505034100207078202c01e0300c00081c0310340042032103590901c0000d41d107420742d0054040106d1441010f5030114020040c48000d401c035200d01d500f1001c60314040201c00e030800c48082d04c442e000703801104942c101002415068a800da41c13448040c039075101c0c450890300300d0403003070010601c00c1581c00b04403144240c00d804080c100607910001035040900b4001e003890b100a01803280c00400c1030080003155000901114810b5044e10030000366070710708544c038040d1300032a00c120a908440540610304503901d00406000c0c0c8000d0b4803520481030303c04040c03112144090207000c04007514107010402088060b07019081040c118a00114001c2c6c581ea18009010080825140860b4010592482c07044013442c8200100100080848084030218 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749770287 1250 749769037 749769047
    0x60512030d09020d05060109090c0506120f09070305030f0a0306050a0806040204150905070903140c0105030c0d02251101030515090403020f0d11010c020703020612101205060a0c050901 81
    0x24024140e450340d20308242c0115102c8030200780e4016042400d030303101580c0da100c46001900708041c00329905208620049941c5c600601920504009280c802442c2e584008849154000c058050400c910030303000004000350007000104414050b0710040c41e180e07100300d10041c00703a84083d04424498100e812050280d0f000000b946a48150115400329808002124000d080041c80d0041c00f42c00c3d0800b42005000c581060b2100100e900c2181c1072481c0d442411451a1500b0030f208090f80011400c101107114030074a4005081c4041848900500d490805823650382816208050141d5044e8a440890300b0703c04003a034400ea00200c03c1c24107020350718045080007002c0b485030321914890b0b0318000201d828135200308010603442d0b903000c049840da424010310240c0030034500703414400c00f0b43c02c0c046c0d40081c41d0310128151084a5014090500b40b4504180460749048000c299103400c540b841da0004440c542c1da64011072241c0980c015160a08121003420142c8294101c05402e02408112940140c0d80c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749771537 1250 749770287 749770297
    0x30c01020d0c030302040b03180c040c020d21021903060e04080a050c0a060e1b0d17031f090e0d02060408030105062802030301080f0f0a03120b04110d06051203 70
    0x1e850300d0345504040c1c3c0381c1a4000d00454004070001e100100410185801d01c0c820601c04507070a50445654429001c03c0006603411354071a00010f80102802c40284c500805150f03180c3c0c400c807100080b00407170308201c2e44105d802403840c054004800300d61580034150180300b410060042200e5a400c0c41c503054a1b040894803440011804000002030042510340043c070021921562000c424007048090804d0700b9901c2c0380c039001d2041403410300a01007819140402c00d14624660280c0c114000e90091601a042c2e07400003004a0310b10011405820030110703559070540c0c0502428140040c0d0904034502440c50421001c0245065610407418000456071401c25a81111340885542d940c0d9000c003801c0d4180041c16042c0e030001012070482e0000c6d0550048084c6040c2c403103103000c4420310558850b10940e254154007941c03c584d00600d03140f00109216041c24044000c8007070022490020420125044982040070001c00c41008034103610f03107000c240501b4009040c02c440c8a451000c0030050640c0728480c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749772787 1250 749771537 749771563
    0xb070801060908070506180405040803010f0e0907060c1a0c120a052a0d0221070c03141605100f0507030b28030b040606080d14070308190c1805030c0102 67
    0x2068030943d551f41070120265014002c0d0050005091514021085400a003e0303400441c1c0881404508542407a401c180704441c2e9400a000d01480c000302911340c1003400c18107452012608446501c84140c03800e2150084018110899a8504180c0c0e020b00d07d2902618003c26103080c1814025003541000ba600306240480014083c01000780600568600c9440010043c0a0002c218130b641c551200d44080c0c03500202d03143c2e030f900564400d40210b401d00c84911005001c119030454404403005000b01030300f80d05c1a141c410b180b03696400c0e1280b070b24004580f041e07641c00c80c0d22001d124040e1161030140c540c110700142414007407000300000103411140051942c41c0c00001d05840038805260380b60110005580003a55164142050b08156003c0c01150140d0103003440f0b0040304403291485032050180c0d0500c0522028144050395904403070076400582a220280800410300a00007a1803080f00c4074040f082d01d0340e550b0491101407401c0c5a820a5100714403031381001e031900d40b40340d03000300e041d12040d49 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749774037 1250 749772787 749772799
    0x30f0204050906011116091d0c090406091b0e0403020d08090c15040504020a020d0f17040209070e1201061a09010212030a110a1214060a09020c010906090b0708010609080705 76
    0x560060b076072a20401041e80800e0700025000021480390030792003070fa80103240d003110b2888c0004468207103589110603540355410414600004010800d40c0d8098001c940c401d8014800031108480f10040f280311580010100d03070b42c0c5105100400d5010058072180418a0600d000c00389816001c6c00c0d1142d0304200c00501441700462641d807900d10b1141110042e1400400464075841c902800950f03030303840360303603424007081c0e810894028032401001c41640205071074000e02c505665560a000c9064000340104040c4003c054038643c05036610007460100c2c2060760000078032589841e45461441903112503d41d40701030100070000035660301044020088089200c0c0070760ba40c607000c481000a081840c0b840c0c0e0800400301c0d010f180141c0c4901901c51680e0391100901117aa076a245580821034107607040b40d0300441a01c0100f0250481e5005444009000f000000390070205440b02026140c0031002200c040c0309207001c214603140c00c014050b01408140c5800e0390954188404140d85041500810f48505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749775287 1250 749774037 749774057
    0x503040b0a0302160b0103140613060209030a06050127090206090d0f0c080303071103090d1103070302040905010b01080c030708040b0c0412050d02190302070905040f02030303090d030f020405090601 87
    0x5000381c045603030301400c42103400d042c0b00e135030705105d401c9100c280011580f01a0360001981c01701800070b8000c4c061401d4283d05c002d04141540e4141c0254445000c0c00d4050007059495404200d80344a9180241202402c68049402000f6442d159009030500e401e007141c0390070b0100c00541c45020540307a12800a8a1956440d601410304400c03a12802000811701410004041103850002c0040e50151906850f426180c05003070701043e03140d02405070340e150003120400601021442c0c00e042d242100c0009000c2d00c00c41603c0f9004282541e0000c1ca0949203691198900e001e2560300c01142c5a2000f0300207503080c210f041400c8002d02e08c440c09400601000041b40209a09510607800c80b002058980071812940c000c030b25048d516000300c00c00e01005030080d954260703d520841403441442075855405042e9050800780440700800018105076a000b0020025100503281000213501420410b8003e00350b090601d0b81c01000ea03011110100c040b280140400c0000b41c48541f0496080380003400c1c914064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749776537 1250 749775287 749775307
    0x6070207051f2a02090a0b040c09030f030c061b170c0a120504020112240506030106092912010e0601170a020a2d020606040c091e0e0a1a0d0503040b 65
    0x5035842c0c0f18007a5003c02d694090000002e05a40311240484099509014107901d440782641d00056511005d00f000490300018400644210718990220b0704c1403000182c12801041c3d42145031400701000d0011488030215a800000c0840440c2c2d4082d0740220580d10f00300ca24003009283c00340d25214100708548030303c0841c086a000380590f516020b4058410040d11030b041e13104500006012010312444008208041082d05015080b20b0580f2800e0311042ca02900c1d200160419801c00f4504100c986c0c45080038203551070720513004080111050341c41206030350410746ea140d4001406010181131041c034640031150909003644130b41d03100d00c50a40050300e4591410b0b007a52a112100860a152025400c010b42c0303440481c0240441810954211162aa640000d01c02195403a40c3c0c0301d808222500f02c02c000e02d40a402058034165517000c128480b143d034890580c108280305581042005032200030001140014800c85502081d080703441c0900180310781c982c261244174138001e61081420006807881e030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749777787 1250 749776537 749776607
    0xb070303020f0a0e0f04092015030a14090703050a020f040b04051008070b07020a090b03070b070c0918170d02130f08010c1112160506070207051f 64
    0xb41c21000065a42e94040898008100a041c2c00c1d40511a00c4041642219820710340b24003102c1a51041d02c0400002e084d941005a8040040303105521010650803429149442c1e4095401046440008074000b4031281c922141090b00800094095022820400110310000344030b0704820b405880400c0c009141c44081030180c1780f22031845401c2400d16040c40b245030b882211030400c40d0140d20544840d03135120368103140d80d445215406075014030490350510074a403190327100c3d0281c1c01e0001c007103c103516501c072030360107507504401030039103107918450710412072200240104807140603294815404c61f01590340e4182601c280e0403802282d90004038003004007101c25412104d44c4480c03218282c080c03a586518085110240d0300800c5180e50a00c600d4152850182c500c1454808542000c1c250f040e10303c10300700d00c03d60031450103084090001c005803008070394203000743c5020f140a42d000d01501802c0c40207019440c02803c01075050b500304103a2800317800394440c01da0841011aa4000200e2182d000030207a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749779037 1250 749777787 749777797
    0x5030a180929040605060301090506011e02010b0306012103031104080307061506180b07050a140c0a0e0702151e070216080a0f0b0a091212140c040b07030302 69
    0x5425240c02040104046460034000b000c00500452a80c41d154000c10300083d600c3d40c1c440d09400400500043c08558040d030441c40d4800d10600d0014500c81c4040c441c1400c0384001c1d003200016075502d9032140210308050182d580501004a03000c800e0780028072a6140850141c0005420141d5641d515202001e49200710f80013000e148040b603840d5500f90030607070b00500070744801c0a000c0000040001d19a40a644111245066210617000c414a404d64a031125400860708650b50700500054400089107202041c1c45600e141004040c0c072081e010910074800c081c0d400c0703500480c0c1800200440d0f15800580340c1d04c1c0b1025400c21544540343d40c1800d00100c48024041c5d040d8652840400070065800182c542c0408044800721410350350b120b00c1e041d00c0300e414180141014a144040901181003c0000340e00000150300c000750340c030042c0c0c54008400071013081030b5000440d12401094105aa801001d0007550102d064040a0514035903041d035920440c4203005500c540030500034103160199040c0c070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749780287 1250 749779037 749779049
    0x102070f081b100e10030b0d06020309011d0c0f01050904020d0506030601140a09090812090105010617160e0a09021603110d0903020f062107020d020a05030a18 70
    0x28009520340c154075031600304405589034a2110155030420a00d041040c2240145840d212082c0b120320400030b0099030605040d00340185a01d41c564103111fa241c0891031391040740922401a203d044c440d0b0200d0964031084824408683d44490700504500041145440440301310f0380e1038940d400c5480140d545005008074550b0091021916022660b0a0b402052040404409a480907a22400600d01e4040c80394601034102030251018071880d4100d6110059080c0a80300b501e09001082124501314001251890103a94551004124154000f0500403142581c00e500c00d00510340000300c0c00c00c40c04080c9144040214940b826042e41d00c503e0515801b40c1940760040d552844020030141d1b4141a243d0300b02d0010741140350110205601240e40301c8600341f503030355068581d86160200801c41d00b035074000a078401010031007500c0044042881080d8408006621261882c6c0003802908090035800840e056400c070031480000144040201e40a60348642003201080a00740601004420590024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749781537 1250 749780287 749780309
    0xf121e010915231012060203011707061e0903020d0c030c061d09060402070c031118070203180102030d022a03032205071a092b0303020c0109080f12010f061d010207 72
    0x140107115458002354103a0321b603070403408460020361a2095076560a0702c200c20025016100018074024400c4040341c11106d0b6180c440e0400d80c032a00080c02c2b03a402e6000031a1941d800560810030410003e211400611003410513011003134060f05010007070303150084114401c0010307000284040e940c0d170341911500c540000c03642600d15200d1030180d541c080384c041c0513403140c0c03030b00c0d0f0f80d8440c0000701c03000d0a8031800240d07010358248207841a4000307000600005032070650105010340c0780b840e5400c3c806446055070105424034027108025103e8254403000d0b29241e42174008108010720106241c0500350150004540a40410414200141004140e82148101400500c41c40d141000f00c1e5000e422481d600b1170f07940c5a07500c42e4481c00040c80036000c52001c00030b01d4849409020a0199000d0028240004008650524603650304900e640c02410400482c6c80007080040d505200f1611803809444046107920350a400c08001400d02040d4030b4800c004a0a40b85c2c541c0380c56442440044000c242071004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749782787 1250 749781537 749781569
    0x70e090d0212030601050a030905070506210a0c05030408030c0d061d060103090203062e0608190204050105090909031207020c030d08060f121e0109152310 68
    0x1280d45505030121150014820025618910410001164082c4505844039894022119003ea000e06059202542d140c09012000103081e107858000701041c01808204103c82e81215140401c4050090f042c80e0481d0315200c145041c00da0040e080303a0b0010b0700510307060344030b507503d50180300c280c0310303101c1c000034004d00f400310015601003050350b51a0304490703070440d0b0040ca94a00c00110200c3e12200e20181d419442030780451054540481c030901c00d00d100d0040c03110001c280078403001285000380c1c004d100103449401000052030036440042c604580d00081946843d20703042c0020014040c05500b0782c825201000810001c1400308212007601d006482051658509500c005c3d40703c1010790803142c024040c0441e90b4410912555140b4450080200540e08107250641845450010944c9002140c40744107000d8254410b80c402e40e06c0b415808100104880542d8504080a064500052089181010504041c03803044c00b80800c10a504081d400700b2030358461072100b5910382d0780c0d80104627403402014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749784037 1250 749782787 749782801
    0x427080309070f0b04050a140901090b010315031b05060a080106031127010305090a20010302091804060c2a151a0405160f05030a0b0a08150a1b030e070e 67
    0x1d001128000c994005100d40c8d03c0c00d0074104c41700004100c65100c0002c0006008020483d40240c10154041c500000d407822440c188280c251020707081a610400c40002c424042150105c0c03684c06003000b9640281840390020016008541c18012070003815140c103250811111303142c082c0ca00c00f03091400c0d4504118042004030850382d07016121a40005d04007400990383c02c07000110f08441517841a181b0b02c100c41012401d04032041207201e011704050302000121a1640d40b03405a10010081c0c0d0800421400e003840d04204440c0310f804404180442030034a074501e4034514a545800740c481c5104000101c40520300342e265004c4a80301c583c86180352224a200c240012844074004040940d002c02050b2102448588100c0404c007042d030000e179171904013903000340c0b02d6400b1759048292580003007050300f08a0b0000d03130012882d0300400b0b400e9101d041514105211560484d420094580017006205a120f008240c035010400d500c20a154071030020224400c4104543c000802111841c0002410585 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749785287 1250 749784037 749784059
    0x60902031005010201020c0703080d2a18051809100c0c0311070e0c1803120d0c090e060103020c21130b0901090909020301090f050304050427080309070f 67
    0xd2a02201d41200010100b402c1d4014401c542d804900e00e401420114070390380d1032529642c0401c201c840039035200c1c3e8013a01c1c0c1030003003000c000144501c4110b0491074909484018284c1a0500b4161107108410300e0400603074580c280480c641c03190310120641c00eaa614460180b4151038a0740d880010380c0751070302c09035281c0d41c03082d15010322500c00d42c0d0303000c0c045144c1034581c1c0da01c40d0f07540500200c0c81341d0700010600b21030014006040050b88841c40b000368802c0d10700082c0c10441c1e81c0d403185070301580000317803a14254401d2080350303850881800d20100850915018030918000101580c0c10305d903001605829000c020002259500101d5180040c0880562000301d0340390002840405d44122818010038200780340b400351647c1780c5040c1c0d101e0040710b18080c0310340c001d0640c03040d0580e0155030b205021404a2031a400c1c66000d10300031001503645510386800d10045900407510201e00e03400701031a10100030350f4001c6080e107554004450644075100c0b080a6070034000c2c0f079440310b034500103a8400000c1c000d80070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749786537 1250 749785287 749785291
    0x70c0f0f050402040b04260601030309090b06030403080601030e01090f12030c140a050a030e06070305060f032b181211040507050d051b041e0603020f070f110406090203 74
    0x15081003610281e403002840140d000da802013008800c010f201c10b01401000c02814580248020000100c0c007244001c42424401c003a0800d80020b60040d03818070103c082c90082c250014400c1d60300c94654509500e0043c091500a40744134105a1500000300c4210025003007903030034907004809030000399070625010060480183d03004002ca03050580c0b000c091030240030502c00c1000058041d070700c0d1400b00207040380c15502c9410010f0600d40d94081d22020003500300304548c03169589840000e1182030400400c402451060740852180d800040540340807011140c520344030440304403c10340b50000d5104140d03a0100410301403148036014000000d902600e4540030804070740a0428107520000038000d010039100100d07007103004203404000d0301500c00d500d0742c002a400b032403205000d59503482c48206021250722540c00101910900c440c000c60b07010001503808010000350070300b149410314514501195019241c000323050714915442c02d20900c10b4007200071318402c3c8010710030000d01d038960f0141c0d0025081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749787787 1250 749786537 749786549
    0xe0411060f1809090a1707030504090c0f0e041e02070203011d0a0b060d11091506030c0a110604020a0e0403030204081507021b03060c090118030b1e0129070c0f 70
    0x1603c008105540d40125039042c0c1d8a401c214030180c046000088034000f940203100803420843c04102c0003071078000611400c0e100072001c0da1111581029800300500403680c0c209040d220300d1500c024015120110383c481100c0354410a40940c44a5440c00024014980c0e5400c2d40d010074003086c0c00008200c0081000002948030740440c00e025207960741440b02d00070003008010950048880105c100f031901034425944503203a51000c04040740040c0108280c2d030400d48074081e0b52400880d540341c010307800100410201d181d01c4000e02e05c902d0f040e0000740810800f072042c00c2d0040c40c8100840d05040c46601150058030146085074507603102c00300a820903034002c5505000501502001c02d2020180f0040003c8801c0000c0c0102101c0d20b901540740200e07840481c4507814409141d582e0315a0500210a0b8401103004203040c0240c0d02c0c14140c0f40d45040400081d108a080000e0014800350708a02c00107042d035a00c0040c50750900213100601091445031801c054422481c0003000209e60307607007440324020b0b219 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749789037 1250 749787787 749787799
    0x90608090105280e010c180e10150c050604030804020406171c020a1a091e1002250c14040c050306040b0604180606020d090e0411060f18 60
    0x80c441080508030303442640c1146001880d880c00c580190b240c0350915250903070380080059803402c07404007103084406c0c0d6aa001c020403031240f40030060303041d540388010080841059500c1c0e14500000e494a0710724960051030707203003058201e204001ca4072079000682c280d540101281c569052030304024200d0b090807501240314a003021781c0410750880d460080c00c1201201001015100389281c0d2070419801c0b0880c4020031803090389800000b01e0781c040b005401c050304001010001c1e040502129003424004201c9410f120007414608070800d40001e20812600c81d01d2100503255400420104d455104611451130312422564100c0140079550014200b100c0e5100702d1405000c02403c2440140c0304c4103810304010030400c0c80054a1802d01d90455942c15500038107207441c0c1074859104900503604400c1c00840e11780c0d1681d0034445941c040051740b103140f0640c20044030315860066851011040104006d107100700a2005110589481d0180c2d0b008800004150340c49259802d42c0002118040114600c502 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749790287 1250 749789037 749789041
    0x12020a090b010813111503151206010b0a0e0d03020f0f01050112080924030109050105150f0a030f182904170d090c180e0309010e010203070210090608 66
    0xc6800d100301124040181c440446aa560303e016500c0d00311100000e854610640c1c000320180d80c0c1d000c03d40c00c100c01002c074020703459051401410030400002030fa50350160454140c080030a90380012401d04482811210640d6400c4d825000c6521440780501e194025500341030703c004040c0c0200c1d038140c0c1c1e04281001c40b141c550000f140319080e42e10a02c03420740d0180d00c41002001140607403004003d540b00240880c40c03010b44030003544c6a04091125041400c403400300050160b44214000d0720300500d002c40d080402580240103022461207080c52035200c0c030100040165440c0e020745c1114040c00500c09041205564500382502d03880041d0794125244944041480141400c0301a400c4c02448049803c0205503210740c2c850a002010b00c000e0588910240080c140d070402600468422900c01c80201014501e080c0d0300380308190403640301c0e42c0b03c141031810031141080d0000c00d540c0885e40920380b0766061141c80005174250b1241c82d01c0030f0741142004040720a075540003e5020221401c85e61010816 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749791537 1250 749790287 749790299
    0x7050406260c1c021c06060f081c050d09050a05030c0106080609030706230103150501270c0c050106030b0f101202010e0a09050a0501051005180d0501140112020a 71
    0x540c0c0b01c2d04110392080070003490181004070121804031035032010740144c00440c0100c8003c50300c1c4100030022102d8036100c41c0d080c4401c004108101c1d0040c14404014014543c5118524880c102c0101402c81040004114581c1203181500001c00c2c06070401c0917500c402e40c541c10200c0d00e07503008901070030340c1d5802d00c1000644024001440d40c4944000300286080c4060780e03495002038828149291450b0b8032025502d0010311320442854021403058042c1c06608915201a40a03264140c0c8940d003079550908030100106505191560341c108000b000150b105909041502c1045981e000074105601c2d101010003002140d9640c03a0040c80c4400c4101c99580e00c450a00c21044264001d00003030246100300b110042d4040e035910000044001c06e003c20441c0c03501900000c5030b41c104e030b03450321941d03e41004020710308107401400310403032051601502d441c0143c0c2c009680ca4195a0007540169040c0100c503081c000f00b0f611105440140c0601c280007940c2d20044111607070706400007a846040400000121 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749792787 1250 749791537 749791543
    0x9011401060c0b0c0a0e09070906023705070b0f0c060f0601120b0d060e0c2412040f0218160309030806120a0503030c0703080108030a1b050705040626 66
    0x900360340071041d0746032581c0d0603050502c0c0c5c0d004890f0801c2800300c004122001d42e40c0700c1d803500f4814890341c1d64850107030345082802031600d00019030180021101c1d201400554880c020315400101320041841d198008520380346140c41a61303808a8500300c00840c0c8040c0d06140c0c2c0004052010704030080760119194615031044c000010b6a140c5c1c046044215405182d0406800c10a00410000c100b4052500e8070b484070383c203a80c0701003040b20494020300803440c0186800c00c02c210b24813030021381807904d622090f8414842881090307000e07108d0030907503c0018100321142069014041d0301601500c2c040c0d08148414202c0401a2550040340c1c80c20801d6103101e0307201703104401180d0b425607542c032040e071619400d111080c1c0d40000c410543d4081c2e14900c0c00400c2c400c00c004c6001c1d841b4003980a0b5216581c6c1001015050f0603006075010341c000300848054603501038038003c0200c5d42c400710940071301e282e0701d00146860742c2c950200390024103010340000c50790500004108038020050342101144828003446031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749794037 1250 749792787 749792807
    0x20a0f061b0615030308010e0f0115050f0f13150f08070309031814040e150105150403140a0b13120f05040e0f0412020f0a02060d140901140106 63
    0x20000d40c126085a01c0551216808041540525070019030100b100c00d600f403144841c2c2d001a000f040341000100440d40e80d0f0140c00c0d40c4003049030310381081d9504100e0b04900c00d81c030a103220f50401002103080700b040c1d40b5102c1107844600a9001140d0345800500d00c941450509200b1600e45101411500314000d006d04001e0001c0b00481d6038654003039845c40c900b5001465034200940801003030881e108150b100ca9191100540241618612004010020441030300c00d1407100505a4101d5041442c21010350f0391910f054603030803075412415062081e40d10301e041c001d940c0042c1407030704001c60000c543c80c00410051001340c0501083d80c6640e45801d60250f03015004d18000340812040c2070414103a5224415080d140082494101c1c546540c5a404440d411000d5502d12019910308003880208260700e00782d1000d1a0041c00a0010302e4101c420031030315200e5010010380a0100068640039100017580130b010080c40d5840040c2550404000207402406000018600c00036128008100c1c5070041c01048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749795287 1250 749794037 749794049
    0xa080d08011206060302060a0c0606080a0803041202030f1801030b062502191707090615050d060b040303080709140a030818030a0f0605070f05070f031119020a0f 71
    0x303940c591a007000c100150016207000c0d522140d458901100581d1024010900382c2c5003940d07040c1c00c1d48a2420320004840c5194080445540000900d200007007800e07081da84c0c82034100c003220701804141007003a03042d846000e4184150400c00a2000410248181d101040c12000e03601086001e420800303000440c07281c058443c0b01e00108460000031046e0708189000b0080c80500710340c64501240081c044c1d18200380d0014010344032440540d1106000800c802002014481401e010307041c0343c403001c41404088031a50000300031001800040c00e11041d00460000c0500b443d00954850f980d0900600c030210a84a44001a40c1844001030f403900d0300708c2414041a0040c0f442d08164550f64640c24140d02500351010102d91150b84000c0580e005e112500040e030080c074103026000960b03c2d2500465000402c0c02c42070111203110b5041d090703846000d4660240e170041d6005443d00007414143c0b80e6903c1840561001d12401282c008180e1200425841b5141709481c0810810344940101c1d42d0315050340148 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749796537 1250 749795287 749795297
    0x160b130c05031b040c020111031302090a1b11150114012006010513110d050603060a02120c0306060712030f0e060c2506090b04140f0d03020a020316060b0a080d 70
    0x80300714075045d0b0002c1c003c458240000242c400c41003d890301150001c4507900c014a02c0300e6841c500350f01304141d50b5a4080c0c205001004007030b116500b8078160001030380450007044400100d422410a08200c10041e140c00c800e0018408c3da5120466140d041c4034080b214002405000210142c2100c0030b646000d031220700b00603107010307030800003803008040c002120071036140e0f161000052071851160040411075090f00c000700741d0740307030500030700d032400700050990140c20b84100010022528120040c6070011130107500e0302d540340c64000004607540a9000007504500403030108810f00c58040d44107180c0c1e80d614000c20b01c940c1e50748007640c9071110002c03100d220b098001008158515043c0c500c4481c080070600c881c0800141c1240c4410f4100c810b80c2c1802c84054002c0003c2c082070086824078200c1c00c401c0440140304604954035841c0c0c81d4141010128240f640200d01c1444507030080c81662080c0e12044683d0b060421141440000f8004a08040740500784246003c41d14900c08154000c911a0740d07140e03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749797787 1250 749796537 749796583
    0x402011b0f060b060f0d020c15040b07080a1119180f050d030311070302010506040b100c020f13091110020f03040303110106030b0c070c080f0c010302160b130c0503 72
    0x1100054070009900c2030340081c08024403108080c511780946100c400c5604016100d044818407945001e1840d0455040809100100000150040f5076194018542d02c0c0440441d160300812030302801c0d40c0309911400d10404034140250707440301101100c6041540d580c40c5500c03501100000b6465102d405002c0d070250b074110702800181010800140c01c10311915001441d00040444001c0940154604400503519403040c41150f00e02030007240c902c89400c5900700829280841c01a08c1c100c44844028003e02c00505992140d985a406080c804141480b00b44102d04c1c1620f030110007040c28050b050b20428244140301007451000420030000b44151005516250450310103982600c000986202259240e0401100040180c490309000d10185000b9984860152070007400343c00b41e54000ea0001e502100204030b50000000d0900301d051030a00300182d403080c20813040905040c0383c00021b000c0b000c03060300b444030303c50014200b0072030350740603161007402c685d1107004058561038000c0b000d2001442a42d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749799037 1250 749797787 749797793
    0xf030503210603280206031608010b042103030605031f051003030e0d0501020d110a120b21010914030c1b01020a230d09060f0311030f220b0402011b0f 66
    0x8401130032100300c0442540d1001c040d90004d680b80d40f00300e0300200c00d5900c0c07600c040649508044618050002445124240707810038449140c1e40180c40d00300c0c0304410210400006050081c0c0c00302d000b0f090085d065071008034614a41107505154140c141c24002d00e0b02001810b5001600008807c3c0c1f070f0715030740c0d98420020010030081c80405404041c2c03219582049144080409485000c14a8144269141e103600d501040900150480c4207540c00d000e00b400c204150552b500781a1442200222414008541920314228010f0140f001c0c020011b1a00314400c000748080000640a1002600c0466140620f91500e04400694408074203001d0307408480c1190000782f1030460642d5000c01c0505030500c151080710a2840c0022160581e00131640901060283c660700c082c1c8045014011304003405821560240241288401404880101960404240032070f4802440303001e00311310024101030b114180e007403451a00d64107803000c90221380700904800e50750000b010610a0590480740d40d60904940361 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749800287 1250 749799037 749799073
    0x13021921021e01050c01020307020606010f080702060a0f09140304050411040f03170910090810060e130c0506071b1211310504051009050d0f05040f030503210603 71
    0x1860b50307042c0b1006204005440d00244080c5206115a034003e02d11410800c001501c641014030b0000c080200e20400c1003007540c0c00250042e0400c19030130300011400c1c0040038110041003800801030400c0c8003401000c01d00d64002025100341d40085071304002648000c10355042c10f00ca14441c1540d0320308502410000f00b42c0881c000c0c5082c0700041455890100d14100143d14100120981340119014081c00d1103031600401039000e0280200108110450a0031003008003007000038050300c070307840c441c1103040c0420090b541160020070020308025101e580c1480d00c00364003000340b4840314844641000000302c903040009011102500009003030a03001000040c040c812805001050b0007141070500e24032216800d103103080c0020003c210000d814142843c1c41814410440000d01d011810110034001040d40810076165004407410301c000c0d40c52119400fa1801c1c06654072420651100c04030010620030701000524100ca13525001d404490b1004a1001c075611050b1a460342660040d01c1050041d00740d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749801537 1250 749800287 749800339
    0xf0d1a040204020418051806090c092a19051801120b120c010318080306061b0a1505100b0d020a02030c0607020d140a02060f1302192102 60
    0x5040545080d0320780c041c040c01c840070b804000b030005d59a10b08021103031107014102181c8000341c10241c21141410410a40d85100c01030f90340740300b42c013030b2004542c4005034003107034440d41e0440540d14889458030318821452074000f04410301c00c0e940da81c0080e920b0144990200c03000c524004400940300080c0000440e481e4104103070b070501d019650030004819a0380c1c0b000402546443c3e10041224240b440c0c0010240d94507201450314085400100500044820040d02e034460f03030503900300b07482d0345c0001e24a4612070b540e040141107600980c42038000740007c06016800044100e102802191a4610400d400c0f80c10792042200005043c401c404200c103494008041c1007049104503030230035952006440c1009001c1d0b40c2107000da4025202500c069030001005032403950750110550900162482c0030b03454000c000c04410200100b000001d140a46074010f54003c143c01031300300003c14100700c9003800300324040e000f2800c01c441c03080e800840c1184020b0010030415405800000340809029000440c2040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749802787 1250 749801537 749801539
    0x7030503030f13050106151d0d03080402061b030901090e06030a020415030501050a020d0506010f0c0f02220501090f0207080f0f040308030c130e09060417041706060f0d1a0402 77
    0x706450503c08038109005410144ca610706450080c0380802034094541c200c00c0040c411802c000c4011503030f0990f12030b010f481c11241c050502103425074680c40020054801c1040307000910380c1131090304810707080000140c170600e0001c1e2a15800103454042c0c48a0001044801f1545035010000f820b005081582120002c400c42d094900c11050b2a540d4107800d494085424094a03540030070101c8640c2443d014081d0010f0302030078266040d4454040c01000c001c04428003510700a0712204810464035040c4510030b4401c0030340041400800d8440d44440505000e00c1180341c0181043c8903e003202100e882280e604c5540f0280c014501b40585a622210350805031598918040c20301001022401010046210b808100b42503541d4281407851240390541d039400110035510fa400410a000358000307441034216030080d403520f5412100c1c0e0307126469407081e17810502076a00b121200416443c000150305001d0282100c4810036103d6170800d010085955803c0a030219006c42100ca4000004058040d00240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749804037 1250 749802787 749802811
    0xc0905090411060d0c033606050613091209080105010803040317040506040816150801050f041d0f06091903050a0c0203030703171302030303010b0a120513050d0207030503030f 77
    0x14100c00c0c0011104070301ca01d00d011036264450610842207510011040c401e01c10b8140301d25043c3e0309085807605007c40c4004000c5d80e03892010035101d43d90f03440c0c8825460780ca01401e01508100745403107003034209007494210115191070400316581006001d100e069500702001141410710b151034540f503141c080000c140c4841800c00002c03805807035003030080c0302a00180004240d010f11207041481c144500d52b001c080662800c841d0074411541c0090300504490003110f50760240111040080c0040140c404500441c040c500309082c8820008100a4030500c0c5050941d9aa0b03a500c510f007946410035850140f8901c3d4030078480d400060f0086010b00802c3c0403a01d403214041140d68042490b5902164042e4013143c0b00401c113000c010110500c00390300180580030740281107110350229991380010302480400390030220309124402c4c401d50800001041c501401d124608101180500800e142d16040d40c1d00c0c02401c032140c401c503000080034030840340e00000845c95a69021780d90003240c50040d181c002009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749805287 1250 749804037 749804047
    0x1707081f08061f06110307140f0d0e1005031306020c12030723070c0306240b04030c0e0c1206011e090f05011106060907091707030203010c090509041106 67
    0xd808201c80c520a100480004070401c800a9141400d1201130b4814010003841e0303000c004d0480e038040140c81d05140d008903000000e0140307a1000e030800034424248401845035000746402507034408141c1c41107850584445882c0340344091b00700d90300c0c482114130400c0b40540c4801d440003d6440d60041052400107400d40c4c106064141e045a0715500030389101c80019240040041c100300181c150210081e0340d210641d00d440344559507074908854074030011306015542ca190f59440c00802071181078a07400d41c0444004140c41b0601c0304080d1b0010b0005a440410a01c1d011540840c0d01d45d1b584c0c011000d1840d800e0400c14410095005150010610b0b410010085584144070f440c2183ea90189005611405051410309003c81c1c5020385c1640704504000014281607141500880c005030428030035140c10015944054059410301c40c2d40c1c0c000c6004823411002c80c0c80701c0901042c2d01c4150b80c0708070000d009104050318203c1e2510741d0b5010340396001c424100030074006001e4002e01e480c0602c1c0030380014100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749806537 1250 749805287 749805299
    0xf1505091b040305030d050402010906090501120542010215130203010908070b0703151511010902100c1a0103120e0f090702011a0a140603130c0b0a1707081f 69
    0x40e0003040b06e25900d2074981d410b1208643e0013030410320207031101d03182503203002e407030710b40001c201c00410004902c2e0030707584034049826091841405c2d885c480c07203507100030310082200310941680c905040c2005c484440510700d401c40c96102040c1c0004a141c4c011044580391030300e0100304141d0440e100102d07410740d0b8440c260030004041c100500300b940d02130780901441c1d1900e00f6019082e43c48640e480c6900c02c1e074490060000c411011701c000c00c0c20110b46007400d003165920448038010072040e440a5400b44296041042a5034403c20180c44a48103003450714100d040b42a06085a010a00005042950301590840c1c02403003000003401c0918024a00325110401c07202003110034005589200c0140d44036406801c80d401c80c050b031005801001d8410700c00840c40e12605004249000031031510440000002c100c40d102090301c2044041c0d004070030103010650729101c1758107940c481c4101e00040703145a08802404c6170300300b008038818481c03a218162140d55a44015407007049a00140485071003020011942d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749807787 1250 749806537 749806543
    0xb031501110c1c1e02010503150d0b0112051614060918010b04050f120a030f11150118090f1209030f0b0702010e0a05070b070c03150f1505091b040305 66
    0x3c0d0880c00110100c680c96418603102d450181e298103080b01180b0085400141da0000459a0181e1058156600715100d400002c1b5200c46120010380b2800c07894002090780c2d159801111692071065088505c2d4012184009001c26124883d154a103100d2841034103c03410110300404642c0c2e40180f004c4801c03500c2d90a130319900703002a00080302d040340110f030a10041c00c0c01c008281d440e075001c40da40e42d429100407014a9680d803076808014100000e07800d40761482030254100750305060002d030680340c2031109101d45000c0d60710700f4828408401040314040052540c54810005580d03007180035991920001d40b1081000388042c1c10050400040100c0040460201c0004001c200c0c801c092851060401550080c01d580c540e41038096160805e804542c0042c500041903c00c87d00716020454403242181803401080f2a1039001503c81c116403c01840d004c103181e448010784400c61001044902c03448001d805451040b40520390b04800101c010502054442d00011940012041e0192610fa107958031a41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749809037 1250 749807787 749807809
    0x90f1802040b070c03020f010219060905070e0a0c26280c030906060608130f0515040308092a0603040f06090b0a05090105070516030207032a0b031501110c 68
    0x2a03104541100b401186801603003d810038800b440180300d003205202b050b44c407401d042107004040d00c0d41c0300c10031000c00c0024403401001702154071204071285010207060b40a071008007050700006282c910a48000301c0450701010085070300c9440000c0303a0355940d108041b8a020801c00e800503950311112245140000d014440c4600c1d01582c010440c4181e510700013007a68400c1d0003240134001030301c040201c0399403615241d00443d50482d03003c08070103c050030114240310740101c4042001c0d55460400061540086182e4003515401045070403140040c0c2150010f031580c1c01e901c010542c1161110a400d10f8004003441d04a402808903491f1000b40791b48540403140e603d6000c07a400c000d10010001070381040d20505920040301d01c0281300914000341e008000b4450301e00520b4200607050890707070515100304000006950f20000503030803c51452144034600282c10410b55800b00c03484004147d00c0d0500082d41d01a402d00c40e40a0006491000156060460b810b0f010540c0d1046000480041d520382034011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749810287 1250 749809037 749809043
    0x30601201207030201060f05030a0b040f02040501091a040b2805060c060f071e050d0f0f0614042919090f0e030c1b0a0506070503090a06090f1802040b07 67
    0x1640d0b202680341c003909643c0d007903010090780c4200e49000c00060310085181c0e06005e0f400113641d4819516458070302c2c1607038400c072000703500540340a002140014695000201c102c114602031007007414580100b1003524541110b0b10380120340d0002000141c0e4400180b8040500c83c243e1a2001035110004907482d50001d1450401903408141070119003044100201c1e00000c2c07600d03058424140512144115a80400c0c040f401c101c4001050640203640303a0294000c00358400040c048440d600b1080805001340d401303000c1681d14141c1c3d40070005c1ca06403207001541c081107a00d800c540000e10700d13013a0f25514840003468201c0000400c1000070440228004080c0007110000518401003400c03100446448010440240e801000101e05064000615a0b9040010b2203070903000c1090305c010460710603460340900d4201902241c8201008004405001d034000169105100c1e603507100001c540c0c0c16a41c0c03040044548407840e0038014084444422083d4104c800f2003d850603949084290090b840700c5825 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749811537 1250 749810287 749810323
    0x52706040303140103030906051305040c020a030305060105120a091b1205070906140f0105040f030f1e0c0e040206040e0108100c080106050d0b0f0325060f0503060120 73
    0x40304042e0140300d02d804941d0018a251100d605503900540250303014000c00302404070205c0e4402441c4002c03c581e5010f020050024069005205d40c042e56484042c02c0441c0800d04020005407154414020b59080850320355010341e00c0d0310740442d40340040c403c2420540391681000c3d40603000c2082a40711500a01450050307041c0301c852420228181600e0f070f00700d5400181810410031214109144081c109001103442c010900600c0c00180c0b030b64401c5500520000b0644103000007448030b0b1283c116a1280034812103000c002004100104009201c500206410001c60080c444840380310801d5a0291010301030320b1800752a4030507001481310917030008c3c060b41c3c007140e4601a5040c041c040d541880e1060309010190b5410b1800103849402080340040c405c5545080b142102d0341c1e070043d01d40c0070034000b5098440c5c681282d0820b038002ea5103103070b80450004130324100003501d80c80b0381c000000803140c9944050860300c40100440d00003500315515002c5030440946190510004e00c107804445440b0251 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749812787 1250 749811537 749811541
    0xa0204121505060108060d300f0909020408030729040b0105040c0807020c120111030f010617010f0b0306031f02091216092703090f0503160306052706 66
    0x1d20700c250303080200640d04029041e41400415103c0c01960224254002c19603081d00070394900c4020f641e440c0300d100e0001e0b94151140b540d002504605100d20094107560b611202c2c42e281c00c002c00c140e12907403051080c10340c82040044080b800406144c041c81d501c01030345980782242800c10b50702ca000c00b40c1e0242d840000b81e1004200c9803034075200724007010426040507411840e01800203920340d1444030240380281e1002d50041d00e070200070b43c05840b41d640052809a10b03420700c26030711440850240107020100c1c6d0100031003041581621072441c12501ca000c0709060050522000c01980c2e00050a46501482206c4070902a05d070b81c100189410443d20100581310200c4d94104088040c05003040a01500300721002c404a40c5110700003001c0d6401e80c000481c4200300501000307e603289202070000300d038019000000402d64000c1a42044403003a03682c103241b10303440b03600301500c5200c40c86159030107241c00a410800a80135401c103da0003010410714020030700c41154010b060b40d2100034007000703a42150007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749814037 1250 749812787 749812823
    0x507050109091404080c0f03030a05070905010203030907180207020405090c0f0a0305121810050c06240d030e040908040e090f10021303080408060f09030f0a080a020412 74
    0x60380001882c1e5440240146020151100c401c158080c101030b00d54540000c1d081c0c00c050701000000381c0b14000d0300841c0d1342c0745000c3c102000281001d54a0a000503a4a1400a425840042501d006d20010701c003804a261818002c4141c003049a400c40070025005d2000034050b9540c0e22907148641a0003001e042407030f00d60810010410340c05009e452080015420500c0480c500054200890560010351565402d12000c00c09182d0092406a40e0112610540c110541c1e4881c01514068003110212041511800304e842041c80c01a84da080714040740c034012034a0391800501d00c80209019040c603800049401002c1815140441c3d006d035460300d000075003041100e6213284025445000400501310501500720159110401c842600c03d0158004c42c40079000c0720180e180030000d40c0c1c000e80c142d039550358561100e0384419049620f500c460041200280c941c20000c01286c426123400201a8130b407409180b01075642e01300150070450941e40c213120120300c03c1880314103c01c4041c00380ca1400d0201282c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749815287 1250 749814037 749814047
    0x1911060304050f010b1e04021b0a0c1a1204110a17011a040c0509090a0209100f1107060e040c110d020a0b0a1e020f0903120d0b060405030d0809030c070305070501 71
    0x440f0703d80160280c004070051a04900d0910300d020a080f00c025070b27035850285e481500200505c0d14100f103800341601c40740070405a40c412404883c40310401060540c50310a1511040c010b2454440b82c2c1e0f000c1c1400100020030014542c0e842590040c000b54409480d5601400b003242c1200100c84540e64070302d00200c40404d0320000032217028040b00c0900402c0300c00c42c0000c1190003821440c45c0500080c4000c2a8650060b40599500d5800540500e00549101c0c0e40101036115401c12007001c90501da40300d204100010805c1e9054a2042d11020240010842484020000584600304000380400ca00f07441c1d58080c05005145c0ea81a40204540340d401d040020704180c001d420311406c0c501d092044d034914100310301010308810078004010f0300c40c44c220313038142814841d94452aa1600a00c031041d0409446000940041511a032041041c0b52085040c00007070b00c0b4030b0103115410350002d10342d203e80d64420790500d9407062200003940d00306070031b268001c0d14045d110381040724650040c0600b84041e5030300c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749816537 1250 749815287 749815301
    0x604181203060f050307080d0e0307030f0501020a03060b09030c120109050a0f0c0608010e1302010516150509190f050705090f1501030612030c030e12010905071401021911060304050f01 81
    0x49001d0300f1500e20303210306123694065004a16080c0842d01d400e002c406c0c4c1e000d00c00c0070011074100314103001050f110719089000b54014580340000c40d2904d0404a0b481c09140c003070301c441400c0a0020100400d1420401c05280d80c1c00c0042c5100f90740700c02c4088001079050000b03200d100d2184001d03040c22442ca207481c6080c1c041075000324003005001d6004225600c03030740051540003640c0e40c0c14080c0d40146800100d03907606c5071904118882d00101005002c200a0403000d28500b04100030402964030b503603044a4844a000d0498103880890b04100c01c041150603010f0600d0300d07c00c2088480342603964001c50241c5030300321001070304100d040041042c42c1d80413488208a0080c00d19003000000e08014585400c8405490003804005d903c66070001050300131410840c1444006000904107400800250701800d1400000c48080c0038070b03000091007007100700f94031000440c140c0203482d4508207612080c3d51517000250540c0d00320b410b01c0c2020380d0b0b030311032600450269003c0c801a10244e440d6020447c00e440207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749817787 1250 749816537 749816539
    0x1506171c05030906070e040212070e040614012015070203030a05161b061409010e010b060301060e06181e0102010b121011091503040c0b0903060604181203060f05 71
    0x10410419502404104c0e00e0784501c40d800c010704108200300202d0020b0140c0c1c100340641322400024004165040a442114582c1c00c0b00d0510480341c440007100414200181c0590100740180c001c80d50340e6040c1c4c24040e031010589000c840700505100d02c5203a5100d000e881c8140542c0000003846039461050081c03507070080780e8420844410403041002402014a60359039442c40780640c82443c10081c164101c441064481c00c02e51030079040c840c1d1107e00034100315000300125813902c288060703281002d5058904995140e11400c040c60024418891f956112034a03845840415000203038503136450003ca17607820400540d100540c0b41581001900311101c0041d52440744c080908000c0a2100019450a900c040818080f032800c02c0385000010500500c644c0d15408844d6050881c040700c13492002d140700340d0282d040c2c011041d03680c03a1890450b2084480b0581c0540284001071200d00705900040d202da080020040304008241e11400d00d0002c3c00d080003800280c581508100c0f988507100c0c180d01503d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749819037 1250 749817787 749817797
    0x9080a03080103020603040501140f0702160506180303070c09020d0506090f040809030f0a060509210a0c020604031410050a020a05090909120c031312050a1506171c 72
    0x18454602070104001448000c2c4601c200100150404c0303006e400c400040551203ca488503420203103044031002c103049614000600c500515190784007a0059040708940002d4800c6107480140076200c440c52071005056609480100311040006540460500040840c0080181c80b4411000c108040d2031016040034840c220708810b205d132400400d642c40d41c02c190b008001956981000011904040c44a0510800c0e402822144d00078442c1e150006440b40320b40d80d080d02c130140700c074403192404181c1800001007000c40c11301c002103086004521681700d043c0010400384c00c0c02e541b80d451030300f0340268503d04001364100b0301d1446d403181000d000342a00044849015410805407440c0108140134101003188611000700c0072174504501070000707015920350900c55135075071502c4450503580c0343e000e14000b40340c80f00ba110f40000c500710750b110300000392940030300504205a12601c07010814111803042894241d03503034000080c51103525907411401c80c024409003040d2107520000c0000d81c0c03000049801441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 749820143 1106 749819037 749819053
    0x612020a050d0b131e320c0f0a031b03050127060801150e07020606060f220807090501121101110c100306140316121a040308070908 58
    0x40c2140c0c42c180004144218814143c1c90b11603c040311100c800440300e0051b018078841150000c2540041a051034260410020198000d9452201180e906c152140c881e02d00b01040c10403681103810100501e42c54041c02601d085000e140d0103004280c02000454031030465480320025084a50003001121000005070b48012828009e10142c0d00c81640010503c070310000b80c1620032507001d090789040100e2010074100781c0c1c000d909081c0303000c01031072807a114040c150b03014600180416001002c2951a00084404841042e0802e034080102e01120303001180511000e043d021000b86441000f4640030b80d481410b09210001c00f17940b1601220700c008030a940354100c40c0a603018a12441d80c1900480101591007a03118101450200c0488080009400b04d07c0e460002c2c901030102d0340d035041d00c1d04000304c0458204840c2200400c032000140301c4410ba01c840d111018200d034100600000f = true := by decide +kernel

theorem cover : BRFrame.Cov 749640287 749820143 := by
  have h0 := BRFrame.cov_init 749640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 749640287 ≤ n) (h2 : n < 749820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
