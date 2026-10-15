-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:52:14.53932+00:00
-- url     : https://prove2.me/submissions/9f93010c-61c4-439f-9f22-fe49794b6bc3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978057553 ≤ n < 978237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978058803 1250 978057553 978057557
    0x1611010f0918020c07051011071d0c0f0910030e190803070e0d2f1e10050f12040c050a03030206190221070f0e091501020c0603190b01 59
    0x12003841d00d000a864a5890107501000d0b580000795140034003411302c005805018024902c00b0840720f070f40707001400d1081c140c62284d8640314007003021a001014011480007445012043e50041d500d0101c244d485400c1075034481c00c552424030651141c0d070346445201d200340d40f09580000e04103a42046091034502089480907480b1000c00d030500100c0c0310307107088a6101c40c0c80d040400c0681c04c0200880c0340c013895074001030000701d40d020b904140400d1404070071504421282000101c1c010301130410080003c5905003034900e01c20f00920141a003003a50032070b4814980c6041103400c09983c0080500d860b400740200c4508201210100010005450302d4807010b00001d485111109065a8010f0364803c0d000d0200d08418012004a001e40c0d41d0a030101c428440c000810182c00d418440705120501401b0381b0040046a0000340c1000664800c068100d54000c0040c10300035a0389508117800110100841040c1c11802445400492912110000c60190512000782e01214007d91180000c0f41c05403440c01d41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978060053 1250 978058803 978058817
    0xc05030318010b1e04201206041b02191b060809010501090b1804080d110a02010b10020c060c030c070e040323040504020310090f02070c1d070f051611010f 68
    0x1004403092041e001c84d50100b91000078040c54100561900710790030440ca03140c607820019505954004d03001c00f842c054a02901d017400118150032091080e0303441c81aa2a00681c440010704078208090050410640e020326000092104102024030082070150841000704810909210041c2c0c000d104a6006007807030802046642000d00000d0484007031404003d070f100094001080601c00d0388011030700341c62a41350040007403403204640610280c2000320000c001d54a811a4200b09041405c4640d40710000c40d80500020f81c01c00080040f260420202c1c2c8445100510490742031200400c01600030348219150000940307017501e0001c00741e00f442e00403180740750f040d401089840d00c0908165001c3d43c0c001c40c2c0c050707100d6a583d4a2040081d600360301500c03105080245491480c06250b00401a0398000c0c4191100243c0340c4c1103441c1c411441c1040320000380640d40c0052912845847c2e00c03d45001e852400d1494a0502c0e401080781c061030917400d441007552118409201d60700085600341040040c06c10751 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978061303 1250 978060053 978060079
    0x312090a03080c030a110418050a0908040b0a030e19140703121202160b070e0603060901050603061c03120e01140106030e1906060504051b070204020a0c05030318010b 73
    0x401a60000c0c00c1610f14150200204030f6119041d00070705420141c4007203d544541d42e8404c94102400400c01d02c170091443c0502040b000358140c000c40c1310a03030b042203410703180c240381c1101c920f01503024801c5041056516211052812000e00c003c61118203000602c0382c6280341402d01c030100d0341040c18803040c02d9010301c40030000104a6180f0006214581c00c0102401c41d2595516001c0d10803080d0140c803854411071544200003000f03004038010310140d80c40c0803280b200c2000340003540c44295161580b0654031001041a890100001c6d5408980a0950304154030b503c45801c0b50f03980c02020450105001e26a001c002c07940e41d200e403c1c42102090004c1c0f010303002511024002e0300040c0a06000c03d40ca401496041d58000c20000c0026141201c2c401800c00c02400c005004141e94007a4502c12414500803d4a0890203801a0400c45444001628200322039003008002d5001140000c2408030450300307103011900503c00303548120750000d48182c42e40300c8150407908503001c070170325103108600f449600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978062553 1250 978061303 978061307
    0x90b011509150908030307021b0d03210902030a05010f05130b15061905040f0608040503030c210103031205060102340e0106021c02011e051302040c020312090a03 71
    0xc14216046609944400c80c01c02c0400c5540d10f500313070041c2d00103200010900c00000d030b000a20019804000b03c0b007400c42030302481000603079554840c003c2c5c0000d40c000b41d480503c020350300348404021810940012404d10340c0d40481c3c1040c050f0310041d9101d035518540c8040d8070206014040c3d005240548000542220750303500744000b440540724556078034444412150075207a00003100d0030804440c0c1c40c0d0340c44207a02100100365031b00500480a840100d8000042c4180c00744070002e0013280e11902440c11030b82c80b9604003186070400c034076407803031242004c8202001190841a0740e019500a03581ca40045e081003050740c0070340724058056811548a40610500001400e02d00b02100c1c00b10810888c850110b803c1e800903030038440d00200c80e021b60410000900c0c1c0e0b0000b0300b011909003401003140c00300c511843e00b80d080710882c2d4200c1d110085084001e003c145580c1e48a43d074428001440030140820903004501101c25002030100075900c00110710728401201d02d1140ea002c0d030158001c242114446e500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978063803 1250 978062553 978062567
    0xb040212070e191203120603080f0a090b03153d02010e010e0a140d050306130e1005090717030a0e0a0e04050331140d06060306090b0115 60
    0x10440402c4040e03820641e156544804007030240c8a01c0103c203219a480d401d84040041c00c2060450100d007804038220400900c901801089a82001885041443d4088240120b81c4020080c0c0d0400c00c0715400481d030000c04401450195404000144d010562607090204c03064580c0a45564014120001c2c100b07006c561410340c60550030360b540114000c07114036040e03000d030100c8a5002c14550070b0403901c01e503d2400040300300d010b81c0a00040303032543c400122015250700c500208031002174000c000050450900d0076100310742d5039002c44001104e4513a454280c1c1041c2c000b1000074070242d02c500a010f2681001c00a00d000b8044500c5044143c016420710141e0b40d02c2641103810030b10007682840180c0d56030310b031800c00c010078080e80d810091f0700e054a000c0351240d00140d003803108415080807040000340d0880301e51104110f0ba03400654000d0402e019259142c0200350300caa400140d1f420f0103000150310380110b20003503100703e00104030035400d490722414040b4140c01143c440002ca101c24101603a01202c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978065053 1250 978063803 978063811
    0xa020f1314370c0c081602011704050d0c0213020c061f0f0504180203070803030403030606030c1b0507150e1003270f060507020d02010605090105030a080c0304080d02100b040212 78
    0x1c1d00040c4070f6007400d01a1100107081c1009841c144000c201000b2180c014010000c46500c01d07078590f039640c11814880701124106070b0b000b07801076101110180880d40120b204400480c0000c21030764a1072a5260180f044c1e0b0302c01c640300c0e451a0480018400408110402c8112820491302c1c03180c260b9003050000c16034400c9a100e01842203480c0c0c4048038a85a4600e154404e4540145c1522425610340f100c50b6501d500540302180001c0c030300440007840034800c4c070070105564400d0741d600668840b008005000107501d0842a5054010703c4000a40b00341c0e410201d824101860701c40406c142052002c00c4100c28180320f0150906007000394110940030848003070044d2035020300c00104200342174249658426100e420085c83c0d00c0c40e002c14040d078250005005901c2c92607a600901205803500e0601611007001e00c1001d415030721040d1100000b4443da0098200d000b0500100c0741080e5440d280c180c03512043d40842d1b009a04941039a941018580c0200301b4120b100703031001c1d490110321031103494a24034018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978066303 1250 978065053 978065161
    0x3080c031603020d020403020a030302160b0702011d03012703180f060c0c05130f0b12100914100204060207080c01020327121e0109050a020f1314 64
    0x103142d90803032407180e05607800307148c015215a07031090300c030301d0701a594000102e000c0c0303884451b4000005600400404407034032268103964182d90b4213061103c503182801c06140c3c0c0341c1d155488241c14042c00a1390b2020841d0145130080000c2070540504000e0821401c070880350403400d0100405201541e02c80c04100111a55031a116040ea0b02604040004490a41200b40e01c0000000b405040340080c1d08003481004c0300c40300c200030720b501d81003c10030040500c55000040e0340043c00d958555022070381c41090114001d07258250581000300041d4207002000e003d4000466000c078003446031300d5040081c100034003403400c0105503400303548001075628001c10f00034109020a007666003071200d508140d1004030107805042c80d03250410750b9103500d407515481c2140302500220101380b0311030720005000d002d00e0b070364204d005855810340d41d4080c40b190340b01140c5840d40002c0d0001c080c040e50005e40c418010009010042c1803d0703810400c2811056803a0680031284501001a20b40c44400180c0502c000b03d413412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978067553 1250 978066303 978066307
    0x3172832031f0f030312141504020c0109060e0c010c0c0504020a0525050f07030c091107080c060106090b210712090818040203100b070812010303030903080c03160302 73
    0x20180c00c441d0440251440c0b214450080c0c0004290b0722480c0380e407003528869100d80c0715084a11080d13904a40051480944505a01012400c0e0401030040c0400b0240043c10240c0707040b00e8440e01509407aa56681210116696a241030140741d0038882004140000d182440c250081603c8418500c1c0c514000c0c2889684e002415181d018007500441e040000502c03650741e4581c03442400711364442d100b02803e0ba607600880315900440080442c9010a1ba948031900c0c5c8106800e10610f04001c10141c400c0c000c000ca4100720070000702c2c45020203007841030350140013880b19604204008021001c1d46e84100c070003e90902c41c0c40568041c5001c0030041030744940c03013038203a0755688408681c45100c070810095554a00030101040c00030b96802407041c91060307400c8841d510508030034030080b07210482d1102d610806031801070007000b4141d4002c100d428081c2f00560f003803504d00704100307145800a900440100c0d90b035800700300415030000360041e404038110700034074210310b040c0316042c0031615005c050314105a40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978068803 1250 978067553 978067561
    0xc0b0a0905102403080c010606020619090501151205010e060114010c030e09100f17071203021524010305061e1c1410090c0317283203 59
    0x40800b01600030015081c0f0304800c0c9541303003081e007850751003850760502550074654049a06c07030000940c58000d91030f11444041c401e501a42c0030004001c0340c18101c415540703c0c0c80a91085941410040180040c00102e1036107804501c0c0060841d074400140c0320321901b02000400c4002d81e40040324070450002e090180c20002c50703141c100d60360743c1104011940f280e4680203101e41e4034981c100c0303901500e03c0603a94404081d10b071022500500e9550000d40840e0740140130600109800510100646110b40121015019880d1488007580c41c112000903600140c10034400c0c0c0080ba0344559020b40c030081c05e0802560514601064030101c286c49450125041c280b40c80360241c84090521020800000f92251010034510344a003004010b0007007056244641c3c01003140f201440e1142c00c00c92940402c5c629042441d550ba04a2690070000c3c00341ea1800b801d10143ca841c0d034445103192100c42c614218218403000596002e0081c01d40b4103d0b051518543c030088250580a6403110822170000d440903d0703d0f651 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978070053 1250 978068803 978068831
    0xc050a11150a020319050c0403021215072a1a100b120f090601060503150d0206070318090204140915030a061509020c1f0e0a030c0b0a090510 62
    0x400110300e08035031031080c00c00400d140d0b0b55015500801d005c0b80801000144075101c0d10a507441a81c014240c0c440421042006140020701c00d803807102c0c20341c1980c80c00f28001a241da000e00d0112201c102142c121680e000c042c01d00d050412118208502c1c0d940c1620700d168582e01d800c6003104040b6a1220003140215852400501c1d10f90010034040c80900d984014840d079510180380300381c078488031a160520124051040200e4503505a030f0044d640c0e50b0a6680e40440046c90100300d0550907005100381c82c891025803a468020400180262140039400c6800c0100c00c1c0201140d03400140042d01c1404248800600c450000207004811189407c0700d4894400e04036070307a0001c05000d6454440d060040c41000340c03940150600f450311900202410740d96443d018113900c14011071020a4100b04140d100016400010340d0212523032070400908071405840e0249021241a820307400304505045030700421500c58443c55201c8001d6205000040031556003d90300c0c2344021291032480e80304c0342c4070400c0702c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978071303 1250 978070053 978070063
    0x1501081225151a130c0c03030506010905130c0f08190e0c0910080d021c0305090c040501141e09131401050a060810060f050d060204170f07090c050a11 66
    0x800c01c002c1040b04001110103000c0401503100c01c280600070404000020309180c3c41844601c1c0c40503100c8a10758001c60380c045002700001040c1300d052110701000401c083e04c2e400f84800f01e840e1140000101e181100001403c2d62489244010420181c40200310b060285e000b2642203c102e5070201103138003e5144615030510b007900c0286600128071070108841c0c41e0000c010301c401c5620400c292021007401e00d40490f110354019041003d44140c5040d01403100e0705c2580015070050000050f101600788160004080d92420307030280c282c00801c0c182e481c40515042c000700a01c1122848140c041e40d9145010900c2584010410400103104040200900100d1103814000c0082107000304964a80400e690004041600a1b01902d11840c8681c8401c45450300c516019198400c060b6062107240c5401c022041c00c00034421981a5028440056484030740006400f120002401919090011003e42c901d40b42c4103a0103c2e80302c03410302c208500c6464000048408101061a0002d4400407009050303240c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978072553 1250 978071303 978071333
    0x12a11100e0a0c090605060306310203070f0903050d200a0c0603060b090d0809012d141c020a0306030b0f0a0614011b0f051501081225 59
    0x107400d1007808036007040d01042c1c0048603032040035070922554480703c00f8400c40e125070003850782100040001c11020b02d010010382d05c12205c1b40741c41c50808185202007900481500c03640108c4c0c3c640220a10a1140d0030017201c030b00c8101e2500d024810949142c548543d1100603403c21700070710402e00e9000c20b480306054070070080e21003141b00300c0d0880f00e901d2510381000030340c5100f0300c000685880008200c04480008541038030b0070003048001000c1d00c50316151495488080b8145c144901c00d0b401d15040c01c0205214100148020041c500d800702040c4044c000030044c40e0802c0c0c4051041009998542c606079442c070400e07101d284016241e5800007020b070000c0110380c101420150801c01089840e1328102081e078451421040144243c0755220400f40c5a90000f0127824049003d900000111008070480301c8801400b851019803034070700325103425040807401c04885002c4d0208400610006108020003084d403032070701620a00d00492448103201048000e5031203045211804000e80c24408071880880030703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978073803 1250 978072553 978072583
    0x60203181606030b0909030904240b0301050f040b18090a08180301110c0a02060d0f020324030a020a050108100f08010603150603050705091b0a030e012a11 68
    0x1904420441800700d0030b441100b00103070a181c4072403c10b0a0254055004102a4001b1824041d118003000080c1038041042d403400307034605d15400000c50400040c1d00041c54100c42da50303038950601d01405005041402031034044d50400d401d029440d110808041949441c894890503562214001d91341021454030f0060300040000c1001c4440701e040c0f40000050100490003008503007a002c40e9581c6d00d001d40d07503031040c90303801000340c407809070500340d00400032141140f10024180800c010520201c2e08240e80c00c581c0405200210180407040c40c3ca9a42030581c110b00425500441c0d600150000c03901d0701426040225042c086840c100e1000000009003c046212440e03041d101c2600300e0003043c0610055611200d8803440f40b85400c000d02c2040252034011025101c01c42c144010b1000100b805442c0385280c5410981014844c41000060005440381d5a0085000c40360340c601ca600f55401ca80d20440d150840810140f4070000a0301c0d161000c10140c186210407a0048150604080c4406240c1074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978075053 1250 978073803 978073813
    0x308010e0711060f061008010806070509010c0c030804030309140303030a0906091505070207050d1e03050c151008010203070e010806060c01150501170f0a0f0b03030711120102070305030406020318 86
    0x1303000b00d190b05803060030182c909005103600480300f01c45c051400e104408594100b600451740e140d02c1a0001c0c0840c6006051101d045075459645c3c0e1001c1c0c0c1e60340d1064501c1d1002280502c105a442200d540003041c00018000401c40020300094480c40081c1c0039000c0745036100381c002d00700b2600d600000320307664000d41c0030b44180360b1040d02e0754081e0804845080c014050000c020070645840c000d0f042c8680d411611a010214000058070720b4210f034081c060b01405014001c4007046a8208101401c541005d81914411b091208030b03500c16a00903000b1081d80d034010310400c0406907110410400100003440c21201c00e031104004100544600900160f2550a1980590088218020703450840d0421f99410030b910420015884204c44e0642d03410f40341c0b0030301c540810f200240c242c1000c4003070055101d001a213505070710b001074a550703c84001100c00d81212581c00040d4988810400aa200000000e500d481c525560060070f03880001c00051074175a0110201c5d901490642d25802811840c034220382c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978076303 1250 978075053 978075061
    0x70309030605251103030f040219061e0302121b0d0e0102210925090612140c0303071e05030403081c090b0a0c14030c04060801080a0308010e071106 65
    0x100070902d0090f04844100401141002044c0c4601c1d0381c030002c0c0070414040c1d8190348840d0228042d440010b0001c5e0b0740710040780501100100110348550003821151500300b180086448013007080a00001c0d40800d00d4070521040018501d16182d066202c40748865901109900c8000381e00c02e40200400086081d03e80700000450600c154020207044a02c4010001075180e281c0c200c808414045448481c541c201802002000b40c1501482100d14001040505140c1d00d03841c1318412508540c0c4010542403040001d5000d01a081000c9020a0001c0d03024007003610382500800c0c3d81348200400141080004140c19060f60750b858111051a030344802980d40e519500d04050802d0f41029501c03541d2803082c00c6485031400030921494588541c0320030140321a680d1040c00200030000500e9080620180030510390000b0504001984921006454039407154101000101140016081a1000d80c00080450003080c0c2184149045480400c0d4043d501d6a4010040700c0f0342047d500d4000791403140398240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978077553 1250 978076303 978076321
    0x1003260c030a1d0d080f07020607030903021f080705090f0d081c06050a051203070b070207081e0303060f030304030b040b0123010c02100c020a08030403052e02070309030605 76
    0x50a1061503955040a4002d4003e4640018040e00340d4155002c0240744d0180c0c002581c0001415084240102150a165141c0c0200b42a5404080218001400f10405104500c0d0034070344141181d140d86c03e0320380e0301651414090145034014000e10240800480c030114195180c0244c045000c1c4c3c090301600180c001071a110581d0380003202482c1c203200b00340c1610301540d48035109607021908000d10214409207004213010340c2440c11107081d6014041001180003007040303211041d006908e80d038020200c00b440d210825041030380f000e0b801c00c82d841e60b100d40d40b609410000103a0780c02205c100d0b14100380e55002c0000910b58402d03a40010030184200040105001c01514850b04855880985060a00c4501202c90151807032200087c0855000b56480303000d418801d80c8000e1418885c05c200900400a40004444100c2680310888a60001a003841040000d102c1c03401c0411085100f40c4031000f0f5044c0c002e0110f003281d0351960280b0707408500442410f200d0203038a001541c00182c100424241a201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978078803 1250 978077553 978077557
    0x318021014070227131113060e04030c0b130b0c0306221a060a050a0c050111070f020f010f05161b120218060a09111210080601050303031003260c03 65
    0x8044807204e1544002020004201042164035520116202582d4020801c20884203004010003071041e5a03114089403001108104034000c0307002c1d4a441c8000382041c1780903180c40364004d02098007142c50006020020f001c4901942c0c0003088941480c0c0c9039500c91000c91104c02022590f014a81c2e100b2800941c070b01055803240145c40080074524200054640510440d8400d9100d5800041d008002038006c80344510010350b0501d103d1800852a01c040c0c04152680e50402c50041c0d60300400c82c10b0050031860704030307181100c0300c8080c00c180519a668102c044c2c10760003040740c40346000f6a4564440200030411a400d80310442030840c42625a23100e201010260b082250224090300d1805100700d982d400401c28540703d50001441c5200480c03c100390000034003942100c00d21844014040c41c044400342000e4144100501140e02c0303411b031700d0205481d190200607405180a41c000704107005090090400c01402d032074000002218a01c803596030000803050340d03420304404000100d0400e440700d03c0440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978080053 1250 978078803 978078859
    0x201c0212070303110c0a06140313020a06120e010e060c07030306030c17010509121e0702030a0b2401141b0609030a0f0509060702040507090b07110103180210140702 72
    0x481c0c4117800040c042c05180b0f103140c0107060201d1341040d5102c0201c0d80f0b660043d54406090038402509800c0b550211301903600d55001000400c05203c800c8810203050710800e1549a514002805060907800600b46c4500020b820b0f40c19191001407880140340c0a90840e00c02180c3c090f00500318980d8030031501c010604000b03130305081c0354240404100e804c171000400440217010007408504d803e241c4240084901c0e5940700903084070205201c401e000d070358240f09090740240680c0420800780360840d100200c000c403407001d042068481c0c114220701640d0059a00303040504034903649503211917101e43c42240c07940100408050b48142e0040000c0c1e40743c088042c0030b42d070742d4540b5070200d1549213141c103449602440d40b04a0700018103001d1400980b409410040d0050b40604152040c241c60700d0345401142d100d00d40071b0318041c85d4100081015641807181c4000307040341800b040240840fa9002904195422600008000c01c02804850b41c10910080702c0700258000c15120a032441401074805800c1460 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978081303 1250 978080053 978080087
    0x1912230412121707081e0c07060b09010b0703050d0902060c1e010e0a06151707030b0c0708030604051909030309060b01020706050403060f06090216201c0212070303 72
    0x81c000c41c141c003404420f180c1c0c0341c02c11541143c994514108a0b00b2407030051510103000a01210110307079604540219001e155000860b1750b8401e0141002000e80c3d800b0000280188240d6004100c03034807404081d5800c1c540c0c145421681ca41501ca00381015041080000e94403201c0024010b01d03042c070024441da80581d1882001c1c42144c0c03800f6010703007200e41500034520f40703820042c06040081c001d03600181009054403044032013141c8828105260410307441315a60194050312052080c007400d03500440c0d01040300c0c9089850b0601a41d503140d00e40c0800b400080c01139032541c003c9240c070100c800d5103000301d058040003007144c0100c4d801c005018155104090316500e140181061581d4400b041460580d07406840d00c511f449e00d150345e41001054500042c9440710b69a044c0441e0000090005003565420300004100801c82c0303080c544030f111031082440034508400b50a2000b2038075180503030134078911041e4001540d030b0300030300124003842180c408254242c01070340310100405400100d40300702601a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978082553 1250 978081303 978081323
    0xb03071703090a0f061202070614010803030403090b1305011b050321131101120e0307030c0b060108071416020a0e0f070507020307090506060d050a0b031912230412 72
    0x803d401e9210030041c1c060741000692040c0d0b5006c11303007103035001001e40a01c23030540019009142100511500400e80100301c56800010610080c154030107140c501402411941c585850b8110922000314203041c0304240c10300c100342d03143c0d5001d401020f0284003125001015a9a00e0345403600100950b000c1b0350800000000c0100411407500700240410116580034011802010869005441c52104100792001e0140c4586016008030424006007000701d00c251a071410303440e0580b62080080000074080b60400001070100b000d41c0e45c0c01a6910031404043e46030f142c0c0e0741c01a0144001c407400c40040a50131192510380000e480c400009603620512400e10004116140c21000b11036501c00e001d0081d44c0b66120031410f0007481155400b95030450002003e06180502400740ba03010789600b151003200d280e546480c13402882c241030100003104d040e4108d40f034021500308c2d0f54900c083e5800d500030608202082e103840c050100a150110206481010400e03200c681e50807a11f0902c006101e0102c07003207249 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978083803 1250 978082553 978082559
    0x130609060207061d06070503070c060e09060909070312110106150305090a0305032d07081630091403130b04050f010f0e0418020a1203050d0b03071703090a 68
    0x10680c1303c41c1c1d150074940c010382c1c01032081c001088200d400c0341400344c80034003042000100103000001c44070001c0260303480d100c1d5201040010003070400c0d0024000c40c0250342130004c00980d101d0100d040c005407a8850064024016092003c803404021a180d4210b01d6190400100b1800032248200b800811203560601841e650f650b20b098a940003040020080341081c40401c200c0030001d00e410790880b030610006081510305918038817541c48240c0d600300210380204103011140d070001c46408181020f0b420411210302d0628a028101141c201140700a401082d441130500c0c13000d078114103031454010780382e02504540320300255144c2e44100e4818900310180c40d0300090340124002560102e0f0b10051501c440d0718945801542c600c400000c0800810016944210641d0342e18801c80440050a1440204211080c0f06211444200d030300011600303203040c01e409002941c06400c51b410100e000c1c0011544996600201e4540500754001a2084e022030228458480d0000302030440b00b00c0841d0001c843e00e903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978085053 1250 978083803 978083807
    0x14070b0f04060e011707080406050705031902180a0b030a0b0f0a050420041e082b0903020d141606080601030b1c08030f090c0901140613060906020706 66
    0x45039160300a180c1030248030400c6038501a12001509103418100300103079010300300a20504d09400c94001010078500e00c1840240001482041e6001e601400c0903842c5081003001681d1a120948600041540004904041000e0340b500c0d00d2080e0406040700d5015512102030940581045a8801d004d0b0702c0c01c0c000300c4a42c54418901c0000340d030050b10303a40c83c082c1498140005481c020301d0005215a40c010780c1b070a00d515010041c0002d065950551003c0300c5a24405144d09416501c1081540e20040854008488008040c02e40f95501040850700c2c01580314251000859988065400050783d6141c10500c48807034085070081c20244244c44205820070040e6140396542e000c0c900010b0305c13220000707055500952100507070040052070414803d19500b4910781c00c0c0071040042721034420100c14880c6000900c0c2c865500a0381c4030019014205d00100440d150302030501c14010089200a5510703031648502003159104100710004d2000651a180c0c06464041a44500f00051107802e0000076818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978086303 1250 978085053 978085057
    0xc093215030f0f0c0a200601031515030213181406010603050c1303060c0306050d0f1106160f060b040509010b01020601060207081c0201110a0305070306090e031603020c03070314070b 80
    0x2108001225041c5042c00314111224540f450780031582502e0b503a070262621501f007081c2d60003144200080c02e40d19031401d40b043e0903a21400b000180130100344100b440140c0c0c1c1d042900041120007540003810503001d0408111260503044c01502d282c40b00040320080c20b03808585a810b84950361002d218680b10750181801c544a0a9203810354110705050520002e14940c11906180312103260215101d51200c0018444010142044070501c8143ea030200070002480c64042414100300c030703a181080c20310300c096003119000078001400c0c491140e183c3d404000c1198414100e50201410801242c548a109113000f852242c030903e02510445000003010703840000e038007007551a82806000c041102555203031046640b03800460039035403550000d0b450780c3c0f135460285c8128140c541e8046141d0800050250441c1c1c0160010300013981402c590340e4400c4000801c031515030980000794144403900d0b0070220305180070000300b81c5c0d250141c0d4031f0020900280e6641141040010340a44240c540c0c0c0e21484d803458 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978087553 1250 978086303 978086311
    0x4060f110a0c0b15061218070e09100c0f03020a021e0303060a0e0613150503010c02061008150105061c050117120a0212130801110304060c093215030f0f 67
    0x44402040701d02c0c1600d06d0a448580c001e81c0030f4805280c12060708945604250098100100040060003000074815003005000c00c52a80d0741c3c2c08002d40781404400400007410341000038207058000603c01452442046000d40011548074030080300e40c15101102d0700c036030090b55894469081c1c82004101810101e204038043c120081088581142108181016004c07108400741d91407140440060282c0b4280101402c2d641985d000d85020300d03003000385071050400c60700844219404451103a125048003c00300d815100119030f034903141c4d00c02c03005010426140660500c842c40c1007100002e0005000e50040b0541d40c03800c2c0646640302040c0c0007844242c0203403202070b80144d00a840c001c440c000020b0081091030301c868564140c17607072500c0c141420b41c2d0300c1140c0c0b0300b0000400020001070022600c101090302909280c60b943d447c0c40d000c0036100e02000e00040d002c1c00542c44848180800c6000208498104040c000c400e603203280c462041141e41088031060300c07042200700003445200b100300707010b882 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978088803 1250 978087553 978087559
    0x703060c123312120f0c0510020306060c07080f0d110606060913020c07060e0405040b06060a031d030909060306091002090d05012a09060804060f110a0c0b15 69
    0x80c041014a003000a4a424084002d00e210222012070725840325070b0b0125140c1c0c00703201c11650030211000c00030517000c0c0c000c410000b044003142c600ca000800115400c43c04030518040580c582e03e9280c001502842420300c030010b0b5114240000032108000f240c2d01030034001c40700940d203807c4c81c240003e07a580d07810002c2010283d0022000960b15142100241074084405400030500c92140441c00b01243c0c040b600c1034000307911000c010800c0541c1708000341d8010000707a4040c00681043e81d41e40460000141840d8800d80b4041291804117201e030b0b011500c0c071a00740480c003c00d075030184020303501e9902110010303000d48500d40003d10304d4280000c1d098042c03c05400104401d002c41d0349100d0080d0844012140d004840c46000008601c0034012180016448069401c0f01681d1021765180d00041400c96000c1c0462610200446600240039960140d0000400300d0100f0501120400070500702c41040f040403804030b04800000e5202540380087d5108000411107a00c0354083c141c24501c02002c00da41c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978090053 1250 978088803 978088841
    0x7110316080115062a08040f032315090c0a091b0c02130c09050a08030c011505011d0a170a0606060804080306130b041e06150f140c0703060c12 63
    0xc0c4048011a0408603041205d18540f01c008280c1e10407909a000b54010316480c0110b4100382700f880100c840710f120320802d0042008510560f070403920b03141c40c0b004882c944140360070b80c0010140c100c240b2810590039401031410700301c29169940b050040c0040b02190036210314002c0088507290045046000b01900205114003c1e200d841b90a400760101050850800544450024054880e001c000e0080c0c1600009162100014800e01c1c0c2150080300c40d1001c0b07210a0403080000c0e9820503020401d4007446045281420403a03c0130680101056020030403809160010014613500486d00e07152061140c20305000217035070360700112a070090555001e05081810404961186400b95646d070003080900c0002c02c00c4c0810500241c101c0e0b44c400040488101255840554038000f442030f0030183c40420328000c02c80c3d40c01034005001e8515106038006100d03611900c0840a44904261206e04e001a42158507241c0c4074a8060050042c0030302d0800418400300009003210540e00950005562081d0313242 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978091303 1250 978090053 978090077
    0x80607020109060b0303031b0f0d020a0f020c040b0a0510051c06030201020d03111b010b090103110f18060105090105160503090103050717040305090d170304170c0a080711031608011506 81
    0x5017540d020021880d11049c0c00c1000c054001000d00191200c0c04440c0c6030b42c1c98207040d0600103800c1c145a031883c24451864824141144d6407242441000c0d00c4c2d06440e5025003088010058408d80f0442c0850640d200b5a49540d2002d0a400e030400d50135a4401e900b034036000c1800007020790035651010b1703081d102410107000000f03183c801c0d8100e10100d000400008074a03080c081d4045401603200380c006440c04e0304c581c400900c2d41d04110120354107201c42a0345e1102000c00048c0340b9240440058405410040c5c0040c0004641c0c0c031500039a030423459040d03030840140d1110710323040c0c0e900d504c840b85207800b1a0402c1c00090549014101e040743c0c40101010b2600d03143e07280d6030111034580c00040c0995010240b1010a0080f8051490511780202c0c0c00852036a43e06050a118003111303010391780380c65180000c004034044108003007070112402d0750210002c2e80b5111549000186850a0103c1603003600c00c0350014800f00003c64000b40480722000d008212021050343c1501c20070465003e01004030790061a11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978092553 1250 978091303 978091351
    0x6050916030507090b13091118060d32061c020d020604080d02100b101b060b040207030305100503160e0c0c071508161b020307080607020109060b030303 67
    0x4268000302624244c842140c464507000c03140d030004a0f041182d00e40801083c01203c0d250303c5483c54404121450b50300700392194800c88001c0c021111407034042c05000c500910782e55002e4020800401d00441103140000c56050112030042c0307409010000311070460041407960401e180404090135030a01c944451070341c16002e221210200348812070700710100f04000948131034140700b400c083d020154090641080300319810820348098101d40c91241742c8400039006016089101c103074070900c4120640312084c425007000c0b0010083c0c1041c064100d400052171600301541a8403051050075280d6040c60410380318018103607201294030640100b2a0400c2e412300c0903070103990f540c0707a0180094400b01d1608000040c0700e800e092641e4002d04007010102c3e0311a8049411200340e6911021515440200031070020000700032001b02c100030500e100000c50441e044d52401e000907405040c410048500500300000028001c0c0455007040d55024642a10801603180110803680101c40340c01c0112a08a689804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978093803 1250 978092553 978092561
    0x2731060302130518062a040b1204080904050c03010306140912090609041401030b07050c0604030c020f0a180e0a050a06150305062401050c070303030f060302040204030501020d0605091603 82
    0x140504c850b40400c45904c1d01403c10680b4882d160303a00d000000804030b40081c0c8140e1140044118021806000030301c007480c902d0003078690200124113010255111414565064415111410382103070a0404114880c0481d070000c3d030403280300c0d101c200081600c0c41150300b02003400f6103051400d42c00c8a00019640c95115003d00040000107050314a030000d1b001c00a800c60709150b044940c0c1481c0c000c010010710035081503032903000c1001d007001813410a4079000d8031b4580500078801014818a803858400b59242c90301d8001c011b013009400740078441d4881404902c0f01c1c1d14030440c1001141021140080c5e00008106800c00c1c42c1e000c0001d0580422a64860000d0000c0ca0b41c2c82d009581e80300000404a601042007901030310183d690b240c440d00110241001c2d14110780004d034180042000341280210001628004583d0185030026031088240d0001c40a0b01842c1d03c060b50190021402206004065009000c03040c1165400c200059880007480b04010341122126809d52400c2440c144060003a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978095053 1250 978093803 978093811
    0x70b061c121817150903031b07060204170c13020a0806060f130303080910110702090705090a0803040e0a05010e040605060a0b0d0f0c02060c27310603021305 69
    0x40b0300c2c09801c0e2910282045055180540400ca0744008940480044807080035904101504007035455890070303a0f040250320010074140b108002e400129802841041c3d819100500410b0040035250305050f488181d584039a042c80c43c0c807600e029004e154142c0c00c82c1c070844407510b0b041d8030f982c10695075050800401d40c00c2082900c0c0104410002010400716011028000d035209854080e21401d110300d03558034000c107100b19a0801807511084820510081e020341d0300695044a038429a40e41e1070204503480c1c026004881c2d000004600040303001e03d8040064403d4500c0c12042c1d541a558501d0400c1c140c58085c450140400102c0d40440c0110b0171a81145a1081000d00940301895403180119010b80c000c6180c41c0c00c083e0703078180d07400c05854a80100c210b003007190701c01402a8144403080146510500400780c0c29200101c1260000e6050409102c82c0590002e01105040301e003c858418200e05a100e2031405801a07820345110390901d12407081981d40180030b2042e51034469410340300502001e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978096303 1250 978095053 978095087
    0x9070e030f073605040309140f0a120201031d0717010203072a0f0c17010e1009020f100f09120f0803060f0901031b05041109010c02060f070b061c12 65
    0x38078820300410107001d6035015500c02d1f520b054405207860303410700c100c10300c0322400342c40f0b03001400340c6000316610404c1000580c4c20405940c0030740800d610068005000f800011043e0725a0300007998150390010864408039641c102c500f504151142c01e406081344000c4234050007190746810300c01c003d001e00071104000b402e42d41049070700620054a4003038561001c0d0408840000d458813052002c40e00070748180303a5009050300280111090250300740c1e01d450b420004000101e9554240000355961a54406107520001d0310a2396156102c2d07200a02d0302000303645060220388000000101034454545901c030103070708a01842d406203815a82c540312580058560390b4061200a035410140c0c0c4c405441038001c40c82042030400c510114211458100310343d0740700501ca28035110302c0480b004008402c0b121f60500911701f03044c4a1b5102d10010340d06008050610020782c50100f032540c100300150340c4050140c14212030030412848135003040440311401031001080054420320140641c1e015151043c0110240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978097553 1250 978096303 978096389
    0x306031a0405100e0307030e0306060108150d08070501240e0123100903050d360e04050601031e03020a061104091e0c050c0601030b07030b09070e030f07 67
    0xf02d0201d0b404d85180702c0e00040950000580c900805400140d045c0041e40194080d04041c0350150020b41010320003040f0711811814400d00703803c0303a079403244d01e9204d041c0e004907400e4495a440c202107000303108198500000d204404245507041d5290a031910403a074281001c19120303800d04803c59107000c09d42c00182143c03490211a5242542ca078100300c84001e032641c2e035402483e89941081c9241000360744644050201c248864081c0d41505180310421400801011204100980a0360400142c0780e0104020080440600080080100d4003e0403a800780c20085101402100803001c02c541d42791300280982d10101801c000203d294100310344281c00001d91300d04040d41c03a034560f8240d52140c240100841d44101242e1407030311941c400c0c1f1820300e91509c1c045040c08a142d001542e1600103001c083c200030190400502850f1094002e04000390024103c00000d09041c04090218061400001d120780940f000f60302c2c0d401d000081da81c0444081905100c4015003860410f031031003000304502105540701d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978098803 1250 978097553 978097573
    0x30201060306060803031f060909021803010527030f2d0f0a02070f03050a031b1b0806090d0806010e0f0901030b100b0403050d081806090d0f0306031a0405 68
    0x34030a443c000d1080d00061603991a005401a04000300841075400700303640c1103002d024040e41300710305d5429a103d1510060b075902400e26181d10600350981119499824101000403415001c41c1d4441410325800e200d0394500c0550344440d40f0790144c40c0c0d200c800c25409001010700008044001c1c0d645480c03a050042900d040c451700c2d41c0300d41d4001081c0b12500f0400180d0340380140c1e41001820010552002400c0c003090540c0d03600c903103c0c1c241440160400503101c03d00c3e80c030103a4580500c0d0106520840200d650305900c00d000c05c8505140c071403613040e80590400115054008598a0300b20011695040240e684000040d41e5070f0824408950704a0a09010746d0f5031900e03900c59043c0694040e600c003c480d8609000d102a8a410310303000441c1600301803000b000002c1c4005008410a00c042c10400859034411038400803074940741207504042e2003403405220481402164000303590803241c4d16054080701440b020380070380c0d8040c03000a0080c006028207030092790618001e2074020b8407030f8040e0b8441c412 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978100053 1250 978098803 978098813
    0x902010c1e0f0b150a0506120903190905090a0209010c0b09012309061807150e0402070b01060822021e19150816081b0a0203040f0b04030b070302070302010603 70
    0x30b02070803c036800c40c140c0701806040131103200318401c00e203000c40741c06130940d08003070119100f40151500c036485584c400000c106441003c1c4141c1c0c20b0101400c0c04140310030482c0900070108503407445001d00072141440840c4041d2258021601940c1c0103840d11950300d0340e150b0340c032018440c0c011302d00c2015568400a5554000c404000c0700380030754001d01107019a00b41803003d941802d8014100e9241c1c0007140305c2c1611068008201e490071225420100001c0c010b403605e0a0784d10584003180b03154130510000d501010000c0c0c003c00c080c11703a100e81c0d5136000196070381c10f051110102d50059000301c2ca60f81514400051402c0b1600e81034620001508444c461220300216030390b44031005030b000a20050038024083c0c52030501680c1d00c0c1d02e5603484d011005d030500894014084e100d0b00c1d042c1c0c003080841000180420400c7d01500311001813240010340da0004280020b4490f00113000b941c03580400150700140400000c0141d07010380340c100e070b02900c0a4844403c00c1d4001e6102d80c2049003595250400007009c50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 978101303 1250 978100053 978100073
    0xa110304050402070c0f0b03041e1b060804050709110418140f040302010b04140604051305070602100b0d11012129091005011b080a02070f090902010c1e 67
    0x135105200c1000c2590a114614112184603042015444010b000b00300104038418004541000050004030011015080184880340e914030000040303803120f2030018085500c0080148224019000c1d144095200c00002c4240d03204890542450318040c00144802c6111800035004203012280c0001c1950070f281e80102640703012290208898560401c01c82455028002c0c981056000c403030805c102a045a202062a0400703820036000740d0342c07000014a401d540b250303090095900142220046030b501c19000f95209a03280603031090354180b18a00710a81803c9180d0704005600c0003035030010b07040c0d460044484400454580c035401c07559503110845504a40702d00c44610581281d290b482346d862440090201c04d00100460058000104104448102c42c0700281600c20910b000070030100fa00c00a58483d161000003c1d011010010345a00020780000724002112600e43da00b2401e179940b003800900310740e00c07400d0280c0443c8850306101c0c0003499580d50b0322000209103c020320b440341d00380c8609000b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 978102553 1250 978101303 978101317
    0x1608191803050702120a0c03060218041103010f120b0408130f060314070810170102130905041704060f080c07051b120c210a02030d0504030b16050a110304050402 71
    0x82140042d420f820b508010a607000c01c254650002c11003040d2681c0d40740c031342074000c1c480549129808206000c3c3c202242c0c41c0e040008200500c144200302d1a00f0a000a0b64420721801000e010030840005080c40300510070311040740c218106410b2580d507a21610006da0150324110030405031600e000c07032841c2111030b000c80907181c2c583c0d000420505191380d00c501d005014100ba018040d4107000c022000701c03040f10f0002610104540400095041d00160303019000b00f443d442c1600c110b807100441d21001d141e002c544101d025100094403200e0002010380984624005c070300c00205c4034030000401c1e501a01d1031a8002c2c0e00c1c688450324006d05a1141801d01042e100310419425030343c4000c0e9820728012091044440307180d805403400700e00880004404029400c42180262150442421545410f21100075603a4001d07003aa8085140250000c1540c0c0c010300003150424079407004500d00408420745041d5204568841a10b000306155040d94285540c1c209000c051108200128158941d400074101d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 978103803 1250 978102553 978102557
    0x2150c0607020111160f080906070b0405010605040506090a110403020a090c020f0c0102030a1412182b0c060f060603020d0e01091a100e040b040b1608191803 69
    0x420308000600038259220784884425010301400070700b915000790174505080c0d0b0303480b0b08019036901c80e07464220400d0281c3c907000e035840800841d030036041c40059407503a482240b00340001c12079143c4450800044032400c3c0c60f820f0304010803100060503060a0f90020500c4d01c017010300c0d207007031596030790004000c01c00c42c1c0c02955074181c99100c212500358041081502882e03030314020707140d001400c00000350381c1d0149001d18030400c500c0c1400407440c4c183e8101100c0594251648500342480c0401d0245130844048030014410b216264034482150100f1160b90700010201d00585e50021104008484c10321001d10262007080d034425800300c51120501c580070081c0500d0300e016072250501d410340c0741107401c2804010b24613414030180d103001415882110101c0755010001094585540091119001c1e46801c401c40c850002c030280010301102d030412905c998400c0700047c2203540c0381d0950120b2174506800c41004214104080b8844542e4180035450400120300c0010b042c549050884502161020381580 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 978105053 1250 978103803 978103813
    0xc050d030e01050f0402060f1303020d05010e060c031003030e01030f05270708070b032a04031104140106030f0b040911040c050c0606060a09080105102c0a0902150c 72
    0x90320030a008650f48441d04c412980c81c10310b00354011914921030701e2004418001d000410f442c032180c50504c07000165030058080c03144001e0514000b4001c007000313003070400c00f403081c400003e40c03000200c01103900c64581c0d08450901c442c0b071035900b5643d80340e203540c0203418147c0341c02d2040c0c040c8255206840c0f01d05001c80a030b2307800c1c2041410840c151408018065072940240100b031140f4400011203400720b840f84114581d0302d6540440302442014100d003500c0007151411540c05014442002078019240145420341c0305004e00020002100c169000c410344000505004120460107544038000f64543c0b000041440040c04000038211020078800310f44213100c801380800f980c24248102007a2041d24141a464000500503540e69582e0003841503110b00f07000600e00485511030010100240b012100910550130702c0d101d410340c001240d0089500080b41d2801c66511002a0300c942c400326080354144031001e8130f403035030300002038043c0f2401a81c009101c105e4005030131420b5401809800e055501511f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 978106303 1250 978105053 978105071
    0x5070e0613051c030c14210a031118010e01110a0c0e070302070b01031b0315020712140f030a02092d010309113304050a09110306060a0c050d03 63
    0xb20031840383c4640300400d0f2074003000d076800280c0c10200c840002a000710707003d038a880c0c000185c0e51418010350041c05000703940b48440701c10310b410500070f012540119241030107401ca94180301c5250b4011804030031404241c0e000014110b5000d21400c1410400614045140031040240a0310309202d0000c00c85041406400400040143c040416000750302d0317280951411317132a0b4451481840060101401c0181e00703a50049500d681800140011544801c01c1100c6003e0201c4100c001e4110b103a00303580d4140e42100c24922140720b005541280041c04d6a0b1a0910b44009800300050308000c2811949641c00c04c60b010466031203003062090b1401c0c503c00c541001c1665000d00c8a0300d840d00702524141070810f86506c4c009085c0110105140c1800c1c1c1d8010507070b402403a901c3c00c0c00c45400d411184556503d00480756240846030040003511026500f0b0004195078580c0034007103e011001c81d100501c0e09001007110b0340750040c010000d10700340345400241c50499032103441c206100108102c000c60380e40c030b60103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 978107553 1250 978106303 978106309
    0x70812090f0d0b280606260906070c021201051302120303040804060f12050415240b090a031a041205070b0a020d14010915050a140405070e061305 64
    0x8014500041d500c1c00c802c11000c0e070b10702c600e008001d0310300b031844c280020038207881d080031070045a005192204140000c664840000e00043c000c04040c82404002c04403c0c1d0b90949032148041c025440d081c02800566181d1904507072803004070360102da0107040180302e2038220a0074041e4a02a142c000040030441041384104100c22060300d0940907507800034010000031501600c140d03411951b15091070609038000c05401c440500799021000d41e0340c0d1070042480705010b21650000d0365001941c01c20000d00c0101c2c1096503090007894548500110b11042c140b211151b0000540815036024001c0403180d9100d56600080300e00d048680d8040341440010081480b07641c020550001d48942489880c050664440c0e5014000092101c81c00340d8000403c11043d070840d5000c1509a009400085220750712001254080c055803c966841c89070145000b24145c90005e0500044034070b4407040d84103d20000060002604009200005000c082440007849440d404000c0c20b00c1c0400e004c100b04130600700020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 978108803 1250 978107553 978107569
    0x30a081206010f020f0309040c05040801140f0c0408060103020f0d0c14030d08070503040209191d01050a050c0403060f0204090515102604050120030a05160c0303020c07081209 77
    0x2009085510017286070752415000f03c00ca801d01c0500350f401140c00160104103940c684034a074094862503103050191281120a00d201034001c00d1f00320491440c54898a4406c0d0650050b401341070301c0d0f500000f004200603d003003144c0c0c1c40c0501014002034440720f000d0f03d4507032080c0342c0d6034040540f00c9090a08407003249070501c04c0168200310303810310450600b400440140b60b03000040000340a0015407000c11800c00c3c894140610307034013103001e0901582008864004000c45104520740c035560030100410100780c0e96004461160245c2c1d002d4a00b09841c43d143ea00251044414a9040315420003000c601e0142501605102d000d0b0f54480780c10240c0e0001c180703d4911041503201040125a2503e2070b14092600080310081c254107120345041d0315a420064010080c0200040c03031800309002810400200e100654820b10740003004200c40d0f42d07040403010340101c105080e40c0c0021017801d030b90300009000b640a06003d807500c10449001c6601c0d40300d51454001800048059a0b4001c00d0764020340c600425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 978110053 1250 978108803 978108827
    0x1509041401151d010609120204140106030c030b090f0601140c060c0301030201111b0609062a07090603030503060607050c0d061a0102030c19051002070c050406060e03100b030a08120601 81
    0xd0f2001d4540c940040100109118003443c49400782c103650100555840360030000e6003507290800702c010303543e4a50003c1c0041030a42480f9010900f0300d440380c19186468142c8a100f1001140c000d007190752240c0045441d40c80460864035a100b05114031920900c0800c03c091143c800c41d074540f80d50354114000540080003084e01580c0c103a011a00d071010390f48101a04406900c0d09480d25521072007003000162190046011503e00d05410240d4601c0c0705400c0451000c1d810780d1202900c107100c4e02e07141124103949441c00003402040c400c101003030381d130b0411100801c000740c051403e0301c03140d01030400040e0200c04019426940380c1c2e141c50318069001003070b03240c0c64081c2c6000d0005500e0940e000c1e8289855000d0b00c22030702810001402e008041c0034080c84642c02e503071054a0215955182032400c2001e00a0a0003000d006c1e40c5000c0010030600d00418800d4100a0001e00a29401c02e690782101c0c0545120b01c001c540600689070b0b4600096034110242c0750311455022049010f00d0004001420005543c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 978111303 1250 978110053 978110099
    0x1e0507030806091612060b031302011b050c0609062109010c09180c02030c0f2a090a0504061b0c110109050d0605070504120308060f0603150904140115 66
    0x5028800e184e480ca05443c8210509102c182d030440d80b82220020801030b4040c0108410010401c45541032103640800158800d880300140c1506020b40c0000c09111a03400610507400304a07000103070b10706500070345602cbc1c10042845141500076002000303a4511000c0840d0b1074500d400c18002900e8081c0543c2c0c1410607140790481c203c41c44c18000804a44500d00010300340340d95403030403140261090003102e075072648600840e8006942c2c804496078820000a40c9900f81049140703044c203500c2e030b1412010f20650000c29444482c0c071a0503a0600900d8080d00842c1c002d6139940500c1c0042131b0001c403d103094011a00d4040300950b070707410076102e0703600a0944503041100000303040c44190740d42d51007099266000350002465540780181a1002c2c032071504440305110520803d84201688008203a209400680d42c14a540481a05001160200b9503041c2002101107030020f009040080c20706034003d010301103281c65110000d850781d0031100348080302c10a1a00c07814007484100070300c15a481031780c2404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 978112553 1250 978111303 978111319
    0x170d1a0f1e030307050109120f020106050904140f30070218090106030b010b04080d02010b1e0a0504090b090607021b041a150a02010c14030a09031e0507030806 70
    0x8240040c0740d041c294891207880150030708000e6540c0e1020000c1d03070019030b8428003c1003015550304003001d54002c3d200007040052140001c04590383d106009040440e280985000c1c10346d1101e5485503620400520029114412483e182440ca00c08101ca8001c89202c1c00310014104112503440198001000c503640303040300d007001501d0050b1243d941c05c40c82c0c54881405440151102500280136181c0c6900190001c11007000101d04143e04000620031250003038100c64183c01d47c4030042e4261200003a490354040e000b0f884c594107100c0403a1240c46d0304000140b42d607003c0c6488d0000102159081e0030180e40310f0130003008001d0964005c100700d9420000c03e000526440490100d42c0d00a02c15240d03443d4003a9898034071901c00080308040c1000c00030801822122296800c00220816400a041460040d13080441c485541d0303000d00c0c00008012039001c10036103180da80400c0c090203014280021020047c1d101c00300c0c84021080280701d02c540c100355544070340d10031903420000c0441c5001341c0f00768828055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 978113803 1250 978112553 978112579
    0x801140103090f02240a0f0306060309020a03080c010b06180108090718020f190f1b0b04110316080610090e0a02040c05091809060a110313170d1a 64
    0x381c3c4541070411941283c100b04801e22603049540390107542d1000501d00c2d080418502e584a030015030114805440e07070340402c07403c0c1c0d517080120141c1c0c018440c0a500000812070520120700720100600c10040c06400205940b048100817925541c002501000175210410940180b90792006d14541c01609060040c03910ba03060010480079810703032031800620243d00040217080c04e5500030951309681941528041440306c2203101070a001c14074003105001488403610608602e0021068000a03a00000e51401c680e486a0b1860f52000003510155414846c1140c081ca00c2c1449a0254001d086540080d0001c1e081c507400441400303455800100d200c9081110200c2501e00000b440407240390100e50110f0044001c032410368003845065110b94000d180c00401c1c81d00085d10b500141c1c003440032603044581c2c555803001001c04695980440401101040011a070f100107448010070000d402010300e0004000844082d0300a580289142c06256849400710303070a1348401c420307002e0032540640b01c0d0249509 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 978115053 1250 978113803 978113813
    0x807032303030c13090204140a0b0f0703081806010305030409050c090f04150504051e010801020f043c05030607110d03020d06092a0201020a021c030e0d080114010309 73
    0x4020f010010300c1030003003904900607828810a6006140d0b250b0110365a030f840e01030b031200c1d035400051414010400b4240c0020f054031500115602c100d0b00035600ca00788207095404540c40c00707000d442c000c03995154104407441440144180c83c004d601c298011907459140440600a4860041c41d8001c85035091010a4154440d404250f02100049800040107031806240d038074504221341003250001e0ac3d00040002c03072628a034441d440e0031006800a5501c0ea62600031500740e200b00c034510b04811005100c10002021b0811034101d0001900e0010704612603003202d50003a40c40b4403043d500503441c139910300b00801d05007805800c1d004072481c5840706141400d00c440c10350314020301040303004140e400684181002440e51013000503100030174050120310800000312000d0030502c03017152084000009031501242c014030031204105080d401808000340d8984c912107840c07016140c103034203041d121590512145410b02800c21803501c9d0f03468000c000e5041c8142c0c40a144000c0840d01c1c18189403805210101e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 978116303 1250 978115053 978115057
    0x303090f010537051006030b240f04031a100e0f0f0601090902130807060504030b0109021b1c140a0219050a020d0503071a250302130807032303 63
    0x116010200740303003000051400360544583e180c101c50359034a080107204002004c80131034822a4503030740d004d003e045030060030044a01c0ca00d81004101c51001181d80c00592803541c0030705182002d42c04c110342080d9807500d0b20054050048007080c61011881c00b04100c4420a40000e005054008100001c502d000413114a1510b4003400c0d81480345026400549207a2090074800043c0c90581015500c808092465002c1c03041d141c003030782c0c003103014412020078500c0c0700c0c1d82968110390f00308081802991801d50110000d41c080c080d40000ca20680003598074421041055030a024004040b8429450044038010041142070102d554486420070034041e400d0b50004450380314000004030408841828504a4a04240b18034000c1d08281d071405040248007003c00540740042c00780307081c0c5600d00c7c0b103412180d50700c00c0112030f414018035400380402e1141c8019990410540c9450038018a030000e25215204400e0003a4040c40c5140d1004006004114404404400c002428501030000714000c43c20b035510780c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 978117553 1250 978116303 978116341
    0xc060e06030f151809060105030a03050a030e0a0b01030b070e100509010e0f090c04090b0a060915140301090606030b060a0f0c05030706020a0c0302010c140306300303090f0105 77
    0x18441c1c0c000483ea04601e006800d503e6548000d151680c2c2007001c2c1400e2440d441c04640b90355050040d5400010075040102e130543d4090382c1070340c0303091820078074010503001402c58480d00a07052080909031b40002e0042d0903080e02030360141d0b1030500c4510f00b540f401070440c00030718205d0703000b1112410030140545e0000b05540d0300e103409090410002e490718011402c05041c500040394403018100c01c0c0420ad150000007082541c001d04001d0000c008440f06101c1801114030a0758005690110704002954501c0001900d0a01c41c0c644a0380070011400b42a55640007a0040d00d080c5d5601c1a04005a0f501032007810100403060341c1c40e40c02c185d044500941104e0910845009104503607408004120041c070440f4903c0390b100303000715102c80b00e450b001400c0c10341d41e0104a000d50f00c3d10b00108007035801840c01003d5035105c2a1424910383d10311052003111503201800c00d83e400c0303031580200b90800e04551591040b070010001140c50380391050046241504101144080c1c0e450701040c492a0100c0040f8040d00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 978118803 1250 978117553 978117571
    0x180615030d031a0d03030b09271c031805071403100902090a050c0c1614010203120601120207060501080a1b03150506120f0d030c020f03030402040f02160606030c060e0603 75
    0x60400c85d00701500600303c0003000542c001050400c2004161800e10444014075a078005841c1003954145160342c0ca071004000300303010480b8501c8801403284640c109181d812800102040741e007866507103051038070305503400a10350310398042c2141140c2d06080041c50981c04000c90f00344414046900802c410303940151042400310703282c00014912121080071107500c21109411280d050107100b40c030803001380c40783c080d9982c81c0302c0c100d01d400195031000090b9000c2011100f000c3d5020781300c0b4001561049034151011046a800380f01c040086401803244500800c900f1010b17201003c281d262100c034000e1104001c00c49414805014404500c20701d1080601354510300c00001ea41d107840700050700320481c180500c50b15105400c81060b084001060805054026480074001d05854417002c1c1e80754034011032000601d40c0103100080140c9050303044846961218a4018602038012401007485101c401055844588542040041241c2040c010008040c1403400042c26804000022120711002c0c014404c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 978120053 1250 978118803 978118819
    0x60118050409030512090706021506010e091b0d020306040509011e020f0409180210020d02151f06020a21200f0106080d170601080708180615030d031a 66
    0x801c050013107007140d040c00000d01e03000d240c503d84a1620756881c140c0d0300840e00107000e6110070803043c0701c1e00c1141a010314816100c01070709000400500403246001040306144120502110f0a40580c402c028a904019488003503a00c0c039105007031100350307800901101c4071607240290f603180c0301c001d1100480c0c039804140d0303000d81e80d13854504620247d0b01554100120480c58101005c80780e161100030018494801e4901040b003024058041c0e8580742008121400740e0000d030034807807040300000140766209003400d42c103980c034403041800180e20656581014004d0b9104140035818040344041c0010049074151a07000001800c1000506c0d0810b50503840c6e800c0480140e002502081c14006c45034102c003104020440203175181d030160741d1049544802404151103800b0070034031100f00308010307210b44810707194a09181c484d2041220a10001000c03135114040c0081002c070b03040c41c10f0007441e001c1c90130700c42000d610500c0501010b00b45080d100381c0c4420f0602c0c1000c02048071420301c2150b04243e000300c407960 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 978121303 1250 978120053 978120071
    0x9021c0218100306020a03020406180f0b0a021606020c03100e07060323070801090f06080c010804031806050d06080609073807061b050702040c0c08210601180504 71
    0x1c840000103403c000c0080b400416111042d50703141d8090003c58100741d6812010084d10495401030300c03101d0203200180e803074184050103071507611001401010980c1c8119043d40700d64507212030141140e90000f0005030400c1d04071901c94030f020098050710002196003008200e0b07803041103039502c1400d0b208240a0640b04ca02600e4070104500c01d80385403488080040e9400e1411403801068138609006803080a4585010100d07503103418880d0900361b4030303030b40700800b03211005100540708214002c00480c104807090000001c4000030001c03c4004080c540c68850300c5402800c41c0e0401d0300d9058001075403c1e44804100000e545c00050100101c07556840209001c46217444403921002400420740d8200d5030007131011104820f4000189032081c0200c90402c04441290401c000c40030040c0006800a1001e006107000b6103056840030180ca0041d04000c440803845130703a142050740111800e50710418520000e40a4940c6103003000c1c0d440034007464011280c01c0200d40e200010301c81c41c014503016940d601501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 978122553 1250 978121303 978121321
    0xc0d05241e0d060b010305010803161b050604060f0e06030708181608210a0f030e0a0209161707050406230c0a05071a07020904050703120309021c0218 66
    0x107403507906000390282008032001d040c034074090b000b03c541050003c0d150800020724854080284d07400400c0b80d001114460156403503080300700d106104011440714285030300044a6603080b001b44028401519200244e451000020b0510b11806564034002c840c108204041c03c0d5006040e15808814003045e00d80072a600342000d454103519001d124a981d8103000085102400000c0042c0094402004a0004500c5001c43c59160082800f41d40c042101ca00c1c07642803940c001d03080402e01c1103828049682161064001440740007090340c0003041481c0020710002e06a502400701c1e0610440c400145020382801c07080100280b08501ca0034042111145001c850135078150009a03c05d60b41d100c040751030b031219480064403240c6000045035603100b22000001c074480301c1d00c1d1040494561911060410780960244a9a9440107008071a240100c50010000651110b04034004030740310b0ba40090608101d00c148002c000001014105450020b0a500016542d808034095070014000c0c601c15035403940104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 978123803 1250 978122553 978122599
    0x10090b040f140304080c030708030a02060606030903190302030a0e060103030f0e1305040b07230706020901120c08010f06020f0a0609020d1e1e0f030f0c0602030c0d0524 74
    0x9a82c080d800000f40010b80c9450005115003200d03811002d40704035907038401d880c03952031040030291409604190005041e40c030303013040510380c40401c841c240e0303182c182c08000a0007104401d100c113401182d0301105003c00701001d8805c5200714500d24009002c2da5048d6100a400c8107800001c1c0c1080003660b9810340ca26448480f001c01e01e14051001c02c1c481403e01e89404a510300c002c84a103000120b030b2488903580c20161002c480305800040000500e001d41940314400a5070000110341d041c082150588140c28610340708680000c003440d83ea502c11541480c0202200d0741c0194070200441d0f018485c611841e00300401c1c81d4a11550000d000102c84105101260891180f101c001c0c081d00030010400314120321041e401100703503100d4028140729091100702c0c03500340c8141c084003414414030010f4540010b40594000c84041c1103504091410351030554074001681d100704c0d80b8200e00c540101d052408092180102c035002155524100c3c1c9550040c0b025405002d4807516181c421400070711014181504451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 978125053 1250 978123803 978123833
    0x71103042d062d0509190e0c130e1b03100312050f040e10030803090a06141909031101020f130506030112241b1403060a0311030115030f0510090b040f 66
    0x80040070410703598051b13400c903038058400d80000108817400038090f4144502191101c080006100451904101500d000904020002c9040d1991243c10384030b101481c0002d1803094180c035200b80d00090451070b1600c05100c803031440909200c4d040c081c2c1003d4440150550382500d95520035151943e5414110000c402e50366400902a204004280000700c080825000d04481c09844d090010044211070801d0440044682686070640154050b810641135000300c4c504a000785060b40c204005060385901f2a4022480c2c1d100c0348400250000c180c911186540e001041c0c00c848c0380c0d0440d85400510138480102420042248020344042410640910080340d2250000d90007002070015034101060891a8054440c02181d9080c0103107171706010300f40449119040160450808034510f0383e41c0c041c4c10480c0349840741d00d035407215000c001400d0281c000350f004501541c21011200c0d507900741a0308043d00310143c1402c86d401c01c442200480e8440c1e441540103548074004014204050800f0b000c0078007464 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 978126303 1250 978125053 978125059
    0x411040b0304051e060112080c21092b02150f0d0b180c0d09060b03030a050319020403110609040f1406010f020f06071103042d062d0509 60
    0x220902003486000544954111400e0400120b260714401c803045e07580e20309100f10b010071600100020009000c07000a804e00b40d924401300c0d0303455608202d1076040d580544e00406101d0802140b800391528040c981c0c0f541e2a070142a80303400c3c200e900f10f81d40700355501a100c080c0c06210044c0300c4101e82d824103002c51301030050030310016868410000c4002c002d840300c13014051150f200303c0b0044507400314035402240140c40ca81406454401d0001c0120080e01c030140040d901d295035010040b006032000c0c03004004550042c0c1c0c9165480c5000c0d00070003e62404040c070309401e9441440300b480000d4404612650207242100e00c00e4646564100084c0680741001800c5260307030400d108aa002d03c410340000d801f444017603c0e14016681c5280e41260748410703402c440030f010b51280d008035285500881c40d0b054098000d10599207019100c101260404000078045003049001d040c010207411240c0d2660f0000c3d1501e46007912641c0c0150300340c03000e405c0141e000710125984928211040700c1c00b4008540075802c001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 978127553 1250 978126303 978126307
    0xf0302120a080f13051c0b090f030705010903080108070f06052506090506060103230a02070f081e0906070311240103050d0c0203070b0901170405011e02030c04050411040b 75
    0xa00c520401a821001c0c03c1040381c81010381c00b003007520306205131b40400070304111008000604d9455401c20840040e020141d103000340d01000a0282013403005003403803802030300042200c00440c40c00801e0b814050303015000305e07000200c0600010b00c070354120070103d80c13044c0741050b25095620b4111044040f034030392912403610070401e09010001c0c0c40d080300e44180c2c040c100703a9416507540700055040d501040c5250000c40f0300103038481e4521100c41c4989810080ca01801400c0142543c0c4644918000c1102a0f402d460040344c401d09070058150082e00f400c0d03c0d1035044e0705200115010440301d003c0e414004061103036002c400c003060401002505c8612028120b021076084013000c0003407190303c0c01e000a68943c05001d4402d00c001d80100e00c0101201d5006e0000c0040514042240c001600114041410446160f59820b4055540004140034a008100010759000c0c40100199030210606200030514014003c100b41e09000703034196802c9540640f4003060098054560010a206a030440c40c404a80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 978128803 1250 978127553 978127567
    0x307110312071415091c050c1905011b05040e060f0d030c020f1c11060325210b04050610020601060327080a0f05070503070f1b17010b0108010f0302120a08 68
    0x1401d802210342280005185100c407001c04c542c40c0c8203105902555500c4940302781d0020303011000741e50005005000001f810508400ca114100b07885200703120000d00003040c00d010181584036225000b80c0304542801c83c07402503201041c0040714607600030f0148000070206105646400301c2e10600ca401c02000b81c610100060b01188007050140c034280c422031134143c030080a82c00c0c08800c0b64080c0b4600d0303101210f966594400a07441004800f000f00c10000b41706130501c40740320100c40001d003042103084045020f4543c0810310045400c02040244a0200345150b41e05490b008150113040d00d9041c40c0108841686001d6000145200c502c0381c00f01c0104140054107000310480540005401c9a039103d00480000d401202d55000c4d4410150481c0c00400050000800b006e2100a00394800d0007071b89181201600c00415464942d44400502c0f240441085041c4c4801c0c45070410b0180242400b00031541401e00004100482d404000d005120740000441d081d00c0c20402002a940d2001c039807503130303506 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 978130053 1250 978128803 978128821
    0x1103030d050c19030b090f04030212030103030905040e0c0901380c0601061404330201050405070f0e0c070305162103060608060910080f0307110312071415 68
    0x4040b4943d6800e01d0412201c0c40401071103409070b0b200098004000741003a484003000e40c81421400f410850551080100346586880990040c500950080c0c403a00d09103440c0c9400e10042daa100c1e10310700b640f6000b80aa904095a404803580e0640301140e5040d07450300d40000c0c003800100c64145501c0c1c412100c05103410760741c0c080c007402400c9110181d001d0340c6090366161001e82c1c2c41142061846448075084c002030003150450724070035040c00030030313401e40e04052595404045020340c0e01d614980103035154010001801000c000080040c070780840d61004491400301d00700405c0001800c0c48041183c00140074092603c50400d640f0800c1030070300510300410047c070b0113240e015502c45248450102404040c0315682c0203204030f00403648991980f4850741d545408000005000a220480302d881948020400714002c1142d0010760a22000950b520440b03800d00c4200c0c0c801a110443c42507011180c072a602c18024000c0e5103a0070f82c00136411040f8450441640d040094002c1e4800785100d181c0200040c682c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 978131303 1250 978130053 978130057
    0x906030203010e0307020d030c0320030d11090109060815040e0a050f01091203150e18010506030a03020c13140408070201030f09121b080408010e07060216031103030d050c 75
    0x900c00c03002002040e2541e1840c03074807801082c0000c2e610200803440d190100340075841c201c02c642c0c400d03c1d0070020101c10b83d54880c84100318040c0180c142c1e00200d03151050b000c26100d40301101e500b542d501030805000d100000c00c2003c50307008150400407102c001c18100418851412049003005005010104014005c20703941c025040c0151194030855410040610042c03054600c60f94015111344480c1070490b000360301034904952401c52443301c040c400200007a0b5101005d000c1c10311094a82c2490304070044540c20741d10040c0002e0b109400c00403002c400280c000540c4003012001791003034501c4039800100c240003030808000c4110410888800c1008200f2004000c008052003602c041000844000d210411603800300b000522040000b90b1407a899070142020a02107414420320840c0c24419503940b05994016070301010450b03444058038842c21a0500c81c07100a840c480c8014581074242481030300c900080d80c0302c0070f400d0354034101000140d5142442200c100b1034038800180900e0600d480340d50390716 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 978132553 1250 978131303 978131309
    0xf06090a020f122d100b09060909090715050f04153c0c02090604410903030f0a11041211132d060f060c03030f0e0d0c17040906 56
    0x403408022543c240802040c03d0194034200c103500b04803420076420f00c001c0c7d4000004941e00100078048801a9914032842a1180404001034000b03070f07150921151540003002111010300805000000706410100f0644084130403515982002a0540400740caa500041c402d41c4640f8900701c0c520401c0300850032003402040c8840c200e245e45403000440884036060300b941e00039881600f20003c60010326007900a0f0303020186092004400ca4020050354041c6049260507521088070b0600020001810b400c01503032201c40c640180d4510302d41011200202c420040c40115880e80d61081c403c0b034610a5800d03074028050140d84680010000d08150210501c2c00741d000d84502c882c41d112000d000300c03a01401407003920174042100b600c6a00511214802c2c0b11581420105903905070000752542d0744000d8100600d0251030b0060721a9481c14004c7c1900c0c2e1154541d00b5841c1032148050090500141d50300340c4c80d0030382c80c0500e01c041d458540109482072442444010f4a400300307020418020540c072072021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 978133803 1250 978132553 978132601
    0x1030c0609090e03070308041b0f0317120a0507050702090f060a0f150e0f06072109060c02061b07180b030a020f011d0901030308060301050f06090a020f12 68
    0x7007035a00c8030410b054401100d03103003c507600140440c0f00081d0140c071005e80c119110751050f0b20002c43c0e5000790a0195103640c050b80c0c80c812036071410824050306240c54203603c9100342c6540d142a1001150780c82c40d420191462041daa641c100159040b8807030001c2d16140d56004224001604040210440c144d005444c0f040c403800c1681ea000a184481e0b200f40b03c111500b0030b02c2031907500400744c0f09032440440140c0b0341c1d8021541400030111b030350f00d00b0700402015114200320a40c0503d500307545682c2200d903010600900c208900c050240680148920100a034104d070110b6079288004800040d0500e213016021452060000c0442ca2043c0c000c03640b0700c0d4101c034510030021451440c04066940742c05c6100a90450400f8074800d549500c20240e03510b44010800d18040d80161140c003152440000b40e005800180400041c070100740303002e008d516000200292030b01c1d040e003010000101075035005008041d8490380020f81003500b03690001915900614041030300b5040c9040d02500024088088017000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 978135053 1250 978133803 978133817
    0x6051003020306181b25030504030b101404020705010e10050106121b141b030307081303140a0e180708100f091503230c03030f18150301030c06 63
    0xc8a03409076800d4400c4501c01c1ea000740300c1400d00c0707280c0e03400d6009190002038240711b0b1825000c200303058481503103100d2107540c459589a00c1c0d401c010b4003024028114259440810104000054a64400390302101d001c46005030303989800d150030b034010800b20444c4031050041c41c5141102d04d0503540b00a040720079644501d03010b4104c18a80c04200c40545510340742d04802012210f502a01c503484984140300050440d03440c22a280a1001304844801d034034241a43c8000100711b070035036000c80e400384c0200070ba224010501219035030181004410b44402d500c0d40001007401c6044d00c1c40b0751003400d80590301a240c0d49501c0d03006044074600d07000c00c4440d40081078900d000301d0000b80800403504115241c1c0a074010f942402e2068100207031594040c030f130706035100c820408000702c0c00310000620310690105018903103e000b51121070400a89070005446508103005c0241c204105404881c2c2109181e1849140c800c009400101c4070483d0a15104000030080f00100401440980d01020b0714007d4860304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978136303 1250 978135053 978135079
    0xf050411030a050907030b09060a1d0c040b041b020307120509010815041d0102090f060c0a02090a09050715080f011208130b0a170109270606051003020306 68
    0x1005440106155000d04402080001c41008859202a0700001624107942d021396a0f52038840300114192070707060041d00b1050a01880c0a4035100b41d200001501c174410910300c9060f02520b460714007441d0003d000c2c50f100c03040400140d41e00d07400000403241000c125040300c0003003c4001d603030790044801110b40b40344211810140c030307004ea0180c1c3d4445005948510303081d40d45800c0b41d400d0b9aa00301c040d03a0003540f591800c0700c401c55200c1c1c0e0103d01c06486000140c03104070344020032201507000341149024810402103400303000c2001c100354448070740543c0c40c510b407a03ca1000010003030051003030151841c0a07003000030030b0800201d0400741c0011141d55569159480b161115000c910080c81035403030303000e075100280001030001e1000d4500c0300351350351030824000c0c1c0ea602021499030180030b0b007600186034a46404109084884600d014084140d02004612038543c0000035511181123005041910180201c3c108103481e00103070041c00700580b41c2ca0014449010184c080e41083e542140305420001c451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 978137553 1250 978136303 978136309
    0x1a1e0a09030203101505060a0c052a0a0e060d020a0f2d080a12030f05040b09070f050d020f1201090f1a070c020f0a0314030309070b030106021c17100f05 67
    0x100e800900e400d0031017442585400f00304038031944100028401c1c40869414440400e00030302c4000c0c0380b012045400c54101649081203030403405600810f40c4240303841401402401d0038000d60b580c0c01801035501414100040c000110801c01c81d40c820220401d1100c808130365589a164504440300b102100b543c42c15591014030300e40b035100c9002d070013022743c042e145d03801c04501460141c800c0b1861500b40010420080607040c01980c904481c10394031805141e0500103142002c00c07501009100200a0400c9036040c00005404080744440c06441494115100f031055030310318585c01064140361008000c1451186005181c440220304265070b1313132103000b428081c90300140150f50b06c0b40e0302990307912280b04000e034204038086031384204450300001e0290001c000501d80b03184149005007024001d50710703807910500307040ca44101600910300140040c0300400c2655000141c14115910500e01050440e01c0010212860106400c282100150510a0000040c4048850421360b452900d42002d02c584400038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 978138803 1250 978137553 978137561
    0xf0c2901120803060d080c1c08060301200c0f06240a03120c151d0601050d0c06030f0b130b0901080613060e0a02030d120509071a1e0a0903020310 64
    0x2908050040000424900c0d01702c0300000424401c0340400e040010320440c1c44c7c50000322412500541108036002d101d2940c008090a0303115604030020301800700c03001290050080d5440710714400c80404984544000400d00161659401c600d04440141ca400000b01444841030701100010046101c800e46040c05d010808805594011071018520040030700116811041d0b00c9003524198010150b03a55603081d503008003c0d11410f1401c004000888212000341001d0060b88080c0c841c1c407289440e54002869004440100c030b03203900740029450a2400300b0b001038440c0440c0c03030350700444121840a044130513a20081c2c1000c801d41d9001c42980e01c0341d0300d03955502c00684610b800a04001c848000292482d00600e03170360600e1030b0544410728003660200c1d107040d20314105003011650300480d242c0c60080921506038009211070040504500e00721040d0240a09848002c80264000950800d12017140d5040100604000c07603c655400d02c100c0010121011400304900c24014204400b2907032142d801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 978140053 1250 978138803 978138839
    0x1401080c0a1b08130e0a020a1e030b15041521020a02010209030601062c0105030a1a10020d030e030c1903020709021602040e030c0601060f0c2901 64
    0x251191900c6807403003003620441c00c14a00034525060b0302d005580010091806480d048038801150461035040103449006144001d02009802d4414083c2c15543c652011070112524a0a00c410b0000b80301c500c4220040c150420300c86400c211505035452046920304010030450f03081450204888403120300407115403184c102d400c44917a411418030380c10306030680c0c02803403030050500006103048896000309041940c240d000601044140c240400903040d0184045c004100e42008195800101800a805404080e00341e0184542c1da541084461071990545030545038001d01c10b450811080780001c1d500c60001e000d4500103420010010018030000050303542e41000140907000c0340801d1401c1c3c41c4002c41b00c5c041541184181c05000480c058a4802004e14224449030421102c1c0240180401e54600009640d07403070740200b0188c0d01880c0c0102d41d03181940c405240840c0481c1a82c0412685605100d001400700d00b03034000740c6042c00f82000403810704000c101c011000c490b030340c50321001c00f41c0c00302d030f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 978141303 1250 978140053 978140071
    0x60f18040b06190e16020f03030403052a010e070618030b0a06050d0302010b03011104061d1201020c03130e04080a0806031002040611121c23070801140108 68
    0x2011900041c2910080c1d68007410150078040ca100b010812800303508030a034005140c0480c52000d0007901c1540c901c60f061103001500050901d00c180e00c00b2250b0b60310000f0005402c000000c070f1441400c100c510800b590444d56440052080c21101c0c021038000c00318820b42da1800c1c800c1d844002119401458510380d8031728994a888a4a4075603102c159544800420581d40103035202800b08207a500c3c51264a1440e0107903000103410301101f4141030845a2403840181c00023800e000030440d083e8402e044840620106040c9a054400c190201c1e0300804000c0c4100410f500201d040307114054000702030020142880010401c442d034a44990901c0390f41510041c0080e00c0402104003214060900d680c6c1200000e01100c507110a080502c0c01281c000750801e00000c0c1001c208002044400c108607000003049111441c5410701001842d14009904205000c0041d141e225041d02d00c0b8038062540f0b4092560101490949403405009140e0b010900502156840c01d04402c01c0651043e10350910a000e42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 978142553 1250 978141303 978141349
    0x9010e0a0b0d0e0c0a12050f010b060a050c0c0402031302090f091e1609060602160f0611010b060706020909091204032d03080114120d031503050d020303060f 69
    0x212030742d0700940000094603540d4480c21825601c19210b00310090010310050300755241030300355843c04605200182c0301c1c0d1b03d00d03a030402025100565441044600398a01030a0440e0b45025a000341800c3c42c8440e02460f5109102008201c1c000d1840946002018802c40e012005692045d069080a00c02a100e80c00c05070b1240000766110b0421031384000501d100003084500d100e004000c1c945842807217801a0384026140e43e01001265010010b10179a1402440c010900b9414a500c02458464a210700401c100440c03e561304418002c2d0321140c1e40c201c0c00b5150035580c4642d428840c000e0342c4440619406a4840e00000c1c0881901040d4030410a5800d400c1902e05442d50311144400301007130f1100c3c114503c032110903c7d68402c55448400000b84030f925100300c60361414030000700071400e039503005004510601580024200c00305484212144a0030005505417144007140421201031700003e0041c480d07281083d00c001d4000019520541048440040c0b4442c10800c0c0142c2c9203031243d0071030000d411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 978143803 1250 978142553 978142567
    0xb07080a0b090417160629010f0210020d27140a0f200d0b071b020102340801020d1d0d0f120f09050733051e09010e0a0b 53
    0x14400100005c031055541078845440b1a1034040481d108109551441e07021154160041c01074900c1e00d280c0300d2007d091604040e20040300180d203d425a2484610150b400a4803120341145540400e140d030710000c004203461080056141824000604160781c0103400c90f03c8c2480700c88001802e00842035214a0034164541550382d02c21014800c08480c0383c0846458180c0c042545503908080c0d400d501a50400580b420030490182001205602000100c0350514101d40545d07000a42e001d054aa40d1414a0004c00d80c6c0211503109000b21010246018002d480005c0090054011301070001e00014104021086c0243c40806480200c1d0703694050380048501407400c074000e0800016425043c01c3c01c0140700c12034a901d5003120014910342d00201d070355120007010304c00204820005800d1f116040174010f4501075030941c0d240040540701c00d845140030640742e003040c8034405441701d07032044104802031200c010244681c580c1184000c50b002610f22814140d81c3e1415441150454840e031001c503141c690 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 978145053 1250 978143803 978143843
    0x1031e060f18150311030c130b18130b091203040b0f070207050f04020919120b0f04031b050c0301050c04090c1d011808030d0522170d090b07080a0b0904 67
    0x217160507159060003032100180c5181c8a41d94410b0710307614540e10007d1104e007058204100c45900010f82280c6101200410035001c3c0402003070a9220381181202c0c505070b403030521441c5802000d946d51118000080309020421013180b5003030b406041103034805890766441c1402243e5500c401e205003640304031005030708600e81c10300d640200340c0b101010b0410000080310300c20380b00001c03070594450181c64a40031001014409103400581e00445482c180c1c0307160341003a803002004a090765031411544052a06e451302041000c004014034034501400074080340c81d081c009126a030700144a245249030400041e1804648503842922000c503414881002038088100110f6002c0c0c040e400c5a5041c00402501040840042000d0800031664400206d07107450401c4546900c4410018480110210160104000f5407510744184480c00303242c0b111521034207801c1b0510050980454081c181c0d0030100b00b0f010190358010960352203080e2004080c0805039081c400e11480740000c4501403e84170350740c42c0d81d800800e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 978146303 1250 978145053 978145073
    0x60c0b060d0614090309030d09050607140316031205060d0201021b0f04060f09112104031412041202030705070506030406090b01090c03060906030b0601031e060f181503 74
    0x502624001604001000c3c422891810075200b15649070300c045200c9400349800c0100c2070811b2074078a4802c560a103403101042140c002c0020051044075000c05152040b002002031b5211129500320001c40518503040c05070004042c016044496400c000020718942080031507251401e0b4184d0040c806540a004540c0f080303425680116071203c1c400b54030a503259a5070007104040c00c50403105c03440d071510300614003080754540e404840c4060380c180040c1141030715244084503000b40060420300d8940d100c0c501101e19040c1c0c1070203030380c288a011981040f9030300fa056640c2e208911925005034801003400341641d40780107580c001000c643c03044400707001c54144100a03503003042c0b00300d80100e000d102aa4890403517080980140c402c4507515602070100c65414000c1340010030320030070100304407415034440d0800010000c0649061603100e0085184224105c0304410700300c10078040810410341c8909407031f05000d003d44120007410b604098455008503261007002481e07070080b090502c166140d80e0300c0d52030513 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 978147553 1250 978146303 978146329
    0xc0204060f05060301090e1c1710121511040603020c060105010906022104050924120d03230103050f0709021c0216060f020d050a0b011b060e011814120301090b04021918060c0b06 78
    0x11a10f0b42c82d03000740c037030518000e00041d110548002d078840c0c0380008854913100b01603001c941080f1000c503080024603008590701340c64000d08506c00700085070840070f4400d68800c82d40441d410513140010807a44241020600420700107031000000301420700c00420054072040000c80415070050b00100100c14001c0e4032066a091401400304000851403c0c003810840b00bd034000c0d9216000070195203c4800700744001400391030140d401310308103156030a14031413445110011020860b40060809856a02a0000d0001a40c40141440f16130040300b0548081e4111880c8418500d0a01010428034010360103040349400040e0b64802880c20049042000ad2030000d10a46a00b83c4d42c1144400c854003c2c029200e50f241c0080b04c02e1103034020b03442c00700c44412041541110039003000e102c58a0029105c07040b2070446001840110342c05402c000001c000f4402c4804d860401e80d001c40900c2031a43e000440038641d4400a040c5140340303980c51078141e45010200d40b00411410341500000e08a2a1042940e004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 978148803 1250 978147553 978147593
    0x90c09211618020c07091a01021e0303040b0c0721020c09040206030708060d0b090601030c151421092d0307020112020403120c0204060f05060301090e1c171012 70
    0xc0546e11019001211060308403400b040303210012004d043e507010003002041290301024012580c1404946035101d0001400052981c000d43e000b00300300302603442c140c0d02e005030080b4601440b0709038181f0002c80c1e014540d541e1005030044192a0360b0718a000703020540f00360f4018040904c1c580c0c031450201c46155000b803200c0e51000c6030004c80b03004175210104c1036101e00c1055005001c1c81d411400c01102044003030b07022030741f014541903510f00c0c0c8179844203c00c56030010050899407100b2000045c0341f46002103035100c860314030a9008004c09100000313403001c0c040c101c45101ca03c84c001804044442c130481050208010380c410070848005502c01c81d11900c18a10b00000181056101c0c5e983c1d05084c8241256400000d001400c10002c0d80381900ca00801806400c0300314455924280c0801c8042c04140300380414669100042e0768241010311209848482e640901146604000d6001d0010b0ce80484c0300162140d9200c00500d003c0c9861040310182c13028400b0f6404407455076900ea600c40c11000f015130710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 978150053 1250 978148803 978148813
    0x607081c240602060105090c0901032007060b0f0301200a0507150b01020c040216080c0313060c110108060616020a0506030108011d1902090c09211618020c 68
    0x210448511158801180c01c80341c18980d0702c0c54002d0081c9000e41c1070708030500c10741801c424404400e148108803090801c080c00c0204100d2400298500d141202007920304a448000510310700300a215417060211900407140142142d04d1441410b00b04c40342908500110100c01e035105038080059000f030091100039241c958a0200503a0798074a1502d0700345c0c605c080e00c54650000b44e03c99a010301008103510700a5400314105004582807858004d00c40c5070107012134000090164214800340304590080038041c5181542d25541c0328014540c0c40540b0007910070702d99100c008406907108807c0240a90002401207083c180200c020802c2c00e00780080c02c9901c47c1d15101d00080946402001e14005c108040000540464803080545030b80e0983c000c540654019107010400348003114106644190180d0341c40000b6543c680d002c500390701c103000043d6800740701d4041c2403074110030b0108910764624010302a10440018a11030070034030640d5004070503080c1480341d807a6141601c1540039100003030b29202220 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 978151303 1250 978150053 978150071
    0x2030301261501093b120712090905040b0105040c0c240609060f090c051210061427030718050a0b0108010b0f091f03060f050607081c 59
    0x1450041e00c0309100c0c2c8841c0c145030040200310f9503032181d03030000c1c1200011749100c1080d200030441c1e250171849038180703002c40845513004910002c00c00c1c09111006084503e03038921881c20a02164030034001580c001669048010683c20340c1401600c1c0625032003c8202c1c1240d080108000150040300d141c9810004001c8010011800c1030a000007010305243c692400ca22140b001c103003d8800c1900442142c900300b000c104845940e0b128110103c0708400000a64000307000c0044a0398480c0d40c4070000c4420048050081c22101802c2c007030300315140c0e1784030307000250011b8004418a0141100c0c403820041d44440812903500c03aa0420683c04200030181c58149131120340c6c40c0b807984190b12038405001d50f0381d010003081c140c0078894031020507400d007042040307503250461410301403041400d521501000443c0c00d450755250100e0701219640150349482451041400041c024034451156880e16140308000081c241410404c581c1416000540c0d240740031fa02c90001c641c858450b450502c0c985075200451 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 978152553 1250 978151303 978151379
    0x1506010e04021c11040f03020f040b1302030105190e0f09071e090b040b1e060d020a02060901150f0308130f030309060809010b010c0204050702070801110c190302030301 74
    0x1814610845108140e020799428100c0c3d0031949035107002001e40d03000b00420b020010040302075004407541100c00c4941e10000c0e1022801400c100700700940c202e0100b620400d00002150042c2d4182d48042e03c80342e2290929040c0410182030038403482c4510381600c401300d0214a09000d2141d4000d1300c0404a45100d0b0780c0b1404010410f01401c00540d2124002d00c05200e0b010f07481c01307025070200d02118140140c960b0b0000251181d1483c100d40d1240944042c0b030000980c40d41c41c142c41c0c200251030f50031525072920800180d20341d0400c42c2c41640951a1520318000c3e80301c42d952440c00e440301c80070000d00316421a640d0754200e50190506003e154280c040c0000c00e52038019410001e90310a0340c4030703040ac2d468900060051040a001a400c036410721060f0340e86664410503596503190121004116525400026403d021594005a0040d420f2400c004c0180304064010003298a80d103048403696107000c840f5106480340c1000040050708204010006044000389500500c1c45c0c070002e08042450344000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 978153803 1250 978152553 978152557
    0x112020d030e09070f0806030a083007170f09060703090c050405090319020d021b0103021c0b12030708160317100312020303160807030f1a0f060c1506010e0402 70
    0x10784d40066a40c0252011071507205000d140c200b442940100f0618503250796409030f0340558503041803c99442100e203011034402610412000d503440580c84c0407030500500041c0701070b000034071240e034a074881000b0600007050441c40c240700741d141501408041e01c440307108078050b00a141065440d001c900c1d07c0441c20fa07450744151805245010001d55031003080313170940050780e80354079140000e6400020015941e030385c000c41ca030741100c0500d140311240501d00e0300060b0024001c3c4110012104000300e410b9920801c0c0d03500070b49900c10112005d1210b2121040f80569a10450200406180c0c0511036400007554101241d0240c9109080150454180089441c3c04500c1111004400701c4409410018024a42e40c00c051032103461010b1455490b045141883c40c100e1f0151141c10007040100150606229910070054000001c40034000c00c11816030118108a0f0400c4080c82980d00300f450f4101464048122a00b1849400c098420b241d0070180710f0099410081505040c03050340420510195250b00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 978155053 1250 978153803 978153811
    0x15030a020618060f0405041d0c01080403140c0d091202010c0b100e090105040219290c1912020c090c0f0d05040f0317370603050a0b0f0112020d030e09 66
    0x1c078952900e20302410402500c25043c3c0994035544100020f0408c1324010811821445003802c1044145c0c0303c5207802c840d5074005041c14240d620021403541800540490340302d442e80425940c44444075201c800200d17141c050150028082a00b038418800040d051800040c0c0c840e0a084c3c102d0304095a540d08040420030440b90302d05aa5910070400c8210300e800403604c064840c500c450a6821400c0c24045400f40100c1064049041c107199036820000807400c04442e0074019801c10b442c20418401d6240c02490781e180d0b0110b9406110780e0f841c50a070707807001400601c410001407100145454007c00000543d10041740004140b40400c20591448070714010180254840c03000040078400713500780100085500c950341c1c03480c10042401d0080b170b03a03001081c0711004070964800c0120306021101400c03400081c01400a01c071807c01000005020010669000c1c081c0540f05280b0340c3e0b910208411030a01007402044841000b02a841001d07003426180502501c0c4a410101c0300c4850110000b0300c034aa04603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 978156303 1250 978155053 978155077
    0x12030408030a0e0304060e0f030a050d0906030f0b06040b0c100903080a0f0504030e04020c0703140f0d0206091f2003071b020d0b06030a080309010c0815030a02061806 73
    0x1c2401503128240c80382c0820311502101650810b4140103005141804084401c0e01c15658501d0010035aa020310411580380da002046520005442002030200d15803440f07400c01203842d115400780c007820207000d00b00d900d49000700a1407a2500741100b001c0142c012482c6484c16106010450804448a2103146007103070080d2203451541c9440d0080030161a0a40c0142d0019402d01e4180320010f904050b0109011804940150300e400c0e8160b01e40313241101550020700100e0110700c44540000011441d0350110103800309880b15000d02d000280d07620b04081e45c403503031650302c2000e494190700701b1241f030301501c400c40200204801055400700c0154090704143d0f582c11b14000000d02010300d0b08020802640c0021210400724801150001481c81148070b5026000c030034907400003a903ea40070311245040f2a40504280e8807401c16501c403900034003448001e080802c14001c0400c00340001e06440c034044520080052002d0507040d42440455040b80d41c41401d81007900c1c00c4080d8955071040a08032110140b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 978157553 1250 978156303 978156307
    0x405060c0f040e33090103141f0504050c0a120b07050f0d06050109050130091203200412201003090b13080d021804060e07080105031b09060312030408 66
    0x320004c103550720080c880c401103512404020140035201c0c10300150441e60400054400130f5041c90316941024152030240d004900c100d9080907032112581d001c24040c0e8001d001b01e4925500100c14020702c440103002d0345103520145d400c190002903086950580c40000751504d541840c44000070048a600000302c0c2080c00c50321481d00303002e5175a10a0b00c8000901f005d182942090408035181c50b101482e002c400b0540341c1d5294141d40343e00c0d040f41c01112060354000c034800300354605000018000c0c0b0346a03c2a8003040400c0d02d10030b47c030040920a44058942c0601c08241c0c0c540d035a611009400907001c844250080001c840101030703a1400c0860029000700d4030046406440c5181c9004814401007252015450098840340400c0301d19090722071074856040c00690b1101503582440d209008140482d610a0810102145216075a50464018011500c80e203a00b6601d8008040e19003808003180c0003079050250262415141c0800f01c039801503400746c252012186024645021a401142c05881c46e03240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 978158803 1250 978157553 978157591
    0x2030a06170a1407052d092809030f050703020715020f190c05010513030213090510092006090411040609080a0b13080c06010f050f090405060c0f040e 66
    0xe10441c3c80001c00702c080c0000508000010351982000b920300303100442000721b41200800c0f05840c07410380c200000d0804a051500090309002501ca202124680c280700507152100030003903005581016626071212100121159403c440b960032003182035017103200305040081d5409420142850015107580948442081c07404050f19001070162183e1510043c0e00c284404103008080107800d890303091804940e504954495003804c0505a040030758040107003a950645241640d1115041c40d00c108103441c80884450040341c1150b414690150190141170700480c11500114002071911100030016424201d4601c08202100d015206030310500400140500180c0d8101c10140014050b00004080c03041560b0b60700380341e4030400b419500184007c20b1107002040841390a840c070454124084074010b61f900e0010142c1c500c0c1c9881902d019071041138900b142070508554080c85140c100e802404252103280b060a900d03406070300c1c0b1600c8180184400304024280c0400c9034010035004c0002504140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 978160053 1250 978158803 978158813
    0xa090501030209132a0804170703180803091e0a0311060c0a060204141c0602090607050312070315030c1a190e0906041a0d02190f030b0105030109031202030a06170a 72
    0xc802d20385c20b05100d80b20f02000001203c00017100d101d40c1c03100342190780f40e020a04d402e444d0782000c1e034002d040101c038462022408901c00009030134020422038101e11058001141030426030405080035811954031082800032640c88850034001074000b83c01e003494480c88124181c20040783d04022540142c000600700300d00082c045000901800c1150600114042000304a0852180c080020401500403600c164142d40d50ba05840d0310130740004c10717207540343d1420340321105131102190480046450841e1903041d00001c02c0c0c2c03002c152584508003208242c18130840e0052903910f4880c490101100b0058441d5000409507803110700c1c0c0058841c11603082c116000c01021540003480b580c0690301c0c0c0460200c0c151540c0d08181041a021385003204002014004580c4545a031000d04c02200703900c0c2800030300d409403106194110f2707020b1080000ca076600c83c000c1500b660b4188501800207000c400802407503100590085030882182c900005081d96103201010051205d140d240400703820a900c084103000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 978161303 1250 978160053 978160121
    0x41d06070207300b130605070302042102030102070204111305030a0210080709050613081006030804030305030a02070b1905101a0a090b03100503120a09050103020913 73
    0x1558005400da5500f055540c840070010714001c01003605400d204898021203076018a00c01e00c0c1c01030880d000d54901018000c1d0841460501110030601c1c06001078882c80c440e10988081c0c0b0740301e111440880749403403090070740a158520705980c1558200130200040e680c620407504031520f03c210290702c0c0e40341024402440310701e65002e81d020307030840030306d03c030040c1c0e6007501c0c164403101542401c2e0440c1e01c0301481155054132540155410100000b400c1c01c28407248002202140c0300d0300304035001540e40721445019142c16100080102605200c14000039018202444e440010b5080045c01c180702078542d000c07000d03401d84020401000c100e2803074190080034040c0b6030f031050f03c2c04030080c80c5520b01112420241707403d042c50185840f0104d000003801d8483c40c25031004007048641039403642031916400703000c200d2074031a031442449500b20039611040c01c0c5081daa2200e0b066140c012203141b0300702c01075020b035020b041c42a601c42c540031038441400500380302e4091041c5107071030814440c3d542500340c840c440b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 978162553 1250 978161303 978161311
    0xf1a091009060f2328050c1c151a0304081e12011401030b0306071d0a03060e0706080f06010e011b051506061602101106041b23041109041d06 62
    0x40c10b02e007242940e61a55206110210014517000150340d52595000121070103050000000300643d032a180c41e10300f0403904840f2484070000031602d9519541d05c0c80000c0c070159413900741c0d040e80c41880058042103400025014032961804040071040c62041401c08075401160381420107548900140300344900d4107006202c0f003a081c202040540e54080c0020b40c1c81500034421700410000300345c094141c00d08101240581c070400ba0150040f1078682ca0680e001d030140c000785a60520030050002010351003401c0d01c070300500a0403000c50058503050011185c291040e843e2506020201850050684c100407144003601e01403400380c040e2280c2e80400601d81000606164801c1c03d09001c101c1d100607049150517010303981103034168103c0140f440c007954034050ba07090b802140c1c002c080070001400102d114040c41980703484c1010b80c0c01902c48444051215a1940038400c1424448850909007440c0d0721100c042255081d12034140007a4100003402c1d111000c21301410003500804480168204024032600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 978163803 1250 978162553 978162571
    0x703020607020c060a0c02040903031107060e0609032109160303050d050c1306051e0301181b08060d02040f0c0504060e0312071b0801090f1a091009060f23 68
    0x780c0080c0c804004c061b01689030b4040d20417a591801c5208060180d400780c5004c003048803803c0d40350440b40c02d01000508002d02c9011040c02031100007a2840808000c0f911452040c40100c0c5800c441a8809070300e4240040104034207114240f0308407800400210480300841c401c4d0382e21540c0f103900d159940c3c181d0b00d000c4c100c042c646a0500601814640d051001001d0354040d2808641394807613403440035460500d891110b5101d0381e000001040006170a104801e456a03003020511501c19019486d0148600c0150300300d000840190101d1550b243c46080880c0250005102003002030041c60b180c0203c405c104d201da0013082002404115540c5c000e00c954a042c80200c01510b03410f509807904200c0c5e407181a000411910000200550791203d901c009405000ca450017005003000e640780841141c40c024a09032801f03040d03d0305c200d80482041e00c2041c440d1500e400640302203900d035600c1c00090070f05c05008841032074950064601b001005e114a01b02c6140181d8003042860540809031a16503000d0b0008071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 978165053 1250 978163803 978163807
    0xe010c0215010830071a160f0504180216050c0922080901020115270204030816050a05010203070201060f1512050703061e170f06010b161e0506010501110a1e080703020607020c06 78
    0x404e0642181c2a0ad0440792032010345000c0303240414103500240704107004168086e03141000041070010004010141c013030151074003041c940b140030320101003a030000d0410602810b05400ca000103403464010b422442d4042c00049519803591540e20304a616031b4011200440c4003084104210740f40f00380000e502076040204504d464119110340c1600e105440030100c1c8503602c2c4214400300312007085009800d42d0840000c64403414141c1e4001d002e8020b074070420382652441c120124262100d44001720f21821070b0b4803180780752514400f814019000c024200340030b260350b80350001540d41e100d10600cbe011514199005020720b0802c4505d5003080019400142c482d031180103205402100060150b040d1030507014904d8030b0306260b142c6003a035500076a1009041080504114601e0442ea070303240382d0051f1041003550126a22200111585990400c980710030b5404400c0d82c10114801540c0200c50801515030100d043d035041c1c4903120103502c645421401a03021100704205154180300d02002d0303500031a0614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 978166303 1250 978165053 978165077
    0x12080a0b0901030609051e010e0c04110a0305100f06050421050a03080a0f020a03150b030c0f0d0e070b0a022404030f030e010c0215010830071a16 64
    0xc0c25a41c0500005051079503a040800c14004200441e44240a1b071404030b000f50481186c20034040c001c1b002c02d44909110f60a62100580b070300b402440e15481108086030b04000c0712850407405840054807118413400480c6010502c001c581c003211014003441e84071283d6032441c24401507003da107c03c84034508406120a2100001c901045410050fa0945010341c0c15448010301d2100414030349111645240c8009101d14500e605600300c16964280800d41070700c80340c0d85007101c442c02e110866110078161020000c80c55521212030140c541d04903a031000181050064014900d08401a007210394080d0000c1548400168100300b03540d055034103c1d882400c002c03454a00805490300281c0f000303041c864821041c40c1d1860ac00d0707200e0340603210120001e20241d007802501075100e11340480c070148201400000401d80345000540405000c60303c40404040c1055050311b080c038640303840d5060b03040c04020001440401d40d8000380b18042e0011100d10f40340b07030824031104000c1e90340307141442e4184104901c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 978167553 1250 978166303 978166309
    0x20a020f1006241103070c170f0304090e030f040f050901080109080d0209030c04050403090609140f01230d060e0906070e100207080708031b0f03090402090a1212080a0b 74
    0x100c3c038080e4401c154a84150706150056034281c41ca0a10b0710407a1101050507018031a2510704401225640030030b03145241f0220b80740b1904c0b50108089000a623008000801c19051180d0090050b030305050152410210000101c01042d4041d5211111030b00c1021401c3c08289440e9001f24010070a540c000c01410b046981c600d905c40c09040c9070907544540c00b180c49a015201401040242d040040040005140030b190141030b144d100c3c0920b000243d18002c2c00320b40f640000c220316009440040c24041111a40030045480390403ca100703040201c0c0c5140c9082c102030307001004d041c40340d4072800c0200e1a18101207070420071010050a04450b68480c2c018440000e0300500110902c80e425200d12051480079007050389001c105900010030f51140780e070009140390012000d4441039040f11102c4001a58041e04c45980c0c03001e60f1550000c503001003003003040c80e141c140e00a0460080140c88545825516a00d01c9035400c0e0920303080da0380c0113400070b684000301d9001c110380d58400082b4100300515441c88001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 978168803 1250 978167553 978167579
    0x30803010924061413030b0412020d1115040302030f03010f140a030206070b0c04080304030605060a05010e0307060c060f05182802040b0a0b0c030406080c04032001030e01020a020f1006 81
    0x2c0c03c4050800205d0b8003403001030203826030281d034105d6100c00c5641020f18090000c0c00811380c0880041c0105800c0804440c4a9004c0c04078001c0444000c1030540c45419844c00c0c0300201900440940c4400c016054405201b80003440c000c0150030322021030b01d8030b440b10100c58140d030302c52000d100c0d4408181c00e0005039256070a07510301e00d802000d2100265110b003030b042c540344141e400c00d00c0e03103110100c3c00004100c040d40059126000655016400035510001541e05200700d0420710b6150304030000502401e88102c50100b8418041c0501140b050f8003880030904440b001c0d20b80000341100020000c0b04c5000401a070f0026001c0c01005407174040c5d160449240c009200140244660740b110f242c5822580d49981c004003500f43da01007141d0320f20044480d6035490b0304c03500c01d110201c1e07030800000d1040d1850f682030701c00f126002403407014422041107884185000c044500c134185a03840035035095030074091002d031040443c60740040c07051400f60700c00d03545051041d4070104006c5041c2941030180800c0340d08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 978170053 1250 978168803 978168827
    0xc091701090c21050105010b0d15080c15090d1101201e0703051501051e030303040201030207030c12030f0b0906060d1808190906110a0b090703080301092406 69
    0x5001540c1030310030300b4400041402104003402640c00d01c0c0011410315104802840c0404078203274100f00c840206043c805104810303219200d56908140000900d50602e81d204407407201485000f5460108180001598140003c2c020350300c0c1051400c0c2142d682d60049400880c40c03000c1c1c0e020001c812071003801c480d50748640e007a000442c05510342440c1440c040030026270020f1a4440c09a031400c1540c4080c400c0c086909201e554030a0221941032240084d1034852400960000342c041c40c6550384940056020354030201d07044042010718000080480d00b01104040d49a00e103035000301364404040074840984001d20762041c4180c6041040c400d26660b2682150751103250f221000c80c000006240d240f160701c0c49800040c1c0031000004040c010f2243ea0502550307000349584440030007580700c034422030340c14001e440d5030f035160340c0043d00c101c000c038a45102582d80701a81c032044881158a90703440b51a290001c0e4003800032140ca40c4403911240880740da41601c4020001c402d29600c07840c0490007805000d13161 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 978171303 1250 978170053 978170069
    0x50a0b0112051003080901050c0f240106020d1409060a020f0f24070e03100c02060c0403020105070609061d161e0621180605010506040b0a050c030d0c091701090c 71
    0x5210b1040d41d005da0142c1d41030420502c26032b00e00c025821140d42d00c907801c0c1221052580f600c20420103181c50f001000c14140c030040e034000d261001c4128400d6401994003c0000c04408040c007004005550364001070501e5078040d03004d0150355181d140c0c1d55160030b00400e816a4a60841c0144020400c405e0801b20300b4106008418480f0f9220384005854054002c2003040d094002c1e81441544040e1903044441160101e508940d010f80e52030000081c40e000e00d02000f0b000400c104000c40c0412156000009400d01070100015090024080d0404542090102c021706811070340e078180c48100c03090350305002003480c0003030f801c0703080c0750482214503a4100d80074140c18403000b03644540f080e0700800d100c8058040c0d24a0100079840c031041b50000f010000f008200c034414140000031500381000d2007034800b107503410102c290401c034a040303050700c01c0d8000501143c0705120520940e868000c030b03800740610402d040d0700c038074661505101d201c1081c86040d43d4030440a81c100140440002d080314112812a4280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 978172553 1250 978171303 978171307
    0x6091511211504110c0d02060f1317130317030105150309010924051003030e0103020d0f050c120f071e022407090f0e0601030903050c01050a0b011205100308 69
    0x1003a80c0140c2c1401048403070f4109103003c058405001c000302c024841c0008160898100003141d40b012a0368220071070b80d11742040030110200d26152402c0d01c5442c40c052050007050601c01e288829a800d5800c032800301900c000304844200103011740c000c9980c9a04828520b100c0c0303558100381c042600d00c000c0c03482a0041003070000004410700350070f41c410034103942d0008441481440000700341120240c11b0b00280b02c42454000450080b20031009503804032641500c4502d10400c01000640c029080301034601005070702c030b0428a0b51034641e8440c50348212510228140c0f29507906000f07850b00c0d50003d046055032041d0780d06000e0075640012020403000c00d142d401d01c10030061460104e05003011003002c2c100c40c46c031032031400078003400070290548039814075581c5040055803400c2e498801c01441c420b2000c000703089008102c25520981082040c58001c1c141381c0d00c2d0600c012a0700342103071000c0f81d2004005641e50301e15080f669001041104002c503025080c00a030410451094419040c4d1000038190080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 978173803 1250 978172553 978172561
    0x150801150e06060d060602060403030b18010302011d0d0c060e060f040b09150a020708010e0705210111040602071d22060e0d0806030d080709210609151121 68
    0x640003204d251403d005410301502e41d603118043d640304015541140840c1c103180d4550a03a08003c258203103003440c001250181a4039580041d190130f004048600220700404610400c240c98401c1080c07a15403190541d502603903d0180d00034075904c81c0c00d005c1e03485a03004003c80c400301007107001a14240c80d84070521907518403031440000c0c240d01071042d201040035004600c2c5003545401003602130403500701000a10500c1071312130030a902d4070014001c00c2c5d440242c201a21080c40e0412240710032800c1c2d40c0303000043c84060122101c0164010b580700c4001079024500500c103020000c000120300e02490085808513050200708048000000e20b21864484c40b854081c40078452250407029800200c41d0940f0600c1c03e07244001410500c1c200c1e442400b0b4480c6000c9407111a10644090344110200d41c2e911218500b8140420bc049050200f0003445030640700115000c2052445070f03089061185c0044035944103c600440c040c0c58462100348124501401080c0405503024800d20b20303440a80c4940f01c003561 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 978175053 1250 978173803 978173809
    0x122710030b180f0921070b180a23061312031d0706090b070c0e0c0d0f0506090a0b0f012d02010506120303040f140a0510150801150e06 59
    0x300c0702c000020901c640310620048030389000000d805101d50f001603a074640c040f02c9580344816000016040007090400501c1d010400321099181c10144d580d443d0807040d01d00c003070050700e4408942800d0764008001491940c50013014100e209042c08040050328962400c43c040403440c00c910300c400781c6103051150480818504c69400403600c209904004000704110100e010ba030703001c1c036001c4c1710b002c100150b601240c840b00356410b440d9110b80c03000800080b18101101ca461960000d040488403c0083c000da6225050034000d400c280580c00400090740d203410420401100009401040c14a00c0d28a9084140e1500c100d59a0700358400e09003a40d00030003803100c2c6100312290300c2e0816100d0032020700403000d141d03040d000540100f01c120b4100342e808544072482912072000f660010400460f5201d403000080c421a02c1c00d40e1201c0c50000d403180e0307001d26110107007400c80fa240309813240d690703501c174003140c88442890410203403503814000c202d4800802c80d80c4620543c1802041e22000c248000100c140d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 978176303 1250 978175053 978175069
    0x705070503220f1406032d0703020d060e0402031c0c061a01030c051c18020402120907090e101122030605280e030c122710030b 56
    0x500004250050604051010b64031800c0c5004040700102e100c8800950564584d48030280c903c1c000301002d00d141c441405620b40907a030381445107924080010781c001140c0150f15030a00c03c1000b514050ba03912008035800f4100c1d008c982090421007420070a100250303d00054495a095000220210301c0001c030401f40c444142d43d00c00100b0301802c050301010320003540700059410710400c4e00d062004890b119000d5649004081600100765002c0e00d40341e842c406181c004299510102000b101c000d9401e80108090368030044d0040d4404040c0c00a1040c400d10070800d4100502408404000c802c643e0902d1546a810070126031020703544803149507440100320f00c2150301d813140d050303004902da55003031426101c0da4010b0b2005480310b503c0d20000a80783c408103034134845408100c1409940503100c40e1645401041d2a91000034148400e0200302c403181002c101d000e803403903902085640c80391840f01310003042d18a6101090b000e84c0d00084001125155003000c1c84c8001c6181c04d000c101044c1240200e4200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 978177553 1250 978176303 978176317
    0x418030c020907201b030309060a0f0905040608010912140904150e0f0f09150f040609060510090e19020909100203071d040606050f090a050405013002090705070503 72
    0x50340d1040c007141d400f010000b55020841700079140104080760340300c00301503c0c0d0203010003854220340e0404c030000d100e502c40e89080b4140800c60410340d1841c0e480b05d01040482c2c6075500b1615007a0364500224080c840300b5601d081407100c1d28503103a8031201307040414080e40e00400d0f1159000c1c58585001000a0f0719607420b01b80502006a0301203001d00c0c0608400408001c19a0301042c00008440410301700760005c00c03060103c3d00459000903003038031401d01d011281c00707005100780c0306140c1d40e04042e40015114000e80f03010f13070b034814210a030b9542031090110131141002100301035a44800900c00402d4501740030f0f2400980c04660140d4542d444903c2c0390704229406a40700c942d140300004102900d0f400c031140b0000f903c52485404000603c040030b20041f1640760190402045007401450501c82055004002030751000e420082d140e40c2d2180401c090b50070a0700030140c801800d000b005099003060886514003d215000c034140c117011a004248060300c00b600c4c0030104400001d040007402402c004a03280c13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 978178803 1250 978177553 978177587
    0x190302070209090106030b0106051614010f0f0b03010606090e010501050f070501090302150a14160c020337111c0b180d0906021c0324050418030c020907 67
    0x781d0f1420010a60003004d50f808100c034070001c800004103071a446080ad0303440e40c46210301c46030424000c644070410384040725030340038031550740b56a50401841075500805100300c00d0300f400450130421a01c10142911880d40103001008010b910400c08815020500d07411284c007030034004c0d41d81c0c4241001100c6840b0300000a4119800c2001007020140d0000d22604041000601344943d51034410651007901d054454070380e07031070664038085515410140b801002c103000505217800501c103640e004c0b034140380303501c0049880407400d10421b040e004840e00c11f003d0000340403441c80c140d80005660390031218140c200d00901804101742da69a03204185160059035680108030141a071501c400c3c0c5490980d520205001c20780140301c1241c08443c0070f4500c01040c0c42075074018290300094005208208101c43d0a048101034407840420007803a128400d03400c10070b054040c0041800d09100a101c255101c07041444810034548001b00040f95000082c0501c0d20340c11600d102d910745940c8400c84040f2003002602c15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978180053 1250 978178803 978178819
    0x30e1c0e062d0702040c03020306091530010f06050303031f0f151d0a0b03061306060c1b030201080a2406050c0601080a0321020c0a0c14030d051903020702 68
    0x242c04441c400140c445a48200c405001000da4550100c040c2e000a65095411112440210722702c8250a94001406c0b44007400040307103046544102180d24400c4581d000d90201005172500501e24203001d00c0041601c401c006000340707840c00c00401d5603484004c100d0030610040720001c02e5841e0620090900419070310b10290411926901d031440600c814074210030224203031111400f0050003002803000e20b00c400600030031030645014010f1140360310050680b90300101c41e121030780d42c04070f4510850000d400d05a450501c0703010140380418416006410210b4248540001040181e92010030070f07900900b06a8042410320381c42c00051040c1240500c00f2064120000380480c65076072250107041050700e03910441d070807640e9600c00b0607110340003024003400013030f5107461041124103072801e02104400e00d50303001885c02c0790058100742031010140d0110f07040c0e41200401c102c4403900d29003910031140210081e00c0007a40500c00a0068410590a02e01d0205001c50780010540242d040d40d11071500036003010303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978181303 1250 978180053 978180127
    0x2040803040b0a021614040e2505130923010b0d0321060b0d020306010c0b070206060909060601120e01200706110a020d120e0a03030e1c0e06 62
    0x501d43c0010303107858010b1280d07444030446000500f00e14400c4600c401007400c02079030808207000c045c0c64011910701c1c06100d5000c0c143c3c2e6500e801080000759140c034154101103d4100010444124204c142c000704590402c4858408520822100f251001c5c21411180e06c0450403ca401d003d07140f403c0c1c4007035002111038400380c28140c100f0303090001e058006101c00b03031015a0281ca40200d03035803806200e140044c14440400d0340c42843d402960020414100155600540d030341d00a0080000c403940701c016000101405610300b0719405464101d8090009048180342c140700003892000e50215203c8103070340307c04480743e54420070b511000c0b005175440030810030110002c0d11008503500100d81120ba030b51030b20340004070b014185015200013001c00d030f01a083e4402c9445086410a4165aa084940d591001c0c080c002180030418888481c0c03090b140861546400d200300760820074103000d1240c08041c034042c03040c0826440f1500c01c0000000f00c4400361551050504030307214a420701580350316010650900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978182553 1250 978181303 978181319
    0x30d0f02060a1a091515040e0c07020a03020a0b07031205160f051e180406080a110a0b0a0215090c1305041703091501051009030602072a06020c030307081207030204080304 75
    0x2031305904142c0b41c11142171b501307030641e2919204a101e07502c0e80b102100c000c94004603050006182440c002005080d400c3d44980003d08462895071101100d1007002568504258100d484c06440d410007500c05c1049160403001d019000d211600c60342c0400c0125000106994002d5060318840d0032682c42985026200c0302031055140d01c4100440310000c041260a001d601e014015802500c44d81f0001d413510102d99176401141080e02d4081c941e00c02114400810107000541c0a004144481d50080c01041102180b41c1c1e4840d0010b000d044064004061a0010740c0740d41c240b40103403582c42034001405680f24241104200401c40e42284129800814402500300c0010204142c066480d045480c2e42d0781c1d1403c2140740ca10458903007010410220703081000c510903034060000b103030251460b001401001500382007004489000e008200c114280284043c582c1000340d01c0f580741e0181c00039860000e0300d4031140001d02034407001e110a202c030500010406c500c13980656000f0b189200460b43c07603907154201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978183803 1250 978182553 978182581
    0x5010503071812031808120a0507051002181906050c0c030105150a0f0e074e02091309030912030906030c020a1203020a0302160b06030d0f02060a1a09 66
    0x1a40040c50134203200000e11760403203010084a40040c000d14041525000b9010150000e080880a1100c01d010b4000451340501440102c41142040165180d0700748110819110000195500070a140c0203009007491001240b8001c0c0d40c21070a02648621010601c6441d0051141c40d01ea0503500b00800d0068043c0c035942074030560341d8111146204241c03130300da10520140d8184604106e0301400307000724a00c280601e044c1c038981211041d50510f10000151412111150000008482c40e510b10100c0c44800008104901510710b06038103514080c04d42000501d10b80c196040340781303042c0e0f45100784800c0501407600703000101940c440703600046400e03007006841113a0130711444012905040007284403c1c400306200c030b0031950210300684031800c05039080b00290001c01d180d1041c5035003048410b143c884e414807031403207041c4103032404e2070107207429004d0500342551020303024240404802d40304001900411250340c066102d100010726840082d20907030b0610740c48414160070190102c18040405042c200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978185053 1250 978183803 978183839
    0x20d0216030e06070c030b06011413030507080318062b1a1f0f0504090603050a12020703080d02030702071d041106040f0b0c1e060907050118050105030718 68
    0x140c2c607070344a000c0b03400e010652140c00c400811030122000180005040080b0843c1c1200040c9400e01000e42800d0341544c1580c08881445080100c2d90703002c01c10004100440800750003080d009e141422480b100300d8034034492115007a41b00d4140402d80c940300005039952041c4c846c100e070814180308021202c44500500c092400c43c00f4502540f00c0000c00780c181b4a0000380e9000c803030742d2030244401c000e0900f100c911040e4044941002000c000008a020003406020051070158000c0c004110091400094810303502014030190f420110b03040000c54114000d4503501030500c00c0240c0c0c1c0742e8821070201e04001031a000708049071621022100e00c8030540312164415846071000940c140d044400b0404280070754414900c0c0104c13814400e01060b6017190240841f007200704200c44004031003141c001c2c403c0c010020503c610b1350024041040b80c0f102007100e58000c042c01c0c01c003111011085403403120013007043d008240c10303ca0000f0200307030b180d80300b170408081440d083c1500d660141e841c1c501542c01e490f8440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978186303 1250 978185053 978185057
    0xb030706051803010207020d03031a03012d05060a030314132301080c09011101180321061a2104150f05060907030c020f070e0703050a090f060f020d021603 68
    0x320a04200f4241403081b07030045c9400401005481030035030390032005407181481003c000d0b20720f903040356020380302402040c0281c0c104004551740c4808180c0e00d0154205481b83e0300c1c40003820602841001d495800414094940525024940c0c40540d495030801d40b00e40440e8081201151f400001c012000040300d22401040308a0340003000d829500450b01410180c0b01000e011204020022841d801100440b84d09030409001044138010b0740c40e022242d880c0b0060680110702c00042108640494240c0d0390100055070b00c08010007400d05035004000407402c3c550801d4960001074a01c0d0000502140840c1006040d41d890814680762500b40c008120640e4200700c4a410600d4130644002503010311442007002602c03228103035170340b03c008130050311410203c08150702400700d075040050010300c000c0010349082c0c1101245403c010340001d080b10070052182c1d00aa1400310501c1c001503031141d600401582250011500703000c0c2c2104000203102d00000e80344054400102c43c41e00728210001542c1c444e01a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978187553 1250 978186303 978186337
    0x10c05090f150f19030b180c160c030809030c03070e01030602070c05130b040b0d031407060b030d0e03060106110a150e0f0a0c0e100b0313021305090c100219060b03070605 75
    0x21b0084c010000320000b148181e038004900050710303450201001c1c1903010f80e515071005030380007142c44046103040070790000d80e01c5180c001001145400c040011522007c4d0503001000e1162400c00d00c42c8280c101804014200360b000107400707041c484020781c04009004010301e403a080208480b0720200412a000d07c1c036000d141414010059440c102c802001802e8054035030003002068070b00100320342d5000c0c0c402111440ea440030851560b8900f0004138012602c65240c03e10b600007002c0400d480c00b88164011410401e04c20443d1902e4400441c17140004d540c0302d08415904016600f20501900c9a44004d200d5480f629000485000700002d0000d00f00340540c2e1400709290710352605d080d101408507405001c68150311007c100500d1000000d641c400c2c129418400402c4481c0d0000c1c45461401d461403400e0b503141c80900c403036134006000100841100320303406103802100c03083c0039403a8040318081c040154500c08030402885091b8200407404c80000f01503600b608d8444030050142d401801f03480c074805c813030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978188803 1250 978187553 978187571
    0xb15131202010207033206131707051e010b030705060f0d0b100203070b0105030307021c030512010b07031205150f0a051807020d090305150612010c020c03010c05090f150f1903 77
    0x1b010403264068802c0155107584001c06440d40300d030b00a02c0c008020440d030801c01035840429014002e56040106a407840e008950b410418142907807200b95215202c2c0d00b004d8001c010710b660302e82c00c4603414000303544c200e91907102c0300343d00500070200b040e201078210002c03508200340d403a4044010640c3c0c500c40c154808499803103000341a40c034050300f000203400454402c00c211407480e944804410141c0b00b4030b0312034902070980c40d01e40282502030f0700c6014001c4010a100c820190860144494084140b500300490f103003d002a2804112070459280070301c4110b007880d15240c54200c81c41e4080c000c050500015a60400e00384250f00104031022001405804d00842c00c051017840b00c60100d0b07400c6001854030f5258010002218500540240d07440000039041100c104802e005003014003960741c0107409603c07404010316003907440d030705080c4040145c10002001d2566070f807001c23248100780c00d451440610100350600100c40c80317045900e40d5005070100d8001504031012007240002c80c680c3c3c0d001d0110b442c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978190053 1250 978188803 978188903
    0xf1a150307080616050708040b13030309050f0f0f0d0b25020307080d0f0603021216091103040b0c0918071704080307080a0f0e010b1513120201020703 66
    0x1001341c8405901d03c0f11180720740c2d5010311681c00751401c180a0000149015a01e44003508103611003e180084610780840800900d0742008501c001488180d410303680020319940000d43d8105c0c952412445110100f074054000d48881c400f40f9080c0303a10440d10b950904049003e00315561041050000c0300f0129941d002c051440842510b15059110344118101301140322001c0241c842c80c103013000026501c0a000000d079884130650b80280e0180005004400070800145089800340e030130984090b4244072281c440610007000f242e40c0503420641c0c0382c01d01d0301e900700007080e24070804210303540c004c0e5000486e48442c4c82a825090180b1060386544104912045980000000c201c80251000c1001d20004014601900c0e07140d52007044400001100710751600010304032801280c508800ba0342d600c24515050030325211030300391900d400f1451410084900b0120000b11070500988014045060400086900070442c00c0051a408041200c40a0520b0012208480c22040c050f105100036041ea9071084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978191303 1250 978190053 978190063
    0x415020309031005061801060314011a07060e07090504140607020c090402010305180f0304092a1d061801030c0f1e020a050f16140604030f1a15030708 66
    0x80c074040c0151050041c4001204028a40100b4080d00822001003c0d82000c0200c074116003e80940e48001401e005c1142c101d2088020503003061402410215810f00840070f0300007540c50842e40b0090200c1c0030542c455880d0b0500300d10f54070030b51640c1d0500e0280010801d0310204080d031044c03507504444050342e80030000c03070741c0e04a241c00d07803600048a440441c0155209030003103030f40000e04803885000a1280c0700030510740346081804003016000401c0030300050040d80102100e0410324010000400c1d00e4101070a0b0801c0540b419034240803410b89002090401c1c81e1040241002c014191900c900c403550000402810720b00e6404c1c00281b9285840403032501a441d0020325441d42d0796941c560594480711141c000c0c2d0310b00040b03c1540304102090001907170400c404003c40c102c00c40a08806483d200b01000184a02d400403e1541e541e46140c0f005a281c1d00151400c490308001007a030001d48034209008081c54510900b07044c8a00c403420003001c0800201c800c10b29400642c125440c442e541c590071030b220 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978192553 1250 978191303 978191317
    0x120c0c0925080c030a0b03190309080712021e030f070308040f05010813081e0304120807090e0f040f0602271005040506030c0c150a06090624020f0d0504150203 70
    0xc00814000b045800300035030302c1500b050b13501404440010139108d00c0920510740d58102100060b11060091080e14000d20804004004440800208031000c2e4001740051030429401d0102c07043d01e0b4101d4207695020080c940c0302c00514810384a11580f00d0801d281141d2140c05405000c00c0c0040d40014035501c0340304054825052403428210b43d0840e5900c106480c1d016922200c005050307003880c0980b8909510042d80510311070780050004084808018040e40070003401c6400340061007000700250300c10f66001c05d600900c1000e0703908056a03245404084400142c401605c010310100d04e0410360480302d00180c0c0d2003030100f2610b0f202c65020307504020004d020700022500080c01480100030b5814454050354000710748d01055428841d18410051074200f02c01000d840804040c0300780100c0c42442e1040d403024100d0743c0420310650342840c201e002828841045508800350300100a220f407882805100a001101001d444100000e03c02c0180035411500607604a9002c0c000c140591900020480d040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978193803 1250 978192553 978192571
    0xc05090603150403140d0f0b030d051b0321063a0c0b0f07060c1e1b0b0a06030510090309030314070803040b15030f120c0c092508 57
    0xb1220803003041140c001d4411402d0081c0032050b5483d1007500300142c1001070910900045005a94403d94181c80c0d61031122402500100b802444c0d25a1000c119400500c0b40c0701040084008001064550712840280480d0401c0b40440040700b44000e400304c6000c1d4104640d8600d002da03030701d00e903000c40340360850001c502e8540c5002403008285038503588d07910b95402550101d11035903407a4204c2c4010fa2210b24407030465500000e02d2410062548240b0081d883d061a10101c0c0900f0343c4000c02c40402c4242a240a0041804c0c90b410021b040c0c2e80325070070752035114041e042e442c10301c44081030190044d40411070b0b9a0041c0c400c189441e0306144204036000d9090796031519100d01d5520269101031400b03039101d1910300704000050104208800850043d4401d001c2010f240c5443c10070000360105100b5028400d42002c2c0365014031841c0080d02000146854080660714000340c42d04500e020440b83c80150407601503400c00c0042101c1c1426518882da0007088503441848800c41183c02200840300081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978195053 1250 978193803 978193813
    0x512040518070207090b03101515030b0d030825020d022b050306031501080304053f0109140a0209100b0403030e0609300c0603060f04090c030305070c05090603 70
    0x80322040c0c021540c2802c0143c288c440100506000509683c0850008028203082e001e0400541c0c01c03680700b004000c0382901c0d0800c003142ca001c000900b0035003010b801070100000031000c03a210038040c0215145407203440c1601d00000f180408042c0d00c80715041c1c2c908015014040009044e14840c4402a10403519240842480000400c05607000d4002400c190742610501e090103200c810304451550113052100025900c5d1450042042074a01d00002c0c140f00480101401d405241c1c00d05151108050b980c1030a4150820071082250040c094a407010700f001d1920013083c41038403c0030461b01c413144e000380d550305541da40b0703100c80599072412485040e07920b100801041010074400c018007402e0800041c51315203004295800030751011400042d80008114030900c602e98410407250050414008a001d004c2c543d54800003d2520701004081074003a409000030b443c1159216401080419448499100c486880e4140101960000f900480e046100603901003440d107007282c15a0303c11400140100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978196303 1250 978195053 978195059
    0x31902040905070e01060230031515210a022703161509050108060307050f040b040603080a020105070c02101215090f0f06030f1e0512040518070207 65
    0x401000304540660300b5010748030000c21103100d40001d10b4001d0038603900610040782508444011946660740a1649104e0901c44086a846c0d10007030384d500000d071080f00c40ca01c030901008100380a240d11000c41032100009110303240001904220ba400c5181d44950035056690004200e00320f2040d01040d022800034000600c00b040d01e0304811386450300024040c0d80004421080c440400303201e940104410070030030161003e4181c1e101ca542c0d070040000f4070b41000d550904001094a030a814000c0c10701a8601450782e94294455800c0b25040c60400b410810490fa130702c1c180154150045080800103509000c0820a8a4414206249510740003230400701403100680b4295610021012109400c640310403122f0020302e075101c2030b000245002c80010951030f0800b00e002c400c0350290280d008841c1c0c6005000d0010810191080b10541e42c00301d0700d40c501006001c00c2c10307529094128010010b20070401d6030300d40c48403000c010b4012101d060f1103042d40302c0459988402c03000e1040710500c0c0140c0c4504410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978197553 1250 978196303 978196309
    0xf0603030304020d110306040b07020c090c030a0902040e03040b2101030b06060a0e0d0822080c060703022503140f0c0f0a051804110a030c090f18060c0e031902 70
    0xc3c5000d82c07103000145d11405078500840d052480448080d0b850450603002c10480740d4052100d038181a000710351100746c61502814001280c08046c0541904581d2000641c08644650f48001002e82d2198100da0321a550b41168003602d07806608401118280a881c0c180d042c80012907580c140d95011a00031102c0d40c0b00c0040c860305400c440c0d56036003080003c0e84a0000340d141c600043d88414000c80c1203d503182c2030000641e100000c441d01810429000340d10802c10b845d00407400002100702216215a240300340e0800b01c2ca031281011030400c0e5099803110040c01c0011402c05102101d10030b01c081d901c03000d01c121030b003a01c81e0030513020201250403081d04030101b0300e07102020400180c8003c128007040358a17507001c0307086e9107144100c406082e03500c40c0a001c140032840d40300415051040350f52028490540d51803241c240342600c51404c0322a2581e65017001c0c0c4180360458101c0052051800c481e000303040c2032140103006070100d40c10118085044d25119828041140c202140c4d02c10440544c07402c02d0b80c01c1c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978198803 1250 978197553 978197569
    0x630020402030a0906021209120a14090a080f030408120a0f03090c0f0b07020f03010606090312140315090106030c0918060b160605070804021f0c060c170f060303030402 74
    0x8000ba4040d40c0b030081e0b00024101c0d10160401a0a90b007040c6030500c8c041092074a05000c034800d03021401004d1080d102000e41c4217070a0807040c031828049a840303030b1001b8003059490146403c01603d600440801541902001028004a40c95201180c4002c031400740714a620388a049110400281021a4800c0a40c003c0c2c00c2400380901c0340c44241031b45a5a81185c23500030846400020b038083c000074a850662520a6084201410841c000c0040503c4c00001800101441c0b00c000c00a04003810044040703405912a60410003480d8400341e91b2f032900c04900c29040d011030250a1280320f01078004a5118800d10620041840c29103400003101e0500084c6040b0640c1c110454552a4652f500802c08a52010150001402e039641000382d83e042031078040c041e958014404010480202c080001690712070404640008090511401444408008842c01c0700d140d8005014a400e200000750040d034054a2503c104200308401400e0b9280c196900e03041030f0095840c0c0d541540140f0109002d0310341141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978200053 1250 978198803 978198811
    0x110d09030c020301110a090e010b03011e08010c05090306090d050f0708040305030a09081c1e02011407050a0e0d0c06050c031c0207211d0312030a063002040203 70
    0x14410300710003207a40043e09607018040ea030750345810301060720446140c0140e440c10181180c501001c500750305250300309241e40014441d80f0f45c110200c200c400c20a540000c904000b40455034020b0003c0491400c002d00719a00420307402e80248105030000d26442d0f008203150ba00c0034060b6070f400b4641358030f40c1400c0d5025003158405807040c9808010020001b20104000e0840080680354902441d24100d0f0103420003a162000c41c0125848502c038030040c82d070010301d17480b59003002d04440602c1c40c1c80328822801072138200007032081004002c046c4083d264219000c0c041d103002c90f59a001c0040c4455050010b41c1c4901d0303c00070040000f402052018900500140c1481141581102d08017408082910311409040301d0f0400362660020b02e50052005808150680803041c032101204a41121070040410600c15604800a0110302c1d0403c00d95400384a080707400c00301d0b5804c60b07840c1c0c00c2c008440c40091070340c0d12a1050036040c030b190300c41e205234211180144812101da00e00815183c103070240710280d40010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978201303 1250 978200053 978200057
    0x90f0f012603130503010e0607050f03040c09090501050901060602070602030f0d0213030f1209050120010612031d0f090a050c28091a040909020f040e0a03020709110d0903 75
    0x30355015401507040001c0c009000c1040144a100c603c2d100c14142150340200d80d542480c2c10110421155680240454070510b492400a903a603a40c0e5082400c110603064101e0f148072814200405c081c410150800c0380110a00c000030841039640b40d00680c0c0e540b90502c03a01e0b0240e002803002c50b0203851803902615940c1780554002d40343c01d03280b000d41c0201418a400c01c9403502c40260258040c0b100740015403548005a00301f50600c1130400e00060815598001042c5001c0d200036000101c40348290001401402d00000640d240c24692a000d000d002c46420047d40c01c0700c200610301460f1501003611140801c02801d103075003c0d20382c00c2c4c941014140c018180c000703211082201c01c02c2840d00049400c3c010105848100224240c810004d050000951082d003006510035607040700c03007100100322001c42d0006140000c02000a1001c9020440302030045540203140901c2400801004281d030f5400504c01d1303081d146495240c0b100101100c0100f442c00390003c009001c40300100c05554480810340e8024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978202553 1250 978201303 978201359
    0xd1a0414161d0a0305030408070b04240309022106060a060807050a09050a06080405060709061b020d0209010b0909010b0f0307081306060f0f06020705030607050f12040b06090f0f01 79
    0x80d4020864400081e4005c5400d580002400c12581d401032010101a000c1e1410b480d180510708807103640c480c4003103480d9021001e410038604400500907401a11480d50150810000f500c49030340f1686102054402003030030307010f0800007440e140740c803089801c1500da00b0b445903456034444601c22141900000600018054184c80200b5259607008285009000d55681c0448918042c030700780741444800343c4001700340300d00740100780105904964212541e5459814805800b031440c00003c064602850000c2d402c0742e001000820340d04041d40081c50300b0901a41c0d00003d036641c40c84a00c3c4240f080020401c4074100510210728000d100f05070480c0c100a50f01086030300c81d101c1d9100d11b0200c840300c0d0700c4a558003085180400840c034807814410002c1403030f8006080c88a04e80340120707072164802001c0c3e000b08000040c06409050180d010390300d0072140601000814075152401001f00c0e6015a2001c2c0700348a400d0004440480c0d4280184c030440d40503a01c185181d10b0310480d848a44920014104500b540c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978203803 1250 978202553 978202607
    0xf1f18031b1403071509030206040b07020c040f020a02010b0108011202041508031809090304050d0602090109210c091b030f0f09061d0325080d1a041416 67
    0x604407a03040800c0042c06113642c1c00c12841d10070098020404600e02560070b010001c0c0100c0d03000721340789a015400450f51001a69003680403410039506074652540685010b0360003001c1241036016051800454000f003001108400c015a5a01800d04c00d131085024412040320040c00c0c60340143c008408501119803040d80c65034800d500f941c00ca85c81d524403900c08401d01034035074540302c10345980107200300010303600d17190902e404a0000845c00401610b082d4000801e46400e0b4490740d907510040000b8203641d41182402c11510048030041c80c41551000e00c015008120b6180d41c0c41403550345105501c150180708401642a805043c7e5002400d040d156624a0b03024806000c2c00f544120912803400018649140a10001c0b0144209a9000d0941c8244514a00ea00d000003200c40200e2070b07216145041c030031500d0700701c0140c4140940403c1d510b0030240c03411440a1401005c075582c40e07081302d0500001454075452460b1410840d04c0300c0c1d03113100086c00c02031664001c6959030320b01c1c9500a210308407081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978205053 1250 978203803 978203813
    0x61b0d11120c07020901060801060e010e0a030803180f010506100e01140d140c030609041704050409080d1a031903140403030905010f030b030d050313050f1f18031b 72
    0x18201c80c2d07680c0118000070881c04514282c503210340904018101a00c80754140302000300301d0240f5840844c18002d804600340d0090741c96100e204000d42d80508650740d00c0c40c0040c1e9075a07180c950240c40f080c182c0308100c240303069602c040c01018452a0003400d14544202c0814080b0340e5024601031041c10302004100321100001d4000041101098080d404110030200208041c9100c1c8000e00718a0400410b10034070200d40d0300d54202c42d8015800411a940310340c4503408040742d620a50740481d81c00741ca0052600100300b102c2024003080d180c450b07410402f00c40140c1103a0710341803110312501e0307264003d1100301d0321800034501100d10503402032401d64031420403603d445440d503002d500180e02103008031004200035070740042c5c03d81d0081030600d02404031101000203e65542c2d03002180805000011000031010342015031003085803900301045481c024106140c00384c96034090300b441001108451440210300c02540501e1031005505c0541d18041c4400d91011125070b01c00c0c0310000c0540c504010081c021070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978206303 1250 978205053 978205087
    0x30010f140d03111c0e1905090402030f0d0903030e0f0904080c071e0806060616020d030507051009030e0102010e0c0628020106180b2107091409061b0d11 67
    0x1440754441289040e400074006800002c4c0042c865206da43ca841c80008241c202c900e04200301c500940701c080058840f40300090401c21050320004241c4603144294a040740d203c1c11100840c0d0003900da580d48101c1c45828401c80662374041150000b6001012400081095000349108001c540c00d8400042e00d034142030916208480801c5d00322816100d0a00c602c003404d0241c0f58100b88112040e5160030703480140c00b4403c1260f6040644250507110080b000d040c001c0342100d50840e0b02c2025202522500040d140080540c120198000740d12100d941076994014811039409408400041010403a5001001030603403020104440c42501c12490322400030b0940340e05120500a5000850b1a900704801d0401e004810f88220041d43e042c00b80d40300c6c0b2a1500ca00000d5020302004100c41190800c049483c0303002507030791020820030f280c45124511800c04040360b07030103910080b050b40c60b01d456649421038441c03018003104219640c00c000c0b00380140c100742e2010510060710100c035030074181e0804000b0008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978207553 1250 978206303 978206323
    0x1203060b0712090b0c100e0309150c01090c090507020f0c0a1e0b0a23070c030822080c0909010b010206070c06090b01090509010e060f0601050d0230010f140d0311 71
    0x20b5000340f0410222803014080e41c07807d19181d40085040c0780d400000511511414022080840000900707040c00074000e4001011554020b000341e02d6007581d8511600090a0407a518001405041c82c0440002000304854000c04c00c01400c1000060421000d80450013000540d40801d0460b220001056010f00340980400107540c1c403119054100100d140c645081035461049040c0010441c0c2c10004a0341c503910801c0d60307044800c8581b0743d00341003c8040950295000348103191415000000c1d00000018161080042030302c10701d08c2500d81511040c00d0b145049030150151300309100086450744615252a025400707517902003061441c0b6200c0c0a010301003038108024041d00c403400c028440c0024000c100480091100524041c5095801440a082c3c007402c1c160421100045100390304607160142c4242c1c2180c800018107000d0040015078049e140307014141c0c0b80d02c0d403d1000003091041e0750400d1048610345880500c01418003010491410342030142103052151141c0f4802d20458200003034014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978208803 1250 978207553 978207577
    0x903060f02040503070e01081b0102010b3c060301030303050702100204091517070501110a0503040b0306011707020a06051e0403090303180b091215070c1203060b0712090b 75
    0x601e6040c6400c0c1801c041d02034021b00250b0940d44010441c2c643d000410440303403503244860003420b84c95500101d000d01840c1d540c442c0c1c03043c80c00340002d0901008000060616818101d4102c408108aa601182890084085901180520041011a00076002141c0c0010b05105443c1a40141c0c030600c0d0481c1c0240c0c01c101221592040d40c54180d1211501c02c0c006002c44003008000d2540381c0c240c8942c0e80b03400b4002d090400860000315805c40200f00a00507202c2e9021080d65100e43c4c5a408020a94004591050005181011710361b590500c89c07a095008030f1141d40548101c0302ca03612150081d040180038105a08d81e90310000042c001080413081c0661b00c20b81e5042c00d094a5030a00404144034035807406100a880402000000404c078204ca50501040d14465440d406145046082240c607070021140042440c00b082060341d070000319410760500c540f040341c0d40b03200701c41c20460484403140580c41002d10708010810104130301031a004003100721803411480e11600e0304000b010a030010800401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978210053 1250 978208803 978208807
    0x1e0702130507020c01140d11090607150501060f1209110604080102070201030b0604050a12050a1a011e0f0311241b01091a040c1e17070b09100903060f02 67
    0x400d0f410301400440d00c0003460405c010a050648a164610500c14000909542c2c0d65616140d400210240c443c1c100c001020a916550b140c10301c6149282003801143c812454200041010303801f03004400307410509a9200c1c5210b4285403d600c4c010711032120140c440c0e400111400600350b84a10041000e400703903c0c00507865101d6480090700780c400c4c201d400340c0700c0c0380d0610042c00213440d400e140c5070440c0c14141c9007000080280c20440e0030188007020180030b40310754541c1c0b460815800c03182c05048a40c0005215030724440c3c107041a02d00869400303444410405004c2c208040ac00d00b04680031041d0b8010040240016002c00060010b0079080c00e0003d54000428003184001175030305004092844c0070003d02a1681c1c0e941d50909140f0940391070120904040081400e03c03001d40280341c09450050301c001c4580c0505145a45c40742e015200e10007980038000c0e50040c09481c04941e80044404840030103040c030b001c250420091313000c014020b2003000107100d4000003013640d41c0280181c00d06880c000607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978211303 1250 978210053 978210061
    0x9050102150910020f0c07120c0b0301140628080709081609050c07050f060f22120507021309050105070f080c181f021009081e07021305 60
    0xa410403104141400d8214484002c20100b0100800c10705010040d03140010b980d6144100100d101d030203150710082c0c03244116040070401d807180c004100900ca00919040d1040e66880584145c1440300f4043c07005034000c2411140c406051407030161004c4050102900d242e45404c1014840c0e00d007560f1042c20001c1c202070180040300e41c008007800b01030010300002c0e1800e040400821120964184116840d260703403031002414042004041d03c11031070740007041c0c4006c4015140210fa40d91002d44060305012030010205005c0000d040d903000e400e010345400359540c1196501e403007172900c05a140305001d100d410041000160766201c00000e000010510004180e00e66007446400c4601c000c1040091203801c0004420003608144460351115a0030701d80d5649403180c0300528120580303141e8160f080310030816810401c42040380582c1c0441c80d55401c0340c240000c001600c0094074a0644042c1c4090003c0285601200801009102c0b400c89204014682041a070200e03009442c03004100e60341c03a035904180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978212553 1250 978211303 978211307
    0x30201050a0c0c08091306080a060c08060a1d09070b0a0909060e07090e040f0b280b01050714010e06190509070e0609131202030918270c10090501 64
    0x305180b0a654580741e814500542d60320212072103080c009610070a91441740120445446c0c01403009082c1c401c080c1d5071100030308d15248024240e0300b0100c102003189200040c580c0c1c00c00a10a20440d03505060400383c1040c3d003c00f11805601c06841d00f400c0e03000ea0a004210b034010b0700c0084c90701101c1e40d500c1e58181803510680b141107904981108210300b14074810b05c00450303880740d911816107262580d5200345480b94a000600074081001c014541100c1d0360401594481100d283c011124403251144503a407109003a500c21142103404c0707140468414800c1c81d000c01c0700d039a1181408043c10b0000034407041080b81c420710345502101c0f00c14609403010001c4c3c4801c41d440c0101c41c2c02c503410000502000c3e040040150450500501c0b660190b080f11f00003070003074840c203114003100300d0700030300c01c01c0d905582c842c4000e489503c400302490081070140b01d090400314100e0220b40c4075222982a030081c80345010000c0340c040310001648029442154080d0049984900b0078583c1144d0540720400c20600d05000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978213803 1250 978212553 978212561
    0xd0f020705042d090501141e09070b070305091e030f0f06060409050c090708090c030c0d030309052e0501050603101e0905240603092e0504030201050a 66
    0x4842d02a90410001e00c83c000742c00d1410180c1c000d000080d500e04862001001c0e8024014080c0160080d0700788098501e403200e02c1d81c03e260207000c00c07400d0b13168429030444118409840a5801d40c855501220040240340a12009403d2041c03080c50454940034004000803c103000c40303081070f83c1c1c4107520200c642c0c951508121400c840c090700c0d005480c90070b12202d220760b25464002d00c0c03e0302841c1c8521220042010511146100c0d51008200503940c5c20f01d140300810b003400c1201c0c421003d05c00ea125807100d9143c000360301700382100000c0190008001b140d6040300501542002200c491040c03038200740d03507005107045401009140200a0321103107240c034400400d450341079002c2c500440040040c072680070f48040001081d182c07820810f28042000e90158071080c2c6084d800422100d2810091204030085500c0048407030b0209818818600791242c00c000c0c0c0e901c000d498006c17880e4400d140300e0009045013192010312903400340e41c00da03858044a03410000d0710b60880301100141d540340c0400400c000e0300e01c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978215053 1250 978213803 978213809
    0x11070b0c010b032b050c0d0f030c0507050c0d0204090b0133080a0932010c052502061209160806010f230303040807060f0302030606071e050d0f0207 65
    0x1000b011041900c00c5100600c180d44110001389002e03a06002513410b00400031a0000394002c1d00b102d044ca107000800400d8401c0c030091580c006405d0180807500380d1b1117130701540c2d02c00b504100030700f080d10308035820010303203c0c1f610074203d8010f6280c910b210086840700450a0003011001090010400021503001a41240240705041d00c02607186540c0f14079413000e1060b0b03110b00e012500244c21556420a80d41004201d00e0407403940c0025805150403000704400b600c080c0040320300902c00d044e01c008050769a8090040607440340c1070390014142c2510407031603d5482060010b400b42e8545010a150040d503080200c4041600740c0c48101c11100328000c284681c0d0007044100040c08031541400794405100403c2d103c1c000c40a9041c500020304c4200440c145c45041c54014101e07075403160340e015202c0e26681d00d48035082c00b00d090708030300d800018005e0007100d104610003468980342c8034041c0c2d51100701400c1c080248a601d10b4010201c6c0000b441040510f500700074a840704040a0507440c0020300e40521030b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978216303 1250 978215053 978215059
    0x30a150b0a03030503060402090f0a080a0c150c02100c060507030504050c0d02060a03021b1e0706030203010326071505091212010311010c05150f090a02180711070b0c010b 75
    0x1c00401c042940b000a49030000411140540c1d94a8502c0c0003a0211007124181c99000030ba0b0f5000103101040066045031036071081c0c004c10b101c3c5a99000d4100f4155880305000c0c0030510502102c8014a4591280c003030f1b0340650300707260b509000c841c1c44100071107800f1280c240100e40c0d2403080c0030900c00204007040c1c0d104412285c2c03480805d100c1d030104405028090041044c55000306080030106690050340c2c5800400200700c4000008011080100c000e00b146c40b012a40900c0001151003031007030089034180d9400041e03411900302c02c1681c0206d40c12400c0104800c020040c050b03540003a00160011401c600540300225190900c4880700d03081c402402d00c8121460720801c0300300e11504148160504580d0400810082140d00c2c0f00142c400b6a0392280c014034074021510761a0905204010b01c40c0505c01c4038803650595614001504d903541c4049002942c040d0380403601c5690103810020b8507030701910500c0c0248802084802ea24604101c035004500d180c400070900b02c201382c5003403191902c1140c1c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978217553 1250 978216303 978216319
    0xb030d39031e0c0611280807260c250318050d0b0a0b09040302161d15120a05070e0a050c0d200a1d030106060e0405040f02030a150b 58
    0x10000580f6016907807200908040d00c52208100e00f140c00410386600c00d4404d154030300c3c98805001c054010581940700d10700460503000110721818410049018004801c400303d40d074500d145000c907503201c417004104407480b40040240e180107200340c0000e085074200c050381c2c06580880a20b006001002e01d003000c510b48103070001081015540c0d0117054002a500501d00e40041d49520b10003a010388909113005801203030700014041010741c001550b02400c9140495880416100da09001a4051744101000b01c11021008034141c4040a842503c55620040a200c500502440c4040c1043c0761510191165001004108246400c0500140e8407910040d4200702602e08441742d0b03405400340540001c9010358640360803d40352442d01c010f02d2195003525119880b0901c6040080204070b034100d0b100c0c2c003d259440c5c0d045280c02c05008d0441a95042d4070781c024140d100034188801003000500c00da802540c001c0c401005a01d051040c42c003c14010341255201190080c202e60646094410303807406100341c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978218803 1250 978217553 978217607
    0x19060617030d0507030e120f07121e080601080a02030a270302010b0301060305151e0103110f01030902100309030507060203010f0e010b0702010219081e090f03010b030d3903 76
    0x1113410041f030b0a24100203902c0c1c1070403412503d980c0c012904014003002100340b034120555004a0031458080d003640300d01c081140701c418100e41246050341e01d6804101d911010031501407090f0007031540301c5070240001601c060302c50785500d031400502507040409469082d940c0c0070f0540c203004a120301007040e0028082c1c540f5640d5000d559aa1741c000c0315813074040e1038002c40c410f9607a81580b0103c11801903001788055840e0300741702e07086443c540010f034401c0c0131441c46200c0c15400303405030f4000c05030028818a0303c1c031000c1805034085d05401c2011400c00070100200400202244059030182500340c2800015905180f00c5200030303c030603000394038889410b102e0500140e074006000c01840e603181e0b86e05203054916161001c414003c1550545180c08908040d8031301d0548000a000e00417000c035403004640704240d0505088554210015401d40c21202c504080700340620007030408903a00b180905c04c250b485841003c00f9003020b41903064000d18404008043c983d0019010440012060344101c01c014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978220053 1250 978218803 978218831
    0x2130e090a02040e15070e1309022b060e0604020102251a1918140f0904020111160312050a0527030f061014010219060617030d050703 59
    0x107500e9400038851901e40c6803802c0c840c401400315081d00000403444121a040a14000c4d040c2c13800200228080c001c0c9440c420b0782129079025070894150041c04994520040709070b840040c0d140411050140306444200c2000aa40c2d407003104c04410a00015000508042c03000a041140d0380d6140040c03080b405005055078015684842c080b19028400b40812a0b5541c007019010300031102d80507451440f0745404254035401015102c000f0130f0810b41102148c1c1c84245919019a040c48455005109615880c1990500c0790a69400c2070050410940743c0820301d0004e0320300220303151003001030024000304204102c001060098126001c1c00d00f503091410780c8800800074080c809000c13031103105040c061180315118500d85c090140028069900000c0f58955081c1d403007100796088804040403010010300d4490301c5d10000b01070700c0140c3c050018200a80c10b0500280d141c000300395001540d5150004000317003620f8080c0c840c101c5540166888501e81080d201c2106c2d00140060281410a201701412038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978221303 1250 978220053 978220063
    0x1020702030d05070204060f08010c0e10020d03020f040b1c0f0c08151203030703020c1b0d08130b0307090519030b160c08040821040e0403030504080705010c0302130e09 74
    0x950500c3c1840d01e540890000601500c899805114013a81004010403c0c41040d001030509004030f80310004064540400d005581d21003034803400040e00315900d1503107000d20039002000e007451449407403401d0545480709460141d02a001c407075078a1602d82440300d6940d00383d002e50740c0300c030254040c10080404c0740c20300a01929402007904d00d104014004160540c1d030740300c0c09202c80408030000c9984900e4030480c0900254408a13401420348550b00c43d003031060710120720007000a000a020001102007a035030b4191560130003480c65010000c00301006c078034450b102001e1742c421a400d54076822414074000c24083d4a0300a00c4051103042051802400881c1c002640140c00200d40b0b8080d04107240e208604841c0000780390b500038811180050002134200d4000703a00e070100511800307004a036580c0e07890440c0c5180310350b1040d001c580d2125000180403074021f81c8190b6211307001321402c5280a60540c2c6003070031901c000c4062400b007640032074150031850804803020040c040000806a107400c14440c503039510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978222553 1250 978221303 978221323
    0x608070c0f021305150316050a0b16171c0203040b070f050c06100303020607022e02040503010f0c180803070f1103150103150203070503041401021c0f0e0102070203 72
    0x3040786411501d402c10081461403901408000700d00f002e02d00100040083c070410f910074072070b4051000e1014221080c0d03204695004142d442c00f5403502069100c207401401c481d148040041d00e180c80402c110f501030010b03040040d0b42c070954640c4d0140500342c420394500c00c0c45100324814000c102c0000c400300c12050b0051880d080840c00040403800c1110700f84504180c0c924a400341c0303010702000001c00c01d0100c0075a07110f0f4094816aa0b1442d40490742c52042150818025400145803900c01034101c031451903503000110051701d420384804c08a401e5554a03043c2e030818603030f02c2901c40c880750741c1b02d1b071895008085094042c000c18503003d91340703660340030384000a0b0002c40912402410441d600d610781d0042c1c100a4151844a5980a146000300c40c00b4402521350600d000341000142c800c52017240e20684080e240e0f5406c0d44c40e079445498242e00c170b5140c101c40320b65081003c0f105050404001c00c03001075003010080340005004603c003080da148680007240c5680144455001694040340310190 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978223803 1250 978222553 978222563
    0x20304062d05040206130311040b011b1407090603110108182503020a0303080103060c030204260709050a020913050f0105060c07120b040209060f0f0618090a14010608070c 75
    0xe50340303c900000d0f40522400e80c49004078064071400004000d04c40400c01c0d0402403c40302005000d0040005464402190308404110100605100300150864120030325404440003140c0c42a621148035008031603050700705030b1b8446c03c1c000c00f4140a41c4d200340e020381d0004941c0030948540d10180c103401e540c3e500c070f405460030908078028501085448040994002e40d0001c115010003a580d007806803004400303000c03e0303a0b6070b4144140100c92501078000c0700c080b502c0304000403100442c460f206a501c0750400455500034040e640000034542140d010306405403030707400300c0141e0312100341c4200f00080701a1488039102a09200800007040800700716603045031403d640b02ca589144040390f4078180212600298001a650102c0a041c84048010b80f8411482500c2801d0f29850322403c1000e4402000503031580f000c90280b40704800d06109018010031000d192840c80394401c250002030410404072020341400b55142c6882c06d2803409500b480b030040c94175090562040c2807040004001002c85007024203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978225053 1250 978223803 978223811
    0x60b0d20031c08160512040b0a1409160501022103070c0f051b031515040204080a0f1b060f0e0f0d030c0c05030316120201110d020304062d 61
    0x85440c18450300552820700b00c000b901ca60b000b80e1000d001040259940030000030344d026159011343c01601115180f5600c2501b2081c0781d0350390340d21001c520000030540040e098840110411640407410464000c0340c2c1c0d0001f8000b02215288511141d200c503500c6141150302200e9900c0c00c0d507201b6416250500b104505056807903855001c1a0f588104e803000003000d10700302c00c5c5d6079001d02030b01240080700d00503d95100b03240c00e8042c00c201030fa00c0d03a81c000c0d140440c0c0c0302070012904414a003400800004005003002d4281039403414141d0501c2c04110040d00c102007204210000c200c4a18001602014507034502c0041504000009003400b40d003903000d1003444882000803250fa0790b00d6826072007000005100c2c004108840c81d00410840b101c1318116904510310038080743da8030700882580c10a9140344100c81040ca19600c840f5502c00d4070a8108066542c1c920320700c2281009000103060443c0b0350080503960b820245000c204071002100e0300081c0c0e406401c5400900d0110340c480300006441c42038045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978226303 1250 978225053 978225113
    0x10915090c0e091f0f05011a091e120303090606091308030402040f0f0c02160602030d0f020903010615080a0b0603071d09100f0b0906190c0816060b0d 66
    0x38036085852204130482c4100d1008060b0510098000c01c00c0e07414446824061030340e0310500110a41aa49801204200207000c00b61580c103284040c10011442081014210f41a082c0032440d02c0e074118460840300d403c00420401d021404000f59030304208140c1c1d0620b10341c640310400c0005030101c00c070002c00005000022405668850300003020500ca100d00800c840440719114500a080700c1c4040c1015000d142c1c1b0b078000350030126420508458580c0c001e9813500c0301e0a01140028090b0051040506a0901c111035082d1024071a44010b03180104c651039240301e80300e1025160400041458010742e017002d89004035610340f40141d9421115908194151a444840c0c27442c00e00850b40e001500700f85c5130000c2110f41c08204034620126103030010015402030f1034800d615502e1003140903903900314004121011072100d2103d101050400d092401c0c1c0003000040d83d494844d036214819507610b40720304069800a1006502c80c01428540454809a241000f41c0d103034440e00040031a1401c1c895103440c042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978227553 1250 978226303 978226321
    0xd08070609060218010210050709060f12020a05031807080a12121407110708030708090a0e0106090f05060903100f0905030d02070b0f010303090902030621010915090c0e 74
    0x501d20480d4400000c2d03403140004002e220851448242e13941c018410490020441e125070310803d40280d203260f541003440e034101031041e60301a1103071401c88100004c581d2444140740e01403001d400b001d030007582e40e15aa42000035400080308041c89a2850030740120074100040080010000d07030141d444125003c1c3c600c0c06600c1950b50020f1144841d003c42e08001c0c8031f01031916224072003442115070f510352130110b69280040780c2e91030645001d020a29407003000311101051001000c5c1141502c01040c00f83d609032a1f101512503820b00303038084404662240310602040c084c030180314026150540d4240e003000641c00001c0d42c2c0305901e68419524958a1510308a40d05840d08800074003030708041126500d4801c0801e03c8001c0d40803070015980c0d111240049080038009008081c100c1e9003540d907010001c2c0c24101d0200017540042c0407280d0186041d485500e030129581405403141065100000b588080c80c1440180d4280511056003003d203000c0c0e00c0340005001c004d4490540303500c0c802210460340c881400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978228803 1250 978227553 978227561
    0xa171906020c06070306090c0e0109210515011503020909060906030c030a080c0607110a120302040f14010327060513050334080a0f091a0403021e0d080706 68
    0xb00c511140505020860099090703040001140c01c031000400c00300c01c0000c01142c181420604460014000c00020420007a580010382849010b03581665810001d41d80c40d0b51601002c82882102c48640d4001009080314150b41740f9607a082500b400d620f0700c1014000036105032030003006c052103100307540081142c070b850802100017413450141c11248003034000c0c1003500c884d0304480b2000d00e00384501ca00040e01144500307180d1350780310706a100600908159503580212070300428a0350041550a100010304c5250703854a0000410031460400150070700440010f0968030849160200c0321040c10400703c003642c01e00c04043d503058200f900007030144c803007501c4d0000e40c4200c0c2c01c015109100200d000140010b240300000d40c006140035180c0c6940e1018607082036000d10f410000f510405003800001302c0749005684004001c90545000800992928007220404c3e2582da68050352480203c0c0030301c118107180855004c00b140025180900c440040001038081c0c0007150018500c100c0807da80003000404d400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978230053 1250 978228803 978228817
    0x50c12130b0109110313140d030605090a0e030702130213030312140105010f2303041a0114010525050609011b0201020702030d112112060f130b010c021503060a17190602 74
    0x10030b2380c000d030a000b00010040e00e42400303454843e007005008507030049817074450b20009850120156040440c2a020464400449602200055003c120030110840c0240350700d40514482e85484e811403c004d81104215a05c4468052120f071100005220a81e04500c684000c22602d1038010111440c1c001700c407941c000200806a0801d50220034070040007035041604039101941c0100d03080796a6181c1c505400204a00115404620100600d81c84e20345030390003040403444620840b0481c9649540c900d0716040b022208108540d41d100c0c11100211030518400041d01765520096050008580009440c1c00c1400764000501403200c0000166441c00c0c007040d40d0031065840c0031040c09202e000442d007964840d0940d44201044407002906615181036111341e9154082c0040321103000ba00004030040091960050500610b20026801a9034418911100241c0c04030304d03503101d041074801d0055907031490300490241e00169040003644200000c9006031480024030201ca13a00c464208a0000c0c45110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978231303 1250 978230053 978230093
    0x901050d05010909050f0a0f17090907080907050d020609100207050d0503130626060609040f0e190503070305090d0609080c0d1809050c12130b0109110313 68
    0x1001c054592144a0050040c0191070303036001000b81140c7c03134101410004248124a0500f030b00400c021840001d170190703241c0704117840c110700301c2c0000f168100d0440c0c0170b10015000004002007000140541402007400799460350760135481c0d50000303c040c022050702c24040c0c40c1c0541e01c880301d144200b02400003040003425058607843d80d401d00a032294803000010800b41000f120015806d4403800c428002c4030591608041544451810712952020240c81c0543c040c0062003480515621881102d81e40d07a25060001202801104030a0a100403007180300080d140d07101003200400c6010040310101c65251414950702c100e1398000403003501020320043c206a14100f500e6040240032802010402c1071b186c110780b41c8030682c403400c840d2482d0044000005114403442040b0b280c1c100c2d00100d400100400300103080800001150400480842e40c19580e084000000000e000200007086d000d070003410b20070b00811130585641450b9207c01382440102c0f441b034550b600280320500e41da0b445420000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978232553 1250 978231303 978231311
    0x40c05062d091c1704060806010e0114030129070b0f180d05030a1a1e18130c14100f0c0f03090501020f0c030a020f1f081509090c060901050d 62
    0x5040e4a907280907000700441c2d00080d205036070f50110b40c920060b1000c1b165150744d090410740d5080011100704030031103c05418443c043c0008030350003a140000c0d6010301540d41040d2448408800318000300091030450300140f090810030200450000200a035110204620600e07480d00c841c4030506581d0403c600710060382c0102c5914490381035000d0001d50003000d07403c0701400185101da10300c0451145220185520800c1200c4016103001d403122000055a001000303020598000c003c041e0200c00e00700e40c98070284038030400040820911440780c130046e0003c01c0180c15041d0451020441d0700303450b003400728140f006c42041050543d11038440fa1b03582c0b40d40240c004c041425186004bc041950300c1c020580540900b040400c8240c43c000b519100000c0000d0050040507650340070f100100101c88911600302c0018000f5495400c1074a51408046a40b50b8400c421032400e000c14662841203071364154407076000c01c400c0c0140341000042000e140c080841f0241d50f00c0d081c00c07005a441d17107ea180201705580c20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978233803 1250 978232553 978232579
    0x4090c081b060430060c0f0809011509110c0a2a14130e030a03050f0108030f040e0601140408060a0501090e060a0f1b020a140a0309060503130c0e040c05062d09 70
    0x100c4110800d0b00007d6407101d1510340c0341c01e4811404e0303612030700304460840c514041c00c0040c1501d41c2c010104002d0b441844500e40010589030a0810044c14020b40e4021895040b0740071000c02c944051061400310740107407420600b044241c002c0b51082010851003290544071044000840d60b04c400c18400e98a401c032035407040048406000f40100700c0310307410051648000060b094501100300c5440445a03c4024905420301c000110217800190529041112058184c0907010f402c03401030001d0540c0d000240800d01e82041a0700903914140c00c451801418a43c0b0301c3c1070701c1e80c0001d0031504420309000102e5000388440301400184466146020815a28040510200c2d0085040e0601d940181c1e80000516007000c490355031400f00d004001c0c0040e0952004201040c03251000d1900011105d103150740d000b106498044008105410001031401c8400504c401c214440307541d0402810152162400e01c41c00d0154100503c5611813903a031841400310500c10b907200710304229000b00000030074101f02116 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978235053 1250 978233803 978233807
    0x402030703140108062811040e150619081e0c041d2205191202010c0c03080109020f04050a0602030c060708040209041104090c081b060430060c 63
    0x19011400b000c807840408000704243c8000708400f841051404402c0a04403c103034030481054005885150850707948000c41c08130320b0322150081c40201210380c81c1e203c00341003803a0140c00d081740302c141c07051180e50b0410004070038501c040761501e9045400e0404240550324025103640742c08a0326032100e43d040f501c80c100149644045c0c050020f0707440d000755900c100341320404000c40810096840144c01501c0965400701031200076a040c680c0340c480c0e0161854001b030b900d214200e05005103011100e00c1043d4200e07020155092248079298051841d0801414800c1d0f14040c01c000e07010b000d41d21816030000f4040d013402141c40b00300c0d00180340140c40380c0082a51040f009403a5003000c1100b10241c01030f0004a980315101d480c240740944c2d0001e01000703c944480e60b61800500104050300d801c191200046c40124a80003076403401045103030090094030140c220f82c00210070740d03008003e1058400340800d000c2c100c496201c400b0361100701c540001c0461100180d1a41206114000030101c0d401e00446070b0142c0c0e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978236303 1250 978235053 978235061
    0x905012106061e08010308070609030c05031201051002031306050c010915020c1905151b07050a020102070801061a030612030d020d11120f06121902150c0712110402030703 75
    0x11081c85001c840044143e0b0045480c2072081c880a490b20070123101c030030007158041d40302e1904030b44a420043c4141d10b50390307595070840d003000c02120a10140c6100420040c1004030191807d030005101030742c50401c8110710103c801449000f80c07410000301090040e0060002d5021078421500a1541807001c000300516401a40c0aa103034995140901000303150070342040c80c9e086401c154072002825a240c02c01c520740500c403e0007081d1084d4921449080c02c8070f04a0200103085081c05100600008900307400060b24048080d800301e68141c0c5040c00c100071500f4417aa8250f4803d030202ca841c1d640e501d800c1c0c00265012860712142c8007500000605400d5498194020500b0003140c40050000005500c40c42c0950700500b092000300e0741030040081d40300c3c08611020703903000d078006018508040071032440514000103102d9821400c0f64a13100202549800105200c4030700044440c02c1c40c0410900c0c1f27103a15002036105003a134544d03c40d03280c40c0800c0b540808644015002034801c54407482d0561000703010f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978237410 1107 978236303 978236327
    0x901020f0403050a02100e030c0108040f0219080706090518070c170406020f01051003120320031504090c0b0d110703031b0c03090501210606 62
    0x1000d408000d4000755004000a0100f24014414483c2412030f805251051180e0a68216050b030f90000b00c80284100a00c0e02d050b403074895160150106c1e481400081d4040c2500c80c1e0503141e2031410b1808421684400f08441005a030755205442c02800d134020301d9001a0140011080e402c0c0e403250031901b240203480d1140c81070070a80c851b41d0100e900f05260349901000041c5c10403a282c0e04100030398851b0b400800030040703401c000001080c443c101c2e10004001109100c0020407240c001d6009030f6110303680c0701c8011554650140360114651040312021451070700c0c012400001e060a115407070006074000aa140003c1c01e101c1d038403440380c002c10b10040040303484604003070321410f00340054106180304e074500bc1811080e80d010626007035000315001003041141d01b007510210340e0010641c3c8c2194400e08140c001030041c3d601201c2106001400f080109007007100c005003440d801001d615003 = true := by decide +kernel

theorem cover : BRFrame.Cov 978057553 978237410 := by
  have h0 := BRFrame.cov_init 978057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978057553 ≤ n) (h2 : n < 978237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
