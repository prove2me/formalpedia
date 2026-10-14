-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:21:35.080814+00:00
-- url     : https://prove2.me/submissions/8e0df52a-a34a-4994-ae39-25dd0630ef32

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62589931 ≤ n < 62769787 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62591181 1250 62589931 62589941
    0xa0b01030605030f01060e011e06120209061611010311030a02070314030c0301030c0b04050622090e03030405060709050904120302070218060a0b04060c020d0507031a041e080406180504 81
    0x300c04c400820b8803490005810600c01c0164041d9007035032141c0b102c42501d00c1254014a08a9415103407806240240850003c0288a40300503983c2c8002c00050302045001084030005400c0e0203640c005d03d411400e0b1300190152100d0786103071400c01a003000091400411039000c0d105076406031600d40710070025201083c0560b80107640240f07c1103404001002040545c000d100b0290500728900340c2058580300c003150f41c90140d55203007558206105440c03001105110313401c0380200380940c400e0040b01400d0408136160340c000d40d82540e1a00030034001401d40382c029480842150f0002e42917400664030703500ca00c008060711030814001c041d000c0001c000582d68613015400d51164108004000b030510f40f0030400c503450356604c0b0501c1c1807402d001c1000300681243e032400713001e5019611141e0000c1e8901d400e5042c44150b410080255001654a561401c50f80c403000e403190f48500300020340b40104882c00e100c0c420030242e0040c44907108001c1401030501c903c0b520f409030b85001c0c04004c1110b4403400044d043d02c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62592431 1250 62591181 62591203
    0x512190207030216060201060b04030b040f02090a0f1103060a060c06060306050709051003060509061903140d170103050601030305070602120106110d09050f12030c010f050406050603060603060a0b0103060503 91
    0xa48207116500c04484c0c60340c8000700400e02c50000704001440c2c045000c150740541d1001802483d030088c0010140306294807030f514440d6004002c04500d02d841c8510740300802e8a40c0d62085802c0c584450f0604042404007201d009060051148103061310301202160303400c01e840c40c01c40d45c0c5503c5041c0040024014010b1a0240d099511031032072403810f00003072160701038024603202c0070942000c404010766154a102c40303411100c203542003810002403441c2809000c0e11070f400101484500c03c1072017605140803411440d036003403aa9461050b01e544140d0700c85007036030a002c013800c1da03040340c80100002409080180846d9104140141c246101c10000c0c1c040100264001c1c0081000c0c145010310501081c0100c60509000e0f0520104440c101f001091140040340c0c62540114030301c0401d031002c030301c0801c01d03030721950f000c00000c3c400701e6010001c1c2c0015013802da41c01c6420a04140c0071800a140c0460303458403940c400f0300208101c2e079400000c40080c121090400d4181541c500c00400c040d00c00381f1101c8102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62593681 1250 62592431 62592433
    0x4090603030807020610052b06050109051807060810090504050a120906050d02090105040e07051c061421070603090b01060504080703031d0d1101110102030705121902070302 76
    0x440e145007405402d2041c001d10320411504400c040040f070521352a200d405590b801c0d220f03001c3c0f094034405010008a039131000405134107040c04615003040802d420507411f0b200c000c0400d00868540020300407401c0c17005a1031003091f4100754001d11180344500039441d4000001c0c034585158039950211003085420940f03040d00d0540280c035000080c060803a541b003151141910b0030300d40c01460b01c07500034001d010300701c2e103d0160368000035075450603031040043d90b01402c44110018494205003201514640c00100d09842c001c42500f22414004100e00c14101190041960328902000708030070000900400c10000b5040503190402d0303400d41200708604400740c016501c0001d03030030307410342000148054168051401c0020410060060900c0801d240c01201d5041c100301c9217003e182000201c4820b01ca060319904020041c40b05d10034043c441d101d2100080c0c003070301c5942121a0031b0980c5800d030f01c002c4901b400403c00410800c4003421002c0303c03040c0d020001d0344c211000c03100500b14281c00c4c0d0703004550035401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62594931 1250 62593681 62593691
    0xc02030304050c1c0803130b07230301060c0f060623180c1207050c01020d02091c031d040608010507050306011d03060705030c0d0905030307030b0603010b0d0905120409 74
    0x42100c01c001d90b90083c48115941c0c80e004413582e01c0880c90000ca040e00804040002c4042407041103503c2805c0700999104031080c0d5070349801030340180320300058580d805c4032842c0c00041100d09084201264180e40b2507070b41d032200c0c0c0c00e1603444201c415501d21800302c0e001d65580400094550816442d42110031003913921806911490041044082e03030080115000c00c2c0803824007034208100e408072249201c502851035600d0395003500c140c41c1c6018800840c1241d5000140c900301c00d080d664010030309113104550b40c0084c0061402200007045941000501140c1108426140c0010303200f00c9811240c1c0040001c44c0c031170f464030748a46c00e48100742c9651000c0759000c070900c5665038101c2545514034581c4413581ca4100002000250b03500006004002400f200101081c01c20200c03030219642d446001000f40314030091850701554030f60080710404002450710b6041c1b00d1516049040701c0c103d8030703418541e505000700c0742d11b203100034048040100d429209203040d103601c07614902e0240000304450400000e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62596181 1250 62594931 62594933
    0xa0203060c031008070e0f060a0317070309320a12060b040c020a0305190c23010e071805060a17070504050601050f03070f02070503070906090b1021060302040c02030304 74
    0x3d01145507811904035074010803400e220704005122141d9100280c41c0d488200c1d40c442e880031401e981e000d500040d00a00c0c480c0f200141100001c002004014071031395445044a80c0c3d00c04940b4929201d105a40341e0315060210342e0000d88032000c0013504441e00a1694001c142c1c1c40200c440c090015000854806440f038050003103a00d032900c01c54444003101c0c000303040b6440040c0e9000301980700d1a20b104000b01c0c400002402c003188903801400305681d0110822038060708001c0707000b03086407201074080b00d55070821080341804800400c041040b200c0484011500100b40d881240203424000c04c0c0341d401400e80580099003500894800b6000002c44005d0f10080d81400140801e4480052416051010800c45989400c529004580e8440c601d8601340d45c0c101040d4104a00b4000d081d071089a1510541c070000c40d0081140c1d000c1c004135041a0000c03c29240200c0500002c00c1f2060896008107081d806401c4200c8401541d80d40c14802030140015210780360340c0001c0454086c0c00ba0713580181d01c00b00c1000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62597431 1250 62596181 62596201
    0x305010612031b080906071b051e09041103060403050a030f02030402060706021303020603100e0105030c061e07050a060603020906010806060a0c05010e01020408010b190602030301060f020a0203060c03 88
    0x5026240304011600d141d98a01410f03c001c1e00c0710404003036100484060a00c0314100503640b0310903000780010f6507041c0c03501f40780c100d01c403031120116884280c2e10000186464a10180c01c4008129a481100a80520104800410300500988014400340c5256001c3d40c0c0070720070507120300c3c425140c854440407030792001800c03070340703103a00480c074083c0304200340310144c4c1d1203800707440e4141d030300c1040540d8458990f810a41200e8056200130f4008070044144950410101f8a007001d883c007401000c03255a0342d0f40f04040d641c1d0381e252440c0e500304104001280d9000b48100d806c6500558000c2c0c141d10b40f03030300d582d51189080c2c1a9401078039401d07034601c0180304503d020078030710b80c00010920b000c020f20300302503000402c2d600c2540541028004120740150030404c1c00e4014030000606c00e030085440380e5503411401c1c080e200c3e00403c24821488260190b1100c070300b90302c8800030ba400316801503040da824590103955103c207401d030705c1c0294841e05e40f150005035000c100c0b40e41b08100d408125a201c0c20300054031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62598681 1250 62597431 62597441
    0x705100c03170606071104020d05040c090c02010b1302130803070606060e030606221401090506040b15030106140c100b010905040e100f06080601080105040201080c07030e010e0103150f030501 84
    0x31401c1c40b1010148081c5645a2050360030254100c0782c071406003a21540000d009100315807038489882c0c05c3c1000c1101b40900d1054807030844003e0002848880c0213000300300d00704c030f42050846606c01101d0181e880d03e50402d0707014040e440c3c03100961030360750750b119101c203440c5402408046a8064803280c040c000d00d45d000c011250849025002090541003413070010711916410345500f800182c40300402c114400341a00302140c1c0010381c15080c4884c2d61204000000b40070110b41c07035401070303043c010a090142021050603c000c46070444407130450b401e01d003044a40d42122003800210030014091503420f807a040c01800c00300000001e0002c2d40c240c4150015100c84107617402a0f100324500340032085414408030b88064550702c1010b00181140450a20000a040036041383d0414405d482c00420510015840304c2d00541c001d80707031500143c1d0344140d02e10f601e00c186000140007510341c014060455010b140700a10f419414100800c0c00c45140c031010601100350b034400c94068154110800038860b0030b10803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62599931 1250 62598681 62598707
    0x604050c0108040503090405091002040315050c072004060302090702030304050d0801050604090f0f06060f030b0607020f010f171303230a08090a0215040513061a070201020705100c03 80
    0x11000c00ea02c1c2c5070b151517440c0e0050502040c002d9455400251045105114690403820725001c11034540f0341b24100b83c03111075002c60520300d6041c0303000040340780b4101d500c081c3c3d8911680000504c008100540706981c01c003058282035604203880d2880031006a880340005449856a41d0040d0b849103082d0520a10b0465002044014000f62500522280d03c0e0242100c082d80c02c0301e03001080c1001c10700c04050045c183d4940040240740b8021010800c1640702c02840c070220001c2d40c0500181746544100710851080140095009260854003029940245215031075000302d82030242c0c00069285500d4600901114002c1d0003903101100c4604040d04610300408e580c1c500c07024400e04029030040c041c0d6070300c540070544050007280000540c0d441010000344982e03a501078410f444081c0c06017010140303a0014012035105040070000220540c0052060720100c0300058010103400d0306102c89007000780c0c041c8500340e04500500d50042600d80750725165460303440141c0d030780b01000301050170010110590908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62601181 1250 62599931 62599937
    0x8071403040b030f060a062a0203060a090308010b0313060905160b0a0f0c050c0f030f120a03050c07020a29030c031503070303020d0807093201020a02060304060f06080f0604050c01 79
    0xf4009154002c4801c1c43e807105c1d04441414211009050300b040c8c000c6240001d40c18844d05040200100480e040030700141d20036282c0c183c150741c035007404080c4d074081100d0110089030401e20020102d0865009080182d001b8025620071401c40702d10750000315556008848001000a000600070394000a40f10182c541480c02d100ca2a8050b070750140c43d00d051214880c403400035402d10649a54080c00001210014002150b2801c5040041070450b0b0300218001800f180c60080010895440c0c0c0044801007075005000c9814242081070ba0b00305084600801c580101c80740d04004400035561004500170000c01a85503182e00c0e014144112100700c0340641c0c2c1c001e0300004401c000194001861085080d1241056021a80d82c0c1070100c03504600d9a100b4510301c9083c2041031001e000050018810030045e1107459181131058005aa4403030641c000250050b40820019000c03400550100043d0051032001103246555091080c0c80d0405003440c0a42d241c11100074042084010003240d91804002c0c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62602431 1250 62601181 62601199
    0x50607020f0f060415020105090705010905010c060507090b0706051603061802031f030f03020c030718020f0c071503050901140601030b0d020a1415030c040308071403040b030f06 78
    0x5408201c4002002500d90300401400000289654034041500d0151408000306100c101007080f0080c00703040203640c0e401540c041c10f880410700354402d003072482c00e0b210182c480340002d4899555880041c50f004203005c0411441140210f1005c600400070120303240070b841d000c501da00341107820065003611150180107040c90304070104640080035603940c8104440820061300e80d40c07030080120204960b01d83c208680c1c0f84055000c020044d071a425607144074000e508640e20b01007100141941d038a680d0059130f4140300503051100070b50f1000e0b001031503404144003001e41807045a1219610300600740d00020800d0303104540741d28115a0501c43d0544c8140500020300c000165030802c540d200303030007500c1c080c10140c8a99644405407124204a4041036000d041c00e51019643d02c4602808040d40804500c40c2c044040750103c90743c400300580340548048a032680c500b514550718005c05900c419400c40c1e00c01500050389030780ba54140050001030000c0d2401559924000e07001c0040c00c480285094820300c4c0507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62603681 1250 62602431 62602433
    0x213090603030e150f120108010f0e03090f060d060608090f160e070c02030601030b09010b0604030c050d0f080c16050301051b03090a050316111206070305040606090e0c0901050607 79
    0x3203240100d00010703135600045200042132001c3d68440d0342160700f001900041d1501035040c14820890486406a00130444081840d1190041e2a1713440e00c0000c1c00d41c41840a0f10a030300e0812810504020f0040c81c0520f00070508640300161542c55105001007851082001104101400701d07045006030f041c0580b0008200100d004841f454171f000711054a1091000a80454051000309030b4441c0c006084560755a502d00d0315001c14074080300c4982d0f1550801c05520380c9401c20001395002e403a4401448201d21f410007041c400c00700490f4a0035a01200b401c0d14440205220200926007000050003034682d03154000403050882c0d480754010f5010713a241004100c0d882412040a54807440709021040d40d0b0f03210440914038045030006c002d0042c1c04001000c2b05842003446005004501c100303070780792110f4020002c05c4502c849528801b002f80d00700c00c0011b41003e05c00e40c0101d501c00d200b402d00145403030b1a002c95038100c070340c800c4031224958801080c0019501d0044440d90062204807085031030b0001c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62604931 1250 62603681 62603687
    0x5030604150203100506131505070c0504051b0307020d02060609010e0a200d02030402040e0a05030403060908070c03050d021006050d08071110050d200a0e0301061503021309060303 79
    0x1481c10701107202603020001c10312021000c1c21074402040020403881e02c41101596840c192030191055989404100c00c42110381d0303004606403860240c01045291303426261009010113494001c0000c03000181e048185000004103202440c05244181e0040c101060341c1400030340b400c8405040c0c1032140c0480d1004000078000003041303e91040855002154100c14a00020088071126640100149000c580c02c003060030b003507000e144520f008a8062040b03c0240c09040e4662080d41c102038a00c0d0420013081c0003040041c0c10141d0701d10300c602c509904e04082038030703960701d60289071f0422292a008040c425044c0e650400032500c0c6c9010904c001c1001600d000c0c00908181d0400750001c00c00c1201142503024056034180d44400b158015045440d1000041402042988282075a013082032a0041c24060f0600d80900840d90f5505081e120f0704e000a415001d80300c80014000c2c03079600d59220a000700720000109013202459449440258541d040029440410200303500400c801c4e500d4aa000c00c04254 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62606181 1250 62604931 62604953
    0x8040902120f090307210e0306191d06070c0f080301060c030206060a080d0f050d02031006090b090307090f0207060f1b03051306020c07080a11010306050f090a0b06041d04030905030604 81
    0x2044000d0503041c4001100c007a00c1002c0c7c0e200306c9035454040c03101004000368052000e40741d201041c40c000c100030040102d440030410307010520242e050340602c00080040e4045c5000c046098001d05d40f5003042c10450755010603aa100741c002c400022000380303102040640400800340c1100d0221a140019820040501e1b5501c1c2040310300e030100011804980d0401c1d004e03104075541f40b0091001036542c1e103000c0d2110107503803850b4468100000e41101001500c00000c005542071054004d0141c0081440c080745039000c0e00740780c00603000e890750810040f0300003111031050060f1801955408030b00340c145240c095208926042500301494180030400c401289540d10f41000300354003980042e200d46a54407100e20740007807504107418612070b4614032014484040b01d070145140c0b090f42d05001aa1703c6d1414000c134901282c00250300510007401241950189400195002c0d10142266040694480b03840003040c08010308160300c240303190184000d050703000d02ea000103003205400502190401e9074400c16290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62607431 1250 62606181 62606213
    0x3060903120b01300e0703050f0f060903090607080405030f070906050d0203071203110a11031c1d011b03050903070506030c0d200304150609060602150408040902120f090307 76
    0x48050220b040e080c04c0700c2c0d4010708a213440c1c00e003120340c0213480f41380180d07550719103190b9069644a40342c2c2003001200d0000710703103100c0d4048801940c100f50040050000581040314111090001400040fa49850802480d541d101083e4020a030851600088104031a0142c00a034051400741c403091025031070010341081103401341d054044500441d42412924208040d52440090040d1000402070007021201c40d88078460440c01d6402c1e8107031840d07d8030181d43c40d40e00364134081281c40a05540700408c1d01d400e2200c0c03e034103041c40707481e400ba142c1c101141082d060404602141011810b445242001c0000b00c01800c01900c10600e0350070b101041181900440c58558130365a142c19030014404851030704201c1400d07950642a0f143e007031138079011360060003000301101e0701443c1c00d000003020810f0740100001c89005402a00d50402e00403001e284403000180b00b910a15000c000014888401d8402000e8402d1110b181c4407039820300c248000c06211001c0c0071048146d000340301a1010900715a0415664 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62608681 1250 62607431 62607497
    0xe0f011b06020c0a030507050d05190f0212030106030c0e06030618090a0203070308030a051003020f01050a03110a05070b0106031109090405190602030115080c030c1303060903120b01 80
    0x32980340d14080010303108250a402450007410220820150490007802030395200348262000321110800440301e030700403000b0300c02d011551607445840007400b5480500c2c4141385031050315007402d01d80f00000c003107070300070b900080005c0e46d280800c5074416845000741c01c0f0200c1c201d800920310b007000c0d400140d0101042c0d15442c103060450002c070700840c07003c000010340c050340035003594400ba6480c1000865600b08a480300030046c01c20000621305080c2600c0744050360341c000c20014101c0d90075001104c0580140101d1070601d0313541e0161601c1c0340341e90380107401407a903640c0d2096540c041d035140400d000c440682c010818103051140ea0340700d103170081055500c155801d551401059865041080c80c080481002c04038003000b0740700190038070040d500218165221108080c00040b0000e504503552001281d288034610024000f003140400001d005080380b00725803220440796034030b03522600112090034030301710045035200c9c801050b5400306010b191140102424a9100c03030720311501a4054001c01020200700c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62609931 1250 62608681 62608727
    0xf09180203090a050601060c0605130302060c0d020d0501080303060414070207050402090105040902030f090d02070501080a0b0102070509130b06010309150c1209050f0c06030712050601051204120e0f01 88
    0x1c0c2c200030400020107940002c01c07a41656034072000604107500191065071040d003040009141d200340f5030b1084603030642c1a0300038045552003100c0a54241c1201c071032154101e4081040746281c2085d4020f850281c18290003075903503030130410f0400c0304071051884580c0360400071b04108000c294011851200301c620585016a0320b4400c100100c81d240300351340210700818800300511a00d90360000b03868cc03248011000b110314103101110182e9842c002d504c00c080c0060311078800540d001c11542c00020a00300180111503186880e400041d80c144400c03283d039848014040400d07400d202803c5100c542080087c2410401e0b42907c1c1c1750040d030580800d2080b910320b52224880c002031031181c142401e112002e00401c2143c60300c1450703c66210445460f0291782c0744140c429140844c6040800c030380c0220156251408540703a04800d0700040c02000340750300c0c18014144240a448000210b0061040344251309401039481540006005078071900d407a02d001d401f50111400240c0d030807400c4018404034512070501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62611181 1250 62609931 62609941
    0x20102071403031b1006080708070303030e160b03090706030513080a090b0a020a050709050708010302090c040803030705030106021b1516050f0309130b0f040b0402090306010e01060f09180203 84
    0x101d103114a04111850420003d0750341a40500030a40300c0b0300c0d1200801c21b114203555030b4403056941c98640a441c1d09508903000400004c1d0090f4450503042e07040303000343c40d0001c0b4410414000d2011a07804030b100c1100000400040c0002031000c14050282418200261b05040004401d419025440113240100005402d10014000d148000080240d4580e2a135200103040703000391544075003441141c0da4442c60783e0100d100c1c40d0501a0b42e00c110318540d80c81c840c580ca550200914520702519100e40c407a01048040b440520a00c0103603c614095221070360f9a51402c3d000a01e4030141104000c10322655543d003d60703c2e900d510002d10a54044592541c5a080b4030060000d02da1588800030b05603c1101182c070040200071001d841d070403004540141817002000a500181d810f0000d0859221200c0b00c0c6041091401c2e5100b020701c44400781006041c440300202003458258281c124104a82210004200a40c1d008000c3c1550007041c0c80c041d151907250002a02c0e40c10414120a8850303500800065 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62612431 1250 62611181 62611183
    0x3110105070209100f06020105060310090f0807080405100c02030c12070f240813080a030f050a1409190f03261005041a1e04060602060906090109020102071403 70
    0x740307a5540040400c042402e0001d11131821240301e00c070744206490b0401001824078018441c4030f11035180940540413040aa8244800800c84400c044428181e01c1c042d074400703d502079000d0306c1040e115480290340c2d41d080c24104001501ca00c1250000c20071070a4601e00141c80200e201c82e0320310000c1d40d445000401885016040c0070464008507030300140444001841c2d0a01c120725070f90300d503641c0c0d00540031143c1e1400454076030008032041404030310001c485400282c4c03802c009101e2464140340025081000000030000d4900c140e8800520944030003492002d08140001140c02040141c0102100c0141c0b941c4030b87c02400c2e941c4007400d01800e048218050600820b0b860308440300504020003148007121444903940000d90710070380c0078020f1003004201403e00d0b02c0380140c40043e48120041d540404010022001e0b188007d4100c1020b10f401460000c0e1035034090040074001503000303405203107040f00400b403600e103004106c0c0700d440e8105000d500150360007281e0b0800fa00c0c20780c401c1c1005207104001007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62613681 1250 62612431 62612437
    0x3090d020406080a030216060c03021c03061a1902030a0c0f05010f23010515040b09031609020a08100f0e041e060504150509101d070807030209010803040b030103110105 74
    0x81c1803c1e008903e160005c0560200300c4506001c401540d101890b900c52508030b42c49210100001d0144c2c1c1f003411107000d6500036084205030304406103400300d24191149a0040c0300744880040202c24040482e03140c60b84840c0d2040981c9200f0a13200450400c800c1e0b034001000c03011908d40141c0340a00c030303070008024441c0030b410a60800174071442c00d10040c4103100780385030303556071250b4030042820078a0008666442c0204004a4003d0700800e5103080c40d081c040743c44042e82c011518207525104d024820041a940d14030404003c02580400588a8484c60405403444100420615451720341c0c41c0c00740b0004805002c0c40059908010f1300c40740c43c2e1344501d00700d0340b1034407030110344100882c03c012120103301203504100d01c601d01c146100b00001c100c40500100346d850980f9002110b800084042c51500c01d15840708800021041c1040d00a0201300c6c440350400205411400d40740e08444014801d608050000d0760040074800e00a524040c600140c1c49418007040c007000b400304040203071480f8260300c035800b5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62614931 1250 62613681 62613689
    0x2100501060e031b0117060d1a01090b040905070e060d060501080304060f022407020a0804090f050c1201050d03090506120106030e0312151207080a0303110a0203090d020406 76
    0x1042256180c54028100e24114000c0a109104007140c407032200d01c884ca03100c200b032801a11901c80b1448034030100e1620500040c141604003c082c1041c1d4041800100c3c0c07102030151100c030f00300350b65062040950685d181d007a411070243d414124407d00080002032003400b1119158080503050b00c4049c000b920072610644007401c481d06000010448260200003007040717512076181c1c1d10b0007201d101816a111f000f0b0391100d11000c846800300009000380c04500907408502481655031051180c0d135450429006504101c2e5045c1d03407800100c01074010361244680080720018482d04000110400c1c0e29051814040ca5010710310100c891001c042c0a6072070480502401406652220303020000c1c0340c22048240318035000642401001d503007402010003180c1c2e030b0803660444c1104541e034907007166141040c540002904a24104000400c6c40824001c0700c0141c0740c400041c013000e580a04008080c2c5040e40400b8004000c00c201c2d601c841c0741c0001c1104c07100e00041c4c41d2080c0081072400014010301107644 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62616181 1250 62614931 62614963
    0x904050114070f030f052802040b0a08090609120d0b04060b04090b0103050601080c0a0c050f01150e010602031306030506131a04050a051b16230d0807050a0f02 70
    0x1c140540e00f80c00140304810200260741c00c0024440e100380070742c2a56401d68040e200c1e040c032001d5400030602410b050741074203250144090b103443d80da044080050b0f0f22000c2c2000c006840c207803d02119100034419190880000001840b009103050800c000911a511900380c0303103030b0381e48207400a94965400c4032000f030031840e40e41500c0e143e882e00107501030103100481c940003a1500700061011340c01045102d000b407a100c950070b402c105e556617055444010100307003981d0910440d1404891500240914403101806c0039241c01c0d01d514212000309a400180c00040a54100b4420b0700c9100381391040f94401c451451402040c0d6460b1040031990101c0721144a50145080040b10b0250004001c414641240700741c4040207180e644036900c0c0103d50090354000d010781c440d000760001507044400502001c006c0d40000030f4030300003240d517548806031900369510b0041c1e00000d103014404505129445100c0d1190501c140700f032406500c010101e100f81c00000c4140211900b58208803407003005060100110b100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62617431 1250 62616181 62616221
    0x201020d08100b12040302012405060d020418060302030d020309030607080c070605070e010f05210c121006110d020c01140f0301290403051911030102070609020a05150909040501 78
    0x640d0185903c3c0701105c040d4007543c2008a80c050010180c210060046201104880114248020090b040d0f1003290800c80541c0c00303020102c1d101c40c00040f40c0341c10b50000c6000289584c6107206050500c0e94108411040d5002072090410980300424050f40c00310051500040310756032940c83c5c0185002d18607001d88000d24140c2003000710f41c1c100d5442004068240c0b555402407070882d40840d080d1240401c0c02c0d00c04d0320f84450354514900c0303c1c100b90340c1042049460604144a400e4003424802017160501e8500c2a41c042c2000a41d030001d80502007070010300b000d0072041d403d001002c6e46d121342d441c682d681002a1080051401c44d82102560008184415007543c5c959680e00304030012005541da01400c91079840304040703454405001c44003129401000b03413420007032900000b90444014002034501c40c00d111000c080f160307400e100400702035100c0c3e000003034001e107540180a00d1018a40040f03016202e081c2c02c20102c83d51090548426075801c9501910f1030f038441c5440b0f0f015000f242c40317071700004d0150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62618681 1250 62617431 62617447
    0x210604091a0a200f03060307080d021011040503030313020f04020c06150301020403051b0105040308030f0708010e011208030c040906080a0512040b03011e0e0106051c0203040201020d08100b 83
    0x342262500604801e1000d0100e8090300f8041010080c10030007078288141c040100710b4039004014003465000398004d040e11038031940c400302182852440341000005810240341d41000000512605084090703100d40c450601d8140300109581e0300c4050b041440c2d400101c2c103c4011903442c084401540ca0000e030095440d0407a20140c6551504240c07a020700d129907a50302c1c40c0c8a03046c14403e40d401c0b00d41010041c800c0c00ca441c140d03e01c00b0307420b2001603410070034104004004503025600031801080308a076809102e20380404014890303881a00440011881c07200100711000400f561224001d8001c590143e59407903030000c00c140751080794086400c0c2c505040700000c1c500c5c004164900100d01030b000303860313107000c54035001c4160313216074003841124080c144011b0000c012440740c00e018003404843c151140c1d98036020b4032414008268014000141c0005030036280c4074800a0035010407441850035400d41c1040d900203521146154550b40401401d03000090103e0b417046240350040504200b11a80c610b01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62619931 1250 62618681 62618723
    0x2107090e0309090603010b030c120c04020f0a0305061002031c1805012a09032306010906080d03050408040302010c021807170609070f20010608010b031221060409 71
    0x180782c007544118000030000f8260704040c040d6103400b060090162000e40d403420100b08401401a86a01040c031440402d00340c0c0d52110b00c0108919070308002c01d15111524080c00400340c90b0300401c0e09004180c060340c941c0d0020380000548640405420603005103545c0300e881c00c0c000b44507880c96448400d444d50401d206114041d03210107000000018001100b104060911620101594005c40011900038081011501c2c0260000326820210010544e40e96480d050601d80701c0282c115511842e605d2034100910082003081040075521406e0a000610703060b1074461441c003803884081d040c00301040d614011555030201c01004107489070b848100e07174100190005d0600d0315180c184207101a64502048041c0b41c1004841e100d43c030240d4a940e101c850340c48045034800144081d041c000801e51610954050080c0140707805803001000010702e0070701d148c1c10103240c81000100202c1c1d5030b02c200401c1002d80d84080301c40d0041841300c00200c0361900c1e0480890700034900003074007904c1d4203c01c081d50840c51030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62621181 1250 62619931 62619937
    0xb16031d041d01051f180f050a151203080606030619090204050a0e040b061519050c0607080705030406092402030609010b04080d0c05010e03030c04081207022107090e03 74
    0x1c01c400800045ea100c0e103911440713122000680200c1d1091103004c10180741c21304e02d48001ca415003503010501d00e0406082000b5694166180c2403400c0c4c451b208000306c540840000c800600e11181e480390309000750b807400741c8080000781001d8000c0c01c0010008078282c580302d551b101420491000601155560151000290014054988a410261400030300407000e010464011070300b0000000e050788520003045814070300078030140489001400140180c030005046000d244041e0f03113809a54403030152030346080c0000200381a00340524401840311041d07100701501d50166201c00d001800a02034208182c006030901c0c1019825070702014491040c024030b402031401400c060701c404045980302c1c5500103440c06140510516940540e8a040d040740c41003606165060080303000103880ca000003492821680101d0310326039941c40000d810800046c007048818271112031000c549080100da85e0000301c0e482d01d00050b88810b00d4610f01c0503a0200d000340001c40045c44801c0302008140300c614030309a1250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62622431 1250 62621181 62621231
    0x22020d32010b0f04020310180b18010f03030507050a0507090903020c0301050103150b06160b1008010902060409020a12060303030e190f021c050f030409060b16031d04 73
    0x4941804610106014099802e0302c0d04000c2c45a40300785126400d200080d0802400c0d084241190440042d54014400b40171081210024000c100da1125109022002c0592841d208005451000400045d814105070005580c0e042c504555900701c03e060003850152040703000b0f48540100d401c002511001580019082031013034003500c980c403110400701801c88d4400d110140000c1c3e031360440c0c600750049a85c0902901c490040c101c50030030100d1000c5a603044112142120824150700600295005901c2c650009001c0726000348115042075000c9540c5005602c2024201500800c3d0903030114003403106009201703041c0303800f0440e03550303282801005002180110300c25401001c200b040081e280304415140e01d40c028108000c1c540c003960030b0209148a21541c000c81c0080004a0f1340000d0090103200b051101c2140119100c500b401100c50486840e03510690000c2010840e21300c0d1226800c1c0051109501424080c10010010000d01d4008440c44c141942c06440c1c01e168460b9a40d15041081180c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62623681 1250 62622431 62622503
    0x708041103060f070e01051c02030a0e07030c05010302031512150703020405030717030415080114010806090412020f0709020408010c0e010507080306010306050d060911060322020d 79
    0x4040c0e01050540301c0070180c03070b062202c2e601000001c6140d4040c520300f00034640c061503c03501d81141c0c00003401f088522040465000c503000030620030300071701500400c104040010090300000707146564802c0d03088014454503040c55004000104040705552805090f86005054010010100d80e43e803900d880c00501e031540e5200301480841c0741c0c280300c0d1096809070741d006402400c4542c2481c295142c01076003a410b1420300c1c84200000f249005404500c00c103446251384803003050b541001180015400f1200700c85040004031804c011140d5240da039856005500301c000728038043e8414204906255216022552512808a00041c01c043c10343c010300813a5110303402000b40481d41e480440d010381030079188070700041040c00004081604440110f80003a0705040c00a4002e9036a030214842080312981501e00344e81da220f0210900c2a48200041d5540c0f040f651280b540c40d00702d4036600903002040110a0034800c0030552811074031903040c85400305400880300e0b81083e42076040c40002002480800c841 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62624931 1250 62623681 62623703
    0xf131406042a1412121c020f180d02030105240d02010203041505160f02040b030604021309050307050a050c010908030f07031103090a0b0d140105060706180b070804 72
    0x120104100300c1c0342c40c501902210a400d00c0e00d44410700f14000c83c8451948040641010040404208011410580501c8942d6290f051180f5680313800311461241d500c030700d401088070071a004132034000c071401f50b031407501a2aa10340340f0038040760b002c1c05003190003174041d86490240728808800b0114411080c1160600b8541404141c0c04d0220500301c0c0c640080c0540e00c1408144580d2203a002d004000d00b07900e240080c107184401c502600e484125131400c1d6a00f1480072841030546c24140030352090081e09070020401420b1950104a01a8603c912030001c01d0b07403000018100001030044495482e0440100d8407070303440d0390a005850341d50030349546000c589103550004204c4008001c0c4d41048a9000c002c0342444840e440c240d405e80140c0800d0000b42c001040600a0b9640d040c0824014065000c14030b03454100c5854203504440380403c0e004407481500d001000a903882ca81210110390744030001141c0314400724141010301405000040402148804102c845a400500d0318030443c0034443c4009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62626181 1250 62624931 62624963
    0x2010b1203130303030507020f010c0509040f0213060e0d0c0e0105040501210807020a0503060906090f010207050304180605060d02090406060309020d0222020403050705130b01080f13140604 83
    0x340d00e100300c0190341d482102ca0760040020038000d9020743d5101a107030041d030b0113142e407102c200c034211440f4008441c04207101003140c6044e428144501901d9400880046103802c64131030718448008205e00c5100100020700501320160b8580740d800d0504540d12800c01000140c55003400342d141c10090042c00d000700d1034600001080540f02a450007030b1440074024005003022074a944c801980102c50a80c1c00100c04c100009240c0c034100b0469104003220f0000d8502410940040c5007001d10003030105496038018000000410404001c0710201e828114403540c2070204450068007a18055105039444000400c002003000f815030005c2c44450303011a801c1200c1d5450b81400d504650000308042d42040c0e01a040c1340060070712610301c150442c280419204045007540c07055041c4c0c0d000d50030448107500507030303820003003030030007241c0c0f24032510142c0e02c1480f114404000003001c000d0000c18280d920311642c1b020650301e4400a039103500b01c0fa0041080f0307800e2080001c60540c0e604c015030701290a8a002c3c62480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62627431 1250 62626181 62626183
    0x6062115020a0522030c080f061b04052e020a1205040e0a0203040221070302041409060f13150911040902060a0c06020c0304030f020108010f0b1c020903070602010b12 73
    0x66190b051540b14141480c860020040c00c80b00c0d65110304520700d07201c000100c0460421298500240541c000401c02604560a0241480406411010b0089030080207000e00e00030703981901d080d103405880307007500007400c20508844405851050002d40300c8858800680a502186503401d440c0a8541000c0005401808440a09c668400e142640c40b24401141c4500000d4000b0354005000604005040755502103000a003807140c0008510313540481790030000c508040c0101d264817001900812142e1804500c0140c0b118401000c501c040c030600000510503a01e10f80b2003818607600185603100d240c0c0004809002031081071000c0d0b41c00441c80102201614050160b0039219902070035250400303d04880940d090322000304101e80243d001e1052b004688410406840114064180510741440d1030002400c0749006800034003440c585078001344a007075011011900402000310300005004032a201e08402402a000a103525000d00302d800282c107541500719401110301118140403155a0911036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62628681 1250 62627431 62627437
    0x1e03070b0f0c0f0711031006091401030218180304060503180109170309010b120105070306050603040b0609070507210923061809010b040816030b040209040606211502 73
    0x80c026010030004030070000f40c0800a440320364499030496142480c4c020000707040112584004030300d00d98480081001e0b07804d0340503e512290344806e803503240354195004242c0c0101c0d10320102c100ca584441c04116901454084110030001b000c0503030780c880342c0b1550002c04a40c002e840b400c130f0020503d00600000a010300c06e10502580c02010002400d142c0d88203100c55030001080c00c401550b071031900100700e484480f003d09500440d07100003e034601d0081c80241c1140e24640000e1b015541c24001c000008080800503900700c40121050481656a07260442e100d101d4500c005025090702030800448403140f1a808220b01d6441c1c0720343c8490780e215032400103a0026900c0d00300d0f280e042181c2511030b604000d0010010b01080d1807075841d180c0e00c6d1001081d2170b5002a07100c8180680700240c00c0041d11014000845031110812090b10a1481d6448050454801800181c494039409001c2010811240d2014008145481180d108241c400b130000320b070541034190545142c100c01c5044c0340d00702d03014030032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62629931 1250 62628681 62628691
    0x1312140703031a04060306060305010e03030403121e020a0f03200a03050c070204090b0f0106080c03070f020c1905010206060d2d1502031f0b03060103020c1e03070b0f 73
    0x8554106042a20704030090107034590f20340840b8121100c140625122806260051030144501207205440c6240c1203007180c4100a240e101a04140140000a42c0c06041440d029141034000325640142117440e00601c42c1c110910b8489a10000d404007090341c000e40540175000541e10200b02c171210003009020110458003100a00d40800c1000508150180d404660041d0507404082c0c101a03256010604403044040165001c80a0700100b01c041c0f05401e400318054070407842c0c0f9144031b00340810070100d10b00016107110f0a00200d01c0001c0c212602c204009201c3c240000c0076040e0900140c01c1004084409004081c014095100007035843e06041c4440c03114940d0055002c0305221403000340d42c0c503610030340092052000c3d6400c41c41d004200c040142c00c855425030500186d076401c000011744982e0140d503e5901030b154520031704100a203070600a81780c1c881800e080141e5104081720180707040022880c0841d07681c0c400500607030130440c0b000000c0c0c44c019202c0c10300c1c61007a440e82da105e10303244281114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62631181 1250 62629931 62629967
    0x3070501050d0903181d13050309040209010302130e1e0906040605061309050705010305060d0b220f0507080d020601120f020103020c033912090a0e1312 67
    0x100718200310545074001c4000344c0c0a4549941101c0c404819500d4000107507101190318030f44400044020302c05c082c0025001a446400072240000c1999201c1e02c0c0d0040c5003032644030303c1e030126583d04564000d07012a51181540c0c07648a030307070540310700d00c2014170f41081c0d036040840b01d4030001418443d004403803501e01803003d00c0d0003040d041d5182c0c1e40d0000604130080c4503a41007407a101da00c80e050056805070861141c8100e0181410f141802e000404840d80100880d05c1109020340520100b0703002d002e2150000e81d4001582d621500c3d05c140c40005001740400100202ca60741048420b0081c041400420b80c1c41004c01d49410050074401280d60344028010b5043e0129000f1282d000182141038000d10700348103040260604420304000b03401c40d00491240f100d040000c151460708048540c400b2012441c8810700712008010100c03000f03503079580c02607180d8204034001510100c20740c0d4200030040101400c9038500c9551901c50034403590300c034111008607451030180441c000340c0b500600c103e07080f00f48220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62632431 1250 62631181 62631187
    0x203040b03150301020c0f0102040e10030f0b10050a0b070501060b070506070c030c020a06081e070e131b170906071403150306071107090203010501090522090317060307050105 77
    0x180c0e6200701c021402000743d415907080080001c03080040c40413403141d014000c00141c84500d0301b40700782410f003030003030010184074501101800018074026003011420b80007050426140d40d103855a411145440e0002e07a44008584400141469000020103285100d20004d005032507480f2802103043c014420000e00d0303600001700181e1240c0c07041c0d240b0340b82c1d54000d160140c0c40b01181c0d00891a0400150031040c00200038004002e10140c000c2803c0b650140303860010001443c020000070030301c05000305034502c2036030703428074492011456410074990300000a90740c00351a559248054444001c0e0701010855550160000c0c4100d4000300b00c4602c01c030081d49484d8074a016040400a6607400108014402d0201442204598404000c424802c480e20b448042c00070a09403402460040d142c0c3c1f0440c01540100b006020030f0f42d1103d404000ca03107060301c00c80c0e80c50400e84105081c0c18081582c041f0703500e2501d00070900785035002980c000c070b0320421149510203844240c01e16480301104d00510380417075810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62633681 1250 62632431 62632441
    0x409020a060c08040504050c0307081302060a0c020f060307030c0908030403030c230f011e0204051513031208100602010504030804030e0a09090f0311060403120203100b16030207060203040b03 84
    0x94000400851281c10420701c0c0a40f04d000040441c0c0c170585001485240110400ac849a04031300c0c0350b508030a501070911428442a030004d5400e1280d5080b00f020003500d02d4400d0110745800a5511030290001c219548901d40034000600801d08444605c000075054030b400035000501104640c01d0b42e4066031907803075548058403000c01e0810b6072140101603600240c402e00d0750201c14000e02e000c0c01e041c81c001003091040038000c508102c03450898240c48603c10841004540d03682a00aa03c000104200d0340c1c072049090804542040c0680c03024000645040080407030590103042c052140d224006168852929040300700e08031541207070000d0203d0b110300b0225011a00698101c031645400800c0300708803946a01c1d2150030786480313010850300c2c03300c00c8400c80101504502c1500c0d500b10080c00500c03481c030b0252001810029003902c608041e9034000085010b0014000c0b22401500c84100c0701c5e90744130a03100300001c5002204d602940140500903012070b102d440801183c0840c0c11001015003103882e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62634931 1250 62633681 62633687
    0x31305090c04150e04090f20031009061d01050412080405030901230406020a060506060906030103061a18100807050a0618050901030f0b060303030c030403051e0309100b0409020a06 79
    0xc9208807814401100700255255a45c1d02a51002d1807050865081401c0103180250705030440703017401c18420500c1c0030b00014039180011700544001c4024804240b04001e820303c03400601807104a80d40c10030b00c0c52441103103a001500020b00440c42106030140d0031012040c12101000140c0f4001c0903a0400c1140400561103100c086508141a07007801415034540c14841005a003d6401100580c01802d952428040c07144100c0b40c0c040c206681c40352510240800045c0350b07100500000700415510441604100304182e01d41d030304c41030302401d80302d2441c10300b03000c100012104945050031240b0250010800d5400800d800040b15000ba104089550a0881c16184415039050f905800704241c43d00049030359444041034003d50042d2240d41e50b41e00c41c2d0408441840303004000ea40640d100700144620000103000302c81e031180d0580f03401d580300d540c0c0e25801100184162000103440901009200d0343c0c070700100707810b000640d4054040020350941e6050200783c0b5072028000c2e43c0000881300801c20640 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62636181 1250 62634931 62634959
    0xe040b070f2c09090717031201030201270b04050f1806130207060c110d1106060609030f0703210305060d0b07020708010204150f08060904080901030e010905031305090c04 75
    0x40c01c1103a80408144500120780d80c804202e413040b4065001c8601003040d414030062094006880c0c101039440c2c405411241c424688040c480241004034032124082d00201c8072840d0318412900c24000344070103030b4806042a0720f400c0350042c9446008154021819444c003040c0880407034900d040398a00341d41c0e0f54001c11400a20b2310641800054082010b1300c0010090b2240200e01c041c0c984526540140c1c56041c1c0389813501d20140c0384184803d048a11100b01000a581e80c1d001e60102c6800350307100c20403004a0b00b42010031001c4442c91007611404400c1052101141d051108039051080107040c107014224182d5206a5100740c00940d0f00d940341c0080355030300a0381c540c842801e004480429035602e0301d03182264004d030300caa41034528420604030f100d507100400c101c002420307141c09040d904041000407034030320025100405000d000541580c3d85c0c2d00130f42003991542d80210003000300d40d00038205941c0700e80c0924880ca4904e4150340b000b00d01c624014210500503d808111541400d00340268036034205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62637431 1250 62636181 62636237
    0x14090a0c0c080c0a0b090a08040905040c030203061608060301020403020a0b0f09031b010201150e2403120903070506070b07080402030109140f1615030504020d020405010e040b070f 79
    0xc980551000041282980208203c2e034006000b0540920f2906158030300304400b800760305854104103d5200460903107010368040d1003003044002081d466515103015600c08a074002034242c0281810803030700845082030078150b190705884410709071b520401014200e12070b6002c025400380354040c003846001030f900c01800f1840851488036181020020010340f40002282c0c591071054150524800196030a0103a4100c3d400e6019002c0c40c82c078145040140d440000401000c00c0c10800c0b0003a0020200c0c5002c1c5094052018080d601d100ca4412252400740c2c0c00203811500900c111074000409081042c203ca0030190406070060040d2112803040b244100003a000743d0b415900c40e0017910204180d003145c0ca14480c10140103010501c1c103103012030f0802c0d6051a90002c20b01a07000d04216140c0b4410101190b506285000101c554407031000404040d020040617421628100012440041411102d8090b60182005e0096680d80d500d0844a040c44d1850003800039254440c0329480d80c0c02c021003d0301d04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62638681 1250 62637431 62637437
    0xc0a08030a050d0f0906050c043312060e0108030a020c030c01020a02060333010e010915030c03110409060303110606012c03060c0405040605090907060f050d0f0606030614090a0c 78
    0x112584a900075a00e00f0b469940d503d00000500b00520402c0412507008000712a4022041c014552040280131080040b0307003050140104841098812533070040c2c026286a124aa5643d40c545491690740e4200101a101500c50012410002d240018064408040c1603004201001136503080c0800d03900094100454501d02442994529a0701e01d18001ba510399a04510f0003610040001085031801d0102241401403010080c030408003010007040a501c3c070340c1030105483c03621070011402060396055150140d1008038020480000c10740003402280d009a44542c152111805883d80302c020540c4d07d02d000c20350b2103550001c444091050480c152000242203020781c0340302000309082c08003c030f03521444070600140a00c40751038540300703520241105580701003070361408100245e5910007a000d42414081c42016100400b8030030b6040710100c000e1081c060000448256000e0040c068034000e88000c02d0402d60082402e11107002c01c41c4900c80000c0c1048c05a40b1060400030007456619035082c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62639931 1250 62638681 62638691
    0x11010f0504091406010e04090302060a05090a0b0f06010801060512060f040212100312020109051005090a02030a1401110c03092404030b160206091b190303020c0a08030a050d0f 77
    0x1940c1110b206140c0c1c0f07041c0c40700380300c0b000d0300e02a00014a24084501001e02c80e0f4988030309800441d034001503c5600c050305c1c5c1000107164503182c09071460a144544024042d1481c0341c200050500c0540007a40200e4081e00c80c00c01a076203072142510b56003d140c01c5030081480e401d000520515102080c20103036440070700018504030b0000c0c84a42d1491044400b15440c4141c50780401c108071141444104cc6842e81c4001c2080c1c54290f500d4640303849603070b203004000a40790030115103150010300442d02d820f5030003812201041020303d441100d64081e540f0315440d55190100102c9015140e50440e00869203c001543c0780581400800c030f10f208140020311000c039000e090f100101c521080040c8080c500801c00c11304a441d152254240f60b40e11500641c0444d0095400e1000c1c0d003000058010348107100341c1040540013a10004540d000e12660b140c402e611709002c000005240e00030404511045041e03440070031083e10ba0070029179901c02c890b480030009604208401c544602c561091400415840700401c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 62641181 1250 62639931 62639939
    0xf24010507150207050f0304180b040209030a150c23070302010b04050109060503060a0911060f09060a03021206090f071b0f0303151e050607030201020c15010611030711010f0504 78
    0x440002d40206038049290700040d04000c1c00010400c079110200410b004500c3c09081030390304070440c801d40c0c07505a007081d19040015240d5032182c0644003440070140072503d141c80e86007481c0b400b403004000300d550a0392901807101400c621a202411010100c0c141e684144091581101e2456100100070b07006c41d543d422013110199100d0081500a001100d00404c525042000b014108000036088011a5180126603800540a00103501d41004200ca00d141c440b00004400801e920031a4100d42d4002000548491b01d04c0d0103501400400842920601980d95210300340007541c80700f52405440200d40301c001620f054810424641d8040c0a8585a00030104a5440442109a00320102d0120392281e000d4070407042807030340d81c50003480d0720418000d224109149079120403070140640c40c010400005c44406050007501260700c168081030490340740d8440c1c903801980d41c000a0168800050314001d01c103002c18000001e40da642c030342089000d0042e80281005451100700001e5803410302c070060100103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 62642431 1250 62641181 62641193
    0x6030a0f11040e0309090c07030c0f080414042a030b0d080a0e0d030f030c0903080c010504060608010b06031503070b0a020d020607050f030703050705040b0a170f24010507 75
    0x1211030348200040145001ca05040000f95020b0a9120009610600c410391180e61605030f030f540c01240e0b1072403050b034840403410101d03004011000080d0088024045800030403100744010700803281c1c824500d514000d04c85080206032040c50110000c4142c25140d0400106011207841520701582d04001030b0104854012a94608643c042603a85450205401d4104d5070000044110510304035221090315507199406049018060307521410580d0b20707003800c2e03141e0b07006000780e05c041d5401030700080e10b5400000d4198042c04048030103d844e5801e1100000b440709050054940d907010040c01a8290399406001801400a040a55501d4410500d000442c020030b40000c1100c0c119a5004d4514a030301d04001918200d00035150400f002410809510111031001c1900e41225491401040355150004100c03210b01541d00031a0750914001500104260003804510b06001040c0039001140d8440740700c003031080400c0710340c1850840319006070385001d00203240088880c4814100103007807800c00d40381c01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 62643681 1250 62642431 62642453
    0x1e02030d3206041b1d010f02071a0d050a02070611090d02040e0304050d0c0806060d020109030312060902040f0806010f080601030f051002032404050c18030c0303070605010f0b03010503031206030a 86
    0x3000802e40d511405c880500d03044034140c80005080c2409a90300d070800b030300250303504c45a108202c01014020305508851001500f100d10110281c0030503c00340c100052420000c1d403007030340d040712000d00d03007194526901e00d44401e4a002180c010050380000c0f8840d000e00010b0610190040c01c00c0c041044085180c2e07890895130316a5900490003c0300d00c50410410520744140a055148101648080040141c7c3c1c02001102035036418685080500f000c078420502138042508008501c60000c513022541400303141407102202d850208550490f61f0b140d10951084210380140041a0006001400400c520728003481d1240d01c610300712407501c41d2a421403012608142e90b440b030119400c00e9074441c801842e03a504881c00104a038104035600740554a1030280c401d007a180102c280380880d00c100e055400340030008940310302600750387e9078200a00e49000288000d000d130540f10004050003151118040042e24181c54000e401189058500580240c88500040c4416410f106103820440041c00d04010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 62644931 1250 62643681 62643731
    0x13060315020c060a0902061602031504060219080603071403030f07050d08070e090402040b36010b0408030d0f11131505090f0d02011e02030d320604 65
    0x5840300c8610141c0c07414540f0241030780c1c50070750801132420f015a450108a03404183e8100c001500a4032510109040011400300180c03001c0701c9000b04030074042140c0051070a84100f01e048400ca880c0b40400781e0f9902d40c01d8803529010380c04030748103100e0381c005042d1854403390300a088904103495802201034941c01044101c1e03064021740440c00c0c446820422136030b088812400c210802c0300088001c42d800110080010703200e0390b00c552640010f43c5800d01142d403004081400075403011902c1340803000050036100c001c4413005040e0000554086480207031000d8a4400300650303c0c2c1724645400385c0291040c000c003404165660703401070700210840703002800b0341c3c80410300c0d1958881c80e200700201c5030345442140d242400000c11808501d13a40d59a41954040400c40e10401444414001201c2440c6201002c0442c171076800008958585c0000c0500042034980c0c40500254021086d0070101d5143d4444201582c140100d0f42c514081c484100954030100c0504002400e03444031240607204040e20351 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 62646181 1250 62644931 62644973
    0xd0209150c06070e010c1506050310021b03030f010311010e100e0102011103090c040f0209040c020a050d021b0103051308030c040f0b0702030606010c0c050a0b030a050a06050a05130603 81
    0x407000038400091052550004060604280b01c00007a4006080d2104041c4020328200c11002c12a80e140070a45c484809000e01038210390818031020a0840258004076242250f2951105a0f01c000326000007224408c2c43e829212400741e074078590300c420600d010030781c00c54180300240c01c00140a403601c001c1c41d1030201071603443c40061401400064211042c2c001640f00d02041003013005284400043c0e82044100b0035100040c05a82108004000b40150084a43d00600380641004079a50024625056500070001d481841c145070714140d80e100058000031842d4224601c0f40c502c01d6001e40e00040d4410842d00801803076018581d100207a541c800c48203140700000c085414071541d0b0b28016128080e16101281524015450700000d589800c0280340c0c070304200100a1420401210400d40001000060500d01d0600d860b29954030442d002190071043c16403501c00000c249078828080c01007181c4010b0440e90a450410003070041d0301c1542c8141442c4207840302e40000001c3c01d0480189c42c41da5103a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 62647431 1250 62646181 62646187
    0x3020d050603010b060414060d0e0105010608160f08040f0b040309140d0c03110a090513061a0a031101091d060a050a060206060105030415090b0907050409080f0d020915 74
    0x2101442180d03009007219000381e00d42010300074142c580703000b201c003030b641042103401e640340c83c0000248030b43c0b082454500e00d1505151100d044010150802416503030541c03150413184d035802d892000c94088091002002502c060481c0358003034000c4070441d4105028228030411542e5540360082e01d507000f52400ca000566444080150801081200d1411f581c02c1ba801407000881d6145c0d00c1400c10180009820351078182892281a41c901005c10005c1521100c03c0c0710500e06048903032440501c41405582460404200540865200403000301501006294000e6241183c84648640340140c4043c1d05119401c0f902048400342c42c81813031361118200c0c01d031f031065241070414082a040302c0c5e07000c103024600b40c0d0b07030510029402042040e4454402e103040c1d40c0702d40c2c4504005110540c0401e001d1441880d240c840c0007800b0a500b0040d1041c0c40c0d05c1c080b20080f96580c0140000c661010300c2c050003141042c0070003070300301e58103000400c41034003280340250520140100040f0710714600600c401102c2000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 62648681 1250 62647431 62647447
    0x3220f05010c0c12020f06010e0c28020c010c0b0727080c100201060803040608040503130602010504060e030310030b06030f061303030e1216060f050703020c0c0901061b050a050604030302 82
    0x6401306600300c540342c3c809002901c0e10b500e000380c1c0e1010180260075110800100150009100b0b005a8070b4640030840710030101c80456610f9061595030520070401802031000c4105607500a040c00400c03107a2161900ca0103540704402201c20780c0e05440050240c101040c1d462201031400380c01e00c400f40c2070150141c9100ea140c0020444800902c2d0815425039041003010011900084142c0303003203894600341031640750360386d1400c00c1c1184aa00c03014090001084004200c107a4158042d43c800c034403550f4104000203103e100b4036138a02003110019504082100140700048110800503085400078048030410000000a20f042904c02c4510014800f40e82005105050341400b40106007800c2c180600541084846410040e1003991a81ca04041d45000c0000030402c10f50b0081c1480300f4084020802420152402006940241c4010165104000c000445480c2c011716841c129080f64544030040030015201d002c460040410542c0c060051036020008594103120340c600c41e51199038010303070b201d000f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 62649931 1250 62648681 62648693
    0xe100f14010e040b041403070b16111b1315060c02030607030c0c0b04030c050f01060510030209090121050102070f06061205060a020c0c130213080303220f05010c0c 72
    0x5902c1154140380d00300621001c14901088260025080441e48139010b808500300d40c510b01c6100001031407449460108052140806080d020442e020760320b9030f1680000c1c848540c2d4800d030b520401c080300f00000705030203541c1c900350050707000c140910300300807624409901c0034107032000070390b170080c0041a0380110725021440d0910896511001c10f0400b00404911038400130b06445400800410100c1c0102c04901454064450181615484001c85460500e0b046495011306428440c1d2400346941100c0344103c00d00900903240c0c0101c016080c0451a8640b8009a0340000300c00d4102c2d1000d108580e840d030104500380002e203d100d00911820a42208528010084811940c009480440c0c0350a414002490111707060707400c140e62480c00b50301c4640c40300d009400c00c022141d40e00d038015000c1001a00d1390402d900a0904011502c905a5810342e0300c00140ba00d170f11048500c02890300fa03d441646905041803480000c40b4040d00032800b003401e80b07a0f2603908454075a40400c020440c01c038407030320801c94 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 62651181 1250 62649931 62649971
    0x2010b030a0f110612040204110706090501090308100e0a050c0702060c0105100e0702060708060109150e10090503070303110313030f0b090d050708031308070b010608090a020a06030e100f 82
    0x501544d200f4900414000c0d00701602c503010784003c0c03140e034a4400c1d0071031101d501401e4840081e045481003200c000d940ca0000e000300040d0000700c001c60392400004124100500c44502200c084810441143d981c410100009090040196401150902c030b81c0d800768540b500a80102165403000041c03908001481e8010481668010f50001085000304420310398041001a00080d050500708929210400180c9098031182c000141a42d81540080815980000900c0301000103440d0341d6000300200340101e80d40c001e913020305178041e800300b501000000d00c40c820f0b510140b1640403d0f64144907441c44005c841c407101794015640e4412820b00041848034440c5480d801c020000014004207103510750183c541d000ba0040504100c0b004000500350411914803115807550000c0441d64420300d5141140681030207000e40c0001910150005120450010300e60300510f80003031105000c0d078600b80c011030240600c407808003524044c40d2940c8c05052a24021480541f40c6268081040ca0345003020000c100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62652431 1250 62651181 62651213
    0x60504020a0905040b01030b03010f2012011a0c0d030203041b14060d0615051c05060d06020d1803021b090408040510090332031e0a02010b030a0f 64
    0x500c100444410303a604440d40800326881943c020030160720040050303004002c010011600755080c4111700b6001481580b11428500c0c1440070070501c120b001c0ca0040b0340c2d000e021880e5103414190001170024102e61020300303c41e0140c1c1003032240303401c4030320304500c1c04c1c401d48050003008680c01000744020132035911a6600c8a8881015640601d80341031401042e103031035a20003e01135070b400641c0d80449102c541081c00507000001d1b02c0c10307000c152650014001c1e4022003c4022860528860380040030281c06000c0c01014000d00702c0c1710f03c1070031752158402503000303010040f14982e4440c1150701d0522900d2030448194040d8000d081c450100201c0304c520b1004d000200c92040c03070305130104800260400d050300c00381c89003a00c0c2480705003012601954643e03500d0300081c156581d58501051601c480d00d810305421391007558081c0302f6585100c0269500e020b400814001040342466031900390b01c02d0400f0780652170481c8000700740c07807190802081c10208000c100361141010741c00c6d14810b201e00250840410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 62653681 1250 62652431 62652439
    0x8060103021c0302060a0c1206031b0b0f030103081308060403120e0f03250510020c101a0904110a03050a060b090c04090917160c060e01020c010e030f070b04090605 72
    0x800540e0002e4640c20001d024541c0f0b21f95030305403460b2503880352504410121200604000746d0b03440b800d040c8800038070703440100c03840b4810001c0800c00300d0200c419500c610340d60328036480c2036034215542c1d0150340d0030410308840d180c0d849801c000740794401080711a01450003519440b4031120340b90200030075a40c4981190840740d0205140d00c0396504004104c81c2c200307164036250580c1601200d0f240030100031000c000791072407144020910b814100c81c0c1c014030b001808a401c517540305982c92603550951318019041000d00c4c1c021080442c20741000d00402da805845203515a0203004458000b400003a51a001610541d110301d10b02e6003007112a01c1228840882103e40b41034500d05007030300480c5171190b400f880303c2c025107a61040b01003000100c24000c01c0d140a4052a80303e04400c202403442d134890352400e5030f420004c0707840020084c1c015000280403036010303401b403c034040040b001034400c2c2d030803811400e400d0310416107005181030040c00300c400a045640c030a01d985600c2c00700701e14140c0740710390441407007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 62654931 1250 62653681 62653729
    0xb10050307030e0d0e0105030901021b0706020708070e04060203130b091b0f0906011110090807022d04020a11010e060117030307020a03030515041406040c090e0106030e03070c0806010302 82
    0x344c0341d04407015112981091805640e00d0b43c4072001540a8042c2d52000307401c074102c4c00c10208401d040400d80e581a120b6981c00c80c3c0010f80e549002540c1c0d02d00e188a41514401107038041804948150021940700030325120200c0c103031507180d81c0e4002159088030b010710950081c103204403100040d142c0084039848200c0702001e0506500c00003130312030761011309180d0500030200c0286480364414800d14401410b005c80c10003864081c0c0c100040d142c1c0c0f000303808034452000c036a5940d101110f0602c0c13003407066140406000d245043c1006108c001d500c0074400009000d40c2c0038000303c080f00c0074060b0400b080c51003000707408c06500d080c503100d80c103849451b140d191640061042107030a583c0011401d001d5909460081141e40b203c40030344a50034a2140c0b45500541081c0c01003540c0550a08070502071b21042d01c0030030141603030b92011203c2c00390600408000c81a80070041200074866081100c5440130002541d1520340942da509016000580c06640715800150042081d0314080c40810001e60660110143d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 62656181 1250 62654931 62654953
    0xb0601170108250f03050c090c190320030109090501051b09010e041407020703030207050111030f0a0201320610050a0324091409010b0303030708040201030b10050307030e 75
    0x1882e8a046003000d050f000300780301c80c0d052002e019980c06000b0a5140402548951a801c11940f101001d11125000300c04807400f00b03074030103848801c40303481600343d0404d241c142102c00c00482c0546683c1100a0303a904c04c00c0000141c1000c00340045000349011100050310406500d003032429a480245440d5040e43c0010b12111003080c0c410840d40321800074a40742c02543c101c0d2000800409a00490222041900c0308014401e0b070002030150540e8081d0302201d10081c0d031000119602d601d860340d03170480c98006002c02c05458000602a0050408500000c5140c240f83d0fa511403560f902254481c4125044259104080c60b458480f60b4001006443c8110710920040001c1d28511881ea0715004243d540c0440c0d040321007040c2d04014a91180e110501c01c5140c1d54140c0310060000c5c2801d010861a0110100e16041414032402443e034801502071819682c804c0401c1d901400014020b9051545442d070780382080c0c2c1c41200c1c0d4002c2e5011034592135101e061121004084440480c400c07065603101d1901c0380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 62657431 1250 62656181 62656183
    0x907080c06070605100e090604140d05040314070e090a0b010603020405090630011d0303160809010f06092913200706060302030f01020a050a0f0e09040b0601170108 72
    0xa42c07481d041080418a61103010195a01c40709984c0200034080003042070256050700410341c1401240500c203030446086840780b0554569003005000804a1000c0100b0800500c841c2184620104503201b510f09856903001200f0200e94100d0ba110700070340241c5145000c10041841c1c0034050051450114102403e00000c1980d04c0406416148a4800142c0c401444060000b004a040404006c2c0340410000301c3c54080c007070a4881051040c000258038201c0c004070000043c1d0784100d51801000035200b001d0b8405071440b4802a041204a54907180c548551a00c103000d00d40003008942c0e000140d41c100020005803100c42e0307080c22142d4192012411205503103d50301c012a4a10071400010303c9801c288000014060001030325000ca240800c124050141d10f1b4890030803a4000c0d01960304c2d820088000ea803c0317200b020000000b044080c0804025140b00700848032160f40d0508107044200d01d45000201c0040c804c40e402c48002c00d01d04108012541e000e24a40e601c50600b01d0586d0ad194100071481d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 62658681 1250 62657431 62657437
    0x105010c050109120801080106060305040203031902070b04030b1e0702070504020a03090c0b030108070509040b04110a0302061305040c0c0f0803041b03030c1a0702060424020a0302030907080c06 85
    0x11a0410114540140a11100f940000c1074194094007480062038500381c044c1c00346400b481600301a500c1c103640002e0080c028041c00d446a40d0080140d4a0001c100765400984030504c118042103216079480490184034480040c40036500aa0000134035180100a8501000c841c0c072103914880c040200340101a5000a1400180e0b0801c9501585a142c800030483c000c00e68604080c15402c80640000760510040700114140d070414000e907038015031280c003032015030b800a840080a100300035001602183d2421041c18401d940108015005030781c80e000684650003209064501d0001010104854a014450303c240340c5180e003011400c0310340d00d0300c0711807008070180405400400000000303003c01400b100c0c4c0e42500c0640144184542e522403c00070100c040c0c40508680b51400b58601e00385021410351030718402c89541d401403095a031940c1c0c070b0300303400000020741007010008110310100300307116030003e00752001240e6401a03c82c604030301e04600d0f10703105900c050705a400c40e401d168403c7e1180012 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 62659931 1250 62658681 62658689
    0xb09030d0c0816141207020306130807060911062101060f090314070801020c060a060905010b0d180b071d06030c040501080405070801020d09060b0f0a120501020903060405070f06020303060901 84
    0x201148481e154106001003404d00003100c689801a000c0c0303042c0500c154000b0b45040741c02903044505544c2e400030a1140c2c58546100544104003c0c0280d50008a154100c0c0b0f0805108000c14040000200d0201e202600541d1420219202d485010728000e5051403c0d50300618241c070b031144607080102006405c081d05808054818824071147c04592074080202400820804008540d03072004c8006c10b9407141c8041e6107070f52207503003440390004508200c1c0c0902410f0300e04903088240740c1018141c100004142928000c54014034407074000c0041401305103064883c12143e15041750310a111890303a10140761451403141b1030101803040c4003580c0401e00641d17055400a081c6040d403611503050161904c012507020142560001404200c84401500503507103061191009200024204042062005007225001c0e0007502c9070400300007005c0095801c0c00d211b4021800189003210401c0828180341c41110203441640c02440c08100004080100000074003541c8041c50860074028009643c003c41882 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 62661181 1250 62659931 62659957
    0x9060906220507051302130602030403080901030506010219120e041a0d05030c0303091c0e030607081003080705030c060c0309060106210509010506040f02040503060a0207060603020a0b09030d0c08 86
    0x88041000410040c0c9005040000c1032240c1c20421100c05e00040d61200300c140c8089856803500040c90342c0000140c07000c2d00d60000209c0e007001c0c0c80c403004500405004288a04520599504000c03003480b46401300f100500421540500c0144540080c12075502c0a4840c1d0040c0d1400c44002e0b10003980c9003c045e0b800c3e008440c000009074442c05c00314a10702501130070840c540400810700401d80400100100742e04c071a80c4d030404404406820959640c0016221036405412100000d00414414401d03180e001d6001810886142d440c1e448035940394000d80c0c001c86003a80b00103448031a42c1001c00c50564045169807005246141c24000300c3c2e150781040c41413805001002d030040c0c9245e02e040c034100244c1d400c40ca108000300e01c3d0404c0e90700e01900060300e54500aa142084458100d00c2c64003c039400c0c1e80018008029940340c4480300d1000394000c50050b140c6569410003c80165100e40340c020041111031020b603228040007003007600b0141c201140c01c0c2801003140b4a50300045001c0146e0b445072021070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 62662431 1250 62661181 62661241
    0x230405090f060d140a02011407051c1103070620031012022b030f02060907140f0a030c1e050a050f03010b030f030a03060e0c030610090302040501090509060906 70
    0x900401d0111030403c4000708120246940da514120002803580c080364000d030384450781140c17035510a0300305209040014105030899005e9100c3e000350210300c40900f084501d0200102c03200f00140c5411604400004c441c0c4a40b5001480e61181c4400280f60350451101401071a60514200c5180010481e00c0350207154091340400f80300755070300d803841ca05035903080b1004040f0383c004909940004000805080b404184500d08403c0a1403000131058421031480c801450703624102034200809032003901c2c13100c1e88103801d52412152525000c12600007544a001898482400c000e0701d001164000108944001001007080040340c0e948040c1c0303001c594058400007130b03040209003c40d000d441040c4240760980301d810305100c40b2440010050160424a80d801c10425407561945040c0c80350543e8030114140051003c10f5440c0f0300550050a0142c0c1424044c1c91203540e9400315060340e43c00d9000b01d1180f91b4400400c200c42d00e0034440c00c0e52041ca0100500311a05c0e0600c080054401403180d1503090300150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 62663681 1250 62662431 62662441
    0xf01061e0e0604030b0702101a010c050f0111190c080a1d030703050705010f080f010308130306050c0409060b1c051005060d0c02011413080d0615230405090f 69
    0xc0e0484108020080c050640d0f407903d9051210140c2c0040c0c692600502c01c030741c52503112980318861190382440340110085c0840c0f207800119003d041d411006d440a004c0d61000000d00442440382c0b41219030b1804406854100c12000081e59520700e00c1c009003400100c1b940200014600022114511244c2c01c08008003044c40e583c814041c2c010f00c0032590103108603440441805800560720049a209030f80d04010214212022566041d054034000c441d00580801480080c06401c041c20759112501048074002d5900c0e21030030240e81d030544441000c044001070506c81c2003000e01420b4090031103034000d185001d100c4459401c0300c4c0080040b152885640300c0210b841e05101324411801400c008000d25220419040050700401c4500000300141d8649130107181c09a500c0b0501603c42c000260b44540244010389503083c00e940709944035580c1903914074000c1001d5003000140758642c40640d845501110116403402c0c01c00344132071514002503600b4001000340744d8581d00165030010340070010304095111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 62664931 1250 62663681 62663687
    0x60711060a0c0516031706010e060409020d02070b010e011806031101030f1806060512010b010518040207020a0e1b0309100f090209071701060801030803040206130314150f01061e 78
    0x5070740d101c01a24084402ca1a003070540c008000402d00080d00039221840e00c43c7d600644e1070142180d42c440d000300050004001c100c80542c0600301081c0001005031070210300380e9035201c0303c075400d82006100051a05c010b0100309100d03031080f02c0c0030f803076400100050741c01d68032410700c038005040590b810140c69a031a081011002d40100c9145000d2034250f00c841805480c01c107000d4102405064041c50640802510001d0140031b0030001d140180c403601c0c0307000204142440b0040503c4900c0360451340030444030700140c840b041300c00014540074810b00120300b404c50604003901400041d0b403403008030510074800c0184001c601c0c40702005804c440014032141651620025200185010354803080710020003025035081a488c08116481e090140780c1613880b01d809a81155081c0405001c0c100705000040041c1802c070010000d10030075140c2e80503496035a54448a100c651071074900c1c0b054000b021900065140c0c080102d4001e107034045400c0d525818404020b001c0c03e5400300341c0316070068000c0d0007003c00d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 62666181 1250 62664931 62664937
    0x304060902030a080a030b01020105060a1a03040c0506130501020607020a0c060c0218010920030103170913240509090c060703050c010203100302151305040c0e03011a0102060711060a0c05 82
    0x5440131066031102c2c00c14002400401280442c1d078055401c0c280010b0302494204504000d540c21902130110f48214050486815040108102d5042001c007c010405545000142400011844000940c0740c20140028140304024081d407003503503c452450400030302500c0307510003034501030710300850b10404a000183c190300e0042c0e21003807040b4140c00007140700c00698022501c01c5440710a13107038030500311038a0404180305c24030002c5c080c4c0e908000842c104c1090b2000825482c5401010404500c0c655080d0504a407404a0b014032030a02c4401c040b038100c4104454070009101c2110304218501d0701400036900d40010001c09803191310300003107810805000c0c90503602c04800360070085480c7e2030540307808a800c0c00c25020507486580194411501c14141c030007162a22072801204034001860402444042c1003d40c04c1081481041302d041c0540c0d803000d00c9284000c91105031109680e10404002a0924001034480801c0000e450540105070700009642600915900e0300000da40952070401c8420740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 62667431 1250 62666181 62666183
    0xf02031312120f05090f060106120209011202120105040b06040501021002070804030f08130e090a02040c0203090d060501090b040506010f0e0d02120609100204080a030c150509060a0e060402060304060902030a 91
    0xc1e01d46103d03100260a00d038440d520030804542203e0f29415105946a601c0009115110001d010301203000b11409441c0c01424014006040c00b00303040c0c0034603101c00180d070851050700c4001025a8010000d1b0b01d4540140c0401c0d21080e5409458241040c00007510f1b5442c0c0c0c151200c0468001038044200907036001218000e5802100101c5421020314042c41558040840c2241c159125030000c943d884180321124010042c040050514901507400c1c00080d12110b103a50341580800c2c440794203e91100c0c002e40316154495140002da41d0f05049002c1d080700c0a901d100c0d4000c0d880d0000b000b010380d0300504030854100250034007280e00d0a00c100050542c80702d0440003901b02c0900280b001030000001840e82c020111541070700d010381d20b002031400881c0035501c280c9506034099108000841d0065010701d24650148460b0303155041080e0706001603450940350050320780e100108000122686d0300c2500300a04644000c4d010328201a00000c01c0c40c0005400607000e45e0381c840240003103650410203100e400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 62668681 1250 62667431 62667467
    0x80706020a0203040303020c010203340c1206110304030918090204060603050402040b0409050319050c030307050702010206010e0609010b0a03090605070207090c1e080c130803030a0f02031312 84
    0x71114a80000c0d02c0341c00501c4210090b200e6140708034401d40c008025580c00074624030400100b00505d0101d0100210148001000c004a48048e803010640d1580c95002804901c0040d03040c215640c940f81c012180001000b80800a0500600000070741c0200300e0f03400c43d90141c40c858001901e104034017006050500c4000c1d480ba10b804800541e10741c0503000507105a00031502080b031144080c05200a0706da1000008240d600104100c0100420b07148042c40c00050398940b4504110540c01581d186a00c00c0e500c20001c0761010034000219a4100245809841c0c8000780884905119010500d10001070055804840011a844a00c0c80c840d81c072000000c1c1c0c0041c4148003c1c20700540107902c80c0e40601559040500b403450190350b96000300381c10100c040b50408105040703c46480101c035202c0300a082c000c0d02d5a000c010303c2035801d5249084001400810001d07541d00d05140c000700b030460304241e00300b40d901e0380144100030034a85200b8418041c141c00c10126800744162000031181c441a10481c0040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 62669931 1250 62668681 62668687
    0x7092709152d05090706111608070806012907030521091209030318040603020303040303030e0d0e010c020411040506070c05120a02130902031c020d03151a0708070602 73
    0x2d5612540e4406a6600c110b203826070824042e4402c41d4152a0f007200e00c860103074401002042420710507055487c0704c4444005442038400c4160411000c1c040944c004e24456124071000c0c0b00b10813060000134010702a04518a0121100e0b01444c0656558101002108900030980400345401002280c51081c09035602c483c401c8101e8400c04c1d8645403e4461402500c65a45848a0f41c0c94a03402c07107004503001402035040c40700e881f00341240307000d400c280a40c005e91203013400001a2002c0002e003010318803e813804554410410382051600c40d440c104101003003d09501c050450b40c10040003480c440c2c058501050404122140e070040d0704c01c561059800020001ea0b00e41404003181044059900440300003501001440e0207d03500c0f601300b030b400307035001180e40c2e29027040c400250300502e4803604c05002d84070200c501007800707541035007004400800b58121103034001c81d8560502c1011381c0c20322810b101ea2002410800b80022081c5488203400f810880000c0400c01d100052040d501210750140055603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 62671181 1250 62669931 62669951
    0x103020a031502071202100c0207050120190b040303050702070b040b0706140a0207051203010617070201090b1e070f0503150a03050307113a060902030708060709270915 74
    0x541c80d1003401f0300808039032500810502c454030209002c0c0071104141d441e907030107000c0146c1d8031078a0340c9404c448a41603c200800c080b90951100301400c94203000700800c081521340360401500341e5000416a40031500311071000e000e4840444180c0e01641c04004d55117440d61554545034000b45106907070300004041801c100680d8140030b40042055130f100d0011f40e13403a0941321480a40c240028003c00000c1012080d0b40c200c000d24a40540781c0c041d1151001188840c42525203081c100415142c1c0000020440402042da024441e00b1a81216661400c59030740045400014a00c0c00060300040001c0007043c0b07840603c0d6101407126019603080360660383d403104035140886150030000305075070040880e01c000c2c80f000010101c04244454001000940c500da542c0d1000c401c14502c040c04641c0c1c5541c1e54bc904001da201082000b0180001c00014083c1d4141060007030907121040d0300a41c03007a81d15450100f844c5440e110740003c011140c0f900456600d5542c81c200c030041c0d2007004200c425900d0600400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 62672431 1250 62671181 62671183
    0x1020c0f07090e0102040b0703030e190f0c060c0b04021207030209010e040302060906150603060a0b18130b0607020925030501060806100503130201050c1b0301140103020a031502071202 81
    0x110342c0c1c03001041000015a030781c410b0a078050b9102d4513800c0d103130602544000c0780c005d0b0880040c00710954190340c44404001100f2881000d12402926000880b0b507401040200d0f01344500c004d070400c5c2c02d141c0c0000103207a40313542d00070308010030080c02003005180c07503402c0010802c80300002e9640180f02c41915070b1941078850604000300d8040d001440b4942c0401d842c0000812424050003500318002c3e8051154404d100d1194030140183d034000101890005600b110710000e45544140d02c4500241c2c181000200118402e40200607441246040d21184250b510102107030015541511001081da8846002c03104401032201009003580b8441c9140215a40c1039124034165540f60702c0d01c1400d622080107114003601441241c8000c54010000f182d40c442032501f2501d40288145004c600c3e0404800e2102c1c00d141002c101d0141c000c503500d003000040d150a0007940c2c8402c201e501041480e40c91030b00000d40e00000c5103c007a1060420381c6803c0744414158040710b56164002c0400d40296040031002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 62673681 1250 62672431 62672443
    0xc040e0a0510061203030c05040905070f08090303060a0905100510020d110607080109021e160c171207060b0418030f1d010f1b0807140309090109020c01020c0f 70
    0x715503a0040c505240c104042da84108019100300c141048038075a041d0340c040c2e0041403001000418003006000016204c031190189611911716680d640000c0a42400302400b00007001d091607411707400920400c0030725190400d8102c1121900300700825191520700c10380070780c0f03c0250800384d04442900c0e480684150005940e602d80e8616954103001c2c0c060341d0480380e8640c00103540c0000001c001000400c000e032010b4024000720f81242180c684400240c0d8001161a4000e0a0f500000d4940c18028000c1c400c0e8084800010703c62860070b240400360044000d900c0303040d5200c41c2e9262502c082040000e11142e580700c000030800150041040c0c90030100d1810701d030040080101d0010301c0314031605000c940300c1c11038a040f803e0403058801229024900548024000c0c440000800091148134818013034003051801801e405409100d0b542e41b014100104084013496a086217940304004c0c40c038094403440146411500f414400580300c0c000500a1400783c032448440850511030f40c4600c4540040100741 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 62674931 1250 62673681 62673683
    0x1115060d02011b0f0c0f030503070b04050c030d09091104080304050118030b040503130605071110121410080a0308010e040309030203010212010e0901060e040b060102210a090f08060a09050c040e0a 86
    0x404d88170301e81c0d884401081e1182d5001c000e0868009010a50001d01042d0a40c1d4002d40718001b0389030f803010460003007460145801030141c00170300794200800c050803ca218a03100600d80540c05450542001c9030302d652446607200389410050752001030a804640075010341d02a41d480180001c60b408d0074101203960307400280311081c05c07000035074002505500407002c407070030141e0040d0200d0005001104200b09000c15644a000780414a000300c40092240e2003051000401030380c103525142070420071003030100c00e40d40100e015a03000c0400321000c06e8100265038115841500ca0050303640e00e0389001c031000d842c50740c0700940541c0041081840c680c00140c9280c1aa000500d10300c0340c07aa5031000681c240c40d0544507910f80c6960040c0420080740020b600c3c242e100070107004481401c00c8035180600c046400110f418104040401c1030309404d41d000314108002c10395891032851460030300e03c10b107490f02c1007e8861305413503a0381c0450104008007404454810200100100702c01501e6010b46e0707459501c6200c2c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 62676181 1250 62674931 62674943
    0x1202030c0307030f0e0d02180a0b030f01050f0108030702090103110103110c010504030810120201030504050c0910060e10050405120a0803130b01120c0b03070306030c151115060d02011b0f 82
    0xc8945c034070303007001700300340c61641d80060045426031080d4100b189900405891065016110710554440b51810000000210f02a200000303203458030501410350018107800c132041c983c00800a24000da0f8500503c82c0c1526003124085440510f01401640103051641328100d101c00c010903043d8070200e040d07000d9442503000fa22610780755565080c0d410700d981c00038007417180240804038091000d94441d07441258018442d0b0308545032601094001101e81e00304030303401d404080c146103051103080d5000c80c2c1a880d040c03040d150400150442070019002d8041c070301489000b06404543c81c000513030b04000305031000c0d800034840d030340da410950713040c0070050441e01080e219040030000002e81280214600343c10701d40c01882861030340d8101050400d00e40e002414800c2015102d0b01d020001c10944101800145050704882c41c803140411806060b0110100005080d60800c01c81d0140200c4071920036640114121685400c104047c070060700e5800d11840c848026408203000c01c070810450300d8800c99038901400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 62677431 1250 62676181 62676197
    0xe06010308121503070b0f0d050f04031b020603070809030715050601030606090503030909131e030e0402031b1605030c0a0311061302010c0606180c03050601020a0c031202030c0307030f 81
    0x1503211000b2a44240d4844e4040e03000700410440b400d0b03000080d01500d00308003180b602d094000754919040d40c000f80e8880e245607241005000405402883c42c010f00c901c40a00c0e4810300180d82c0020b416404010303c90010b0102071800503810140a200311381c1a1ba40c4075404125240020030088000c001c120f80c0240803903c0c00c400030074014041e90040c4200c1d14010002c6180545500a204100c0c02c0a04500a01008094884002100403240f10f0503902d258280c140000c80d1401d0082550100c0c9203214003440c41001481811000c160520300c9101c01d44403010b6540410041c0c44501c00070802020744580008103140400d40e8003c00e440d4802d50017a5207000c42c1001c0c52060946550041e224003816014103101c00b801940640607450029020b054005a07c966403460f6109646070b00181d6016640d03108e1500011540500c60960440020320082c200340e08241e560340281246800042e00076a084000303240000d10810494100460410a90b502e856580c81e028210102d01070818010400503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 62678681 1250 62677431 62677441
    0x60402010207050a1a0c190501022502030607030b060d020c160902270307030f0302030a09140117060a082b020c01120c11011503060f0c08070f02010e0601030812 71
    0x4840790054a6a40c1d01c3d50450350031320a000c407080c6d4828602c80c000344c00782d001101908a40111340700c030030b180582d00160b1780300440500c180100c0007141034072141c040303483c0d0700e0405a140000d415500200c14100020b890030b01e00c0025115015803003250900c94000500040d9140011030000c03030410071218464040398a40d0b0914040c1c0c0194400360340fa00c030716400300038428007805080a01402003e4196400781d03171aa241c080200001d40c07400c0d000b60740006548031110350710004603c0205005000e90406c2e07600388000900c207141030b81e003201076a08102d0104505649805d883c60040c460a0212a101030008400c22080a06014182107400c01c1e02a03007551a030000c24040c10000050b5640e0740304244032072080004141d203108680c10084c904801c0d11040d42c09210f50130fa5003d40341510b0300c0c42403030351a0560a035031080c0c041c10841410164040daa03c2c0d0011203150704910942402582025550022801000c2011003c542703841084000014410304600801c80e00740c0007a8154007917586d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 62679931 1250 62678681 62678689
    0xb040303140336010c030b121b01031a060309070509090a03080f07030905070602030c070602030f070311030d0c030902130504030806220203040606060206072c0402070609030206040201020705 84
    0x20440e03d8100c2c00c0080b40c0c21542100b41254800c0e101d00c4450003244103408100c1140d0b00310358801d04590003082d5036421081c080d00c1c3c144070100030f0148090040414071a10242030704e500b0800c00c0d0082c145600c1d0502032250000066201101c1034000c0c01031916850072190341e5555420611581c2e006001102c04203608690106001400715007503100d00049171101d40e4080d00820005140c0d60425075a00384d403900040f024400790700105190f50085486120300d0401a09202843d0307c01400e40d802040a42c8000d40a0750680710201d0301810502080c114200e481400c610413010540b601901d0020442a103130380545c8032482d803500030741c1d94507038126440b0710000031100c013503401801050019002400707602d84034070980b050180c00c1c000944140c6401115070182c3c2c10a503011141640c8440f814829160b0400c003540d03101d0508e1401c1c1d900345030150906007e00712000150039000d890303c070001e450b54413242c0403502016400301007080311035103505000751580c0003610103e00602031400c0000d0303e854 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 62681181 1250 62679931 62679937
    0x20117090a0201080612012d090c090902010306031226040305031504060521060903030c030106110a0c060e090f07050a03180209070206100503030a12090f0c0b04030314 74
    0xc18004120180140c0c0064402600c020080360303014a141c0202d40d40f698080c001c2030100f07180345844844551546907140d000e0706c4c40402540c011803411001d0000310f48420540303000c03912039600000b501e081c3d900048028206640019140070655036120505c50760002c4c00c0010002581c0f240140720000e440c4106e04410141d40181c005042840402c0034085400e0320700001c400010b000080a1340e45030046504a10001e0901c102404407542c0380c04801c009000c107a03440b50704840918510319112140c042180018002d1a0803c0000301d00310761403000030000b607030b844c981182c020340b8519555203008101c11800c1032a14003401013440031410b980099400ca60141c11a40c88060500c00307284c1c0100c0040552003081c0c459080f5000440d8007684485040d5030240140341c2c060b202c64078181020100381182c60748980c0c0a80c2c010011007440d90740c400c00d60a2840000c400208400045040000c50000c41e4200640120100d0400140b009208001001105d101f501c400c503203e40d01c03002c0254240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 62682431 1250 62681181 62681191
    0x90907080c2403070c0b150102060604050601020a1205070c09020315010c0209011806121a1503061311030706052106091501170a090c050d0c06080703060504110403020117 75
    0x181d504401001c2c0001c03a000d150700c0b49042c0380a15100286403203101c1a040161150941e40c0400c402140c0d0b25603042c004140d1010040d02d0500c003d050000000f90341d00100d80300500650456106166260b20600880d10501e0b0082111800e1544864400000798419101c00c208543c034800b04010550064415420207500140012180c2e80f800312281240f801c200300d20b00c05640c0e240b00100d901d200310040b46200c2401800300940c0d14401c0300d940801e82d00c0103002c0c1e40e0160305800b0420f06e550742c0001e02507800f03003c0d1174080186042c145004080311010406a41d414019080003280c010b501070060301e0b41000107011403e0080385002211040f15040d03901c82e0b0004030440c0000c4c0d80b60b9201c49001243c020600d0500425141400c1c460483c0300182c1e80c074030f0301c1074131001c0d60310922200700700c1407015090845818001c00c2c01d40d40c0380b0340b9200d0184103450501000c600018600b170b00a510900c010a0701400c14092541c86079404407240e403080c00201e01203100104040b694030a8030400d18428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 62683681 1250 62682431 62682469
    0x60a1a01030c02061503070306090b011a130308130e04030e0901060f0e04021b070306050415020301060c02010309050c1002030d0c080106020d0309020a0909110102010c02010c050a1d090907080c 85
    0x185c4580258603c842c141d0684c07140c040c880d4071000000a943c81c42203040d454052016006a9410550000000c40d68444044401403050040340398412620f41120f0449911021695840500c5406140112103da00c0501c00c41c0410042005040d002074002a0200080320090016a00c80c0d07002d550001d82c1c40305103400074801113a003182c981001d50041041070503000c3ca003109007493b49138483c6020015081143c2c0030340c48a040c0f00403c522800e141c0341d00c40f400c41d420360466041c0320000b0100741040a000c0d04068a50701d0714418818103122201c103604000c1c0c2005c901101c0c00c1e0010355268040008544401e14040d41181001e20400000e41601c0323844c7c0c0504808516032108402034a00c00d603003a6400101800b00141c8a5294400c1885240c032507040014088000030002e400c640800307440350196414000c45110b002e5110302224983d0b82c05060203d1180700c0002c0100c0c40d42514442c0542100d01d0100f80b051140c00050180700b01c41d402c03801c9540c0c45988805115100320400304d82041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 62684931 1250 62683681 62683693
    0x1270b0304060f0509030a0207050d020d0201031a03070b090901090908040611070b04260a0b0118090501050f1f030f03110a050d0306080709050910051305060a1a01030c02 75
    0x206481200654010703000d40804036a4805450200c8202c420984080c001d590001131281c01090701480a80700406040b99030821158254010882e1403100c458000d040640da810002c0d4240001e100068180038064203d5402d00d40700d08440410703034003000da801e101d042a03400005031340000c3e0050341c103100d81c030131107645c1050303d40784054800e15405ca0710341041e8040d5050100e007400503800039100070100100d81020361806201c21403503000440300083e01039080755600c14046001280c4541c11500c020306c1e40d078503c44100e01e2680040c0603441c40109654200700503c05c0c0e5440745043d6500800201441c00c103030031004054840300c3c0742148001010884000d400d03801190040c2102140c115251064403100c0f003a5a44407820000740e100340c40040f0faa542c81c10b000c140c400304496006803c0d03800c03042000b4145848165070368140705000b9441c0644a8001800300c603043e00111100c0355000040b40c1d410b05154002307501500240f44140440a58400104070540c8030f8010705204c80110303005008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 62686181 1250 62684931 62684939
    0xf0301061211062215110a031206030b01030c030209010e070f0c02010c02030a030206090c06040302060403060f0204051519080408070b0423010510061107121b080c0127 74
    0x251241080000c154005002c1c040607a60380081507007285440c0010f13001e50b0195040002c180c29922800100c031041101e0702114840880303000402201d26901810150321071141c011140010b002141c01c000e108104243c000410801283c116800796442264010341c075a8861000b5a02000e007102d844000481c031440c00407a2500510710099118018505290361823820f401107850841c0c070348801c0300103a008108000314000c013030201e90f143c10000c484003480c2c01d16540016442d0300840c0400303000b0300e9030f80c02c1c0c0501c2481d080e03045500030000038007000d945040482c003081950300301c50700c3d100030390014410042c14180710b100f90318481c9500c00b8a06007007203d40e8654401101008004503010b0021401144128804090010112840100120f240d03e0b100341814800306d0aa400b000500086544080800902140050a8914035258031421078081d051909444d107211983c2c810b040903076640410856000304904000100c00c1e2034140b4220301c2c0d0244070440310080c00305085013040d021000c0c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 62687431 1250 62686181 62686193
    0x40f331b050705060c0a021008060102100509010f060f08010f0b0d0807051f0204090605030703020108070809011517011514100e060a030509070b0a090b090315150f03010612 76
    0x40c5800740148110b034446515407001c28800d07404942480c403e81c0c41032070a6000c6103002020440604a10b04d03100384141450f0300003035030751854040c1c420f403c607854030001540010254002d45101400702c0c001d001031039036464031180c810300e54000c0407407650811640604500c00350091220240d0050107403845d031603a9446c2c51140c1d800000c0200c4040c01401c2074198a0203030381d209190001503d40c001030303480d403030104800100d4035158030003402034104440400160303804c000485d9208005003000411035480750a0301e40101041407464101c0070f040303000800e007007603450b9515101003a800300030010900c4000d240710110b081403140701001c01e0343c1c000810490400c01c88042e42c000070303400c10502c000c1440c00000c3c6d90350018803081c80066926010441142002c01c021002450000100d500e88141c014009146d0105030040c650b40880000d034004454030b04100314500b0340c1d254045007101e800c010f80f843c02103805500070544511041c1071041131500c0e045c4586004c94a1100305540c0120865680d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 62688681 1250 62687431 62687477
    0xa0806060f0d06030606050a06030b09060409051924020306030c12030708040806041a0f06040c050903160e010b1216032c010c0903020306040f020402040f33 69
    0x2080c01c03181c09000d240d00a403014010307000551300c40c48000c580c003401c2105022002506a110500f050302b021484000c540700e41d900c254004009940c0440c00c0100c074180546019408281c042e200600900c651040c007500b03501410708074a00d207010741400318600314030340168041664295415040003008244919100304038014080c03005090300c2c186401c60712900384c0c0f6005503210b035600740c010304204410000071000000c440054002000b1603400c0c550020780c07415200911203406581d4601d004454603004030300f0342e491311400400700c81d040d1a00000c00440c610740e9205419294074118000304280020b42c094462404400f104105217a5501102c2105a8501c010700b2080c1035481c1845103107040b04105800d1100a1540310394050f00640341c106086550b08801c1508100c3d595005100503980800c025400c541c00c044100034641107400000c1c001e21450744003110100d09070500040100541c42040c000110002800701982c2a02c030001014210b20a40c03a000100307401034090301d41c02e0041d50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 62689931 1250 62688681 62688697
    0x50109060303080a1d100603060b0406061704080706020d0e010506060c030d0f060803070507060f1407020402031f0821030c0a08040807020a03230d1b0204090f03050705070b0a080606 80
    0x8404517101c00ca042d003400c0c403500154000400b40c481c075042c0203000302c07802400c0b5240000d403400c205451803d80004e01205244000d03000e01032070f010208091004a40549144d00e0b040382c1c4c115511140d0282c1e840041490017240003480d400c200004215140100c1039584d0510b2000280d86404000080380c0020718184003455009951480080b821010800c003401c401d920940c0105802c0381001d001030440b00710068114100000080100d80c1c047c52901035507400d80d07050300c01680300c0c1c448110700e0302042e03a00c0d000b07603200c0f01ca100300c0042d010304001410509004500785010800d01010765600081c48200c4111080c9e1a08201036a121032283c1c2695620500804005041c2800c5500040310008164001d84000802c4204003018440b000c0502d0407401c195030080c00c05002084015142e401d02e1843c0c0104290008000425521141c00081d00c0b2a8048070344d0b1416002898050007542108500356500e1103289000b28085800804803a1a4140c540701c0180720fa41e020100807059001c2c4603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 62691181 1250 62689931 62689961
    0x913050c0409051f1503050d140405100806372c070504030506040c0f050301150e0601030608010e060703050c070528081803010b0f0105030a02031005030a0602030901050109060303080a 81
    0xc17401ea81c5101c0000c05d6014601c1000503100804d80e00ca0014403000600c0c3c190072400c1c0c1c040204200c540c2d914030a0760711240c43e505180803980c0d60b40c0002901503100b081303076030f0010341c0c01c08604100d826113001003140d4120241200304d1850326a4003178824514109003400082014085403580d1143e00318110381c5c4003450745046480c160320b03580e84504189042c0d604813810100c88100b4000100354000340c20103000158000c10000000a0340040d01c54000c0c454440300300d140c2004902c1c50b0348217802c08806004028020300c81140d14014169a98030221410300000780f03800042000189590222602d00c0d40210041011364a0040014141c0f80c6181c011a050000e0000b60000100d0010103800d48803040f01c0740200c0c031801ca8081c1400e6640c0e50148a00c40e5100400c10521680c010003525002001c810f801600c942d1402500f101044058001640c5407203104a4482003201c4c0390019031003000400c00901aa907681d4030904107a510340e0000401140c51500016440016917110008040c0092 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 62692431 1250 62691181 62691191
    0xd09030219051f080105010e0303030411011b050304140d0b180312010608040b2a030c0904020309031312080f07020109090606020304090e1b01110304050913050c0409051f 75
    0x42e0010b4800c40040c040f010540b6000d020050f001c0d0742014140b0f004200a090180001141030002503c0340b10040c402044a100c0300612074059202c0d2a16100c00d500240c44245000124203019640c3c0d0424030401d0482d0308079501d0040c06090056580c0c0e460ba51029000e03c9540f280310710303800f02e070b0b21501c580c1005101c2444500320796052030f1103290083c020f54444045d07a081908143c40c620700002e012160401d039112444d00c5203900c0c7c3d80d40c01307400c411800b005502ea80b0761201c1056503106265009a000d0b00220a12075106000b00050450031803846848003142c2d55020904154801048081c0100e6801d0280c00c10b001c11480052000a10501d481052103172035402030b0302100c0041d00b0103001070b131000c135050115001e41d100d0b040c0000040307001030034803884440000c801b42c02182c407103a0400240400c5601c03503020800171381e0040c000081000000d480c00c00540d14418860300c0040c3c034544034880b1344000f1814984180d4028540250160400b0a440b85499241c8840b0f070040c0355200b5591 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 62693681 1250 62692431 62692439
    0x3080406140d060312020609010504030f0f09050d0506061e030d141201030605010513020909041b0801021602010f0f080609100302030604201503010608041e030207080601080d09030219 81
    0xd84180700284d0710800c0300031301c2540340e5a0001e241c120000c101030320b180c0c903200c01d01000c40d8210340e01d820305500901e0a0000b224410404a031424915800740c1d401040e492510410004007007a1036200782800e0b00e1900c19142c905900b47d804540d0b0000468240e00000000c8440600c40c459110340d401030401a50310704180d04c0000d55000b5002da0054500700c1d900e0700113021600d4041403844520141d0340095041c9600040014a024800743c0000c0ca070440012510080c0d1803041500c1000b890184021515000d0a038400001b601c8405000c07800500803540c0c00d00b07201c0c0500c4810301e41541e0350380c441c1c555a0340d000500803203082c040c01c06192040f2800c00000147d40c100220740c8a11720034260814480e007a90401e443c114074954a0610a00004111801100b00c0e6010307a411101e4503d02511652910f0801c008001b208040880c0180000400102803540020b9900c04075602c410071211603a0783c0c0c16000b41c444d0743c2e200300c110005452a4040000d40b6020400141821034915881706007562 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 62694931 1250 62693681 62693707
    0x60f03030705010507030c0509090a0209011103071416351f0515010f120906110c0d030204050105070602130902070b15030303011409150303031806060a0308040614 72
    0x7001c0c0c21902ca0b07440d442000841649401085032032070907410151300701a01d10300042c402c8440101004030403580854221842d85c0725000080e4030407862000d132a03a95400c0d041a00500088004d41140d038410001e94074800000c03030308600100c031203072103001c421006000e1260340301e4054201c40d0040f520728241c4842d0b42c4601070000349941543c02d4815584c60b1180d4507643c0540701c00a0511501191f5050588400d036000f40060402050f545000030f156100848802d0040460440c0904140d00d400080c101041c1e071300c002030855203031700e80456040880e0703068120264401e40c014280005c10034450140020601d40203460010400c1e18101d130140d03100c500d08012a044141c06072230140c2903405101c0742856440ea51202240c080d80950700c0d560404040090014001d0100c5004088c4840000d0720700c0c00c0e0140c4401c03800f20003801d60340e4a09242842a80f903414038000b000080c05040c01045091078010824002c482d48541103506191402e40192140109094441100c2d2000c000150001300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 62696181 1250 62694931 62694937
    0x2040c030b091b04030b10080a11031501050a0b0708040b0a031e0504020102030901080c1605060702010b01030e06040f03051c0204030b010605070f06020d06030506090a0501230a05060f0303 83
    0x25500014058200401c00090034000303002e45000e281c84480a56401c00d0090450702174907009400c9880da51228440b210000a41c0c2c2c1c003042c100d000384a2000c0401c0500d485050708030f4812011503220190000c203001502600784159170b0b01086121041001c048043e0181c40c44e503003c2e401c0c1d80c2c205551807154006a50203808032000182d0740740861031040c41c0f8115202144608500204000d11b02580041c1d0b07244100390529052118100018842c482c1e0398085907484041d03241300102c142c0052814070b5039642c00ba1000c1d005542014203c94040d4440d1040b1081220a04020001368450b03442d0340302425101c1201b034003000810841c0c82903903100f0011581c2c800c01002801a0348a245040c104908581078102c0380030020100300c40c00104504603010b15007a5048040107a0300c3d5807400c1400700400f10b07540300510a000c0d9004200022001241006c40c05000b031000740100c0003001d190700298014562803003440950b2401254111400358003155001700003400b0b2907042c8443d0b000003440c0da0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 62697431 1250 62696181 62696201
    0x3110310051203030c0405010804141605090a180f02062701020d0306050f01030e03090a0306020702030d0203040e040305030a060b07060e070f1a07080405060304150c080402100806010c0204 83
    0x4a902081541400c1e550342c0924003600010314254240003401c5903e030300c954452603040004210101d0188111118045072207604a811217440f11130035011006640c00780c0c4103007072189241d034000804003a05409208044c0b504503c042c041c540702940c0c0e2034407009a07100c090385c0000341401010f55010101c00c1c0d180b02c07003904c40300c0c5110550024000a117880301d013147d00003c2504001c020459900c0340c082d460386045003424041540d09a1821551650190105090340145100b2001080c003961394000d00c100d0f0b009905655a4507884181a0f0340d81c4568403131191030501c02e82c0041c01203441840919005625454045a21592030303074900341c0741e040242c0940d02c60f5550b80381d114079900108000b400034078508a048840340d141c500b2082c80310640a41c481c0c1d10f241c000652104000860003150060300c40201496240d040c2402c008886450f810b405000c207500d0194800956801101e1092140e0b900a1a4003c0c400000c4402c1350300500c045d05d0b4606018100c01900b0069580c0d0107050821 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 62698681 1250 62697431 62697451
    0x30203010507021c05041508060114030a0f150806010302060d1419050a050c040b0d0e07060e01020d020a0b010504090807051e0106120c03060b0303220603050f1003060c031103 77
    0x8210a02c0ca00c01c0c80000c4c461040c4c2440f104120420490f92400d41e105003010780c07410082080e954000040e600780f260f18140c0b109001c800000c20203800d001c2d61005c0d0071601001410890005014454070701410140220304030380d40008010401460444003d1400402500c0041203400d1040000d5803c0318050341c03010f0006005418450031100c0c2c41c441c855200840c1c000510590030600c2070a031661140b40a100450800020403410b0b0040d560001800401907a0031a11515a1280020f088499031160303a801401405050615144006260440c103134118121200c2646030204000052035101d6040700c0c030900c01d01005020600c02d10005032510703d0105041c480d5070006907100d085803070390b0304000c481d4020b0012650110b0540943c060580350312060000c0c0e14aa140c0000b0b24501448116406100090030841d10000f0034481e03400c01c45610391028400d44e101d81d0303070307682205030200c8811104201c1041d080000c155030742c1002120070140d080025844583d40740b09070590f881102c43c8201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 62699931 1250 62698681 62698693
    0x70f08070302040b1c020108070201150b0316020d081501030b041e0509030a05030c070212060103080715020304050d1202090402130e0f091902010e0405010306051501020d02030703140403020301050702 88
    0x550909000d130240e920360860360351200d000039044413503280380c8a84010781088542000681900d001754030040c6502020b13030b140150b2980c0c441100c445907008903180e1054012a150500034103000140c07a81540925449113455542c1b090340d1060320800545005040680314041c400352501c4600c50b020aa0130f01e181c2c1107040e2000c501110341900c1000d400c138182c0790710802600c40c0150344070003929040703c000440c569a0b19910700001d02c000100000004a50142000000803c04003000409840744201018004010300340640d4007240001c86003d05581c200e240300c0d90f0020312403908100615900c41e001418240102c0114089030010480c002c4000040102880b072500741642041c0e20502e9010709031198a40b000c6401e840f500c1d10390f4442a8240d081c4088001c5a01403400c5011851010b0f10411040da5241000400380409880e00213188184c07070382034402544003207032942d2050900d80041d032400206540482e0801640c00140802c50014000400107036800e004042c0150070603402000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 62701181 1250 62699931 62699933
    0x150507050a09060206100e1503010612050705030d090b0c0115060e1309030915050d05040b06011d101110150e0114030604030e0103090609061506030515060a02070f080703 75
    0x10464035030f0050380966000c8010811080b14000c140380030744884400e258103a4945c030040c590311249001007207a1550070310310003040428020002030081409042101d010340d681e581459140d1580040103030000705144410f001c0710340000300805942c41c203080006500024019045128041900401c00144da0030903800020f1510541100105011040c100602c004035030740070f400e0765450305c80d980c0c03141750f41c4190781c04003409201601c0034460368800a020703503d40740c903040d00107001c210b0301c4a02040b00500200031903403400140600c00320024000744030a1060740f105940184c061070309122248980042d01a844649029116035884c00300c0301c95034842c1c02c4c90101200c50034142c11a82e403000858003000d16944d4001610740e0482e4250030402c070503040d80303401200904062340001d0a890b00300488542049017581c0005650740101d0780302c4007544c1d1204000c0b0240c0700d00351070071154004c100e06540726a1034200c00410008199004a6000d580d40b000c60440d50b818580c8400030325002080200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 62702431 1250 62701181 62701187
    0xc040e0304150306050d030c0f06050c040f060203092206180c0905091003030c0317041406060f010207092a02010507121103150a080a0c050f030c1804150507050a 71
    0x141245483e050600104e8201000b0422441d07000c8400303001c200da107a6500040c000511005900360350010400d210600e4980a100003581c8144920084260300703c2c030010355a4400310a481e24030301d005052a0b200f42c060046181c51590107503071124510355411001608441c1c2224440c0001d1114801251031096410040c2031070840c1d9006500030740340a02080000c3c000303194a031042d03903814200032541e62190f080440c6e880903420b40d071000481c0000144001d0101500c45a102900c0520440d0f5041e0348680510a5007917180e003015025030322210003400301000e181c01001d0300d541c410302c20039052210440c148145801d00d2400c00c0160b59140d0520448582c02050881d900c44000001e018002111f41d03400c40b1840b0040c4986020780001907410025580d00c2d00c240f004100600c222102a03845d42481ca030805000e220300c82c8a94401c5050804604021592607010341c801008035124540c2401e600398074502c010411640030b9105418108140243e205003401a0320075a111901d0b01013410003e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 62703681 1250 62702431 62702459
    0x60105030604120815090c130506180609060702030102120907060801050a1e03080a0e04050a1112070302091804031803050303060103020c0111040e1b0a020309120c040e0304 76
    0x480e010740c1000c010400030460200000b0059822842d1000465495002061559007054241d56001000c88141f01320002013401908041c901041410240d6680740c0c2008160b10640400c0c1300d07841d4440c01e9080c414078081d400b4116408000c3c15141c03038071050341d001034220381c404030950500700107403028805071280412540d0302810395030034007400550528000079403501035441200200462070072040342500c80804200021a0b010b074405846809001019002000b4030b1042400b640c070740b20008042e413059000d6500c8500310354080d00d181c80600c0d816520600c0e0000d01e01400c1c1a001c001c190304a0300e80800401e140c0752540c41c010b15030b00f040c1c074005020800441c503002c2820304110341031010030404001c40350465400d08006a0700c0c44415001d90241c00c181000b0000201c000c640000c0a903a9001c1c01480b819509400101c10b040c4d03819a14110700a10300c0c5040160310520407030310103082500a08103101c01903003c403034580c28910006010b95400141c15a0950000f00e0108403901c0403041c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 62704931 1250 62703681 62703689
    0x324090d02032703010e0624091003030c020d0c09020301061209030909051302040609020a0306170a020409030507020306040c06030506010e1804230a0c050604080a060b060c030a020f0601 82
    0x614901a044550090403814860400c2ca4031050715240220790b0b03038254010172244142001f0303154249000340342040a00100210f08000d401a03400c2c86900d4036002c80628405c03403444e0000c00d0320354195241110b40500c0c0040480c1c2007110b82d0300c5480460f14040b400d200400c8a240d0250383d9605041c4001c003c000034885901903e81080c6c0341c0740001e0380200d140b000352a0141c0000800b9a603a64001c48640d0702a54080c0d00b0034500715010960302d00d160010046c0d1042c580b0b062204d5950390307107582d400d4505a040315041d41c001c4015200140380c15008501d006009240407400d148c141e4000070b0070104152021201d268800a0402045825000305580160300f400c080c01000d0417030010031030002541e001c0078801c1d15140000360420003172880101091039036007242a4071002c0884025a50611010160b40420903007a0025061038442c0840c0d00b91455038001e810f2035420343e80c90340c002d08514426664070030018000d0405014040000c0c1000f000181d00030303c52074030144005818044d06804c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 62706181 1250 62704931 62704933
    0x70b030702010225020427020d050c040207060605041d1c051c0c0806061303030305040807060203090a0b090102030c090d032703030801090509120d0b0d030938090324090d02 76
    0x40e4101c000382030128507c03c02074060f621701002001c2c500e040e82c14100c0c1d0700540ae40c0540f0104ad00c3c01030081c180e200d0003d4601c2a030701001030f400620b00e00006a041b030328036821aa80a419015081003103003005404185640c1403180c2015042d0460040c4034901c04d550120742a5140c6545514680c4910342680040083c1c41072071078510403044400e00f00c030b0b13607000250906840300f001c0380c200300c2608121148541c010400319101d00304550700e03076150102d884007070307800040900c0400c1c0510410b00c2241d000d1a03880300032034505031195061103620f81c03210b8400d1f002d000402d0344100200000c48a2416112044100e4030085402d500d07002d82080010f0b00190030040c50203080000c4000300094542441801122898683c0507049104018143c000134464210f0007249400301015081100c800036590382c05c5965001d29401c940c07210400703e00b50b510308501c0c40d8107401186048a500002d061a12000e0150f0740302c0c924076045000142d00300c24525803c1d901d00c130200134540b18140410400c4200c144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 62707431 1250 62706181 62706221
    0x40807060924290609030313030b040209250305070c0b0414010f0b09010506070f150203011a03070914010309060204080f0d0f09050405060a0503060a0c020c040e070b0307020102250204 81
    0xc0a60f98000d40740c00d0058041d03100054070714400d903010000d8403131000d80c0b0042c040b002c0d030b200c3c901146500303800d54089006090400100301030307000a184d070710750929118481d01d00c0d1441c00c010031405441c01800d81c0091101c00381c4590040340d0f44150300ca208a00540080017100d0f046071515003143d5002000c40550351030314516150139034400030341c01c0c11144d044490f244c0710700c844e04001c00d0300d8040180080056110103c0010302500c140c01560407903001c0d40408016181c60b40301040381d88421112007000401c1103200703200009440209070321684041c500080e11100e02d60310581280d125801082541e80070a80182c0310380010490707a03920300910b151241000c00d400c08050010b01240c09443e01c100e854000007100354644080e86001814000c0c110b450305d00389004c03500000c00340302d161940140601c07840c069941c03c0600901c80510103540003004000d02e400402402c030381019100c81d00319502080003000345003100030002041000883c10300c2900c03040e80704000841e42d082c220700308400010703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 62708681 1250 62707431 62707481
    0x906090c03120d02030a0213150e0402070812040519060605030c0d03020613060212010b09010305150109030204090809030d050c0607022107030c02030607030f0506030a050303040807060924 83
    0x500c054541c1e08150300c0004da1a40c4034000c04402a01031aa4030058054400c40000b41c44140100701c1404080c81e41c682030340160a01c0d0900040e4403032110081c100d50810803000104255008480383d1142c0200140d4000c402d24900307100007a20f403d40c05562a90702d0301c030107000c140b50500407010310110403580c4000c044e007075507070107501e0340c80040540d690300c1070003581a02440784d00c0e012980702c4a8004102c0c0459138580c040255150850301c00e9900103032070500010220f14030176a802007500c80c16114100e420b440c550810002c0c18510f0b00495000e0b405009401054900b00b1000050760001c1d144c9070b840302c0345d0140d01850400028020300440d4010701c404126040c030703158005003102c00c003440a40c1c0d40e003080c2000d46141c1c924020094052091104101480b58182c0c0804590002284107200369282c4078100341c0d503003000a90181c0300d80c008102150000311140010901c052013082c021440060715260481c002d4400701c20315034070880c0d0780c08045180000e4070850b5200500495a50a10718034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 62709931 1250 62708681 62708713
    0x906061d0a0611030d060f1e08030f0a0909020d051f03030903020d1b0612060501030b0f220504050d08011d010605031f030f02010f090b031605040302090906090c03 72
    0x42407207200103020080907509100f04042c021200c074020000c10920026a59944207010700350a4410040501403040c03e00c03c0c2048075201410032a0160402035080885582d00030609502c8034a46800b48540d1072000969000c160026045072500542e000640f441c2c801c0c0c103080d400c09640c0c40e4681400101c2d0051001941003405001940d8050340d20496100d03041c40c2500100e40301c000c074050081d4043d00b0020b4101d03440b40540358003103042042406800c0d42c8400642c1070720949244a40c1c0107464440420450400c0180354041c440e0411a0b4500741c070803200a10100c41c07003030f5420742c0ca9403c800301c100c01c180d03086022140140001801b000c9640d440900b072042d50380701802100f04001e8000082212404407001021010710408902119a0f40d80d01e801c007008e0100410403400b007400092144000c5005000700c000700c0c1c4208100034503540d07a800c0c8501201c002d1801e09820700c00c05000100140e101c511000b80724210040080c0b0150500c1c20a0138074000a0310704403442544408001009000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 62711181 1250 62709931 62709949
    0x3060b0109150e0d02130b010e01020703110405070203040e040303062402030a030506040204081203060301060e01080703060f0f050c090301050c030c12060d0b0708040309050609010507020d020d06060906061d 91
    0x9814944143c682020740c1c0000e141002e80701c0301a610446948120031800d5040d40b00840d41a0240c8820060182c1c0c43c00586c5c40e80d100d40301c0a02000c0c200c50b070b042d410781044d421496014a280c07042e06e14080d02d40091440304242a41c00b60300007980d034242441a0310020340d80b80e4400c64089071900c05504070120013903881c4502c0101401b019102c0c0c0201d00b4a4850350107880c064052081605ca10070480c0e00c3d071900703540085854600c61340c02e0000003d01c450750b14440c00d05a45600740500b900760708540342d0303201031701031085011132103a07441100c1e003e026014031030903008280c0d104800340c6e1981014101404c0d210054030036030380700504005000d00300e0111400c54192020441100c0d88a648410019851021800c00507060441105c10003200c16408000c45108921945030188140d80310800c2c85154000c0441e0a400304900304441009450881c0c5100c40e924402403005010019070354440003170300c6480e8009441107803101d4081c0040e6400412100360224844d951010200e4284c00051041c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 62712431 1250 62711181 62711219
    0x60207140616032d0c05010506060a0c020d0807080a0503060f10020c12120301090203040b0906010e010303030207141c030f0b090f040206040b0c06040c08030304030206010303050c030c150103060b0109 88
    0x2c0820402444e81c5a080e112800101e907058195407403110145002504d042d03114903013100c1e0307540f8142c00241c06240c000d0544501600d00c0c0d55600e00c01c0440d60902002c2a02e1403026200c0700024400c81000458203002444886000d03a038894403418031000b03100c11030740c21144c424410101c1b45c0520000d254006080c2801c6481121103004070f11400c02c10a042c00303565800040700002c00400800c10400a800450085100e418406020390b20208801e4441c8400e000707882072481004010130101b40b19402800070140103100c011907000c1c940500710324000d01030000d0f820710300e003100c2090119070705480b4066854142e940c040c808100718500003250340030000d00342000e40d07180b0404a025915480181c0f0080c20f50b0301e00103a500c1841c90280383e43c0d04d40c22101100d030855120800300782c0080100c1628003481d40f68009048a034290f60742911181c11109a4506500c0300784070280a1000400030390004205000f1038040d1541035040240a44d1400c0d10b0300341c14845000010011420398200b495691 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 62713681 1250 62712431 62712437
    0x105030105190c2105060f0a180f0f15060908010e03190e03190b0703020a08040f03140409020301030506070c210e090408190806100305040804050a06020714061603 72
    0x1510f80100740c8800801540e540d040360104d0740ca48000d0000360740011301610040715085080b100c9801002148201c43c082c40c1070300f00b540450b2198019090304085d1840000800c086205540d80500008503000030465880948924004020884e003000d440d4000e400e040f0001e10088400707120040e5a440341300c0d1103c02300c0f10040c080100e41c0344240b14449130b0400050070b90709021150018000e071000d240e541514102d20304808242218028404c842e1252040d40365003140b90344944840c0c0c00d4a07030717100003501840008804c01c1403000b15140200302400020b00010784a505500f40b45250400c004e00440510003403400500c04030b40150b06882c0190b481601c1c5034210350008078210b1300103040c0c220340d036000b61600091208001080700540302c1b071611048400301035804003d048403100c000b560f0485e00910303200c042610686c03280d000154000d0103502014540b650304c2e00404d140b050141d01060060b0030241c000e00014601c0c00e8044020f06040300c00d00c1c10305030600300b00900b4800c2c051004081c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 62714931 1250 62713681 62713691
    0xf0306060219050a12020307030f020d0813020310020406020f011a062b020d06050f0a0e0a0b0604150c050d11070e1302130615093506130b010503010519 67
    0xc208082151204d5254801904001080004000b95403508009011004201031116601c1c0c120320010324541426076a584034045a203d80000420900c1034440698140c040d5540710107402445000a100612690380289404040c14002c00d00319004212031034030310301162100841694070202901c0c4a030042c40bc0c621940290000c0c806000343d0401040034880b4004649110071101c01d034004001c40d00d0584401441102203c104046504240201e20305404aa40402c030781749105e5002c0300c910394014010074a01502c1d01c02e607603481034603040c9101c002000200f5030000c2040074030041c584004c1e68202040441c1c8030034440351301c0d07000038020700c9140744d1248005401b40003081e9a50315016000b8140982d680d04112941c0c001c0c0410f0301502e00d0401a0f00d40080b000c91181c403510044642e5031a004032000f03411703041c030b0140c07202d41c0044140440701031b03140c6200104148000d5000d8101207a507144030035101d1500d000c41100591086200780d1502080100300000405038400c603006802000407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 62716181 1250 62714931 62714933
    0x604050609151201060e0111010209031f060806040b0a0b031506010813080a03060303020712020d06020307140d06030204050f04050c0f060d02040b040906050a15080c16120f0306060219 81
    0x40ba4041d83c0000d4410400700750002078210341180c414180f03e0000e0341d8108080b040100110700747c0c80f0340d002858141d841749040e8142212a0301e900005030350941008035040340c1e01c0c50a03501d020b800f928151800303007000301401000b001c1c030303c1001030034070080d4040d101c800918040300100e14001005c0c241440703d40400181d040740300c041c6030500742c0d611044044d1102d00c0300f08010000c04503404101d0252183c84000300c0c110300741c002e080c81e130164002c04c46500801a070343e500340030b0340010f8a80c00034025030344d00440440c0c03600c402910b810b0b000c907540003a6082c65801004145d80d80500341051503800303c4240301c046030010407030740c240303070303402e4440001d900054800f0840030320503c542e40c103120380301050100d500340c4104028800c4841101080c4038080e1103604114110f100b6125840582401d44608189075014209060b0300c0203102d03d019081a0300c219451b583c0900300001128500312800403001c010b40c0003445c21403824014501000300ca400c0901c06507581924001ca10501d54007102c10b40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 62717431 1250 62716181 62716219
    0xb0903010b0d05030909060102160302190504020c1011120a0903140309030c0c270a02091c060c09030b0a180206040611070602030705030a0806060705010908090109050604050609 78
    0x4000d00140c815680c11065041031031300e941040b5a058403c0c400040400c0c4550f20015500001d490300c6451904014596030030003556180400510508007005440080d1543d598809820505410700281102000d0b0039102da0407504003426090040c1c006200003c1558444044907900c1a0f01003c0007525810a06050301c3d00f0b0448554040824400020131100c00c0c00407014101c4044d014044038101030902e41007003240c00c00c8107800242448520f46055032004158030103a0044418400189046e07141c030045135260042e00d0f20034408125401e0030fa0100000e51064081900980c0b400e01c00d940d0035540c1d22003103444050712000031291103d007001001c0704201041c0215540c000c1102d40c1e92540d80c240648448410100314965008104002076203900101c200d5800c10761041c061882d02c82c031584240d034007440152119801075810f10944000400c00d210741404540601407094440642d10001004448680c0084d40a074005100411180d107a41c0152401034804458410074021610000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 62718681 1250 62717431 62717441
    0x3010317041809110a090204150203030c0d36111e06090301060902190221090405180d02010b0306060a0303080a0216020a0b04030605070507050d0f0203040b040801020405120a030206010b090301 85
    0x13507405079101e00300045d00c0195a000b401203032041200318400326004041aa200d0200b10303100b176144003042210184d0264154401100c04550f0b230400c03071214002c09422014541c41006140140c04001511010300c02c05504d960511078003200c0420041035441420fa0b03080d0103c2c0c9909004420105015007243d80030342002000d1300d0f40240454a5400340300c4841a540d000152000150248d204000c0f2000c5002028100b5055241d0380c561400941c1c0d41130000604c802807806410040d800035841d04818240b100c5481c22880c3d6001050a5500d8800c2500b80180604814460004d4400030000a900403010941c000040000141c0747d20111101e200c54900c014002944008032510105810320705801900940b8005c1c40100803d13512070800740d030140b1a01c640941a5405030740c4100d54203102d0301c40203440c5034992040d01d08140c0c1d9251000610780058000800594001c2030500c2503081c82165040c43c0071013980142211011078401940318032040c003e80900b40740c0044c3c201c046860035006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62719931 1250 62718681 62718713
    0x3030c12021c05070b0a0b061606020403080313061a010c0b060d02180108070504050c0f09030a0804060e0f030d0f050c0c030703060605010315050906040c02011b0503010317041809 79
    0xb0401e0500701a84004043d58411401103480c0b60752080401e0002045204a5808036400781c800382c0b81001032102d00c28034152640d012100d42d0b80030000800003400e810003079030040d440c01c0c402c0708521000386440800c0d2042040070280311603107142900f2150382e1100009c2134068008141101c1900d8000100343c4140d1442c0000c1e42213071284204207980f120b1101c0990485200d642070b22882500c9804010030390f20140c0e100035940d4001e1200300c440280c0b0100078200a42d0040071102003220507034070750720380d50080c0d4030200c00718030801da560589007402c0d000b04180c014220060402d60341051400b030301d00311645c1c05010410001140c11100020b0030010f10742c2d02000202222112540e91030710700045c04481c010f5900103410304140340343c7c1800e000541b0080e01c8008102400540d1014140001000f0364107048085648a1583c88160380e6a401c2e080c1b084201c0da640d440e901c2d07040d428064440000e4090343d0401050800041003003094030200c02201c81c41d07812001c03d08685c20f040184c42c4008500c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62721181 1250 62719931 62719963
    0x60d020907032708040609120809121501030b160201020903070e180a050102031005030c0a051e0d0b1509090a0f081227070b031902071401141003030c1202 68
    0x141202c140220000504100d40341c950300c10407c1500c6074003d9104c0080342d00001c0840c101031050b00d01d1854032000b180c0c100c00b03050084400c84002500000f0382031400303074000e86941c0048420b014128543c542102003500e401c8c0025440d02c190800400e955104610a4890440700000031860005426900c5004000143c4c200d5a10211508000e4003e60080e41c0380304d03458840f4200081c0d01c2c203011400c8001c4280c02424203074240d14203c1808000384c400040030358035010030071800d002c980e503102410421501071803a50301c0502e0200e00f11540c03403e45505141c8030710403070000c100034800c0006260600541c000403803282e00c2091701d002036680c0510018036030121908410081000c441d000080c40c0d0b4458010f91411f000d12034068291603071031901619616860170000074180600e404ca55100c1a24104001403820300ca50301d90002c61150480c035255265164900c280505401014039600900c800d040a0300c8680340d550050080295000020b10f0041d172445011580b40c0244141016085026 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62722431 1250 62721181 62721251
    0xa09020d0803060414010302060a12060801150302090a151202030319030509062802070507030803040803070e04140a0c120e0c010215100302060c0309060706050a05060d02090703 78
    0xc41c0450260b002159058002c916042000181c0390039404114102e03900a0079181c0340c001010b0040300c852103440c040311003180c0c942c507000411040034400c035130001c60401c0148103214210b20420000200c0078200d0f55a0604049095808000f0ba402074003ca481d1861743d0005c080580c40407034154080e0503c031144450a20300a44146600750b08420300c01d0401c00c4c02e0311003694072040e00310300380c0c46440035900c5030b504280d410050550340303580204080d901403000c90720751030340d40d0741c4140c8241e1040b02e0444440e00d000c828030000a400c40020082d00e02c04036418440520030f4007612a02c61b400500d506115502d500301071464602030351800c0c0d66140b0440080c8100f20141034040d80c3c402c90440e003075005201d582c484c2440300e004040a103000e00480e07666030841519680070041d02c1d8004541444a50000b00f00341d1089550380401004900d100d0b88001c18207103040540c54044400040c455400380c08000308020060f502c00c0c02080c0d0183e007509000484031401c0d140e1a1001a107240103440030a100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62723681 1250 62722431 62722433
    0x80f0d0b0a0e04050105090f0303180703060207060b0a06031a010813060504081b06060307140a080d09090c02010507090614070506010b0309011803090510210f060b040609030b0a09020d 81
    0x1c0c0d0b80e100d28052070090240f80c0b10329400554640026a403201c041c2c08c140081803000b01c19800c54103800b012002110030003512901d0302422070744000411a500c0307554803403881d4141041c013103038002400342e4101002655120310600172840c02c40e00442e81006007610000f0044903072300400f82180c0360060001c12a41c50a4980414164001c0c4038100e426880c1c000c040d22000ca00080c0c2520400d8003602800030280350149410300f090304106101d501132414200801c1584c0d040145056009090740c400104600c0d1400e40c0b02103c4024242c0802c41e4186005c000b1500d030848140d10444840f0318181244000300c5502005c0c501032004010120b00600f40001240c55911010b0360041c03440e10001c1002c0303850030b66206c0e0044000500100481e21860041056140c510300e2041411240d0418031003011311b46012192140040241780c1c0051f40d10444542c83c22100e10810000c2e10384800030074030302414800c01411000b02840020f100fa42010001180c4810540008900c280e0140c00c4017a03212503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62724931 1250 62723681 62723699
    0x206011e0306020c0f0601090632030f060f010e07050a0e040615020312060603041703100e0103050322080c0d05010e07030309140105071101031d0708150112080f0d0b0a 74
    0x24642d03100317103a4030459002040d0304e0a544548011511000c16640c404000e45400340700030700b00482d040f89000c120b50045038442c0c130240882c080400803000a80b581e403400e54010003c490040c1c00c1101d66500728010007082c1030304a403c0710050b00007030900c000c0041580e40014050501900300da03a240028201000a0701d03000405410000d03142c0c46500342079034864080c001d00380130440d4040c4c03218031000003200b00c3c082c42600640e00308200920058529881e800e00340d075244400e900884403a4000640c8810302c0da034503d400381050050030716041f1114500009155200d0b2601c410071321071031390300d1800d808210095125002102d40b400c296004950340c1d05001c0c01e007580c00c5c45041d400c0125105444800d620032000c0300e40302ea51041c80f4441e407841c45070044009141109075080183c00c8288017111140e810032112000340780e120005c21004000d00c0704200c01c44010703400f40038040701c4000f0034000175286505a400d08001c0c204a07545410807900000b0262584051898200b00148800308400d02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62726181 1250 62724931 62724943
    0x7050901090608100f0803250c051012020f03060910030c05010f02030415080610020105010312080402031908030702010f0506060901030e030f070606050111031606110d15150903030206011e0306020c 87
    0x41c8800301040c0e40c0402203c44900d0238400c400104507800c00300703051216160808011540c6021854424151000841e04500b00e074001c00d48078a413100c0c044100021450140140380d80401592001c81c42c984c0395982c1e8600d201240c0c01000c0c1800640445600d140e0b100b0425103004040c085280070071050314660191404805880340c5025039000f20340c0310182c500500825040342c2e0301545420500503074040c1241c01c0315010304100c0e8540a01c82040d144101c085095091650040e2a00c5070340e814126406400c6031080a203450440307040c4020040140d40e000c0642e4a801070a003804140100449107480c114030810303400c45146a400b00c0c03441d0500c14550300c984181c42d02030b2110038544121301c21080e500e0181a000411140440000400080403608400c16900d4841c1c001c03400d01848540c1001510030403030001000780d01c05402000201c1c50301003a4252040700f4104010418250344000391a48814081d40e03c81200c3c401c08103204001c15145000103680100085442c0c0b840d8105454486c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62727431 1250 62726181 62726197
    0x11121218090105060403051906020408030a0815030c030c04050601030207050d0c030201110408100b04061802070c0512060f0402010c0b0403080411100207050f04060b030c0703020607050901090608100f0803 90
    0x903401e0004911810305100f20f8040d6500440100111001d0070004140500d00d9101150320750b400744400502c0c0102000900140c5100c0e4841d101035140c20414450030009a128041c480d0b4082402c500040c2c0300070801454908040da00890603130345502c01078001c2c2c032070202c004005208204103401350a5116141d131b04400c0c440e60003400080141045601a80a0741c019a107454111081e200314420f02688222400000034002240160383c4030310f440091103501e9018180b213500007a1850411418042d40e01c080c000c11118184200c40e00900d0555840c40101084401008030300441c003527a0040210800c40e551140312988a1b01d8945001882c150702500d0498001d41c01c004410400d10f4482050035030420281d0050254900c0c00c010004460584902d05400503615080410011010f80042d4880c0b10405c007056640c40c42032900030300d4810014860001c000c014004030f44581e031301c02500c0c4215030092400d00504e0315811030401c0d09840550140100302c1e21040c00145222001c400f400c0b40d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62728681 1250 62727431 62727439
    0x50f0a1b0609050d0507090c020102210106020d080a090605070509090a0b011e0e04020301080102120a0501050a030b041109070201050601170415020c030f0412020405011211121218 79
    0x11000104025848030580c0100780101c1c802c007a00340440c1c2005001c00a80343c0c040c408403121590764600c0c07501243c0700c40520200503500020510248000080008002880692039040c19803400000944030380c3c070b14580c1c03010440e030345021403010712a503008141c1050f0000010449814941e02c05031103540540891801000000002076269213a8411600d1642040e1181e5150b0102440c105020b41d00c808800411b1011403001291152a03170310145000c2d0a001000595030583d41c15940c2c0d5009000300b00d041c0d514145070050080c0d407140c54001c400c882c1d0000303180465403035501e000800c03184540f40d590742150b081c00800202e55415000280661001c2e00c44606001e405140c03108000011580a001619223104811060f4015401018030010032020b0303d01b81103000d450459a6403083d4000c400b2100c038891400151702d420b21a480c0145010440c0e1681c58001d80e40e11a0103540c0c8407c218424000d680c00c0b200d11020034440350500b44002c0342000da69014030006841c0c58198201c0070360013 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62729931 1250 62728681 62728703
    0xd05090313030201050904140c04030b010e01180b1201021602040506041808091c080a02011107031d0105041206060905070c0c090b0609041119030b010504050616050f0a 74
    0x118004411a0000c02104486030341d0a42160015103d41c1e020742ca415400c02e54440049410300a0503642c24007982160505030f036107602e1810b00760070104042c0c01140240c00c039400108162800d40c0184070b841c1ea6092408140aa208130004018202e0b581d56a9404d500020b0120198002420780c080154401c403407c1200b520342509100c2115110038410321980313815a03d40c0e010804000152490b800000e01c80c10b030390300003c2c41820400d0700d021400ca40110001c9071001040e40c086c0a007403001854003040e0f604003e880e440007414000101803800409100f00246585139200d0001c80300500410070f4115034241c0c040c50f01c07a004021030310550345814504004100c5040c032440c0b101c407100c0c1d0440c080c04e01e5241030203d804024518010020780c400e40030040d0f2041a00c941c05051076410402c06003e45600e401008105c140319102031040405140080c1340c24240e8204007a00c0980f03a00340e40e85030312001d2103280d45040d858960800b401d2441070354000e01500c140020118401da200b01e007040c02e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62731181 1250 62729931 62729941
    0x90b191205031918170a02040e010e010608100b04090b0406092d0b0f01030201090e07050c0a03030501060f0809030d0b04090206070501020405030d05030f010e060d0f0b060109050904080f0703051e0d05 88
    0x16076840c005c1024000d4001c648108054902500000c03042c00c1940c00006214428a0900742141e0441c0c2c02965a900700c801c05410801c40351003906a80b200503541408000d40390303038410840800040008291503035403486d4605011030612205d110350181643c0240071420358880c07110a0501c0c0c60101d500c00300880000b2544c007003000005040340d40c10b0b12111001400c1810701216850300130540c1040040602c9500613002c0c1c2007200e00c98540c040e440006255040980007040420659058018451004240000d1142c000100c444458200800041c00703182000000c02a01c0502d4000c0d6004a020510005225040d03005000303d03502142121005003403508282d8840c08100c800300071003c00c42c00108030030840c6468030342d40160010304445031001c0c3c41c0da030840c0c0481400c00035150207400c40200101540c11841c08005050b04940d13a410300e10b0140d982c001e00d032146010704045c04001007140b01c00c1600803810f8480107240303d18103840103562180314080f5038000d0440035800f0350a102c0811 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62732431 1250 62731181 62731199
    0xa060504052512030509120307111e030a11030a020a0308030f070f020d0c0c170105100801140105191502030a180302060d05190603030801090b191205031918 69
    0x30084810b0714035044001801074806403006d030032041c2c5403500305442076492400f03104207000518000d0b20682c107015000084006010200c04c00e42c1b00a02c40305140c410110455400041e00d524042d401000300c0011031011012a0034120b440380000d42000104101204001c0108040c1d4070420020240102641c0d4540d412201c81c10310120201c0940c0041200303650840c0700317854009209000d81003d07203c2702d56461240313440c0c1c441084031400d645d540d241071100c0c0101100740c840040c400000240580c6943c1c41020074004818031402c0c3c802c00c1c0344035500010310300141000740140b40800e40d0000caa4010f62000c3d403030b584a400550002064011070302c200901c04031108080d03076009802c02d41040c4400c0381400007004040d264400804002d5028003802071710740a440051846030792140200d515140d8505c098500d0481d882d8410605211442680b5800310007800495030003e039141101c0303c5608140741144a4215203580c1d281d5072400720440550043c12124091001c04446850680c1d42d003c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62733681 1250 62732431 62732503
    0x21060601020111040b0c070f0902090a0b040b040b071104050f010305010b0d0f0b060f041805191205220f030201120608100b010203120708180a11120a06050405 70
    0x66101c000140000c5c0318401c51003001c2c002a1350000100c800c19078452400c207200300850b52020b46007076000611035045040c0364020790014000c8110f124145401c00951040d03902460084141410010505006100c1c405c11001d10301c9102500801ca141040744c4040d00303104090000791b901e036003000d0740d103100c0e401c1450210584039000500c3e00d9200300d0395541c1c171980d0b00c000740403280e20014510060702199110311441070701a00ca84502c2039031000a1800b9420550100d280c2c8556101d04012030700413406003040180416114035200d80c1d6000000241030005c82d03214105840b056540b600400e07481012100203081c0c034002d803100c91490b460361aa1400344d070403e0040d10750725000300d4400014803403550001d092030441401640d003000e801c210310302602c04084807600d000500d4030003030241c0e240c4122a20051148070b48042c1003c40161b03141d658088a42900c0c0074040d40720341355421030b0050305000d04546036910590500640c03c1c14200607541d40400d40b680c501d80500880741c0850b003a2483c1074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62734931 1250 62733681 62733701
    0xa0e030f03090102120c2506020d0206010815040f0b0109020417030a0e01031a03060f010f15020a0f0201030e060f1803070c03020f01050403051006090b0406051305090c210606010201 80
    0x104401803c805082410350409a84903403603208040c800c5440104011f51140c6420b201114101c01380c1c40c0c000024a000304004a800c290340200005102540700031540000541056811038043d884a20340030001451200e0094080c4000800203d584c11542e0001d004591450b500f91108641818200e0344a00c40c811801000c0740200e45001040d5000307070802c1c10107800740c8119103801c01c061300110b03080070f038110b5048641001c4200140140c102d15602c071005002c82140e03048840c2c00c41440655190304e01c4d240a001c01d030f100b40c2d4420031680710f0707000104a0200310064038014241042502d04144003500c0d083d41800c60071500e414980300c00000d403112280c1000c1040303003036031440d0248900d082d000c034203490403c54104000f10120b1400c000203084d0342d083c4000040e0781c0c0c3c03401c05260308a504aa80062049081c102c04105560340d845c95104030b009616000140380d142ca240ca10300d40800002a00c2d045002c1d59000003076180c04c01c282000c41e02c0c09005580c140d943d441c004908907200801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62736181 1250 62734931 62734933
    0x50d030c0e0f2106160507030909020c030f04090203070e011409060d021908012103050d020c0106090c0302130b04030b07050a02010603020333150f0103020409020a0e030f03090102 79
    0x40310704286816280d540d0104009884842034401c41980000000003d0190070300650124007071040208908420196200540ca01035042000310f82d00203001040e144030310060709401140c0041c44c00310600498607001110340c52103a0783c6645a4082c1c000e50800c440d0400814481449100c080d4081c84090408800c5455518504030b04142000060b8010400382c0b09126828442c5600340d0030140480c00b80c080060b11202203941c9001c078410f030000b0b5144420610000460703090b000003074000c0184c80f0043c2c119100941c0350010b54041500400080c2d01085055051121100c0ca0740d4141d402403117803e03004104008415185e0310f03042c0c100d01c5280b00041802c1440000a070354684994003a00c809441c510020858954940005c0e2070052402c41d00441413039114941d03100d1442c1070394050301d103441d83d4002105504d0014841d592185503803000a0141036032032104c003650381c80b135811a07015040905c011510f03658950001401001c4407181c19001e4440e82d400304142400010585040000c164 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62737431 1250 62736181 62736197
    0xe0a0911090c0406180e010801050603060a02090306040b041e08040510030b03070302060702060412061a0d020108070f05120a1a0312160c030618020f0409030c020d0c1a07050d030c 79
    0x90b2089803d540b1800722801703d0100a030340402e40180700c03100140200030650001c901414510304141c200303400a064655000c1c0f04105140d4036482c04142d440d405a000750001e02660780e01e05241042c002115050504510728240520810691301d000e482554401c0c0ca540c1101042e444081e42118600100554503a100e4001007005103410401080103d00c050062810b295070f07404501c6110100e58012038000d500c40c03590412080c1c07482940d440c0e888003102c81b410401c11640020b0301800026126500f000f5010302840880c0340610200c500000c0074440500c0589061141d040c000c24010f45145080d141a000300050b0345000510100c9406900914500c2c2581c541c08200d00f15042141c11120744560450010200d242d0b48144902d00410b00395030000c1c0f0020b4410071807000340400c4191300c0b0f1032910112001196101e1141c8082c15815035181d94840700d142004220948540c1c082116a0b1380b8252101d030000355000902240d070302c07500449400616200c403d030141c83d407410149001030956 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62738681 1250 62737431 62737439
    0x304030503070b071b05030301030302150c030601080403200604021804030210020702010210230609010812091f17070318030c0204060306020d02090909010204030203250e0a0911090c04 81
    0x3c0c00c2c00c0341c001104d0704210590000110828508990072178084d261a0004001082459010720030462001c40180710100c003480c00f40039001070750202824107410450300c03800142c105805030303000300c0f80150204148450305a07032034bc41950340d54040320204e000f601c582000042c19114400800c1c041c50b0701d9005030104001c1c015400000f5084010241d04500c00d17400c20f1394035880140310382c0c143d200c0886052020512200007104c070400028003160f0062034207800400c8104e50102e2240c2c022001c40c0f100594030000c201c0000c0700140c440350360b8400c858520000030580c6801100000c40c8828124801049546070b000c2a400c03648480e0700751494446550211000a12840744094102c2c03004000040f12030700c036200e079022604001007015215900060803410303480c100d051164400c00340c2000394500307400d6a02203502c80f1118104810001007080c1001c0c900c03c084003120000d07142040b05ca03012860601e00c032001400d0044002e8588014500507030f4520b0808102082c0311701206074010b80b41501d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62739931 1250 62738681 62738693
    0x80303070c140309100306050301051003170d092009090703020904020105031306060806061c081209030d020f07060b010f0c020907020304090603060c08070c0b040b22061d030403050307 81
    0x8000b0000190307010404c50007071a40d9a00c014980082c0c01503a000491504000605003180c0c00901844140b2441d4541000051010f604060030409401c10240c0c80d007030401a40c81c042d102201c4010984c00c00d6114086490440400c54141910200e8008840303449000c01161903e800d804081d401042c1c250002d80554010300003150012a500d601c6000d4003e5074444001b10b03000b540101c011500f010080c1300c16031030000e480d9080c071241c14000c07403042d082c555034065491082004074540300300e0100c00507610074410303c240c03142045800d20a540d9094110700303210039944100c108031070b000c0c40d002c501042c17944200b900d1a0804040e89400e00e40701c4090b020020803480090501046220410000ca00000b0600401d0000c512404000c40e601910703500182001c88000c0c8204100224032407600c0c0440c5034045c43c6a040f070342006403402c00340c03078800c014200d00c09994851050402494804020000b65501190540b502d10b4010604007450b454010340380d100e81d21001d0115030040c0411804209 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62741181 1250 62739931 62739953
    0x1908070807080c1c0206092404030c02030f0106030618050607030f0b0d08030910110a030b0109090c0c050c09010521010b0a06050d0501050f060409090f0204020d090606080303070c 79
    0x8002d500711400c00108890b514079088000480503e0388200b0455540401d4040244d141c01910700009813030107441d64101c014100b001c03030305442c014450381c1d0007083c00d250044069921a07500501514842c100d078001c0180a13203010b00c0102e8246150050400b0941502c694000003154000b02510883d122421b0480c0a8107104007203104107642d07407600043c00d80e9601c600e4003d072403013543c00b2034603450804080d03070520315142c00b4040043d00f0b01002054030302c01d810840d00140e60342e0800043c1140c1100040700d40d80d0444e000381034410300d842190040650071001400c0a14030440854140c0004807041c414665428030410385c10240c6104480c00c4c8900c080c403000f102e01300640000401c2c3c10150001200c1c2c00300fa40c000c001207600011443c030039200710300400d0b000d1302c81502d4655101080401142d001c0c4a18411076010654410201d4100306c40c1b50f0100340003a4005105546940002e0321690080c040c0c2c0c2800c9401c50f2170140009102c107408429030344500a940c86030041034480380c450496a42e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62742431 1250 62741181 62741183
    0x601060f0e1c170c0c09160804081e040b040302040e0d0912111f0908010506030a030c030315090f15180213030611040314031204060b2106091908070807 67
    0x4149980004441c03404102800d0110000310041c20703100207400070700c0074402001c0c01460304202912101088540c010190a40046e031181c000c62f996603150031120392014072001c03000c405020001c0c3c009800521600504103031780c002c480410203103034800f441566550f07012800034046440610100800c081044418404a00419490303015034000700008840282852800d5a0740c4c3c00a0304000680d43d100030750340007074182200204080d0070103100190751071b07410007001410429444102010107200350003400d203480101c0d040070305c265140c022000183c02d04140403c0d0540c0f402080310501c41070701200c0c400f00c41f40e00b209440c85070511180340c00a988100481d85c0c848054030b0340040000d159102d40c00c06e92030402280c9491b036040d490021008445840d000300240d105005034030581c0041c8030001d410030b9100100140b05600600030441210462260002d83d00c5500200c041c091070102e00da81c4180911029205001d203203806821494400042c05044503c003400740e0000211030300010b01d021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62743681 1250 62742431 62742443
    0xe090c12060f0f04020d050708130b06150d09111f20010908040608010f050406060e010315120605040b070306030c1a090a23100c020409021903050601060f0e1c 70
    0x1d8607203240130405a030b000c03552451000b907840b0300700242554440402c0303070014070001c01035121800725100c140f10031501900c1e05226194200036944000e611408548408040500c1842261501c0c10107002c0803040c40103c070f004100701540411190140d541170401d8012a4480b021031800d07005080c400c0140307101c0010015035071440f00402080310070340a480203040c40d58842550750f040c1000300480c2a80342c2d0006005509259040c0542ea400c400b4205c0c04210030310700054034104c82505600c1c0c44000b907001c84100e00030100d1620501c803854200c4c03803086016010f072542070b4603401012011034901d80320252443c10008424015810350124a01011504074412420704001c5400640412a00d9000700c810201034029088820805044220f540b007044410020145810b80080d120b00b8540000a118981e620084021036440c125001d000b000c00c01c2d0024a03840c2c9903d0456a40d450078080c00e4040386901e0000e0403914401c04000e84004409482c0c140c1070440c10000c107030016140c3e070003103c0d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62744931 1250 62743681 62743699
    0x1f03030c080d1b020106050d0206160218090109140705150703030e16060e0301050403091403010f020d0207050f0706050a03050702010b1009060e0604120f0f0503030103030e090c12060f 81
    0x20b000060040b5080c035149036030f003580c034100e400c1000b0b8211021503000c140101460f108000140e95100192a00ca003d81e40c2d41c45804801c40c03000500c04002e040d0070205558542c41881041481544000031561003154030325286120824010f64a200503c101c070b40c0300302902410015001403c1c00340c40c41d00d1190802003580c801c00300c09582882e0640350880074900021504200c403035405000081c032201e0a60081100303041c07986004040500d140220810f81204012021181d2402d5000d00f201c0d4810344c3e8115100c841c42c0ea81d00300a90f0020f1419503291149500f03901e540000031800004440013a1201850402008401e8014041c001c042e4410340d540c0b0007500c01241ca8104250402203016034507014070508090010700024030714200f0342d005100a1000b07024101c03011194161040c0c000780c00550718001450980d012410071040140706000104c00001096013040c50010440000c594104496031a040295490300440f80c800030155054000b05d01d950400381c115540b182c0e070151140030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62746181 1250 62744931 62744947
    0xc02030412050d031a0306010b1308030d0506030708030a08040b04030c0f0303060303090b0405210a02061305040f1406040e071a180103020703020307080a1206080a0b1f03030c08 78
    0x303034001c04110140c6103500074002e1242c0c01036251062120030f005108400c65482d02c0040481d98070079050040c0001c4140c0010040c01040408221074010050b0100312640c030b405a03442200503010a68400740207119603107001ca400380303003c4107469540c5055a604205aa074a1b15402d540e40b0015001341d0a000010159601042002c000c06003441c0c001e84000c203000e4034500d001413a91105d40e000e040d036864103000501003a641d440c212010700e0b00c00882031300782d25200d0252505111200714020b41c0440001405000703800f49684c100c013201c404890800900031038049090a6481e00d011000381c2c1c0301d10000181841c03400781e2102400301070810413124140d07103400c800b440540e541e1103001c0032000d000c6400004405221201c1360880c1d803e03e4158188411550042d56900406400800340040840c0f9829250700c140c801201c03200ca4078600780305450b6500503050700d4001c7d10b00d013a00c00c1035052000483c602c1040412014400c000c90b0b908103030514544045031580c0da010403c07105000c0800042c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62747431 1250 62746181 62746199
    0xc060b0d12050705060604051e100f0602070e090102070804171519051506030711010207020a0303030f051302030c04020a03020c03030403030e070e010806010902090f0306100f05060301030807060c020304 89
    0x100c01c41e940d1610365a9011a0401c98a4003900424007449141031070204405041091880c0900d200c0e8100c402c0f01a4039860a82079041030507401050301c0300c1448100150950303000074120104d072850760341e065194592583d07440c00c0c4d100312a400341041c4010030041240d007080801c85c0e56030780c01040c10307280b0700c0813031901044001c0c0058500300440c00545a942c2d01801c1d052080c0382c0c012540c0711130921039940c0c220125600307000040002051041c1101c85403480395081d0100e0380c100d5801440030041c03540380d14010f0000c0c001e05150041c62841d11000480c0c6513071602c0300c02788854008005010b481641000c000c06035102850902c20181c082c0b0107019608003c201440c0118400e88003c101c1c0510307400e04503e00416641f091800d41c0006004206803400464042d055894005015a60b8514403001c90044d0b850710341c0d1590544600401c000540e6440344c9100b054030f00b14800441c14694541c20444280000c0c000601900010080440010101e6104107141d01c000d0054900f825501c2400d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62748681 1250 62747431 62747453
    0x140f130605190306050d140f0f030a14070c090b060904020c010605010f02030f031611030703020c10020c01080105090a0902030a03030e01050c160308040309080708030d0b0a0302010c060b0d 83
    0x98804a500420082c0d082800400000c15034102e501d01085071520700800981008030b85070000e0107490324803080302d40c001e00500003000000d6090089440400071544002d1340c03a440301c0c18000006103000d010805082c1e01d02d08031424140c0044911001c50306060702c10b80201220364240c0c1e84104100200d045648403400502408600240006051841c080c005810700032100e009104542081150001400203034080d40c0d0000b44081040e002d5500e0140c0c1502d55000980803021103100204900c010507900040303101d12400103503482d100604074502c0690782c598150007a1400f0171784280050001d424103690041d40020a9403003c01c1001e0543c011905064001006030000f940758400a840702d40d0034003c85810101a06501e858940079243d0704400c080d140b2802002c000301000400d092520480c01c0304050401c0005030b9070b8155517809159600e601c4900820700d060304160802d0382c1442c10300308a82c12250103840d90750740c4103161380d6001e00400c815010150700c030b4421906000414409454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62749931 1250 62748681 62748689
    0x10e090705070b092508010c0503040b0c030402010306091d07060503160e030a0c0308070c050901050f060a11011802130903020312040c03080301030f140d120b0301090f0506101401140f13 82
    0x205c50500d00b8440e1140c25110354144003003c2c01000c109000c0000c0003540440d40c85144440f1194a9860701d00c0101d020b049582d01c040c504a080070800e02c6400d45002408080c090035208848072160703164030079102800111020391020120503020701e40c0134041c5660b030000030001820350340c080d6026507802d00c001700582c00c2550130940c003044500c1000b241c1c44202c40031b03040031a60700e4002e6151400068038000c0c03032a0f441d401458089003524030203010702c00c03140035041d040c0002c1c402510b95002000c1c0a000d00350059200d01501c04400c18024528803404421980650240d4501810101070327003812000075000711029440040d0001c08220214084c60195101d00001c082000d05070500080b400d48084004402d9005810100f10725070300040300400b0300d04904e0001c00c2891000740003e006041c44030024002e400c0c101280380c100580032520901c03034052070002085a64a0300038072448680200300c6140031420700c4c6240540500c0c003001400b101e03030640403120306c2c0840c01503070414881143e0344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62751181 1250 62749931 62749993
    0x60301030b0f0718060516210e0603101202010207030602070614011706070e01180806040516060e010813140604020a14030703110319030509010e090705070b09 70
    0x401c0c090340d44400c0d50700e5a040f8140b45026480201e04007a9074003254000d101d03903824800e0009500d6404031810980c0203085070441510186005940440d1016919220b81c480c0002c030f610b44144040e2404005803801100001213440e011400d20b1400469141c040505a065100f03412001002960174001001d002d4441e900100d10000007210340300c0b01560603045205c400c0c0c0702400300751104000080c050f900c140507280484079503d0000058540c49801004000c21010704940410391207000201c01d40524424011503204c54803081c5182600ba521340140c5001802c920120381a42d80b10300c078002e8110f40c0b54a1201041c0800d95950030f181102c9981c4c035503191700302ca4200415840e00e00325140c0204607201e541203c551903040040e460710041e0100030200c11070070040308002e890800003101d01d891403000c1340c0d81c824401d04018200e0307082030541c40c1c0010105020300149081c4509c80130300a8589464541c1060055602d03c60700c03840c0104980030030701c50f943c2004820b40c803d29100d900340782c40103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62752431 1250 62751181 62751203
    0xc020102120a23070507060f020c010f021305150d1a0d0b060a050405010b040b0706020f0f040315110d020c010b19090e0c010c120306090207031119030e060705070506030103 76
    0x110300f00031011806800c1c406201c00303141001407641d000002c80d2036156100400003a0781c070030034524a00901a6000b8003016600e020702025003940540d00825206031910710ba074601550b00d00c1089014004101e00c3d1420203c14040d104540045070085400f5602d881013928802c2c40b26004a0322600010b1000c3d1900340e4005e0074441305040ca00a480e002e007200752002c2c4071540c109041c02d14903125610800c03500b000b0000700c0a0a100f69030303040e142c2d0f04072100c0c4002c1c7d54403480411404140c0190006880c81010700c1c8020f00881400c1c440c0c410b0205100071814244114000a88020740008074402020354817136030306000c4c0d41d880c0d01d045e00040d521108900c1e202e13070400420108a80c001418901154800d11212001c6c0e070300f010104100b1a07101b00b40c4040c030ba80d0031070210090001a484481c03803900125840c010540c00007803044041d5120070031204081c86480b1006148080000301401040308040e04a62030b0405c00001d14050303008200b180d040554500c0450b58540c402d174800d0710b08071410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62753681 1250 62752431 62752451
    0x915020414030c0a140a03080c0c09010b04060906031113081e03070c050f0d12120c080f0402092205010510150905010c0303140702100509010216060c020102120a 71
    0x2000711810710100940003008210500008500c50060782e010f1451602c2070410881d0190703440144030006103501000c0d81d5102c1040201095031400c2d91003d081c841c1c2d10840010810703800c40802d8030f04550b03c2e940c448881381d2070a203050700103018614010400800030441e6250030f08100030b200006001c024005c110800c550701000c124044c42081061154004001c29800f0070314004441c41510710881d940c4048900c158002600440350b0040144810328201c103d2540e0350b00040c0e00e0b54400c1d00500140801d4664040441c0c000704201d80704052032030540c0c0030074054141221083d51004001d4000c1d0400b250809041c286581e0030502180d003a9110300800030002c81c0420710000614001080003000316034131001a01101c1c090085030b042120420700c400500d4401d41220000d12000b9a08110328103000900030745a0100502c4001d419040101049002c0c0e414401c44206502038180690b41c40318550302c52015101e02840b110071590240034404c42c1c4004e4411007800384001450000b080702c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62754931 1250 62753681 62753699
    0xc09031104020408030702100302130305010e060606040e13021302040306091103030a0c120923091807030305130812030108150705070602030a091712010b04030302070b030a09150204 80
    0xc00140c590141e40144810850b4032000000d980c44180e04030b07080204002044421402805402400000324201c90000130130700030103601c8910300401241c16203809940d03100c241f0840348141c0c4180303504e02d082000002c0761980002e202c180321600c01405a580d01c1c20030781c401416078006401c141d0302596a610340d6010811180c030b03130ba00191000e034060f505200b152170700681001a21003001e00080f000040560145201d5012500a0024510104c404014040c904403009038a03a0402d070207039020501145003032264501700c00d40d00080000401c001d9003581c4e8103c50942180c801803401030b49007280400c4094061050f0485034540c00140f5407650701d0100f81d9440c01c0c602086002c0a0041c54050299065005049070300c48c541054000d80d982e10f07040209001010901d1029142030420a040200c02c0c000000078002c040c19071143c5002640c0b0341c8181e40c0c0b2481140710060251340104c4041141e1023103440910740c0701c1c0f07490800280460700c903103941800d560740300701d03d81300180d00041c01d00010300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62756181 1250 62754931 62754953
    0x50d150812090906040e151e0109140a0608120f130b030727121103060901020d0605010306080a1214071a070302031e060a030503070506010f0b0f041a070203010c0903 73
    0x8001ca4044c003a0310403001d4111f848450001c2240c40131010240080c0d0140040d20191501e030900c8500508a580c0d240c01c02802030009812003003900700c50707401041080749103003c1c2209642c9400082c125071003010050316240e0348451451042c3c928240006d80c03402c211908010001c0036520440c0b41d40c2c0c90420002880c001261087e800c1e400c850f0f0055450b5200301003400b500361a500d03070f4590304815490030814049100548a142d0600ca00c0040040103181900901240c040c04807082c80942d0300c400054058070440d01400645602c9804150003040c035180b4801145160741c104018681020740c0030441540c003c1c1804c1c0d540342503000030560180c203808051a400126407800b18150f017005070107080940212004500003c01c008040303491540d500030035100071540001200d60b0703425149805501d5803000d210b0500030394600c81000030b040c64008211130071007401c4411039181c98100b6800a404c803484003404c1d0034400090100100603102445041c80861140e10740c4810180340d8034044030f1440d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62757431 1250 62756181 62756191
    0x60b1203040609181404030201090308130201050306100509031902090a020a050d110f070c0816050913061814010b0301061202040504020d0b16020d080601050d1508120909 75
    0x584100000c110b0746500c0b0312020140c40000141e1240200d1000c0b141d0068250380e04807078403030042c3d08248002c1540544c000602680700791110a2203550b4a80340104c2050000d85c041c0c041803040000407854034120035242c3c540a01d6040c402e06043d090f401092800c3d032442d62560320501d442000d04107514100d50410703406155a03c0641c038041490b00020810700800380c0480f01a5190b89a207d5424200000e41d41100e00e400125503c65805003443e4441c0c00701c9124601e094003503c1c0d08001481c103440302560039a40060100e00d201d880314800a04011f47c3c111044d2103490b52003400364400d4001d9008004054003036260f042145041c4400700342150b5480c3c4569200b030385032000800c00f1118100811022940440f00000d06548034000f1070700d2440161001842c845551040040300441104503851122140d802c607503194a0001045d2038846041c2c07035140c085881070003000444801500400d040094507141c8001550b61004000d00d0040c04800b56000c1401c081950a80d506007020380980c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62758681 1250 62757431 62757433
    0x80a05011103060a140111061006030e0c030c06030405120304320d030e010f090f0c08030a080f0402010201020714070515070f060e1f05070e01030203190b1903060b12 73
    0x142002c1c00040c061341402e00c50310041179102c81030080941c1c002c07010f0b10360080101c4265202841d01c2111b55041c2d140d01d000f1a40841d00d020b51507011002c00042c3d1502a01e006070050050001810070401c480d003004104550b244a0200c00d006c50308000b0b0080c0d4090b5210b20440c41d806603425040d03010503d442810107445c038031040307442130740341c1c0d00002c1046024145040000751211a0301c5218050454005170320300450400360740748208a1406201b420302030007a06500d801e1501d071a40700d5240d11a10175000c1c001140f0802003042402d030030007034641181c81400014903080865545540c10142a1100800d94100c00000c100d1403c0003441d0149400c2080e020301d03d8900c1c1c3e6502e4003880040c4c079a003c1c000711741e50501b809883c1002c1001c80011054000c000108503030801450000c2c26046800d400010b081008840803075001e802524022444004080c0b0419078030341e6002d004201d5480d0240d13012000500181600310b0440190010f18011030b00410f106840e1030900c843d118141e900010700f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62759931 1250 62758681 62758687
    0xc0303070e04020306011e1701120308090303150103151805041e08030406020c011e020a030c080106020a1212020d02090f010c0515060a03060608010e0d050405010c03030b0d0804080a050111 83
    0x160743c0c0c0c083c0703c4d283e00e07001020822590401e401003c542c010232405030000c00f5440c0c28008074800c1303071005071401d0390362081d07980c1c1d115035465a103400d40703a00050300c01c060142860341002059602a130001142c5d0701501c00015a00b5076079080710031144070340801004003103a6a1050000344403400c01318090042008950300020715099850701c9861000600140c8441c0e40070034030a60101c000c2d0000d03000c2100c1c0d080701560541106401a00a501170009440400d25040420400e1390007000090704030740080c0c000d4054074401c1e4503041070700c051070300d864000c102c6600025a203102c454405802080007e030340041e02c86800e1428424030f82e10f5800010306101d441a0070b40c00284000506400005038081e814645449030b40104040c0700030781c0c00c01040642031600204c6d40c10310550101c1841c1401c001203a2504d986241c3c140d900f88181e0050342d000070500031507580407074001d4020040524028020030022507260300d481c101074100da0815202c5800c0f5141280030700c5002d015010701d1740360100c6002c1c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62761181 1250 62759931 62759941
    0xf091b060708090f0a0608090d09030b040212070b0c0309010206060d0c120302010204050301050408190806090c180a080c010206010e010806010e041a0403030b0109080102040305031614030c0303070e040203 90
    0x14150190035402880031000040f00c2d103164503401005481d4401c0a8134456865172201e8002c5c001078400c0300c21407014821201c90400031885030b4401002c807034108410303004a40301c0ea0207024014501a144d019144211900010f0142140c4024a102a80318024580303809012000a0502002400b103078804c0540480800210380319a00e82d0080301c90608810350258494542640039004561110358954a03240030001400142c0b402025030394140d44003121710012002d0241d47e0f0701d80c1034810b00c1e04407881c8000103142898038401800c0310b81649250030308000423400041e03c14101d41d0411042900201c0310703c0c010b56010030000e030246c030307003121480a40e40c181003060399110014403070015030203010700200301840a001070b50420164500d01e140080d0ad0b040c280a80036080158859000504000000071214810320a0360181c0354040007031881c1000c24100d60004044441c0103403903032000b58800001500c010002809043c4418010303540301d141c04c580c080e180300600d6424030301036801001041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62762431 1250 62761181 62761189
    0x27081506030d0c0c080a1a010509040b040201110a08030118050c0408300d060f060203090120030903070e0703050c07020112050705090402070507030b06040c020d0e0105120f091b 78
    0x2e94114036450300e082142d22500389040b07284400e0f4400310540c000c10800c5410300030049080e01c40d40c0e00c4108890790310b0340e8441c284092501d003240d01921031080440800e00661140048812011000c0f04580072212242c84011160340203030300040c0615180c0052101000c0c1e40e00a0030381c060880c041180c1018a001c0e44561281c140c04e1901081014840e01d400403488520081200f400d0440c942507114000d0403e413900904d035074060350800a0355840000f42061001040b61050041030359038000700c2c1c10342d00e150f412109a142c0014101d000a01042000c1d0b102005007900800702201d0900e03130f904001401030201c0c0c3e805401c6449080c030811109001d43d800000860b100c0040010008031691034450031035080c010030807999401800025003400b03000c00016035006a034041c00303209400c4c3c0c903907404000031501c00e04400c80240e04800942c43d0381c0b50207004040c5145006040151400192460841030800d080f154200d44d5101801030103140041048081c9400800c601380b4509160f90344001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62763681 1250 62762431 62762443
    0x3060e011206060f060203070c27050a09080c0a06051608070509030a0606090902042714010207050d0f0f080702071a041203020303010e090a0809102708150603 70
    0x5500380c0700c14115200412038a5400709005010030444035207010b48074074009440350300c140026119510011400318402100f48440c07520503407180000c00c841804680303130340040c100041c110070b03105d03071399414105c007081c220070040c50600400c1015101c021410702c0c0840c11120054100003084942030140c411741d94105000b560000c806040064450801c40000380c41c140d20100b00800d80341c20140005100c030800e030041c03041184200c400b4040044100c1407184504451000455036000204bc68004144001e0f9509158071000d4005482e248042d01c8080c54842508600000294829000c500d883e60240d000700c103202c1c1c14070f0001d681b41800040255500014042c0031001d404503400c00160110000444e401800034a503031206461321070601030b41f0b0b604240f20b0918031210160001d41c24090124048005c1a0701c008524103042143c4148034184803220020014808494081c00d00c504000b5031a00104070000c4180c0801c6042016241c14a0108070303a2000044842040c4101c6030740107d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62764931 1250 62763681 62763689
    0x309051305010b0d24030c081902060f0310090504080306040b01051c0507020a050a05030c0705240906070204050a0b13020c1b030a0b070503060406140d0f0606052101050703060e01 79
    0x450b0040281c5c031019190317007006102069aa1083c0c0000081002d0f5202c90011038600300300791407400c07030400241c201c80c110080000303500090030401200c005422001840c2c00800c04058045183c0e1281d81100072103000b80d4050b1b401c140088100550380c40c143c000c00140311400c2c0780850600300101d0b2045d400710355030106445010344440000385103920800620200c95005000c0ba101715826080c42926940826038440050048240100e65814114811030880d00000d01d04222503481703c0340d9101d19000300c0c00c0103131300c208208031802c00350740c0714010f16003e00b40b0a000080d1030199142081109600d526040a401d801171004150582010402034283d04280c014403501c000c04100081c104a00e03c94010601c2c51441c1c10b00c03048541c080059031041c01c0070307181003101686604021303907408a46845270783c0c00780312100b41800041c040c00c42c0c00036403445550045401c43d2500009010192075007031a00740d41040c401b9080038440b00b40180c0350000d4960400300000c50801402010208050003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62766181 1250 62764931 62764957
    0x10612050a2609040902130c1d01020d05030c03090109020a03030201050906060f0a030201030506040e0601060c0c08120a03090c0f060302071e02010801030f050f0115030501050a05060108060f010504120309051305010b 95
    0x1004401b0340d00c0310344141c100c01c441c040d010480e040e00c45401900000240c201050f0060b84c2c000088a55400000e1100309041345031501410340c6d03662400300d10154801083d41d44130395250088503006031076800e204809107100741c002187e0f52400f5031119150a00c0200b410340f0070302e48920042d407036486009113442625020700c0c000c02c0540d28480400c018100b004a40090303485100c000242c000d0b03004002103840da102d20f140c3d51034075980c0c0080030b503a50840322407984802810801c6c00200380c0260300142110b032003002e001d440c55555507203600c0380005941c46203001c00e800140a80802507000f1035600d83c1d1b44004951140e004403900000c0840710b050000030a0074519084800a1060402101d1210038800c0001e018004406404d05414042072104441540c201710100d041c01680c3c0c00b4082c8030b100c0694034003491341d54400c03c008000c0c01102c003c03814000104000710b203450020107602c0483d402520345d02100c514001c2440114640c002c0000140c0346000014071481c40d021040b03900c4465800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62767431 1250 62766181 62766191
    0xc0f06080a200a031103010803190206070905100c0507080102041401050c0d05030c2203020108060303031e1b03010801020301060f0c0308011412030c060403030e01111b010612050a260904 82
    0x440039001040f400f0103170a245500032000080344040000185800300005800c1c050062540301c0c01c1e81d4035042611400301050070507500380700c242000a90034151914615040c84d80d80401d480f03260500c1d401d80c010022a035000581070005412600ca480302008007803809038604455011029241c10307211a045081000000c0829406010074041d100e24001004100360303e00394100021b1650109440101d001c00c20110000380a49004000e89115071242c02074903075134050b03240714004007030300090503500014a640360700e1046010400c003440c041e1030304400046c1e480d414814080c200190840c00c460403c140da203942d40010f0b601c64441411150240c800071542049a000115500c046850f0346080d48008a2040310124000502d40d015500903102041022020321a50b407d0b0340d070744079402602d1b2108000d0382c2960006030f20041605100080001000c1c1e445032480002c5c012010400d584a0b4080080322040c40b010107490f6880e21120340e1881518810414400c0580c05a00c1010b8802c651311 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62768681 1250 62767431 62767447
    0x70317060307080d02010b0102010c09030807171309050f0f01030309060503060310050a0c080108010221090f07080a0b07020606010e0618060307090801060504020c0a080d090c0f06080a20 82
    0x421500b805011030700141c8804184001d0020b0013891070b041194010340c202414510b280e80035002480540b50495110f500d800d0554a0303015010031800e4149020300d100300301100258118066140180c28102004a0309091100c007000140380302404081d440c06d0601d004100107500090680111002030070724948a03540d050010b810004032070000a02141010108a6540f509a0001c024400c940d1240329031a601d6902d541e00303e00030050301100820b41c102c802041e81e00b04c46103255001d001c00d0100c60307003040c1c15020103050620a61102d4030b02e0b400100c0020811401c000308a038480050b01c0182803a10302400002c10240c14a421180220f00000e40300c880d1401510070400e01240203807820360340303040086000341511902c3c480c41da07035546007010129103850503000b114900012503009146400c0140c03110040c42d0f20152040311001e913911180c000082401300000e00070403200d8003501c0c180c2d180c0240600b0218009180a005900d0070400900072402038a0304158080801403d940742c07950 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62769787 1106 62768681 62768683
    0x30c0c02090114060403050321070201020909072708100e03030c0f0c1507050306010e030c01020703151503080702040c0f0e06031b031602120703170603 67
    0x760200401424104003c2028441c0008002e285002e43c0c80d5240e52031944460351104400c481c102105241c240c500c56240e038401c20500081d4170b040d229400086040c04014011003e21401040c68200c6a05030180c4508282c82010304440d01a210100695251752111154400d1070030142450002d51010040d02e000c1c0c07405003121410101503801e81005600002910401841540c1c048200031001e003d5032405030225403a1140c0c4e9041c514001000012580021341c025840580800c1150b40d00081b40400c803038200d17250340c00140d150101e50025080c1066000c4800440882c08401e114501000f440464400c035010012000c400c2000d0302d071202c0905a0401080c0707002400c550313500702075004590002c0b420356081419020486900c1702608251901004c4a610401810031740c0c0c0c0420503d4181c82043c1c84582c108045968010140b4080d4061006044240c0c0b02240d11074134 = true := by decide +kernel

theorem cover : BRFrame.Cov 62589931 62769787 := by
  have h0 := BRFrame.cov_init 62589931
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62589931 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62589931 ≤ n) (h2 : n < 62769787) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
