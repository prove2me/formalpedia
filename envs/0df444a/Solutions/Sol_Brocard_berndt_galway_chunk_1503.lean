-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:17:37.468829+00:00
-- url     : https://prove2.me/submissions/03f9fbf1-872b-4450-b4ed-ed11541b65cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 270143884 ≤ n < 270323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 270145134 1250 270143884 270143891
    0x1209030c14011e0f0c09030b0c090d12120b010503060906150708031602120304080901260a0b04060807051e03030c0f07060305010f0503030316111002030415020403020907050d 77
    0x1c0401034220880454010401c0b0000e1901600c0c2500802c13a0021034118003409000b086c200086446c4401c2030703900c03405100f800340e583c0034044000341c406025000c3c001c000782c0c0080059012954445c141c4a00104110002c002c2d41c0900401503c050204a60143e406000d07800011414140305070030340440342e100c00341c16003032885666803c1481c0d00700b1200c62040e02103414556006039030400c034503040b0025035440c0074950304140c0c58180c3c0e030744909903441d0305100021440168904003004903d01054a0b00200a040c0c1862805a8054078461450a1080d410704901164200e00820400200c480042520344400b8100c69a0200c00309a410b070700c2d0340f500081c070202401080501105000308840d0340600b071401e01309031000d000c5980682000011b41400381d01130100b03840000c101c9810001c0e903100d0503080014039800b1581103000e40020b04040c043c4082c2a52454215009940514868a81e09491180303020340e41089004610000c1d40c0151228042201030f40110002c100ca0044110040f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 270146384 1250 270145134 270145151
    0x703030e120f0702031018171e12160906030b06090406060903030f0504030209280e0a031d061605030909010b0904050601030c020304090c051b0304061209030c1401 72
    0x12180740e0801901a4501d201c005550801c505e8248054a90058405020004902081001d0a28901c500001001078524240c0b00f40b10f43e500c60141c1c1e031381e2615042801e41300c0881c3ea060224a0b00070600d00440305c440c00000c2404840c2d410400c035540700f0340ea0344102d1107078645042100684202d10b901da400480c2000b6114503500d45003d1040506030b240c41c1e150078549149030090104000c2c0b4405010008240310501c0180c1c0c0e884001508030300c4081d10710700048004c82010640d407066441c0c0b840c1713a9282044520710101c0218458100e42d01a490301d005842e00c1c410451a044040c0403925805001000960300b01c09142c060000024069130899040003000c20200320140710a0300540d002c9440801e40410a1500313006240d400355080c6014880300c801c4045c003030350364003c50050142581c0c4a0040c000c0a51085064030161550210120b6070300c840c030010340e601c9034401e001d1000003812162095000d94a01c0c002c0c3c1101940c1a0341d01d40c1c1c1d601e85615601100518201071410554982152 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 270147634 1250 270146384 270146413
    0x70f050d0c0804050712080301030311010b0a0f0f0602010e1203070903080d051503010b030c060c1005010e42010e0d0b061009050f04051506070302030406230703030e 73
    0x940c0800e10703494946103814200360a0036850103c0300c5d0701004040648291002c0040c40c0c1d0011b0781c2c11a981418103452130149000700780c0c05000516001900f01c400e9007000599101e00407082400c482080110345803d036140c0208900340c46080118800316449000e42e8803581c1f846100860303004000c0e01c0c254030f605440742e41d00601a4400c80507052051703181c0080c44050400d080203071606920840080040048aa010a07100d00b981e5007a03034841c44000c107549249001c2840200075090200e02e0802c00c039a100c10f0011700183c1e0030341b407104000340190150301c40701ca810302908080801c1400e800c4012868009418800e10034100b00c0360400141007144c00135030300c86c0301d10040114030070301da044480d00c1e05000f8008400c0320107244008100d506401044103803180c4812481c60340041c0c0300403441d0b950b80901d0844207400058410340210001078548141503021001c1d006548071030740d640349000c40d4400303800381e07400540d8078024a9113030411282001034003d52103140080054000c2c0d0b414141c00144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 270148884 1250 270147634 270147641
    0x506192a020a0f05010c0210020412120e030703080c12030405070b0d0609050702030c010e0715120e0f0307110306070806010f2109020405061837020703021b0108070f050d 75
    0x5003244d20740c0d19610003804007a014071000d4007203880c440c0e0031400e003490151055010303030541d04003500b800300324a26112164031034038050000700005411112099664901106140e0012550101078060601d020841c10f01080482e400340303420030004c1c40d0a07400d0590011459000b40f445010f91603075050300203540491030288a10804068020b140c030b41016204981c25039112201c03452141e003002005001004600000b800d0003405e518100d0032051a00500d0710043c00a40f00084030b602c1182c2d111420448000000d041c0da42c421081859421120300c02d0641d181000e41d039030804151050000389955205800c2c14201d800b65240600c40c2424940340d4a0340c450304020f9a014494075044680c082d418071b030140c190811801d9030002c111600714014440341000203804841d119089802c1c0e0f101001032056101c00f0141e54103c16200c401211400784001e500005045002d40101254821078186034038900f0400441038454001503682c20000f11980c04103403001c0420300c4405e00c100c5000710001e20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 270150134 1250 270148884 270148913
    0xa0512010219210c1202130f0308031b120408030c0d0911040e0c0907030b1504090204030b011508040209060a08030301030f031e0c020603041e0506192a020a 69
    0x101d4205035002c400b0320303400c0f80031010441c2d584502c1c00d010350064041e605c9100c03e00e05c42124000180c5989400c4050b00124400e6809002c511590711808824000c01000540c050505a040d04040c294240302035011400f43c20040e03e4a01400c07230005020800c2c0e0001160b004000c00d084900d08075803201b220041b0340310400107894500e01200e00a880c1e0400344243d03081001004010b110305420030000400d9004010318100c200340d19400c0c9094175881c1c045180c034011806020450300c03075440d40d92150003908140303c1a64941c1a45000150140b954050310440d00d016a56250a03690345400340104202c4c054070f0103030020b51400d000503e001090000d18061481001e1504140c203290400501c0c0d0784503400e011f0340f0340005030503c0c680190440c1282000c6581a02c10070345a03945c504004c05504d098021114010104840c064104040451098460340c6600082c01c05c90707032100074600c1110791803100704001e2101000003002803001c100e82159802c0c60b51048803210840c0e40e0b00e4210034035050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 270151384 1250 270150134 270150137
    0x2a0c1003060902030711060603011503320d14040302030d0c02031006061d0a18050717040f02130c1b140102121e1e0603010e030a09050a050a050a0512010219 69
    0x200071303283c680501030041c7ca42000c0704800034880c2c40039456030103c20b1041c500c8010414052074400b65601c000c80218000c580c0c00b07003040d410b20000f410314456110b84850500c040003880c3d070840360760301c411038105940560350041d0040550051403c2c0540313000106110a0380d05101f01d0030050485002c42c003940c00a84195581c2c01080141070002c04031030103910f4800e03840750f41129010300241c4c2d100a1203591181e035003440492140c503000c3d003c0e1007141941500b104800d1700301007080203115500d104407002c14426202015110002c240041c00ca43d150f200d02000642c5c03120040842919024143d803140c1d000781402e800d401c1d00710040318226407044160a59803800c60302008000700c41c503c0444100a01c0059946480c6042c00070742e0001c803807002115401d03440e0b00c0041841c50b102540701005000040007117036611030b036950001d003004240e442424440c164204000c40c0c5803c146401c081121800380500d16814280410001c00043d04201d40120350f50a105101104025008e2000c07142d816 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 270152634 1250 270151384 270151397
    0x180b0c070e01050901030b04020105031905010303110d0f2f0307030c0b01080705010804120c0c09021b0f0304090c02030d05130309080d0f08070504090509032a0c10030609020307 78
    0x14111000441c810507030099100d0038804004101003030041803400c1d031091f0309103402941c1e680c805005c2012101d1607041070350841d28000000c000c00d074110114035484401e000490301c0d21100100100d8020040740340314000a102d64285580c020301c5c440082c03510304051026044440146200186941c102400aa00080c46900d900f803c0c00308111065025007400409031004a040c5070020b07041d0500600000d180d1866142c860081505c81c035000c4030f006a00c00c41040d68581d4541e0444040d401c040310401d8070700c43c4210030100706500001d101d442000e240b0040c40c2050300e1b011007800100031240b40001503000401090111121074400c4900c604001c480c0744108032010b0074000c1100426810115541c2e2200301c4181d0fa00380c01400c1c01031a1000c2e880c110380160b90300700040705c0d1805aa802030a500741000280054190084040c08182e81c0d03445e28600b00308424061854040d482c0926100680c100341c511800a040c0030384044450b240e982008900c0559618a40301283d1080b00e076040081c1e00d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 270153884 1250 270152634 270152639
    0x2010e1501090606050309120f0904050406090c080d090b0f16030f09090908070f031b0c0815010b07080306150c0c0411090307050f210a120201050408030106180b0c07 73
    0x615100d50f50141aa9141503800d500d00504002e903100b000d291500e12800000c03c1c4101541000740032a40914000b0700144241e061900c0c1042c0035002101080b01c002021000103e00b0150000710203e1241c0300b0b40d03076000d49925014562085501604801c40008010040c200301461801e1649400d14800e540300c840d03400c41110028418003507900070f000741a040844001c0407036032034015118a01c0e049680664901c3c200e06d800d4490301c0c00c1040514150030381da45e0788018007900c00c00c14000c45064106071030003505121410700c44c2c0351f824001d84075441070500c03c980200305100c024645c0254058020b445c00c40408542803510340004131340c5000c075442001c081d14681000e004c3c1d01c0d6107441d42c000c83d500f03040e00d1a0019440344068000d441c040c011148140200ba6900540d0100b409400b0030180d000500c072502071600c1d41d070100c50544504645102c50742c032051051050320320983d048900d943c1540d081202c120b50501c860144400d00da0190078010400740c04c180c004103850b03c002402440a00e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 270155134 1250 270153884 270153899
    0x40b030a1203050702070b040603020d0b19031e0302030a081e040803180c130902010e06030c0403120807080112020303071b061b0b010e070c063801020d0f02010e1501 73
    0x10f1009003d482150000c0208000b20007210302510182e030110b09002d43c40e400b032a25224020701040040c941e002c1040355040d81d2699850b4524001c2c0c03805440300c984d04080703d0800c0b0381e00740c0120a004006a00c00c01061200717602c18004c4a0304203143c0300c294a80100000b81380f0480840945041e104408000240410000d100002074011980c01c0040d0194400e8440012901003075003500d0522540c4860f100c40442e8420080b003c0d14803c0284040d80f2410b082a0f0084150800e00040795440742e0100035020690007881054407441c1550703216003090b800d00380c2c524840450345404981510042c40f003040000c0e460701000d5800800350340020407c6282900040016164a000041e407800606070800031401503070b6110306641800b10005019115032404540004107004d0242a00b440c00840d030a00755268136001101480c2c11645000036003003010340300301018001b5119400741c1c0c40a017400030601d008845841000540d40000218009046850f07400c20201446e0b56040315030f8600140110b2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 270156384 1250 270155134 270155141
    0x1506030527031c09050c0915030a08040e01050901180f0b09070e031917031b120426090d030e06071103072408040c03060908271806040b030a1203 64
    0xe003000f806004a80311521440d80351801146518014070b030840004900c444498200488610003404071903c0d0080f500f4510100d800c540550750342d1a500d01d000103168685400e00e64140c401584100f8501c40c421180c040081144485c0c0d0100309841e040d8241c0d0640ea0900c802c3e110b034015031500030400f5008001c1600340200b094088407450a1180c940c004150b04409110581080b4005542e407529888141c065a402c1c0c1c000101039820001000912400b0021800d4020361007940c80002807800303003642c048802ca020b1008807070b100013800305541910300810040c0a15000f4100901212202c00100c0e803035910182041d9003280010802c02c6c01400c0c200403200080c00b440c65896224100212180405101d600140f42041007190110303007884a071108010082d40e1100301040420f141d850840c43d02d0b040044038920044507034a4003045c0c1c64451030800c81104009000d0040004440014603400e20080c0601c0c0c0c029555028254098030200b0110204034081c3c289440c200b010f8110080c180c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 270157634 1250 270156384 270156427
    0x4090e10020a0806041d0a06090204180812060306070e09060411040803090a090b01081308090612010501080604060b040603020711090a09050f0c090c070609150b030d03150603052703 80
    0x146d011640c11407071a5840480d43e9014154042800300d2190410f00001d005401d07480c0c4000d03800081c3c1c103040c0c0708001c2101700503c080f91440c8241840c983e1000300301a01d61100300c424a0115440040080300340c5451003055901c4500208000b4a104140b000c0c0d010907081034001c070f515548001540c03016454448403810041c01c201406004c91003403040002c040c03160241244810301101c020784003c1007008010b40d104000040c00342ca403904888100c0200c1c240e420322038180801d01d21008281d480c1841d0045c8020740c1e00791400b062801d85000000c80080d404900c0948202a03a802c4556981d6036141205000c0c0d84510004901c00d001401d25a0030320407008a07002c09a070000e00c1c400c46680b5a199010f600c140311444082c3c8909140c00c020010f8100b000f0010a000e50342c1048082013289036128000c0200240c0c225460070f90f4995081d01155038410440d9080e800107842040b009119801c07682d0b100c0c1c0c02d0b01d81e20072014548011811341c480d440420321a2504041030320504401e80e410072624 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 270158884 1250 270157634 270157661
    0x40801060b041a030c070602030405061503060f0103031b05010f020d290d0f060504050607090b04031e0503070c03200405061e01050c07030f150b01020304090e10020a080604 76
    0x70707280c41e2410707450724240f0074504016940b00100014071312200d01001d03980c901d900684203540d01d10b4240780c003540352801103940c0342c01d0701416004907101c0d06001495a1280781210190b00d5540d0030340e00c01740c80f400c2401e40700c446034440200030040010000e010340080303c51009000760303d0b50000ca0b151002d560052041c060240c0b140e084c1884a0700d4103040e00480c5040075100039034001c001d41400140c80c4188140900028181010301c0308002000446611800031592425030007611000701c04002d202c1c03031001501c00118600301c030b1f65007045c0e14044031403a481a8200d80c9081ea4568461500c201980e00c103441c0c1181004144006110f408070303150340014111810401d5107000c200243c4011008041c124121114242c502c04503401082161301080100007280c054603a00d00e84980e0307003107411600315400400500c142d00405200c2c05080d01d000d5058000c0d6081c141003071288401030070841c44001240c0715589104802c11000d04c024090103040d5901c1796580d280400511043e101d0840c46141d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 270160134 1250 270158884 270158887
    0x1c0302101a0a090c0c0b010e0f090c06070204050c040e01080615040c0c033b0102011103040b06100903060240140f030d030c021c090b0c0120040801060b 67
    0x79001c0d91000d41000c2500c1c1c1424000400c0142880100c8214401d80402802120004004140e0b1500315050b42d12441000a1007207141e44e941e4592900e41d01c00400d00394028509014103401403030700f500310a500c803003256500b505041c6d0f1003007a00841e8000b1b030b2180c07459400a600b40801d080403451030011050098038207000404120380000e112240c8013030007408200f055080d948061f02110607602120611000340851038112240a0842d10800031030385000d0742c40c00c4c0701010903041d540107891003107400035068001079460205209001043d210b80d00d0400c5000d01011000580a102401210410f006c2c9015a0356030400d0b80400a02c54a196000c11a80050f8049000c01461602c90550b400e00b580350038010b0280011074a000034015500d540340c040c0c00c440030881581540501800c007041d07030842d0801c2c40044034601c40989c0010440001490a210a010f020803000c010309403250b21000024010750100041500004030a4403052810030000f010000c00c2024020301e00a0310451010740d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 270161384 1250 270160134 270160181
    0x1140a050304030e01120c030b1306050f1002100e0604030e012c0f04050c031509041109060604090c021501090c0509040b06090306250306050306040f021c030210 71
    0x340ca5800024402410001850014410359110700c403030000b0300d80b041d031051014075242c1601401401a09905601424002081700005c5816000c2c25044a0300507060391501400c0205000c85c02038034002240662141c0b1102c00764180d01ca105484c3c89600400191006003024a0001c3c624000403030180d0401c0703081c420014200c99210305044500d8072100b0011a644142c0c2c2c013045003510b080a4a99002c4e04d0071042140045da5038004601c130f889002140000c05102c402002851001918054500500304010807040d040c10100e690b0080b80040c8000d090039500e84103c8245e50743e604403400180c0101c2107400011501c4001580981800d4506129180034841c004020303019004240f441261a041800b5840d1100c0c000c807404908060705440c000e20f00025012004081c00c40340102680321031503d175102c18824801c600a60702c1c010041c09003a12240c40b10360041c401c5034800d99000718004024074070261000a403440b803d10036000b818880320899494412521484e0b08004259040d8419 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 270162634 1250 270161384 270161387
    0x5180601020606041d0d0e040b06071709040207060203010b070303110c0a0816050102040b210f070c0204060918061802100f090b04090e061005150c03090316030201140a 74
    0x45a80c810402d84000440303506604448080300d000345c10780038207806440d4001100c6075200c1d03400450f060003501c0602c0f40100207801c1c00910710488070068006410031304100980320800000b0320029100500141c144079954072114100ea000381e06c40d1000110003c2d44008054041c000c1c0000489003240881c10803100c2c501550710303024010780003042540c000699082080040c115200000c1e0848021034880742c44281958465018400005181d160b0341048140001d030000c85034891340d4581502c1085440d000c00a80d10035803c1002240d0050301c40802045442c80f40c0326031180b546401c0000040f00d00300741094400c40740d0b002444141c1e641c00f607a40780d01680345c00c00018505690313031820a5601e40c40040841e4000465000b0604c01d01c000600020f1580d4190000f01e050520042503c480f0b88a0465072000340f056071050325000424011040c0300103104802800c00e094101003613a281800c0c910001c3c1c00c1110b8001c4130004195111410b00c1596800100304000c03020072100d80b45010b0100c0c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 270163884 1250 270162634 270162643
    0xd0807080a15181104080105010303180b0f0f1902061503060405030301030f0c1d01050915010e04020903010f020d0f1503030e060307140d0c021209061603051b070518060102 76
    0x16901401d4100b2004000700c3c400740c0c8030504035035101a40d203885a450f08a80c9002e03003828402680000c2c406003052008686080325079080f10310b4025240e01d400404448111140c004010404004a040c460310070205a1035102aa100c803041e0701400302882d0090300c0c3c4240300c00900c0000c0c040c0c2d1040d000c000c0002d00000480c0c3c192030f084074070001e8140031440d02c03c40d080429004902c1c4250740340d13581d002600f0880354003410b84804503030075440350781c40c032a4403581803080d000c0e414001641c1d41c0c0300082a0910340d00610684a001e8004035440b8182140c603020303684007420071600b880d5100c0f20901214110312035183d0703100c90b0f02c401e9803519140da10001c28802003002d59520940000021800c1180524001c5840c881440704c1c41d40c90300b01600b008001000342c202d4000150144e868002c40c3e01c00448121118000000d2001d03043c00c5102030403100d407290340c1038101c05200040080c01c00d10083c82502c42901b1045500400c034032424481170000ca0a0001601180d5001140c14001560380109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 270165134 1250 270163884 270163889
    0xa0b10020d270f0314100924021e0705010e070501050417100c02030c07060207061b080d061203030f020301030206040e25050a031803020304030b07020f0d0807080a15 73
    0x1051030b2032116098000002c409584450241c098400000007000009092031080410100a030350340f4800140c115410b5070f040034001060030b2000516490f8450030031007a4a514103e0700401814000c91440100303000420356004c411902e0049511710802c4024000c100300c46402102a250f00f510344000a000c1c0d0240e4000c030420f00c200242c0c0602640303420825445c034000508410700a01000d58400782d181c1c2d000d1140703480349008021001c60703001d000060b0001103d50544c1d54a4040e010f144449034400450f003c12103514070104155070f00c3c0d0069026140c0900040414411446a9490f020381100c908044505041c0d005000400c0035948200a0740c1c1240c00040d02d519407556100c1d2404941400f0f1074500ca050021501121082a071040140020a00e40e403001c015004800c010341c0c1c10bc400b1040e0040c0142e20400c002d00c00180170b440c466402201c180100c50440302400d0a2074100103182c0c07000400a001d0008218a540d0f0102d9516000fa0b00d0142c00c0080c0c0f50340003da0340220b081070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 270166384 1250 270165134 270165167
    0xf06060a030321110f07031b080919050301140f0a050106020c01050d090b0420090405030d090203120c010c0905120a20181b030c09010e01090305060a0b10020d 70
    0x80200107070245a90704120950314040192641d20f604000c017840d00398001390f4098001942408104094078100c4100f26039041c2c111380d0840c100101c03002044035828502910f043c4441c041c0c40001280c4d1400d024050229596007081e00d418505002a4124090010450091a4200001000342580105d0401c420395020f00e0202d0b41e80e0140c242da403004d0304014400030200a001001c000c00d1002c00f0044040030703200c5241e0383c0c0e0301c101411304001d13072118260340141a50700100010520103c599014000f254800381c20b80740305000056082c1015002002420307001d1751119030a40b40035520446c0d41003d00400c40300940d4050f061040c00742d850745402070081500f0920329030000c42908641008610701b900030314800a015030b01d004070110280030348a021828096078900100c1c21114410b40b803054890041403801c0602a000442e1900580440f070341c140041c008021000c01c2c3c05000e2144213900382c03c80443c0b45241681403248400d0b001d03604a007190060945060034903400b0000c080741040c1c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 270167634 1250 270166384 270166427
    0x5061813030509212803020318190306020702040501050a060e0909030c030403030e1c020105030f0a1806020c1203090a15060909031101111303021309140f06060a0303 73
    0x1004082034000102181d100c00c01000301d84440d082d01c000141030741c1200c0e0800019140c0e8000301d8040d804070200e500000300941c00c20b010317480d02c410010b035001c044020b008000d06d4803050700d450f4020400ac41e5030804e403041b40d000281e240a40c01d160144900511007560010030036031510100802c0c1070300040b0030740c5c42484400d0204034001820000d5900d16030040090742c3c0d032160740c0e10f005841a410102ca00b03020f4804000c800d0b20240760314007440e400d144c040e11900d1566035200c6030181500740081810107903690b41c501c1414000b1200e407407040e00501c101001070384c3c3c4017544092403038070701844402d2100010400410400c088003003a1a1602548480300c8101c078012120118040d0480b03810050600745441491028154400001c0282a1a0030000c2050302ca01000d0004281b003101d008003000c0584a01c10401410892000c000d040c0e82800005800032840c0d07501001d2101d05803205c1c072543c2c0300b200f5000400030140031098000f082114400141841c42d41c0103443c1300b03900c030407502d0151030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 270168884 1250 270167634 270167647
    0x102010603060c020d0801090b0d120201090c060c11040b0618040e0303270c0604180f05010e01060306061e08070c05072702090904061d10050618130305 67
    0x35040a009035600042c148003400400500079982c2d8101160b61001074441c90002400008620940d44100b00c0078181d0802c0540d1034441c020300044180c8884e00f150346c0ca104400c0450f000b54400805490030f5954818414464102078206204406640d84510725041020130301e55210400c851914003841140d800350180f0b080050000c205108060400c1c0c0000000c00c02e0714511200d4140c042d2980c25296115801e80d4085651b41d80e58600015411403010041800040442c154440c45038440110204503071491402d1107082c1c0303d0a91280c4100010040180250f81d0140103c5001d00801e01d4812501c008510081032108040003a00382070201102c045180103104481585000d50040e0440700303803540d03072840c1c1c40d070000f440210b40700c42c008044e40194043c80180221103021000402c040e45039103441e110f0710700a117000c80d00f40b2341e402c480003180243e4001c2030051b6081e412460710006020b01d04003050064110b0100c010b006482c001004001c94410340c8115030320a150146000c60f10b031f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 270170134 1250 270168884 270168887
    0x120c200c0904141e010507091710020d0f0c0306033807090305030f04050316050306072a05060f0106080402030d031a180403090603060f06080a09080c0d03061e1401 72
    0x420b104070081c00018558480c4081c0c400540216024020780e41c0d81403602561620014000309e40301e0b08811f0160420603103091913800c1600544118003000e42c00081660711400d48608a4035940b4507900483c2d11407108005101030b00c0c02c2020104191344070f2600c0420041c0d100c0c0d07004c00c0044000d040c06a0000c002c1000c1c0740c49180c6120103140d1180c05c5075a12401084144000d802500c6414442d01c00d214000c035010032140c014030111103001e0010401e5840b6101306403100e00041290703180c4090101c02000411055202d0501d1480c05440070780618100318840b1780400005070420001e100300401440b005131000070f09603401d486076240008071450040c0421494803080c0d1901944174080c504001d1400340198801c0d0b0240340700307845146d0101e40d590000e809a820500c614070511070302080c100708042c01100100d070702036a603400010389000c5550303894205420103105d040a5500c000c02045205800d80f24a8024001c50b110a9410480b60961034041500c54010f44100800526550780c459 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 270171384 1250 270170134 270170143
    0x31305011407080703080109050919030806010c15090b0a0e0a081305040204231801170708060106080711010608120702010c120201020309121204030f120c200c090414 73
    0x3541d1101d203a9130b40d549981402080f4001c00c0c02030307190315482c0402241303c11f800080d00395000900e401c50b240d219841610140e99486000700301506228080142c80001012550241801e01c00107400107415140b9042055482034001c00b9814191301d01018200b000100003450440d4591198000e0703600c600f050f10091008942e9807007140c200740046404a5201c0c401e83c802c480c503545031000390441072110002c10030200350380e1794400d101041d4000107001503007480b001c10f202d281e020800c84001c5503542c801c0030314100c0240d1108001442400500481c654451000f03c46401d01000034401d4500b04003195441380d440c91403216002d000052010110390141c443e42103126084203c2c241211400c07040a400b0b980304481e4070384580030303000014181d02e11403000c0d100008071002ca031010030313a1566010303201006c01c005990148001e000035600b1050460045004100c1182e40700010400403403000c1c00491109074403403190b50482c040c0c0c1c1d55903031100c0911540c010341103603008a905410031000c6040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 270172634 1250 270171384 270171397
    0x9080303070201062c1b1c0603030207080f0303270f0105070f170109021e0a090602151608061306080102030f0f0f16030b1c140313050114 61
    0x1140400300c01c010900707806600160403110586205084d101d5400c3c0d080301131699902414160718441004258200001b05428010703a0707000c02c05038a1b100305240d01c0051000c244488405550b11501e0a00c20198180840300017000d0b0200100702c08100c0404194681c08001c1c50815900f4601c2c45900e61111034880010b4040c0c01c46040d00d02040184c100d131800b8100c22101d880200d4141c00714910b0b1141b04410328006c4104045000e40d0690030300307203444080d41c000045182ca1480007205c2c180b00c8032401005146803101501c0d010925071a003440a801c01c02407140f54a4181c07040020451540d140c00854501547e0b14940f4800702d5950381c0000d035140c4200010240007603d0542c0c003003041d450541c000c500802424608018950740c0d02c460480014040380c411404100410104000340790389003600d1002d021074200441c102116801103400200104d00244001501501050501000300a00711030140300402552801200c00c0042c0d0340354202c5d1160b24104641d0200b440c1c43c44922070140c500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 270173884 1250 270172634 270172649
    0x2130e07050d030f021506060703050c120301080a05061302060304110118090c03180203120f07020301230f15060705120408010c180e0106030207151410050d0b0604050709 75
    0x25000c0c030b2824010702c8110340c0703c0c000015200f0f4405003240d41024280087c1300d000c00800c4c40d4900f00c15a0b0f0105e41070340190665441c82d205196617541140d10b0b003800b450180c01500010500b92000e410614641000170300440c5580d140b0707502190140c0c0700c01007183c0d80182c0004990f14403011487c0101c400c03031610510603074062800a00418540c50070340146c0c0c03542d030950fa418469541c241c1000151011000070095055110a51009588000e071010b4080d004405208908000060f0086130035220900000816103081440c080002904040300c180c20280303400504046161a01c4920a410f8103054810700c1504003045a9007088420050001d000061122240d06d4566070301c59640a040c00000e9000807a41c4609528076100d00d0319060000c880b88142001c01507443d0010550095105410036600404500041c00411b071090050795003210a41c1d200d1200c9281c00c20400540084641215206820341069207000c5084500b02030f8101d80704440015290b01e40394030a1300c03104a29884800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 270175134 1250 270173884 270173899
    0x1e0901020c03010c1d092a04080f0616080f0601030b12011401031101050a020705060304020f10020a03120207020307090506010207030b0c1306030b1c020103020405150309010c03060302130e0705 85
    0x29040c60f401405000d03200307840d0340c03107170b11040c60340c010083d4060003101e00341c46c51101c152000c0b80c48140000d07804500f082c01407800340f500361100c22450516651b140c00c0f2040f50320a2061202c0d002078a0103003000b051242c030702900c440c1440062803d1401000c4d0004e41015243d0b066041c550360344c00038101500360307880000c0140110184400c10102003d100c1035800201e00d00100620754056400c452301206154094a1440d0401c01040043d40000c1e0044c1d030040a000c140e40c04a48500c8045401c6c94825002000b858045141c000d05070100d0400340d4041c140188001401a02e00140303010907154000008611541e0311310041380b500c1000c1d071000c5c0c01000c040c3c0074001080c034107030000c8c481030a100f814404100d07110f482c244d0550b24081d511b075421507041800302c0030440840b1191480c0c544140340262130207940381c002030440043c44c20100e0344408000140721010509118002d1008000e080600c1004d02c0d50300082c0c1d01085507d07400508944801c0d00c05100f0301c05204841c0540310040582 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 270176384 1250 270175134 270175151
    0xe030d02160c0b0304051e120c010f0e0705030c091b03040312050903090a0e07031517070509070804031101060b03010e041406220503040e0901020712051e0901020c0301 74
    0x15210400341c03440940d040c03005041e010030818041021a403140707401c00e00604412014443d40c5005003103d50401100f4043e84091001341a1100000c082015216002180b6122094140c400711400c02c0000c0d40e0b142e100c000104210b84020400c0c010502e0704403401d081c02d41d1106484500c03051104000451203100004200c00c01d41c002c0c2c0509101c900e110800c01041e0343c0c0b015403555a128501d003055005000360801c0080c0b20b02d40c1d547d0359201c0740c185000b00e0410341c078400410428809400c4050311980c0743d01140100101000380c07500401c0c048403100900e0a144801404503800948050100310304500c040e40c904900b5084140103007130300b4030141c2d0740b583e6400f1700d00044801031310100e5881c1c12400d004400010009240d6020b404032a00031807601075800030310321a211912408031114082400001340b054100b05c0e0b071500c580300c80300015940304a1841c6c60400c180d0b0301e840c101c05004042c4a4500581c03450a0392001042540c59041c6e074910300f140050340303408003941c0c0961b030540c02c11444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 270177634 1250 270176384 270176407
    0x203060117101d10050c1608090a060f0210090c1e0e040614010b341a0406060602120d0f0f0c12110f090415081002070b0a050601050a030e030d02 64
    0x20705007041590044c0e5103486244a241015500117803040c980c82c1006000c54060700078400c03038240080384039074541881c0ca4160b50203d450313043c079984001d020841c08840d400386541c043c84031066010300b0080800c02d000c2e1987c1d61882c240c031140500c10340003101e01041d1404c000c0110000c40500943d0716003503c2d51030b01e8035120010b4840b1038500485100143c00003c0d010a41c1426900030b40004400b8112900741c00b625040300620444c0d800c40c0003e034101d01c0c0e4010640014401841300700d003071769441042c131f010308190f01034440e1503209208543c040240403a008460038213031081102504008180c1ca8100381101c03001e000010440384255151507099a00c4681001500d11441c107900d40600002008220f104058040c001407040700b01c504100092140c50b09030721002400701e41d10a1100d0503a11400e03068607100300e0008000c0c00f1607000890310305000702c00c11156400010014240201d1070b00300c0000301030b40202840c060605072642221401800700340250f41b00d54901d1001103496407804000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 270178884 1250 270177634 270177671
    0x112103031506070b191104060507053007151a0f040e0304050f0604030605070c06140c072012070e060d0317090a060507030501060e01020604020306011710 68
    0x8000001c1c40403003040308600e00b0090300b66044250048080b0806548610b0320302da240b5155410854003d0b034400060a40f902d0006c00780003d0001565010380b110507d2600900d08809140882500901086804009404038241e0707290b060b401c0d100c050300c030411884c103801152a8014123070032a40c100144841d805090b815a24101c0030704450888894a810301031204440c03650040f9480c03500100020301590404812042558502402070340c41d0940d40d031521021074a06559520004000e003248105101c00c9004001c4039401190200d056800c4c0501b00c08520322806000901c01596103600e04c55800701401806d4a5810160040c40030118180c802d948844650050080e0740046c41c01045036400e201e0824180c05525881d445404003050203008514035000701380109520542d01c000c0005030450003140c0c05000c01e074a0101d407550500390302801d02201d03520440c0c1150310880401015aa00050941c1100d0395000142c00310142d0340f0300c20741051046044001c0d503600b400b161450302d100c2d505 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270180134 1250 270178884 270178891
    0x50102070f020f0411091203070c08011508010b090601030906090b0c04050a0e010b070807051903170105031908030907120506090c010f020304050f0a0518010303020d0e030a11210303 80
    0x1e500a0240f50303000b040004441d000000c0c180700c200b0501043e070b40d9050010340c2c107042021000403203040012560746d4200001040c0c06c11201651600034003d4140713402101c050191400c88003c1c808004910045007440710000d24450405032200044801d024071684100e03000c9400c403102610340d1034450a490340d154464803d90f070041a5090700011075191108549041c2e407402e0000d98580b00e141d0f1075003003068104401c191107034001c0c40c0144803c5150a04000100c50bc00e0310780404450380d0840c5003c070140140c0c0f0450080c0c000c504000181c0001e82c00d0200c825a1014101c2e443e0b03107440d007407240303003404035041070800d40c0700c0211400c1032020000b8011b00c101e01ea402280d0f0444200001141c45d4041c0000050240e0310a0000b40b02a00c2c00d45601c0030b04d503001070079031240709a0301d90006032604009005110b07078031901c00052041c075074188030700c00422440303007000c2624488410100755259981c0c10b016011903a032070081c0c4007940e42e2719501d08800c28640b0341081e00305800a883e6813a80d2080c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270181384 1250 270180134 270180139
    0x1701060303020d230724050615071e05070503011a030d03060f0e190606120606030203011202150c0303090616021f0f06030503040b09030114060904020d0807050102070f02 75
    0x20746020f94503413250b0201400d0302c1e085074040013040a4403154030807503080100700302d90301c1000925081e584010200d01c0a00741e0950000031401e0f082640074025170b14102494414000e104201420100c1c283d44200190030081030302030450821a0305280782003140c41d0b000035905500304510303020f000844081c80810900100c040c1ca61110910f60154111101407048110b20903e8800400008000450310b40d03000b04142c412980316007190740f80b1021207102d50080c40104208812084580c00a84100000b83c49241411851075040403083c80c94043c004c08000d101d85807490f441000c0103c5074040d560600090400c80c0d44078101800c406403a00c504503a1580c2545400c20496401c62001920850004c0315400030b600201481c41c0c40000b03090750400c49010103880b8980000050020002480146402e044141e100c60405081500359240c0282010114003000d05000499442e501c0a5030050783c1210098142c520b14039000d2058020349001500303035440412510706008200044900440c801c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270182634 1250 270181384 270181393
    0x1140103090210030207060b060c0d0507050c0306041203140601120c030e061008120f0306060c0a170a0201110705100e070e010e0a0506121e120705070501110304080309060d06170106030302 83
    0x30418000c49e4000c418500805d988603e0400c4c1f4258014002088414011025a5061242d10700030030b14014003507600701c0301d443d60841c02c401c8a55251203a220000c0300300110240504120b00000e2041501d5201c40c10349594400f600d4003064000d900c5070398006400d200303980d4145801400c4d100511890303c6840aa402208003600301504203c040740d6100b540d002d90282181c807050103209940d000030110001501c6010000800708410445c0c1c000d543c0b95403485c103950b0f201d0b80c0100a00b0341d400c04a441010100912205002500101d03102c501240b6440c0d001409480c108112403600b15280d01009804000c10300100e107010080c03609600c2032864074000c2c003441c3c07030315810700c0100b904850882c4601d17040109464154001c5407e4807001c84c820604440011480082c41c0c0801d40c080e4208540300d42c841c48080085580016a03460b1521402020351b00f440d10b400d840300d40342e2041e200220310a4900143d40e5040541c03640c0120090144950500ba400e0b0421400500034902c3e8041a005440b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270183884 1250 270182634 270182651
    0xc09180f071215080609010b010c1505041401050f100602010c0c06020d110a0309031e0e0f04020405120601080607210c02070b0c010902010e06090d060b0303071a0403110d05030114010309021003020706 88
    0x150391141007050784050300a20415200bc203420042001400440c3d40240c02e00041c0010707482405114040c80d40314030882d00505020212000e242c04561040055904003105022520340102895038080c2d0000c2001d030b621034001c000070005144444262500c094003042c2e001d2641c0e403661224480606c2070b1178001509040c42c1c0e8450011030800e170300000140d2030312801c1d1a207060409000070382c000090009402c00d80c88400240c1c1c24080e8261001c02980310900420101504200d00c81c0c126090307061a0320240042e05404807500740c5001c800d0380507505d545403414180d108001c1c3c080100748a50031703961a0306200c400c030340c040c0841000590005e07204060800851a002d8100c440d1401d004080303454a640a544034030240c030180401e254180004e2094101041c3c503e910f04900c00200742c0d14880d28501880c01a007011805504403a0030ba01c8240088081d5401104603415240b84001810302441100012800f0b040200d000a4100441650840b01c50b9010f802030400c16109000a110141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270185134 1250 270183884 270183887
    0x131104030c081c1110060b07110a080c01080403020a050d080406050601030b011b03120905030405030d0507050a0b0613060305010e0714030709050403170c09180f071215080609010b01 80
    0x18600342082c4203448184041109600400307548401e1514075041e45e16484904420320111803450340301800c038040003e21041007011190314000745a0301181c403012060b09200740c080e55040080c4000741846101000305051500030800c84e0ba503140e1040484c4c0b01601070780c0d00141071020580f02110540e050401080081d8000d018400e072034041a51118074501c024030b0448821170011a040d4203120034804200714042c032600803c8203ca004000466a413071800003854034106070031400d81d04000041c80110b0000b000030900040c51a04181c010703003542c540d20300003195400c4004980c142c0f1031030032034008108441074011000c071f0021903059598050347d4580500300410500d08555240c0c000c64014040c0c1c000ca0b40c4030942003806403800390398005e2b800c1c0d10414205030540e104112600e021400344038618201000004c00f076500760220300d150034803441c0079400b0b000240c1050203014084020f5642500c00d507200c464a031011490b0716803110758443c40181c940105980d00302c0254200443c0c48040d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270186384 1250 270185134 270185143
    0xb0712030f0e0c102c0337080405030a030f0e060403022b0c0b0429030723041e050405010b0414130c020102030a050a15050f131104030c08 61
    0x1e04020b0150040a00b01c00c100701d01c0069102c00207080c805641d28045410703529004041c02103114042d07204500ba090810186840c45484403880b00c1c51446048060b0121105006a1061140000401e03191014a02840c0c24016900080c0e0184207d0b0007100074968461602100c1c45c0316600e456054480f4002442401d01c0345002c06504201074000e0203050030440e80b012a1b6400b0401d902ced400450242e550340c04400c50b1680304081000c0701140a100300f049410703c500800854140d603003d07900002002c10740c503010040400040c4024000109111030120700031038801c04941150503a55901e03a0440305490620444007070204149980103d107a09181c030849050790480f2300440d00300fa00d0854a01c0031146680100c6030000301984507010410500c3c002c4020801041d000544c0b2468007000314012903c00409000c0c01c0d03800c080c06040d10700540d1002d007041d40d5095901c40c19201c1d00e40f002c81d8200e40012241411507203000034650b00381c035124000d0401e8030f1044064400d48c1d50b46400e801d564 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270187634 1250 270186384 270186401
    0x60f0904140601050a0810050a0303050a0e010207150f0c0c09272105040905100e1302090a0f060b07050a05160510050c0a120f030f05010e0a05100b0712030f 69
    0x818805c01881c80800e000b030100307076806031142c0a078010301a192004140408a103a0044010170004508a014a5000203001456160038802007075258070704550f01c00c0c02004424400141b20340e641c40741030f0861098525131400c9800090307100717102e42e07102812002000451205510b103a0072050524240c20200c1070760110300c4d0050001407501038100c50070070040c04001c0c0c0d0081030020401000445071003600410b40324400442030002d4491400354001a40c03d00106900c41510304400ca500041e51610260303030700198076800004441d01650560001020345401c03000d020f500c041032440c200500000c1c42d810b0107100d1010ba503540d01e0310300c0451500c03040724054142d00004400b544004284200003a0a14400c590704540c0884180c0c4c4070031a0603075104020310000307004440d40312a00c1d6054000d1111900802404000540c0340404010300d5002c041c107a148603584640110700700104425507500902035002d095503403000c440c80c001c20f62084a04d15040424180b41d6040c1c0d02e01d0403485090700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270188884 1250 270187634 270187637
    0x182d0f06120c04031401050a0c020307030f0e030718091a150d02041407020124061e020111040603061a0901201e0f012004030807030c02060f0904140601 67
    0xa1604800000c091500c00030a42c0031261002d001c0040070800c11811820250000300000449041c00384182c01a68260020401954410003200d0b0000e6402056841c03261054130f0310704125082c0e000085d0a090096000703d400c035410750900c01500380180d000c400c166110306008009035100c00d45d009040d03c412101106044038880d0f03912060b0130301142c80e0311103a1000303000046440c0790a9040f5400c440c19940d180040c1e6486c01d10780703144070501c2c2941006484800d500c0900500d000d070001c1c0300c1000e04104034250f10304040c0c4d055016000750420302100000e01c05440e203c03904c405004004003458170440d5507603c3c851a104c05004e104908481c09810180e4603a182c11100d10345400d03400c0040d4442e98a580300f8001989900c80c00c040050801d202100040c090101d48001642d0950b45480100090440740c00071044520301503008540031242d210540546850950800742d48401c8a500040d401281c00a8550900c00a0000629104000f100c1c00c0003003509560240f100c4440469000c1d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270190134 1250 270188884 270188887
    0x90e090c0307030b09010902060721020309030d0e030c09070807320307120606030b011706240f03070804060e060f070c0f0c0e0910090302070308182d0f06 68
    0xc81c094211513a170040e00400041154000d947c0414501e80c00b102e0107440c07850702407030f41e100c146c4d41c000400d40030348040e40300860418005000007a00c83da014200c80c1c003444010040c03400320392001d2081c040d480d88000c00c3c1d03002c41c0c80c0150020f07101200c101d807600001111760780140c1c00340d190b130880c28140000300f28880201010a1410271400d82c4090b207004288810100c510043c10102d015550144c4803d99001c1102a14000003400000030001d000300f0342e4100c041041031644488014100710903200b28030311014401c80c9591040d0344100c10b400c3e0401071001003049080d54022400501a0f44141020043c0f59a2820201d44840065410b1004075002c3d4021440d200d104400506195000d00d0046600040d9682c1d00d1011042039800440d61290700001c0224440c8103002c00765021600d000207000c103d51580e402902c03861365000080070044007042405440340100c0a1f11440d500c09040c140e0400410a03200302e10308040310311801c0301d41071800714061b5410030181482503e0405020329 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270191384 1250 270190134 270190139
    0xe030d14071e06060902180901140405130606031a0f04150e010f0204090606081006080105100c12020f0706050406050702040c030b030a0c0305070b1206010c1b06090e090c0307 77
    0x10984401c81c401000d0b800c8038840b08003001c100503128690042040020040e46d0703110442ca10603903454400640c7d03118880d00001000f4450003460101000c6d0411240054140d4400750040f860021510f005820310307180c5040423080008148095001d41b9003d15034103caa07407842d03443d601821040750000d044a45105401c5684205600311400980a100010480341e070002e034900100c2c0c02c035910400d101a1100d004001c1241c0140070b140d000300704403600316050341c01e00c500070b4101d031018428a8000c038a0301a1000500b03208003074038115950b006c60b00100d44d8142d010005d66550f01b003840e0852a006100001800c0340c003441c1180d08503050740c3c4456040c034086408100003021344c1c16025051644030780a034800c0d0f940070f004901d54244251b242c84000d50440c00d104d883e020a40d0018604842c08121610380502411901c40d400300b42413819581d01d500740c1c45e18100419545585856038003080c207004c01e40035081076613001030300d9610000300c6041d0381715801983e5501c610f0a403e501900300160a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270192634 1250 270191384 270191393
    0x2061b0909150d03030204140a05010c0f02042702010206090c010c1511030705071103120301090911060c0a050105220b0403020705030d0f080f042a05060a0e030d1407 73
    0x7030394420118008550342d00e48041c046104404074402c1100082c3e400901400b4605501108041004d401e0320420700c0541460006001e4000a10028000c003c00b09884821559160059009a00145c4401920f035040c04040c0c541001c040008031b0150180b400003a0140d100011002c1030088142c3d10b4030b01e0703103d0546a82000e202c0800700b00c7c03812610340325000315241c4005c00841c06001aa40c54956410303450801d2a140e00541681ea4401d40291095640314208001030700d040d9006c1090000d40180185408528032070001285600301c2808908012130020114411141c640614001d1203160381e21040e41044090107440704030b840b0448941400420b09024071203078801c3c8a8011074103041c0c1c4800000c0d281102d04000d60700000c17022000c022030542d0003903000e5086608009540403504160341c50a480e104410300c7d07005002a5505001d003a0380c40c0306041d80041c00041c044c1c03540c84125a00c0100b08240c4170645501a10030080c80d0b4101d00e02c1400b82160507400c40075200d0034500c05036107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270193884 1250 270192634 270192649
    0x11d0606040902030114070e130c05040603020c1f06050f0301050c030c0c03040812190302090a1505042102041b0e04231801151d070203160f0302061b09 67
    0xc144d80565030f602c03182c0b1400390424400fa01890341c0342c90b0441802c48020810200c403068011080f121400e0501e140d45083d0003d00b5581038a03103d0901507200c0f405801c1c911302e41100e01d0f14112091120710400f1003d1040d0f54014403e84000f0741d1025046811a41814265075003902c0c01054050301300009011340001c0005130410042170f030140ca1a04d556100c2680c6454480030010b200ca900c006580215100b5141c2c2001645010b03060550034540150001001c0d003203548034140444500c00d00c03202c07100380b09800701c4000e0003d602c0110f4145070f6820081e00d08c0901048101d004a1500e07050405854242e511140d070b84030940d84035131103241250144006003500035020031801030300682d40340400001c10782452041c14101004804004000c1c011380c2968118a20150642c88841091150000c441d515402c86041030440402d07507211580101d01d1031051200c503c04404950f2103080400015148032400240650300325a0162100304800e110b03284d4504084032078143c200001c3e10300c0d081171903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270195134 1250 270193884 270193901
    0x606030207031e0e03030a1d010903021f090b0a030227060a03021e0406080a0b010e060d020714010213031506050609040905070312050703110303070512090a061508011d060604 77
    0x4d80306035901e0804003c06d1850704180c15100120314000d80000b146158014080c1c039001c024a032801c11a850358012464400c20310780c50191101203603140e035134064019014407000340b40d000840c650b10344089070000c000b901b101d0000c00041120503550307290081c0e0135024002c10031004080c186080c20b4410140c00a500010301c03012460210040403017a01440005440109615124409035107040020711088a10b00d034005414000030024074019600d0785000d50f050010228130050f6242c2c2c10b030800380e0f01d800848550390b0203580001110b000141c03100349030303408071791040d40b1a00300d80d42c0d810b503000184d40f014044c0c590029014450070000d494650440f1400900400555100e1500e030f455a1045190030f240e140017286001600c1c800f01071b4040680d207400c401c1207002d14214280540010301502c500310303110100c800d151001c91042d01e030070b1003407001040c0d12079401c01c50040c080c80ba031200100d00d03102c0d00585529004101082c1071006513200004025400640081c1d603494081100400c01c0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270196384 1250 270195134 270195137
    0x9140a0c0e150301091212060612240620150406090618061a01020307050606061b0d170a0b0f060c01061706062b0308070509030102120a0606030207031e 67
    0x542c07840d12291001e104800c071030760184048441c4c901140d000174002c01d42d00c0505100c9917240c00c00030044107034404016810001d1118010800d2100400b00c2042104140e080c080d452848080c0018110b410000c01c00022042c004034202e641000341c1503d40340e00f080608903890800e0600041c0001c0d07207a0740a81072880c8210000910454411000ea04004010350300711380c80b035030b00c452240f4000c0404d00c007640e41ea07109200440c03404200f42e44268031128058203590186502140602e405a03014481c3e00001199004844105503000b40041c1989504020a1400001c0380c000c00d003204401c1c0140d40212001400f02c10018107050300344446517104030112045950f03206d002064800f40312004208002c0810020140d604100c82003003c041c034291800705141c6020511803032400711130070f00080126003500b0242507507034607002c0566440c4030350002154035500c000740450038400d034076800074011b19102c03404028281c4c07181d20960803032042d02130160101f203c1c0710b112052080c440c0e540c1c458100d400d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270197634 1250 270196384 270196411
    0x30b0112020d061503030e15040b13080a060b01080f090d121104030309030c15080121081605120408070e0a020c19030f1b030302160507080109140a0c0e 67
    0x241c840600311030384085120a1302462039020070a040e440421240900000c40c0c0304810011b0603a80c00c0750511507442024401980410402021801f04160400610707600381030740c050326010719110000f0075100c0101030110b4883c501080c00c001c0d401c00c099210f4100c4000038100c00050280654160202940510500d5290300304030a5030755050300600021032190700d94200042c1186019000006550040a03801142042140070780e94400c4000b41142c0b040940c1000c00580c0701d2140b40b14071031014001d0001c0d0000a02107440c110000c80c00201c090241041d0382510065020f409068403491068603600c2d48005800e12400007100c03076254009922880c0145009000700d203071410480868010841a2441500d00c41410f42010001c3e0a01410b854180695a005003d80f0f080d225035203806010182c2c0401c040034603e184008401005170440110390000380c0d100f11150103080104011079006800002c3c0c10649000001c18001b807551048040c2c410300e040c9a0302c00e240d00d0004094030a0400d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270198884 1250 270197634 270197659
    0xb010e10030c1d011a030718080724030b01020c040b0a0e04060509070b0325120e071502030f03180a0f080901030c1107030201050a170c041707030b011202 68
    0x2525030030203000741500780b103551001c0f940d10303124890807205034004292803001d00000380030300302a8802c6903804002070074280891100310803024092070a94104a6061040c08070126441191800c40202078021a0b0030121490703025008800381c40c0f41000346c6001d40d20608000c0b81500d481c1c0c0100d107044e080940611403095907500c0100d8001d1060342c00303564035690f40b0140319500b503091080e50040c0a036060b0072465820503031441207030307001c01c0c08064447c19801c100e0b02d41c501d0700c601600800308085910500031000e5071000d46495440a12507200321007000c0001e41141da00100c1a52700e40c10b16a284a4195550103c0001802e00a420400701a0060800150005916150701454240103002786921078a060b40050211008800600d017400110300c01402c0c820000198a001d0303950a00e026a100c2c10507020698511038001039041e03501c899101000010b0002d00c0182049070400459500305400e224061a00c40c41c640c003010b04012045001800003151000102c1d20751407015201c11134941 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270200134 1250 270198884 270198893
    0x92803090e061512040b010e04120c11030a0302070e010603090f0b090307120203040303080f06130b040204050616051905030f091f0c050d02010c021b0612130611070b010e1003 77
    0x9122451311002c80c2c40b054107110611000c12205405403e11214000d014141600d480d60b84c030070303420714201c1080181c0044174200b10303d2090312022954050700300c03128030303803030380307000b03516001c5038000e9160041302c00e00001000c61180c00341060440d004020660090100c0e200ca4103814801040c002c46844200250400140c0d081e03d00a400d02da56800f40d52900c0c15807400900004010b4840c210300030b00c0c082842880d0350f606100401454004a00051248254020030f0180c001c039440241d101e880490000180703220701019a45842c0305900b540c206003030606c0c0d20818030031003c10240446d0300912032080d50503000e100500050000405040c0389042410044094014590342c42c1c000800c1c04244104000b810401280c200e4090f00003484070f9054418025504c000560070340010701022442a400d0b61607180032654001d408044014403450110022035104441e800c04981c0146030a034685c1c0c1c4a0081410341e0300303103940151400030700c0e440d042c0c0424210001404000380340007002e20000014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270201384 1250 270200134 270200137
    0x11d100c050f16090c020102091c020a05061603020f01111c060506030a091202010b091b0909340801050f040e0604060c0e010504080703020603040515092803090e0615 73
    0x1001101c003c1c521050621501c00e0907580420046406d40e030040c00a075600356a812013086040c2c00ca0102c602100405000281c207a512a41c070050700000c000901c403810501d40403038024264041e4080b1192068041c4445080b43c84000b04003240150034406403420803442c88144c02411a41c51001c61070980f15000580142d00036110142120342e01c1804404026460800c02d0302210203000030441c00c0805400309024110040040d0155041d844461039118821402d03a2507104000d070a0b1440361918805010b0100d05d03404990858030500360361004040c95041519080505a50320103149920788020701014005070000070398456210a02e0000040081011030310070f40c060b90020500100200008c0c0500b00b848039250304010040105000380c4200150010440354107940041c0d40355228140305007400303440f224951414120760140411584001102c3d00f08103901d0416200640d82d50030b1a40c1000340c5044002c000c100c5400701040a1001080792310b034803207809401035a1600c504240306070316 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270202634 1250 270201384 270201403
    0x80d0309020f09100302130f1b0201050f010303170a1b021f020906090f040209100905010f05040305060604090503040b1c1103090303130c05090411011d100c050f 71
    0x964800d064015468619216004018103441166450030482000103507040c5500020780194050710300010f6055160740704106140e007aa01c10414040e074008010382c4640c2c40800fa40056080c44046158014040788988c102ca80c146c55a000c01705058140000c4144010084114166104a56555103500035441c024003031441c0d0207454a40c041d000114070300704c030a05030107802c5031041c002a44240c84c1c1000325140510101c411014000490f000140640301e2044095000000085010740180d00003187c030050380c0c400d8880140c4500d0101e0200d4440c0507902c0040c00e954858400302e03042c1e007040da221200c50303405202681d140c191034003082d055543c40302c1e4807034246020981c242c1d03420804520480501c252070084a52841c107059007180d69078000907001030341000071440c8402c20046600001002040003805802c03040c502810b06030300d400240d0350408c0c040340d5100c021001403d0300e048001130f0b28100401c07084503c0c0001c80c0803942104400e5040310544140300038481c3c01d0340108500c1e003c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270203884 1250 270202634 270202637
    0xa030303020d05011e090209030a080f040306061401121e0e0304060e0a03030e10050423030d0305010621020d020d0605120a02010e010809100c050a02070f030b010504020f04080d 78
    0x2500c031000d400150440f0b105034891110b401482031900b43c5c100c3c610040c1011204507150243e101e80a80c40040e0801210000c000c12601001801c1d2032544494030292040b24040e0400300704069540c8201b403900c020754041940000c0c2d01030002014034025500903907460740c4d804040402131651000f10411140240154502a40040740400c021f40c0c3c002c9064401d007009890303241070a482c40d6000381c90958060f8001c0d02c05c07040a8960300b903243c41801a280105003040341c00100c51a40c50f5040d081043c1010110f00a001d441c5404503014028007582c0d0417613001da40c2d40c400025204020110210002050003a555003c02c6501e5036110a4000b4203da0f880340800040c10919050411240d803041070500c0c03101d03420100217680582c0c0c221401e110118020308203190315984000e18071341131601805050300624500b1010100d4035901c4400340201f22055000c59000316180c201c40300101c2003511000340701d4040300e030042c003c5040c60b40103040e1004820564a0816841e04402800c11008070850b10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270205134 1250 270203884 270203887
    0x4020d0b15180a0606112d150a0b010314010e0702010f1a030c180c0912060a06030209180304180e1903122f0f2208010209031f0b0a03030302 62
    0x1e80d80d200c078811840200712030f0070641b009030290400c41e0b441e00680d1483c036848400181100041e55082d40d03500310515103907416920507145030718600100f20f005039a100c41c101e04d041c09004455019110ba40400001c01d800300200b60318200d01c21041380d100070f0040d0115500c40300009015100c0d402126214006480700c421145680b0007851315041d104100180315500382d42c02690340e20000751a9a400104a500340c0781d0b94104580880e0308000d08141c101c0046c41540c0421000e03c44a611860949208640c62800c94981e4100e145443c3d03200d19043e4610307041000200004ca1144000302c41120190802080c10581e44445a0919070005440314031002901c1300c1c0c04c01c060340002d10302d588007000b10b0108198440c10004080c00b00c054206414440500b50510810150640580341090714000380d85030b54a0510b0305852140c604100388000080401c1404a05524180262501d80402800030301d10307403510490011000b07230303001d40c284042c1d55225100c4843c4c0d1203007001c0c0c00245001e600d015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270206384 1250 270205134 270205141
    0x9110f1222052406061e12090313060306050a09180c081e150612070902190e0303030c031b091003020901020c0f03030904090c0506030106090f090504020d0b1518 71
    0xd81d0f11605652018450b07801c0020400180c2c2e444003583c0500c02951009805640581c01403d001c0c41600702e03881020040f0030070080c0c600400001000030700e521240c0103c0c10366550b0003d5003030365098043c83d503004888060600140c0c416030b005800201d600b0b030b8200351718040358403400845032103a00002041c0e080490a00d0269020751001640111008000c0102c0100d819060440c481c011b0b0034184100061142d01141c64000c1040b03002510361001c0c115a1094107048030381074414a42c02c400007103840c0e50005180c1d4940407051300c0c0300d0a5203e030707464955075411b00c907141141c5440e0310701644554140103d64980c3c840b079841441c0301c4e045450059640300303100300192a0806298805110f91903aa1003c07529481c017100391060702c1d00c180c5000c40c0c46409403800304201d0203142c01941c0c0120004c000040c00c140d0040d0840f081f907105002840c0050b4a070003049094450440740031f9007104010200d071000801022049a214800a9064401010301800901d8141030394030700f0703c2c8100c07848052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270207634 1250 270206384 270206413
    0x40b040c0503010806010f0b0a0c05030910020120030f0601140c06010905060f03030a0905040513240507051207050702010509100305091218090406060312080109110f122205 76
    0x407501410300c1c100e00742d506d203140920320440e510030509c001d4100010030b2034a40800c901001036400903e030045c41400781d0203180c0d5000340200044805000031140320415080500780440440f8014189040185038a40d00c140065541f040c1c0c514529801e1130b010058403440c2041800701c1806003c10300000309480c100750003080380307903410b21103901d12a8004011100b140e0360801c040401f110402e80340465969950500c2d581c0c01034070560043e124002c0c0c01c0c46464444a002c4440d6101c64a914082002e521a00011289805000c1465542441400c045294580034030041d044880c41403404919000012010944104240d5404804241c03180103104121409002c40315910081403e82814002d400da104070044140082960040340360038080750034032515402c0071000d160085004d280e000613032080203003460000d20515100c03600e80b0321160100e003034420440b0140110002c020342005200600c4c40b800040141c0311162140661180c15844c01c00c4100341200f040c0254042c0005034a507040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270208884 1250 270207634 270207643
    0x18040311030c2b1205040809030703051c02010209090705070204060b040801020a020c090c0d1a03010905150f0f071d1002011a0301060509040b090c0607060e190c060509040b040c05030108 82
    0x503080031401d60f0601200780241e018407041044907000601040b42d0300c66040c071003954420700910540602841d4000700600000007921060040310212401d03206282100c00ca00b07d0055044103a803001c4400302141030180710303c1c060140580001d000140503507403061030040b168003d600c5140c02ea5001705000d6078032901446280412101070310301034203529001c840054503210710312014107056a90000c0da0b141410704074030400b070900c02034001c000360080c60070700f5940c039240181c407524411100d0000424004120030054020036200510725115100c8072002d40e40741100024902941040004441c5241c1c1e5810382c42403501200d400000d102c40d1b6200000e02c0012a044009000e42c0c18002e00b088561281017109a00c00d801000144441d1105d64461381068640c403174003035000c040451000240700310ba9101c01d11545c18501240d9440c1504e20207510088803090000d841001561f4040103140d01a5004007240d44005000142d2003490b07000040442e009c40000301d002078030100c01440507030030411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270210134 1250 270208884 270208933
    0x1050f0f040e16020a03090b0f13030b01051315031401091a0108070902090d081608180916020a02060a0905030a06050412050c0a0f0201050706050f040c1418040311030c 74
    0xb01805d441180c944001d800c91541e442030a541070000551a41c40b4900e003015103842005000302c25038000c0e600c1c2440748900b0f100380903041c415500e8052a44d80240c9503ca040d45008071004081d8910745113444000801c40058030145041d500e54a0034000500c0074040095400c05134401900c0e6035040c000400d00c1e000450f0803102802e071042108030b602e070340c84001d905052036110040580c2d40c140021191805144d90400901c580d001140c001d42203004501d0501c0820401d40d00750020350b803030003410380e000c070742c0d03030443c1409078102c1202d03000542004030042050040d2420700400c25a81c2d0004686482c038881020350310599038106020070403003002a0314040c0c141070301d40542005800c1c0c000645440110b800148058074105003601103901030030aa034442c0d90000000c000c640303030040c00e245100c1c3c003c0390101d4a4070004080840c24686540c0500d05000c4c0103442d0108850070f01d0004810040050402d0b4107020f600035400055480403c001d00d081400d01c006060101c0710144a0041881c145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270211384 1250 270210134 270210137
    0x1603030b0301150e04170a0903050c0103050403050d1104081515010801030c0e0a0b090405010c02010e061e060f0301020a02030c070b0a0503040b06010e19081002041401050f0f040e16 80
    0x7010740f0020280c004904410360300c40c0304070150305131520300c1d000844854070b006681541c40041607880c001c43c0c0190500c001c50703004009549400801d04011011a1001c440040129600f88003140032481e20384c2c082d0b1240d100c1c500c5041d2415031034004480c070b840c072103c43c012500b01e0030b542082141440d80b009018402401c1c240040c0ba5410f41d5511425004640161030700c950f40c5600045610100781c002e2141840d0290081e1aa4201401c1035170180c440c205c0504055030030040070883e2200002001845410071840851a000b40404900310880001d0300303079a4000000011190305507000e00c028610320403541c00656403110017103000d9003495101e500168082c0030510000000d2a040001c9aa00503030003508907260f0350300c4c1001a149000024021504240e02c1e21016000100785a00b28090300c04040484001c600d40c1c4071100c042e84518058041440d4040d12100c5255014401500c14510481182414103002488d0003001303030450f900c5000c00d180c14409100d40740842d0b825940c51207541d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270212634 1250 270211384 270211391
    0x91b17060906010c0302070504060e071701051302090a0f0f0e25030e15091b04060f2c090d09050402180108101a0a02061612020711061603030b0301 65
    0x20000074224400082c00c0724180800a415003013014424031080015240003001002a540c03140000007140c0d0302241c3c520b0204980007008610308501003409412a01c0040c02002d40074440101100a50004810720390440700c81d0101103221509280d42101500c413441180303040754a40002d0412403900905503a680803841d20b03040385921443d42c1c412504e0091420007280400520136000c0c5000e4400c08204003140d0040180304a0f101c0114111083c1c1e450b4600003000400302d0000c00c02203170034500c501c0c3d02e0040c4901d420400c0d80c16020904440b00c21404405009034120b90000300d40100071201c1e6034543d004003003008110b680003865a0f02603d0150380850600f01160240d0b1413402130707100c02a040c44074440003d18428204201c02002d071004888076101581c1254122142d03400054580b4094000c5c4070000b10b60743c1446655551900903a602c4502c91040441101c5c025031102038280c91220310450030444c81e807178110051000c08120080e406492102d41001012200c2c95038006200c5c1c1d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270213884 1250 270212634 270212641
    0x314011b0503010e131a13030f090803120c0c1207021c110f03010e0f0109020301180f20060a050a0815030a03110a05011b090503070b030a02090a091b17 67
    0x1000010350ba409034000c000c80039071018901b03085548024030148191810307510750401203200d40441c04c0b81d504505c00d4950002400d0502c00c01e954103105405201e015600510480d10520303074285030700d50050311503e002440c0c601800c2c561818460128603080942c035001910b20214100303094468600800c3c420441c03a00c4940e80d491544e072000b03c1881074442d2156502d03020072680c00b0340c4401c0b1050007050841d884c1f120043c0206018000fa000c0aa01c00e52070030824004503002c407404840b006500c10b0401c08414280d54491301c4051141040160b911b0049a401c0c15603140c3c14000c02ea003113010345415840719650600208141401014002d9072106140224010b1b1000581517950f0780c0d00d0b0a040100f008154690f074075200031241d0260240d030030700c940b007a824030022282120302562035941054041d2034500303042d03858440b842610b03031f0000d0400008a1107125680a05104200140a030944d169104c0910b030945200440b505014200311244d031081c15004130403201f41c110b841c0c0e80c00c140e03481c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270215134 1250 270213884 270213899
    0x70515010f03060b032e050c031b0a020c0306040b090c010e010e060702010327031d090106030903020a02090f0603011a130209010c120507060b010201050f1b040314011b050301 77
    0x700140301c028001a1100120501c1e40e40030301480440040104685071050b1400300d003094210030740b64400586614090216a154818408480c843c032600d82c0702da440c00d28030005a1070aa40040f640d0790440c001c0b0342e6220301d0780d6000c0c880c09010b1800783c0302c50411410442c844505181c10b2070031460600150085442c0e142e42c11214103e85c4030b10450720142c684401c2d00059026001c40700c0c0000e065010044495041c11032032507101482800780d503614115642c42c280115000700c2d84001e9541c4072601c400100302161098104007201131007481130b20408501c950100b9598030080e41e810500410080800c0f100741000d1240603001c400c01c9550061580d034600110b0f440b004001c0e100d000c056000070b0440c0050740220640030b90349500c0807808000c80c10b040401070158100a104503441810110500025841400f405000340d400202d1007225846042803201151103102c9181c400113818400003001c5038503d61544440520100046914441000388076040c0d09080e401c1404d00005000605c07072003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270216384 1250 270215134 270215159
    0xf021605090c0906041205010c09031a07140304030804210507231207020a09020909282c06041a040201020c1c020405010e09030703050f0c0106060507051501 69
    0x465040e01e548140303441d200e116180c5485542d0726070380c22260000e03000481044000c000880c2074040c1d0000c08c80d030400c0c4034045580130000d100c0030340186181990b4a440b2140c2140c0160808020b0500910103c040f4100e00d1031504106d5045c0d0104a4030f10400090210388850500071900224542ca000c00d145c19000e0214015204043d00d4a01c04602510390078454840d1240045180012034103440c0b80500486020f0340000c20407402811414070000300f0001c180282c42176030300c0082803544903036151420200d000940381f101d1401c54080b21010a411091485901a41d0091101a00c007090b004100302c4c031034a1800d03802a590354050010000800c000d00039484410400b03400aa0700d0b500e072800100e01d00120018000e500940c1180d0303034041c070881060340c26003583c400d0710b0601041e03981704184d4070b13003107401c4803032040702d400030440303070300060b00c80c0004128100e03400099904110a00c06a5403c42d207854000d000440d000003000e400b13022040005940000304103811440640c14404245503e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270217634 1250 270216384 270216389
    0x3070203070807110306010305030a0e0a12080904060f080f1b010207031b030b270109020618010c050604051f02180f0414070203090a060207140d1b060c030f0216 71
    0x20b400401c0c00003c00c600e1044102100b04002d00700c074440d58483c182591a039009011400c081030055880140321300f0208000c20883d030001e204081000925110041aa80700e05012a409a9502c0000c182e040e161802039000c0c000c0342000b0141000701081d6103141c0b20045a05a6007145003c1c030003038003030780e00255100c1500d51001c2c03110a480d03e100206c640140365508010010361400d4200402030402180c80d43d01e542c842c20b84018601101500542280e51010000e50050030801c8200c010010101c3c04000780c000614100030411400e44607a81880c2c0295022a0035812511040c0003040c40b0519840301d52640b24011031404800b01c0d481c0400e000b00c10741c010f008070f80e4021600d8007565030f42e01c5196246c201e804c06000c1850031100003516948150442480303aa00d014022460b140700107052030589002001001282c60700200300910700002002c12290030b48070000354090300104c1d452040c021300041d107805002442520f0041c00014100812070111340c08060700380701e2040342080a108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270218884 1250 270217634 270217643
    0xf0c090604021c020712090b09030a08030c070f060b0102210403031209060c0e0120121e0a23030402031b04020d1d0111040501090b0c010609060e06150307020307 71
    0x98a0301014052160a0389601c2c0043c101480440c4003403e11104462441068040350384d100f144c2525400400d00500440075404d41551200c0300c2d00c0001078100c801507402245020300d090502640350350300d0480c0901604200d8019444486500f0556010001e40444040d441080380401c00402c198400071301480c40042c040000842e2501e140c108143d02400c25035411a0084c0903e414411010b055440304c1981140001c94240064007030040d00d40800305090f281c10083c26880c801c1c00d0300100141c1103c0307803500114040700c000c1c003441d03e40c000081c545a20652240710380901155500c0b681c00300300d5400d13444145c81c20410000161342c08990b051100d00303114aaa841e107008000031034003c0c000e11131078082c1e141c0340003800728000055030601d00748a16400020300c80300c01c6650041150b40201d224213400700e105c0d110180030301d645800242c1000c6100000002d03105580700c41d000e041d94540d07408414884484020301100b428a541c803101040100101980f071418449002941c074490070401a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270220134 1250 270218884 270218887
    0x20d0c060906090b0411040e071208040b190912080301090203040c09020313110f030a0b0a150b070201030b180c070507051002031306020703050c0405071704030e030f0c09060402 78
    0x400300480c590240e0002604070104110008081c584074842400559040e10f65019464959075145028005e00c0300c0a01590b01400340300c1e152108140e0305480f030503002c9445400521021456100d51005403208100491400d044443d041e45c0203815074081360841c0010b04804248107010490180440741115060040140c0d01d581c0c60800b1946030100e60000f0599500010074844a107050710344000400d40611507907072048254004020641303120000003509500302400d50004a03400241095002139007050110303121082580c0b500d005245600300021409001c1041c03415940c0c1403107132040f03c140581c1d18080328100070a00e400c034510000c1114844c00d50019041c410420b003032101500501000e49415560304a200c070281d02c940003c1d4681a40580041c0c0000d0a940300040c40ca04894100c4080d00c000c401c240c05020141200a00710001d000582c295a5a200902031100b44250f00a0703581c84141c0d5100d004050400d420f842d2100c08990090a004040340d9806031240d41040088a006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270221384 1250 270220134 270220157
    0xe0a0e040b0c0a2609010606050c0703020f1c210809150915040803012904090203060d0506180f0d050d0b0102010b03030a03060f0905011203181203050c011103040201020d 75
    0x125010049000041c030314141311004e08444104002c0c6143c0202101c4009000030b80c1c903441c0442e418010815503040d80d43c01072804001504000415000b000c0014000f0798004051201404c42c611010400700d03081002d0341a0b444045070900e041d500c0c01c61091070000034a00f0490100c9641b5240012205010505200820304060007041901038a0b003c40000a00b18500f5041041c2950000d00c00c1040701c4003107000b03900c0b00c901c821600d141071501c4104c00504107401d01c40340030000d42005189a8002d1085108400800d0041113680d1060481d00038a0080e0718502c41c0300d83c242440c9002c8070815031311101c19402c509400009584024031702480000e40003119000403400f618130f041a00b42c041c0000076560711f403117900d5041201030760304082000c03a032650b8545001084410900c2002402c401d8030b0003034030010b4486d5110380707010741c0307103003481e94941d501c1e0380c522070071042020b500720042500010340d601040c10a0080e4044010b880481d2400c40c80d142c0c0000c0d485039070a204c4002049005001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270222634 1250 270221384 270221387
    0x4180515310c0203041502070b0324060724020c070311270114060a09050909010920010206010801050402030703080307020708010c030e150403090b090609060a0e0a0e040b0c0a 77
    0x60621038020407002c0c0420b11007502c02030b4407644180621090808071414501103c0c0c00012644200d4520100a0b4a141d490b0000c07026240c00451a002046a402462404941c0c860b406008011b015001820180c1403c001c100d04040c2c08030f03100f85c1e50b14018040f0600c2c000c40810a0000c981c0c0150a4055501079040001c0008840c105407042141c17110001e010304100911002c3d047c0e58031441c0400b00b0840240403c03940340500b4204400141c03407230000780843d05004d0807032600019008004100e041a96a88448400000104ea00300701000c240e541d50755a4100482801014018000c0105050540100303454203220700014203140700c0000412030f014420000c0b6001000480002c010701281480c0c001d0241818854003c0c3e248209003009405100081c2480d004130b605031503030280c503480c040c1c8042541d006a212240c1c065018001442e107a240d070401001102950b030740f030b5a8901050410003510800c40c0e006040016110410080050b51204000d03812060000d8416100c4040303420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270223884 1250 270222634 270222709
    0x1110a020a030c05010215040803060d0317190f140a02030c120103030804030311190f050c1f0c020304030f060f060506071a09340b04180515 62
    0x20001c0d04810100000001d1103802c820640540358240e094403070002c49100c40035010390081e50f02a00e519010008181d2a00d88134103582e155503c00d0411050244002d01e02c5031207810111040d009811803e52980d801c9141481069000740c0d40010401640d00e8509220b5034240004202c6401c1701d50000210b0385589030807056a8181180c40b542540b15a16460010070381c0105440460109007010a504a40c3c0b03c0c0d042500c010541100400d11462012a000c03180081d440108009202081005101c140001e100800240b400300d100720b540c003588a141481100e054440780c504540083c082800003640224096443c1900484040f55000200503031070000c0100341e100b82d52000300021202c04100e042c074034401e0390369442d04041c441c1c0d40d86c0700c81c2c2540340c010050700f154a42e13004020004001115000300b600d0300c22505481103c15403105015402540310303411602440d03c9242120290361000d000307041e13200000550700c01d040c02200010a09070100714012010200c41b07411050a565003600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270225134 1250 270223884 270223903
    0x50102030c0a06020a05070b2a030601080615130803180105040b0313020a09050a0911030106060e041104120f110d0b041104110a030902011704260f07030905040506040504110111 78
    0x1030440c070740c1040d01461500703091030040059080b4040303801c5127102e40c580c010380780b00c1c0b1f00c113031506440b9645010030421181200152a0b030040340501000c0e6410024020243c040e10001005642c0c1e40ea0301c142c8444901c0e034803404203040110410040c840340001d40c0c01c4d01e40002d0180d60b454407401d82c901c0040c0e070015841c0c200c3d05071146000c04004c02044203812202e00c650089d60010507541d07258051500ba190140210070126296190107285030030b0a0b48280f000429200c1c4c12030a042d1102c8170540c0c40465a907060f285035031595030039010300641c1030a015a00f84100e0309182d280d000e95585807083c030300040001c0c00001000c280040341d6215600030413811002c4841d07103550f640309200040c00030300d00108241d00060700484822000440b064041d070146422841a0940a00201071085a034503041d07180c80c4e4400c1c091040d040108135003005013116a02c01d4455001c0d90f81000140401c0319002080144210700300024400882d050100e001e0743e4520a103041d044d22410914050b10700007159 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270226384 1250 270225134 270225143
    0x50705010e0111031512030306010e2706030601091503080c010209101e051c051e01030b01060e0d0224091305150d1101030c11030a0e0406050102030c0a06020a0507 72
    0xb03284143e0983c2c0100110f2103110f402c02c40480540c2d40c030f0144980108401c4010456600410200e026913000d02d000f143c143e9801012218010140400c6142541c45291202e000f01d000300c1c02d01980b1701d0300380300b141e01500d00c12004000d00c481040112002c0340c9244009403150358000b40d0540751141c20f4046070342004010b0300740d0111080e81c52001300442840081d05c9149030700050f04001461152044404020a00a003001c04a02001d045001000082c0c15100030840841440b02d641019442c00340c000c0d400345e8450002c0c0d614086d406010240c803110058443c8010084100051341c4040e001825030042c442481c501c42c83c0301030310350114468a55416403040c1072100149103809107405c441c4c45100c41340046072560204070140700304801c1d803200082c507018200380c10503404d512a9110442200340740c03805001c4d0400e0031024505651148107042c001030000342e0845050709050040100800003840258a003070a8006940d4644d092014010200e039000604a16851301c68016629600d401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270227634 1250 270226384 270226391
    0x6090a060305061305070501170613020910120c171303020115080f0f0105010b0d020306011b03020a060b03070b0a12091209030302010b09060619020f010f060f0b03010f0501050705010e01 82
    0x1000001030304c0320000004540320721645c100440c0c0c951127800c20036052540c65080c810582c403507004010b641c141b003885121405a0a00c031a58081d6607000004031000041e440d207044080c003414811080d07544202040080c040503200c2000c86075260071000f40d101c0d0303800c4800064141c152504a0140072087d0510480c0e40549201081400000c40c1e6118440001801c07141c01012200c03551f400d9072400d201e188540030060150001984c0150001c60348040145800880c403000441e8004c10040301050660040c1c0c8910003c108100c3d040c42414081c0100703d000f00b00451405541d00c1f0036204c0c1007040d60070000501000c0000410540194120591205c000b030700c070322a00800100440340d02e2106800540c00e02c0315604683c1018078602e402404050b00c45803801c10801d034403e0b030008601c507190086101b03a0b0300c0013807080c4081c407070050f00402c0100e011500310700d8142450303040c007620740003901c0010381000100402110700490f90201c41080c2002c64982d1a01d042c942d00406001401d44c489509 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270228884 1250 270227634 270227641
    0x50702010302132706080c0a150c0507061d0409020609040b190e0910050106020309041a0409060e011a0904020909030d09050607030f0b220603080c0303060306070c0b06090a06030506 80
    0x41c814160010484c0043d040101d9607982041e03603516100071400540240401005104000f014403c10303101c11b0090820403103107500303592103500d0041240d101700e002480c020040003a208020f482180202c6044805004584098002507002e209842c8010721440c0e403101c255090303480d10041c074402e0880c04100324480c6c82e81d45000300c040d4082100c42030540d0060b9014502d44003418855203050399040e500560610201c181480000d0000480b1503400f07906844042a150b540c6014a12501c0d00c1918041026a5421070090075180f000000840c0072608806102c02c5440f56003200b6882501100e03200e8060f111500c0081c10b40c0701d0360044017051410074060500b80800043c0d01800303a80540c1d410051a2030040544080710300e138140c0241c3c014150b4070300e141a02c0c2a0344840440701c154041c00601c81c3e5581d038484d00d03150310501e10340300703e038001104000c01841c080c443e9a504c80c5590a020400107040e41c1d40d010025801000c036803144c1c0400340814100e10566002402540e0f0100490700e8904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270230134 1250 270228884 270228929
    0x1212200604050a030807020604110d03032c010b0117060f04020c12041d040f060506060d0c0c0605010b0c060711030906030703140123130b04051617040305070201030213 74
    0x10210f40b080e8085802d440103d13200078800102c0070302c1070740c00c528501a8856290104040100341050039410551120201544c1010b41d148005e82c8822080c0d081c0010794024543c41d080d54411420181480f010641b0141c00c2140c858034690710240c100ca40d2044401c10100007002401185031000030b910500030603402c080f41d60b86c000e1082d0742c4840403000000c0449001840d01d508116001010b1229100107100006d410390005078000400502007420184043d01110441c2c2000e080c202c0003a00001d04101413107040d1144602401c8105401490100f030492100e6440e800a020041000703440801c006074030b0400c0c403c1c2c52003a40c004126070b550341400c0c2c00c0100034011a001580c4036400560001842d5060405038640d41d03204401004152980c003001c0040540018052840c3d0b59200c0001c0803003503903280300b1540304404800c00a00740e21b000b000c0081c0113620458904100c5080d910500c00403076004000d840e0b4440e030929000d07940d9102d012240c1a00046a4000d08034001994070003031004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270231384 1250 270230134 270230143
    0x3020c03040e0f090c3c03060712140106020304031b090510080f06071b02030c0301111e130e0a090c0806060f010905090c03070908030c06060a121220060405 69
    0x411074941202d82245100042050800038440901d0386c00260862078503a051150040440301050403030b114211030b070b40c0d00101e4100102217410b000021812207610400503854814900c41c1b8a590080203001d60400001968921890001500d0501c0e4651a103100c1e0342c00f12182e83c00390001d18014001c0341003482150f0f00c80c2c4928000c01055000340602e1240d91080003446604c0f5401d581d03142e0740e00c2480c00400444140315102c06907014000c1e001c1089035500d09010710140b03995a0010207a45100d0074a00b1140020b0720b40340380154100800c0105c410103e021001010780326000d034500b8040e1901800c00c0000c0a04220040490f01d42c03000c0011040d40100352548505d074140d61030f02d0040c03020001102c1410300780c003605c2d900404a0000c0b4603a03075a88400385a2016050038640b2095885858081c9190801e0707040c0603590f17100808102c5a030900450040080c00c4050501034034291940d0346520701d0a13070603d900200540c338800100300e24120310940000d02000000d55000741071505115455 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270232634 1250 270231384 270231391
    0x91a1608040f06120b042009030f010207050c0f061905090d050d0201061e0e040f030302070c0e07090b040b030610051306030f0e070e0103150603061d1e0a020103020c03040e0f 77
    0x2524070340383c00417003282454018480d100205403c44500100b65140c0c003801030b0404c100301505489802400301c04010309100034003c50b40940010070390b040000382000300c28041440710724060481800348110104110040794a00c00c0c403410a99241c64000011414056000402504078821a00c01c0480c0d15019480401510701410740c941d034280840703680382e4000300b03580710350320402c06124006000b2071410541080c51034402c1c50090710300081519040d035950419002506400003400900c400340c7d0300005103a0040000451560401c0e181c001e00340224040189100c1c021004080c1e400038440c4144100d940c1d500209030801803007621104020010212100050b4200d403034110002e00c1c1c07482c00a910340417190071a42144990b070966480381c005e699a10900b8607155120341c8040300250180c000c1d40c009030582c6410301541800f203446545000e00c41d6845203039002c5540002d88200c6004900041c0b8039070207003409650385a000342103138910712031640310099407081c400074000c98444500c0c00c07500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270233884 1250 270232634 270232667
    0x3101a0607150b06040621060906230114041e0510050408010506040905061b0d020703032702030c101e0504061103030606160f0507030b07091a1608040f06 68
    0x102940580130b02061380b060340200e90106c0c400701e000010005a01c000c1030b00030007003940046102c0da950b0002c50243c90b003603040314045401c0143d040d140001c4002d80c3c080014000d2900c00715583d84006114040c2c402d074028549002440032510214682c40f241d618020200989020340000031610010115080782c0220303030040d424600491803e15140c0540c01c01c59411101901c4103889048095580b5200400c0e6a004864180000c0000341d0f800d00c0a030820a019840c040783c519100162040010750600c03c450365910304010000241c1c4001602e144610000d4588000b9180301080075a40d503048420b40d9103c01d819185078440c040c0d4080080c0003181d00d1615259908214800c10710f0301d80c041103610075000003091281001a8100c84a03808000703004461860390b628154a070b40d420f20744243c00c04e0311005078400c1400311103580040c1c04001801d00188180c50703004a14260f010701d00c1640c01d035402c0b401600344e014081c4850441120010140c3c02100b00b501c60b0b454801904d81c54008070801d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270235134 1250 270233884 270233891
    0x3130303030903021002160b3d060e10110708010204120213051005040507110f070e060d08180621100906060203031609080604050f150105010c02040c03060807060903020307080c03101a060715 84
    0x82c9503001d80c1200e0040722f0000d0640000d80e440e1401201c80314008244000d4070310851000161081080c4010f002a0662600b41e01c030101003130040c002c00002c26800d83c15040d150908205a0520303005580741030301c000311004940341d2101d0004450000a102240c5464000c00004522400000402e507007254960700c81f0102990350f200400402c0c5044880140640f5801c001e00d81d1204441d07240c030111054014816410402680c8503400300303090465042645407540c1c1d091025407954600300e8401081540d10034007005041100094072170002a00044916800081100e103d038002c00022024020b25001c40e6010324003800c0580e40e40e000c10070702200900410000c15a5044004641ea040c0c4034103841c0c140840c40b0325400d2000800c0c02d02c00810426907504004151041c0500030380c0c0041c11f06903100300b40c16086004150401c03480d07900c9440907a000340c1c500b694907240407440c0d0001640000300000d07900340108076040c13429440c143c420340c08a000642e200801c004180c0c4035502810066040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270236384 1250 270235134 270235139
    0x2130e2403060103060905100501030303140109020c030a2307050a120c0b04141f0b0301060905100501050c01200304050c0a180e03130303030903021002160b3d 70
    0x80d06003500504040c0c0580200c0018004180035030004811188140d007261110103c59a003d01190400e030000c5000a84a540b00c9142c0b00318150494098000700008514069880e80c0e1940c1d00d11803200c6500a0042d800010030302c0c0bc081e10411400d20102d41d5100d584c4010500d4615190310300800c04807419098a80554004e510640d201089258800c1400c0d695440d40c0d2242c0c0d801d1105d005029500c2e220f06040d502c0130a0116068503495410707001d0100d080035035001010309580c8150070001c0b200e890641080740459401051034100c41007030070b20a035504161103009024120a00543c201000c110708080680101140214030845c0120155074a182c4514204440c00d1664840c1a00004041401404100b80e0f5480208201c5100d0b0407689400703695080303803200100c26031081d000309954403d800107258040c44001d40008504604601e0400d20000e0681c540441d0300020300091043d00c0081e89405c038000146843e06c00040c40e61003c0600703580b0280403059001c008400340440c10000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270237634 1250 270236384 270236431
    0x3100b0403080d020f07060e060601201c260703060b070507030602090d060e030a0801060f0c031b15050402040b010203070809040203060d020a060201020d05010e130b07020102130e 79
    0xa40301500da111a502e480c10030802ca140300650004024005904800c01c54100011590f22408041ca24844060200c40c40c0060000d020500760001a81c0e44006035011255204404210131809500c0003911038240346508900301c0b441d0070301412028203940c07500078107000c01482188444c0304e103005039400d01010340c03110038001040c0209503000303110340c3c046802400055542c1d00038004c1c00d00f02424480b000042e680310345065600f02c04006030981c2000401ca0200703903004201c00d01515560404200c1c40c60168001400300c0321307400300901040554680b401d101c50080c4026200c064012620f42600403c1c2e4951a0081909907006c1340f24910b0190409000d50000c0b0030383c1e1115401c03518446c10310380a01c09020295000824050b482000303032184400507034488007100040c0050350300050300c407100d8401201c101c601c10380003680304600380b500700201002040619102981e0103006580c8a0321407240c1a4060302900c040180c2540c140c00700800c80c2076003656958812002420b18080119520f400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270238884 1250 270237634 270237637
    0x190b040204060c26040608010e060f03071502030403060c030e070501080702030a0e030a0203060702100c08101215061d01090203011208131d0906060306250c0c030803100b 75
    0x501c0d000c569a4102a80810100202405103204226204050702c00b405101404e6502c43c0e00a440812814401070101980b90701d10581d200905031202040b00b600d01001070b5864180d8415090400140d442e00c9840324401d10a0310011513000e041072080014002029000e8000190890700c0d1744190f601c0020039600c588040c7d80590340315000303503180c03c105d540101c5d94076480c00c0e1801d416124800040f00181c50400c03400e48910f000d940074100454101c0c144130300b5254060718200c1080041d00a105031500440309080848922025803c0c8507401da1412403c1c007083e41003062542032a000001851000e442031208038442c01004455480c1e8841d0380c044102c0c0070a02401801c0130100d40660005800c46c1d00070b0400c110001e03030319a0260307603501f42010240602101314119141c448140030b03c1d03140400c031084e0054011400341c50b81e03240c10b40727242c1102d840054621001000ca180c2c40711180f4002c8115002da40d030840c081c490255281d040000085c2d2084e00d02d5209102c00e0403001030010380c00e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270240134 1250 270238884 270238889
    0xc030f0305160f030b0303130f0b070c0932010801060f12030c050708010f062322090c03080c1501060509060306061b0c10050a09090507050909190b040204 68
    0x15101030031a1600b0200726000705110b0550024155241401d5445070b40410183c2140b032103142d030f41d000b02c5051902d00745214005610031200e0760302c103020707440c00600000008019203004600000d048440001c2201e00040410b4491140403840e051910140c050220040d042e100800000d0003155034a04469540000c14811448841481004a000a031051603580b2013a4054001c489030300e0b4407000701e14211400312a601491030798a00041069254003072080c0e00d0420305440d121040d68a140100b080f00320084071040343c03509401148015001c203075110101e150381002e42110880d4491070060743c0307580000e807484024440c84414060401b00d000016042c1e400c0d960392103003403205034000e10895810203044a45e10840900000101100c02c1008003080000d900013088469058021301010702c0c1000b4280040240422a8400d0640c1080f00602200c150800005070303503036140070072500750250701c501030707440748541060255444007a0928190401a05010003c80c001030302008100d20851 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270241384 1250 270240134 270240151
    0x5160b07021509150114010302040f0e060102120307051c0e01020f0c01050a0504080a080703331e1205070e1e2203030b0102010605041508060a0207020a030b090c0307060c030f0305 79
    0x580140034141c0c2106c0d100751050301c18107000d400d090303d03403c0a04004080d42c011060b01c0c0d1034001013042e20b40c0d04200c06051090010f080c00d00c4c1d4241007000a24031b2107500107070310402c101c440c04202003401c41d900450010005000854072100581c00d184a141d100c240424120760030440428490003207881041e002d076500010a600d001c1e5200000d4402104c000d00a074103050f6118050424100360407082403061912890010344460110005d01c9440c0171500000b4603c045072000107a81800104201c0c1a00c400c0c1905403524130045c83c01500d083c1440d0400f030200c811140038001107001d25990b0314040304c02c070389866003655038003610f0340070002c0407040003885c3d016082e4826000ca07010b40c0c0a1404980706100100720703d5100d41c00314054520304036528070400010b0904100b06039050140300e40213501f0500542ca4201c0a400107481b00000703000190150740301c4804194100700c10082c21040c1000a02542c08c201e50b588006480b404210900382c01003810005441005403180c80307850702c02c040a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270242634 1250 270241384 270241423
    0x5060307060905090c22050112060b04120c030602120603070b0a122403050d0207080105040510020f040906030809041d0a20030303040809100c030504030305160b07021509 75
    0x4000800c5206580a4040c01030300d00208211041b00705640031613802801c03e44a046d104501e04000148443c911100164480c0d16003a401c4c842d8203400001c4600300c9034072040d80014001a070405119200c000da0000b800288002002e0715942800101140b240500300c0503103510315a101c80d42c10062140029030340c00664016025912000070f68000391402001c0601c005101c0c040304081d1180c440140c10584655010b90f4000c034100d07a0421800d07026150b01c3c4000d02441c00c16070b94103544c2d00002545034450a802040403940d183d004000d94004207000c140070300582c2e6903070a00d10041d83c40940310758001e505080b9203421062403d210046005906030080134002041d448141d502800001200002d000c6040c0c1c82110750b80c01c1002d9070260b40078000c0c01d61f9030301c0c03c8400c100f803500201c100304042c0040541c50001203500002603404503a0503017400d80d650842005580b4144940902c0204503940e10f41c140171078140e0000c0c0035180d80c40b00d8081800d5a4031a0a00c0303640d81c0f006c42c078490156801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270243884 1250 270242634 270242639
    0x612050705060d1b020a022b150b1c0203010605040506062b1113151422090e0c01180303030218180403080604020301060e12160603060306050603070609 67
    0x2404002400e800264583c00034242e410560342400040c600d200d0180142c1c003018842081d4038001c101c16002c010980d641144040030007a40c06071408030750702c010380075102e4090706480040741d94011118640008248541c4c44c0c14162070318040c409482d205034065881c1140102e024140341c4a860701660006107110706000700c501c1160002c01c1780088002055800c0003031148010210b000d002d20b4120030701c0c1041d45404614101c00200701c40ca610031a00660054450280c141d04042c50310452141000060307500c03c10000c80303441840840121590090030312800050a808552040c120003003540e06032401c02281c0001150044485039401c4ea804000040c1040000c1c0207034010400103008084224082c802a00001e0340302000218200344032910000304402c06034001600c40d80840300b19011411941808801000b8000704280c0394080d100c5107001800190b41007003403800c131501400000c014940c40c0d140050180c0700c3c40c842100c25504001c045015441c003c54500309a61040c0e407908045032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270245134 1250 270243884 270243889
    0x106140603061309060c05070512042d0302060f0316090f05061305041407110604080702011103130f17010207020f010e0d080d06060e0306090a030f020f0609010f0612050705 76
    0x95048410b43d052a9440c04514002030b80f600614202003001d0711602d8841903141800740c103010081c402507001000422062040941c03203c00003880d03000c0325130100700c01d540141260b0034900310394101a611400200700c2c05004031041c0021480303100107180031081400183c1082d607540f8403030300400704251a40070f0140700c1c50070020064206484654154608195108085030845012031070340c4110716840820402d12541202203c0c24401000008040364601615081c0f0743d40034280b4002e0402c1810a01c0700410f02c81001502c0d001704400380d0a00d151695444004900744c00c5114070740341d040350140035a034502810710903201c0707003500504084a4002420011940060190a12903200700304d2900c5101241c910030140c18441c03c0544005103890070484043d12460408200c80d00c01e40c40b81d420000c4083d80480c1d10340420340e05090078502d0100041090303062070900842e5003c1403159504100d00b84070150021100c81d641400100207075034039014020010301442c1d00c080d0056018800410030360 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270246384 1250 270245134 270245149
    0x26010306020d06120c0f050a060909090212010e070302040b0d1a0606040b2704060311010f051c050612060417090609040f140c0913110c0a03050408010614060306 71
    0x3008002c000400c503441d00d590119a110140d810b980342d11500b001030246040d0080600f014040481d0780c1c40201e464440000c00500950044400300361b00e41e82003c003152a008511a4020800c4000307020005480c07a0b2307660340b82c94921041e8465820700560102604000a9a15120350412091102841b4086114121200c081d01480d04102c0c100b1001402e40803d502400c0045024034490144445001520174594200300002e44070300c1c5000300420019482039a40808130b507081c2008485a02e6000c41076644d402180e01c0d03049420650491f1040e40300590740190b10401c022180030703070b0382045201d50a6603040c08640040501c1c1d0140750300b0424019550241601c0b004c0100107e10b80740480d0301160680e00d1000c00103d0607500d91152082e4a8880d41006034080400070045040850344000129004c40009420075110390b25950700214400313060450b0724024000c02103d416060502e4002e241c0c1d441441540700d19440c09002090741b0310313071341c2400507149401007100303065031109000c00401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270247634 1250 270246384 270246397
    0xa0b0603150c040602010c210c03240501031d1509030c0a0c0503010f09021f1715010f09060903150f1b181d041403030a020a2601030602 60
    0x240c464580c00d903000e80e5690418511520314602d030b41d500c4518261019094402da44910024400300e28134420030705901c100084c0c0d103455001710200c3d40c400c180d60706400502044104940240030365114402d41c02a0203121802c0f25002c0c0c1e420072114034440c0305044401b95102003142d480e00011064019512000c95031a00030313040300140d0f440c099141d01540d10b41041000d040320400c950284c20031880c070302031180b101280c120000600034848540c0c0001c422500390004a1004060744401c10300062113031860040b030140802886010b070030b0401000200f6449800014000b500c15208a07401e640b0035070f1030401700c1e099a26658040340c10b42d601e411403040001c032001d0f6403580d80c00360030140c881a03004111160a0020000d41c80c914034020040c26007000001c2482802d11000003001241c07111100c1307072000140340c0049607813a110351411040701315442040892501c404800d00c01c484a103176009054000d0079441300c2c120058102150300485242110856801900344010004030340d064004166 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270248884 1250 270247634 270247639
    0x1c0e1305070210020c1006080f120a1b0803060a05060f040306050a020d0c0c0210021b0d1e0c0f050409020609120c04090525120f170a050c1e0a0b06 65
    0x152422a03041d954100c3e0044600b25203640e21900111b10110704030312078a400b0f41203000c0a0007140d8004000d5035075030300707042d01c01e440d03688800a950084180b0802d0042645420010400300c0c14000d41000c020030b40040d17402c04d204010032540021a0710344241195411300c1c84152050816281d41c44010051400400b42022203400f0012a0a208407620036070b150f149043d143c88103c440e0a0052107006243c00c0040c0c13096600c6820802d01018140c800708065480465108038210021b15049041901202d021004c48115500c03000070450800d04103402d640b41100b513061540c1d990300400043e291441c2c000b94001c1010841801242804141c050741400b00310100c0e850b02541b24040340450b8040401910306400542694000380007205260500c0c041c00603c9112880c2825440e0070b040010350703402042c00e2419044182040111030828095204820f143d540300d050320740014000c3c1d0b00c002011909809883c600380384001c0c3c0c40c0080806610444000c042000316999001d08903040a4a0582e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270250134 1250 270248884 270248893
    0x503040501090f20060f18060708070b09010e01021204030810030c0b0703030b061e070c15030b12010e0c0f0402041a0c0601090506010c0f21021c0e13050702 69
    0x2c04a500402c03824920307842040c460080d400d0390f6002d80b0030340b070104001c10304c68807042100c02410141c05d010b407000307010030001070888000c04500003260742c030a098009150440129448040c840e410f0285031041c14a14024010710b00c801c16020708078411800001004200c1c031340402d01081c880d00403264454020200758540790f8881d00d4426040007140c0c008050924001005000c0551501a040012405035902824140c02041320001801c01c2d40c10724040820210303003070050161401c2d861004080000d502503040c80c00c50802406002603081c0c0364040c0c0428246c1c26020b150500c600032041103801301800d540f83d091000c1010b004150300405034095001e002c04944081844003152841e00b036815916941e5000302c0c903e03410840c05030b01c08011146810308001321a41c10200d014125030303001c001d003007814400e4500001c58032058481c03c7e038954132208031800f50a0300020103600c1e0443d034041e10311080b030507082d08480c5400c0303108055070064044840b40360503100e0780d0460ba412082c1e900546 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270251384 1250 270250134 270250151
    0x180f031c091d041101050d0f0606181212050d0504030c110324090a020402030a0b0f030601080307030e120610032a03020d0c0503060f060406050f06070b1b0d02070606060513060503040501 82
    0x3003054401d80e60f08c00760300d40e0780c3c0d80b000c02510340c12614080d40000302602c01c10f0b03001d2030040c0420b0503208501002e000c42d04032007418401d252050381191494a1a090b082041d0f050034140140b0310b400240c0704442908100c207541020b460002468884400d500d000503442030300700e800600c1c0020001d0103c5c852407244962642c016038481c00070b144a08200c24000074810740c40700820860a01c400b241da4040e400140c01031018007008002ca42055816040c01e40e40c14405402140da240c400103000710040c0600c800b03115440241c038036100101c03401038171980d158030325030f400b034016601001c0d8101481c0e410001d0104014100b0380c0c410040540150400700a142d52200420f0910b8001c80b0900030b03566005040003039074a4035108000140006890031100c940040b00840d940740700d029006803036443c4850004080002007802400b220a2240c0b6a5403140ea000c2c00c144042e4005072401c540140c2441800b050040c4154180e8414407890703810b50f282980307490760a80703443c1d001070070689180d500d92151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270252634 1250 270251384 270251407
    0x30405040c030e0120030c0f0d06032111070314010f021b010c14040e04241d01050412080403090e010f050103050f0c180f031c091d04110105 62
    0x207440c840c502646020401405681c081c42c02c68014480401860361905000800550a5806c1d20350240300800342d66514101007809000303034021030240c0d1460301e007800004010810303054030081c0c081e1041e03400b1406001d0b18a01c00c0e0b1752032001021141231035201c0d5800300041882d0440d03d01d00000303581c1c000200244c001003440160b9009107100c00a2549505141d50041424801e40003805054074055942001250707004005104e544521004a5a00340102c0d06102c003000b07811415100501c40c0c0c02c00711005048050190219544030f4503603041d0324919881005041c003590b0710039580600040c2012500050a0350a8800a40f0640402465060114440070ba0601c054007138480500810103651600000500351503004008591410400e02442801000002a00d80900f04079000b41c84040001001c15000d590341101d03d50705110749512151000141c80910203a00c0c0c440d030b00c0106081c4c1320401e458020014070703d03200344050b00c400010085805210002d220000500d003c91400c0c200c8101c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270253884 1250 270252634 270252641
    0xe030c04200c0609060f150d1a1603110403020d03030c09030501090f0215120606180a030f050c10020303060103200703090608070207030c0302060307170c070309120809011103040504 80
    0x522205035109a00b4805000d008102c080d1b8844154280e105482c5003c1c041800c81d04841c1d104d07540a1183d001c031840400c92070f07400c00c0c041c10303506604005180c40c203140c0e01e0845d4040c1000b41d10210345010503030702c42c2008603401c4400f5690090705403002e41c00070b96001c400510355020001c0800034400d03808000100280950b01005004080582d500812401004800c4217400030b01d500050007007180c0e144039500382c0b41499001208442280d1500340c1d074214003e86004803101c3e04e500184248021080180c0302c681a11018000c101300c4003118069028000c854a502102201603441800058501d6100b5081400020a0710741e00210a041800900c001e0780c0040d00c08801095107848140400c0b9403000c01c45610180b6803000b071440601d036851b10b1007400d40d00d01010307004000000000d40018040d0071100e03c0c01203014603241c49480c1084400c1c2c900e40010904a0010b202c0410000d2110b140c0003542c40c0c003542005030b040c90701070018015030b207810a45d0030010341400305000015803540d8622 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270255134 1250 270253884 270253897
    0xc02030f0303040b06090601230c010e060108100c121107120c1b1a0c1c18080304050604090b030a050d02011406060c060115030609060f060305070e030c0420 69
    0x80c0110b40342e00b4a480d0089500303600078482c601644980341003121980c0d03c50203070000321a28114049040662005034440c9120b020204075940d030814401c0ca50010000803120704a4140d403040d16002a000c0c0320b00c400752607a034010b000014600c080002030001d2300342c0c03161083c111205c0c0c00c1442d10b5469951000c001500d115a007020408080d00c020612003d07042c810f8240300f4102010700010304003505514280320004901c003c0040c0801c00401441c002c001062244244200b00d0254041741d01000380341140e80300000c0304080c1c224100040043c1c0c0001a1010b0b214020101c0c0e0820b0b04204450009084458242c6d5040c490740b0302e9000410003d0142c4001e441481d0b0010070303403031142030910300c01d940c0c050051405034104000c04172003400f000c6200307819580b1100e030314080d4074100c002c101c010341980d0f003208031440e141c07040020f0703064030240710034044402c0c544052203076503108202030320a80a0b6884081d0541c00500308928580742075072160512513103904081c1407018049029141e10780020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270256384 1250 270255134 270255163
    0x15060302070b06040504020310090804050a141f02030403060b0105120a0f0e0705030c0105030403140406170a02030402030c0907180e06030114090c150403060c0206060a0906080a0f02010c0203 84
    0x1801000b030003003010740168451001d80c3d00380064103203a4040781e075510031702603000f0f00715540314824000c02c880c0c0400c136401410014a00d04080d502d42c00c0c40b1407070f04c00700c0045500c2220008400c100040604001000162094015508241c40d5441d458054441030300554100300f001c01c1010460703040d05030464014054107034000341c0c0b50f0119410008035071022542e46e40e00d80c05800b0130001a6400502c101a9142c00e10300f49440fa01c0f0707890143c811036002c02d11895004004500420f100b43e0120491200071900d913010309207602c810803520102d201c29140071390140c114044410307450030010041038110005103000c070104a000310304441c409940790885043c074a059010f20234607240c00d00030f00e0b64640c0000f5240c3c103d8203007120b030b0703c1d0b1b2030150154541c080c91241d00d14909244540e02598001c540018046c414000705280003500d8090468519118040765000426000e51511603c01038401c40c4006008140361611107024042015100300d04110a44c4095001a10309000d03819210401d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270257634 1250 270256384 270256387
    0xf14031005010e030102091c050c1002030a1e2f010606050405030c06090a1203030902041a0108010e0112030809210309010f0207080d0509010f06080c0112060e0c0d15060302 76
    0x140780004112520703c000b00ca1203a030051110405c1030b921013241408040440c0c00000489609280542c10407540210b4a907104588000700030304290040004d05602100e80d8451603407500072a200c489452840603600300240c404007135010f015034412070461024507841c010381d0040441d0b103903441c01d580b4150440c50000328049030811140c1800c01101050100480c0d00c41d007032901450210f82026001d12481d070150200076121f4082c54006d500c4910320341c0d009007040c0030b440707024146944510181c0030b42030b0010344103800008085230440116410b8803d60091403280c0d4055403000c0307491020140003460940511403c5607800c00c82e9500c251010081e195206890b850000c01560860b5541b2101c000903500420030100000c0035181101c0f6107040c20070001407103880b0358400038011301d040380c03010702070601c0c3c03403800300e4882d800142c0f0088031642607031046000d44401c00703944159406442003d440c1c00d62000800d004c840441c003d01101c2900003000100c800415403400c0d421202c986c010310110b40d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270258884 1250 270257634 270257639
    0x513020307120b0c0f09060706060e011211121207020301060f080607020d0503010609061119050c040b011d0108041a010311040e030a0c060209060705030c060f0708160f140310 77
    0x440600c0c41d60002c41855111708022000044131281c0c17083e880014420303c0000380204c1004050780c01600039180100030944d0035a1240706400303880ea03828105030b030304014400005109250020b00340c0304104107003001d08540e103a14088840c103a00305076400c03a4155202c1602050b07034141d5140c0c50005100080c002c045505069002038181920480300d0030030403008000502c00c071a008040e900446a00345410000142842000e03401c10714500c041e0414004010501c0c800d0240004030171207a040c085a08007c490851401540c0f1400c60b0810314041a1106804040e598043d641c000d502c42d0080745c09012a142500319100c0141090b0011500381181c0f0080c41002c1c10207214815016000b100118034000c0c0d50b05000d094409822002480141c0010b5070640c0c17506c1e00d400b56086164440120313500d907640e901d0b059484807002c81c2c010200740c2e940400100c02034499611140501c00d000c100314005502d69108642d0030b0072a24620051000344c09504a60b5010803004511504110400c80980d17030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270260134 1250 270258884 270258893
    0x3050d09150b040524090a020d0c020c0910030f02090709050603070203220815150301060807080d091a0304020d02090f09060601260a0f0c081e070e0103051302030712 73
    0x303c0280c40510904017954807048001c0d12050040400c000807240700401ea44c40100d600040e200301010020041d0a1a000122840d000150151016021107010f410f980d01c00e04100b00c3c5c152a0b02c4041e22032180d109406c005800c20036071245e002119440e210304100d172510045151580709840f0040180d10008a810900014103900c0e82c5601d00e40e0a00c0c01003501e0410344039030b24198428407032a4903c14901044803008107013420401424040c0c0240016940c56120795115252442007459501a903110300ea8018402c10717040055461101144080300c600517038480d862780004008a0300a03174804060400741e0b5800d1803462294042e001400680c2c0740c65840d00741032840140c6218144010401813240101c800138540320010b0b21a00b451000f40c0d202d0328440d003d0144a404c100420f464104850300859026a08070b10900300d03902c107610449141d0b0a1100c0c590011a02040050b0305502e024440d98400d4224a811800c1e4522852076100c040d00001d0915102d64400149843e02c0001e160400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270261384 1250 270260134 270260141
    0x605090310020906070f290c030a020d15271803080a020d020409050103061805060112020d170307080c0711040911031218011826010501080604020f031903050d09150b04 74
    0x2541501f0001d002801c040303516604030b000c0074141006490300030400a4100206603c280b0911050341c00d00c40b10f25944200120700c0003402514080d4001445403e070100365554058038111541d41c4076210242510f5072000c484005000d80000d40041d001c0029243d0000c00d40007400103414418000112940345103044800c8402d00d0390305c2c01ca080d5412a004002c40d101041a0781100c07083c2c1001c02c0a03507180e10000e0028007100c4001094144803107040b8484030b541502651044020b0713202d802c60750312aa500d200850203160002054803a100c0d0b400703005824650004040706106800507070328002140002802e140d00d8500c00794005501045084001001c5a100c1002040a00340341003000d0403120300c041100001d004a61400c01e50707002603900002e1884400d10031b00000300c004c200c103503101d11380309843c0c0c8015030b01a0710511840310080e2a41c580415040c900920300b001a00501c110b503036095546410140a5a490f41c3e034030801d48000c18181c4025018986448000081000b031490400044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270262634 1250 270261384 270261443
    0xe19150f06080f0f09100216060c141c2702040c0905030304050f01200a05070603111206040f09030306051e0d031b022106010605090310020906070f 65
    0x400c0b03003241c10312040b4101220303800c4d003200c46113100f20301c3c80e9104407010b4504a02c107603590105610001c0c100c901d10411510300c2041510817581031140e00940312044880b20301c800c15520b4001c0b0700300651104c0c03c040141d00842c00040400c0071a4844810980451041c00d1803001c1c0c1184814207041300841c034040c030401001c0032040c00c2050101c2d06100101c0c0e642d002d81e000d00f0340148102c2d040700082c0c1e0302800449284c1402c18002092403008100341907282d00c4c03400800c42d15407207050707408582e1038003d003c2c006400b44451021424061081840c1001107000b502080c0c01545e1041c1020044e080d45c0600394140d4042d860219601f4940020b1003014100d60580c10702c604201e240706802c51f5035007910103912941503c2c05062a40f03a40c01c203c1d03685903060304000d50040005040d2095a0011220503440d21b01d168162034543ea42e558094515103d01c112056041e080340000c00d000c00b41c241c0c0039001400300544a00d0420049075070f80e045403420018150b42101c9404001444040d501821845 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270263884 1250 270262634 270262637
    0x170106020a1b060e060304051207050a0302010605040b0d03030c0909050702010225050a0f06060b0409060315050702120d02040b030c03010f061e0809520e19150f06 72
    0x180c07460f0074801010903103201c890358412203000000c20140b10081181d40c1100b40140d074503d65550813842c0641c0d0714400703d1002c0b0095400c2c42070004103403505115000d200c2c10043c020741c00b1521181da0890081c0042944801400700c0030901044140c61413050380c0c07145059030001691203c080150035501c40041c1c551a080d410040606400106c02088040d8000c2c0c0c050000150201940741102c09014250006501d0342004100010b0041e20740d0011800c072401000c10050307403241c6110030300c02d8603001c44030703040540c0c09149074411a00621004103002c0038a260014200381d111b61a0303100f40d60080c3c80b03810707841c94007200605c8410301c6004e0700c800804980c103084d44040103070413800103c0340801c0b070028140885140002d400345014840f50480c4910442c00402c4258580c0c4850200c0300b000702c1c44002d021100c800c05c3c900b1034040b00c140000182201c00140e15500c1d00030f04010082004100d41c00340910b00308001c0b090b450f603008101d10190030024178a086802c0c00020307146940681c0c040b80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270265134 1250 270263884 270263933
    0x10c14090a060822060c030c0309110609011202030a0b0a12030207060309060617010504062d09021c080a181202120309060d0b03060a0c050a030c170106020a 69
    0x8450340c51014803030444865041901a5503144800e116203c2e2204041e0308602104550240800072141d101b0f0320203e01c680ca003005500d0303842e54100d04031341d0001c900030b00c0c1d0400d480e0341454500d0680044c00000e181450403400a1158040503030130307a042514401c00040e00c801c410003007445e2124901004d4079a5407291a00404e054400035690310380782c490b2000b0f055841d1240030a10200d608613a000e01100300f1002d1a204216071103500a2004680698801d8600a40c000f084801011005c07802c521004154003280003c4100c000140090707401207900540040b518100b2200c110f001c09641805001c2d01a03c95110020190085404440d203a02c0307203803204418000303c2c1000c041e14500756010f9601c0f01d200060749031103038070303501c204080315038008404220b0001298590700110f06401055080d550b15480b441d034100d05403022204010081181408078010251090340041460309482c5400e40d40f129100e619880022002e0300032200680061020505005140b1321005071440e403c01c101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270266384 1250 270265134 270265147
    0x8010902040608190f030c12360501080a02040e010803030a0b09011a0702010207180c0e060405010c1e021302120708010305031b0f0f03070302150103261902010c14 72
    0x1002c0d0700d1401100505104d0506610b03001e00d4819070990381e460342c3c018044031230585210701c06000e41c02a0305201c001c14542010074120715000b044040b61403404194046c10803410b100c019680640010f081580c526803d00002a00305a201c40c140d008044500240d640d0b030915440c0034069822a12542d0b0080f0881c2c0010010250a004080c2841401035400b43d151901c610040b41405000c3e481b10180300750088450100c8003460b4001c038000c407416190f054184c15400140704840c0140e2154a010071404003510000c1024013041c404903c4240d80842980307400c0e43d0000d00e126001010345a00c555010404101481030f890304242c00003003a062403001d5600d50740d10a550b07441080d81c1038010755002c03020703440030080c00c10100d5807800018064404520300c42c2800c643e20b4005000580041c0314410000c40350100901c4240d0580381c10180f0408400700c0749072a0724000480c5a0b00070400601002140a1030310700e103602000e000d200f91300201e0300040c00800145150343d103100f058000329080011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270267634 1250 270266384 270266413
    0x80f01080c0d02030313060201061715070305061908012019200106030b09160f1a071b0509060103060602030d0b030106030f120311040302032e0608010902040608 71
    0x1014900300085540315010703540340c8041307402c501410001d420071040c80100403e05a4064200358151040007000005144410b0059562081645c00d000302500c6840c001c0349145101390880b5a000e8005010300c20140b12860719500d0501cad40f6030040704280d40d141c403520400022102170110500da111801d5040c1100310010142c00351600c40039074240040b0417200f20740d005032050200c0210320850b000700038052392418140c1074840105c0b100d100500410300049000f0003a030018006690040c07550b01c0000e410002612a05440080750303803441482805803c00080307040329240416400e00000e001030528140a2012039807000d40301070b0506003890300a11140c2d50000c29075811801c6680c0100c0c14030000b1000c83e0041a540c0c002134008010401d8502c2403080301c80394400f043c45165000c20240183c80355508840c00740e4017000b545a0010b0050700c00340b0b03445986454407040c0080034000700040c601e52142c2101c00f90341c000310b010394648582da01545010321981c0c000f072422202424026504014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270268884 1250 270267634 270267643
    0x305160c080a0c06150906050f03010e15060109150e0f040b10081801050c07050c031204090e1c020a05070b0429091503010e1e010b0c1c050a080f0108 66
    0xd640303040016400c1190240100b9400c042c5c842d12450040b0b412058403140c0c0d16014292034014980627045402880d8100e06051140090b240390500150000002c1562050340c02000540040d0421500700d00c049001442d040c0c0d035a41820b890384981e02d01148110a000e821048181098803c0340340400380c0c0603c7d11880f9000002c2e580700e2500d10750300d584031440c0d491070280c0021000207a41c07800f4100082090684000c1c59010300031021142d1a440c454101569a4144035100c506103c0034401001912015084001c1640f065400c1e110312a414a46006e0350741c050720030700c1c401a8043d1000303405200c0c081c010500a400c40c030a03640c1c901810032001203140e12070354890b800d0f2514500240f06c041001c0c41c05480510030000d0400110000306540c109103600280207800400282c0c0c4042000c4420f0030f1103540130101140301c3c192803a8623121a5002540000d60f11054038005c10308500c8d400e410707800781e680c51880c1a4a0b515200c03405020000e0030450020920720941d9010401400344600014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270270134 1250 270268884 270268897
    0x60503060a0c1b030311030c090901080303040302030702150903160f06052a0304080601030b010311010507021e0f0a0b0a0e0603040507031b1707080606030a02180c0c0307030305160c08 81
    0x865034000f1845600c4d04400030880585000d12102c400f10034810950031410040c031600c0782c220340720b4000780d0300c403014552039120544000340035a00411408006003003100a90341590084440d19003040b819501007402c0074100001e9803500c1c801c1040501c0180040311680029100d98a40a4245000b40514000010076640800c14501c1c01d40400c000d0581b08008407005044444295032555940b071a0210000c3e01c01e00046034618010761810f0758551103039054440d803a030010051112808445504148035141c8015903400c000c1400c1c8021490300c0c0c1c48403900040a2400709955540c10340900107180300440c1c08081c0c42002c1c00c00901c4085400010b0220a8a4000c0100340800b883ca202c0d801c80745d08140d100741141e4070714101d00700c403c910108450b030440300400c0c21f0304c1d240d6440e1800c040c1c0301c03403000b01c0080d803040421100700104081005040d90010030242098a00b13440702c0b402c9442d54010010442c0040d44400802540304007001c803241682a5904041a0700441c590b50f80d521070040b031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270271384 1250 270270134 270270167
    0x20a05010e2d071503090c06080f070c02060c0708060a0f0c12050a0b120a030221040306020310080109050f25060503151e0a050f0603040b0411030102030a060503060a0c 74
    0x15a4404102820f0140381d00400c100078602e20340707800c107a0740074002c0c008014044d01c3d45400c0180015000d0301403a140c034440e600c1408450000d5444800a0b80c2450300e40c0f2003a03030410001d0084400c1d012082080300c0c09811210020f100600e0090002000d4a00400052880758148244c1e1070380690004c08034065001498004186a91042007020003400865202a0b000180707810400070034501042d02d00700d0754000d0382910201840d882c8032104c48a8103c41c007a070044c0e0104010004103049034044c2d074200e0f40c102c4042044e0b0313607a030002909580000e05d041d42c0d40c0d080492032000c1068204040c918241c0340b0001004510b4514825880f89900d920401d001c0c803000100060603180b4402030001000340041c0000260084c4041d40c084070700c01c900341c0c00c3c011102a203021501e0318140200d1220504c3c000c0c181e07461940d07280ea0754201c034203015008881c8443d1030b0880201c140d800703001861180140c0c600018030240303005c2c2010725050b000352910001920305000b007200180d20030000d00316400031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270272634 1250 270271384 270271453
    0x50a05061b010906050f04290c0a0905090c27010f050d1b0f0306090209030703060902011209081206040209010f0f02031b010501080601050a0810090201110d020a05010e 74
    0x45201c082c2c05410f065034000c1401c0d1030201044051601c0000b25030007140903111070700b02d00842d03015003c9120109070b050a2100d51540000d90346030609801808150303220720304900b005981e140844d0490806647d041107070700002c11601c1842141c3c100c00700040300d081c07015560b10100d0000207850840e0b690106000c00800083c03190020240d50044080000c4400320702d00c0740d60010b10002c046034501480d81d4006030034000700248440c242e0083c1c6005060007000b4000403440d540d00c4c40014003417079004078144510205c5610101c4814490324144c00d02031603005503603900c0382d120801001e1000313000c3c910503031041c0700340c0740c860b45c1c000301442c2540c02a060100504031a94402c0c1e10718046e04411001c5041140c2100104500640059040301c6001048404603621101085903501030742c001c02e90541e0000c5c03445c01e100c03060b5070041d020650040c10180c0300c02c841091800d080c081d20000c078901691090501e03404002c0c1c00d12070070031502504005083c4070070414403000c2e5580284040b1425440d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270273884 1250 270272634 270272677
    0xa0512030709091d0d0305071b05061317040b0901031b0c060903200f0f07060234030503030402011205221403130e010f06050313112206050a0506 64
    0x1140c4c0d108118201074044a20420800b0790003400f17880c0444082000880c030000b80c096160602e8a01d401d132035030107c0501803070b56402c861460110b0b442d1f0000c1d900c6c0c106a0311074828407814900103001504503640c810396140d806c1c1001505407400704e01e18900d40340c42e40840301e82c2198400d001190043d40444003049820142c00d0440d94001c4030140c00c00081c0d40a1030901900800042c4165007940806c16241103282000b2002e031100b4a83c806d070070150304096444d403000769010800f40784130101c0e0242c2c40040880e030001144404c0c144c4c1c01c00c0751158000020310040d581c01c40c0700c4400903041b4410500940c43d0aa100191405085c652f80304d55003da07000f00b1003000022000f82100c40c0d100d60450b5202d19201c044009030014511608118641c08000810442c444031101000e954681e2200c524680b40c640715078603140900740302a0f400c1e03190202252003030f9403441d000c2c158000751045094401c0070012081c0c411190190f0006100c2c120f14001046161204c03400d07141c00c00308240d07032950001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270275134 1250 270273884 270273911
    0x308030906101211120d0903020a0902071101081305030d060303170403020c012a0503041a0903030702121504060506211203060a090e030304120f080103140a0803090a051203070909 79
    0x10401c0309100d10300d00581001b082883c0e4031110081c107c3c1c3c000c407441450581e807a2802c90880c40781e140c0103410707588900c550070140d50090340b40315040581000c50860f05007050303c2d05070070364010b14030b50780c3c2d40c1352642010400c0c1030b0b00c0b019400d2905504964100707a405c259038065903500d8240c0c400d9045c004030500040c107400f0000c548140801d08807010001207800f524149444c0d0740240614605003100c203040000005040c000d5a401517000b500942c5802615000c000b01007031a08826419481204a403900c116041c08085000714860180481c00d42005420090b0300007042600d8031700c0c00e01d03014010240f5000012500740c112423600e06070342e0341c0e06c1d03079404651180c1480d0132220445040540400d80000e00000951296003c0c1d083c010f00c0352111002102c0000c40203028a002580c0040148040b8408031002180e1450710000c850101c00d0719515201aa0402c03558000c0f03a422988081003481001c1c0b00000d021481c0711200c40c0303145000314003d00048118094100c3c055601d00c0440640c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270276384 1250 270275134 270275149
    0xf030e030c060a020c0d020a082a010e010606020601050d0b1501031b052a060a050c0c0703230609100f02040308190e03010608190812010308030906101211 68
    0xd026640c02e4402515101a4010103903000014008040c130401c3c07001c0d903d140c4046071000081d903019803150724100500c043e0b02c6a69003030301c11480b0040d0001c503501007805401d00c11800c03006240e60002c500c20346401d00107030824005a00442c02425801c44100024460200c00da6000d06c40f08220f54541000400480007041401c2051110180c1da003a185c0d00e058125000d000510024443c080b45c003c401001d1803039003039200400c91580da11a00c080743e010340e15900541c1d030105c1c6001c203042c14500c0003003103985031100071390040c1d9519912441d03942c0d000140302041c112b03201000f4002c0c00d82d0708207840256503c40c028086801d18607070707074100c01d02c102c0181d4040720015908a01e80b01d88a07682d03030542600341c002c20483c3e03501040800d081208642418082c1c0011039488070040c041a00115841500c18140d510044480e002d04000c4100515188410540a58000c802481e04e074503141102070724020002e403e2171190000000100540410b04049005d169405603151800c5610b070070206481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270277634 1250 270276384 270276397
    0x112030c14070b03040615032d02040203010b0406141602013b120d0203030a0b0105040b03010f0518011512090606080c010912050607051b06090303040b0601020d0f030e03 75
    0x40c001c0e02c400050000c00e86010314003950158400704021550030161351364041142c07000900c2d2540d50007590301c5201c00450104807281d99008140038260310383d0300242c100e074400d0b0046100c000d008101841507d61000c800c400946000c40990300c0c1450703a8010321440008140020304004d01c5007000307000324916004030010310200f001d03200b07443c03401004190440c504030b214440c0201c5a41c801403041400004598903c100701e13402039480c1d52104202d030005001c0d515010b40c1407150801c000241021880c0085008001d06d18030810310500340070420016910748141109103c0c40c00005100e100030403008602155030a0400e003000c080d4141d01030000d050110340c058070041c90070350000746c10700c400300700782e02060310903600c0741303040c64407603042c10012400d110002e0603c0e0300043c00141e81c9030085005290341e01c280c001c1d154441d0341c100080c601d4800105d40e251900d42000c01404100302100307000da9007100b4240081d1045d028100001011354005a01240816882e10072007007103424140b044605 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270278884 1250 270277634 270277673
    0xd1b0801090b04020103230a270501060306060e040c09020a030e0d0309052a0f0a05100905130605090f042d0b010b040b0714030d0603060e0609060112030c 68
    0x80c075601800c0005803114201c4069001c41d0400124039844004001781682842c00c8882d40002038481c240c0c103100406d0a540d500104400c250fa0384600c080c02c0c00303948100244184000306103d415803401200f6607040c0d034003042c01080c5080a01c40001c402c610040d080d58540900181c641030684c8044001c0c103068100d0701420b015195403005020790540000b2455801982110b64411020307002c172651a42c044800c0f07080c01c2c80e0076030710301c150318100044c40394a440007007019451984801c001000310400409900200d205104100440c0c100026031340109801c05c07800304074040c5850082140a1001007200da4041d008100240030021301c5820141c450b499501c02e40c00450840958001001d210301043d0b50300c50740c010001441d1000303042128141c900c1c2c103079254245540c2d551003106a031140080e840c11400148502c080b01180d501c0340000550043d030000c10240002420031342400c8000d0304109075500820014400c04016400a032000b641c185030641ca4a40c80e81003402118105403800c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270280134 1250 270278884 270278891
    0x70807050c15031303031a0402040b0d05010504020901170406200403020310020c0706080a091e15061a130b040608101203081303050909040303020d060501020604020d1b0801 76
    0x414050002240c11075050140c03081c0388416000d041e10b0303110780011105000d450805021150009200740c01442010030250000c0d40e001c141d031710004003a80c1190300003150000002c54040440d003102c5c024140102010381e4114505041400007c002c01200c0c2c45401c08880380d500458104a919400400940f41d012a0040c199446107030031881d0740e10070720081e40f09220300b4401085601e03152003141d03e403045020080040600d020340549580000420751134441e9900c1684101058620400e0740240c400083e107442143d0741e80c87c01500b144403d10300720108604d80362082c4a2500000d4014010092a900240d11100149000040c801803508182e01d10840030a0000b0007580104070315005072000310700920f82d65120030020a04680380e07440a000a50700601148a042010101d400c25034002d1800a14240000c80800c141c0a0192001c40c0000e030b0000d142c60344807141307200b440301401c0f09101600307042c20560000303200d81c01c0304180540748600f900880c601401c3c214a0010044c090302000b0b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 270281384 1250 270280134 270280147
    0x5040303080c0c1203010f09050603030405010c020303190309150218060d06030203010e0c0103051602070506031003060e101505030c0616050604032a0b07030c02010b0a0e09120403021011030708 85
    0x1103405400c00c3c4108924603215810224823101c040c0151441400040d0085007042c0c0f501c401118100650501a0303054041044000c0c0d00e52034041c01c0d40b25007010394501081440807498922030000c05102500b1510f48144405650541ca0756240501d4943c03c4403015104e43c00f1a501d840240002c0d44001d52640c83c01c160b03805500c1010407200c3c1c5546003602c00b0007050351001080d4100320b800c81a00d80050700450703400d00c01803a1400c042d5400801806101062035140e580341411101d010b1080d47d9164098114101c010b1264002c1008101d030819003040d440d4980320100b513480c03220100e0030380305100c0459414003a6607141d0b943c0541030b0300942140d1903400c00d403d0280901c0602d4147c0c0d504e00c0c5442c1d201c001d1034252a2410060765520134503420b84c542d07402600318024141c03945101d0442d501c401240701507603500300e80e6034041c102107440d41c0854203202d09150301d400e15079542108000c20901040000d40e84c3d0704a410104001c908100b540c3d1000d0345261341c00d5200b1104002c003d5280414074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 270282634 1250 270281384 270281413
    0x120f090c040609050114101704060f0504031e090614030405120f130506070c050d14030417070e01080307022b03031a03070302090c0711040914071505040303080c0c 72
    0x6103048404e5620b8140c0700d0b5140340c042c01a94902000207c0208407400a181a03582c122581154480e0051b18001400f191541e2400d05a0320242d40540c0040c80b0f50030080130200ac00c1ca0b4401025410b410086a205d19180000d850701c961003d44040400f03001c00041c081c808184140890344040d10616566070342580d2525102e9080005d400c16500b40b20714010034281480001ca030007407500b00c0a012203c51400e802c102c09003100850844041104419103903e142d81040078101410035146c900c10b803442030101c0c551400e9415441074940e54150740c01003101040c00b000b1a2001a01601c03142280780960040d0f40524414091281c3c240c070071452807400741a89a4489509200c0c41c00c54001480d9a40d01055030382c14580c000650701c015444082988007060f10003d11045126021505400c080170300040c080380c4506100750b03038216082a603010343d214103119110241035520601c1c60f401c0c810407401032082c011804001d044c0694600450400b01000b016516441300980440b42402000440c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 270283884 1250 270282634 270282641
    0x7050a03020d0f0203120a09030201090b0a0c14030c0403020d020105222c06011b02040504150c02030313320109050d03020406051c060f030b040314120f090c040609 72
    0x2030301c40003d8101040b0710101d48040100e4812002001044040c0e4407410103000003030441c15011020346d942c80b00c103100080d610a20340c910412a41c24001456568aa005805148510380641150b4020010013018070780d00000da8003625010f68185034000058801a50709106500360300e4016000310b8096000c0944c008680740540f01c103912103902c101402007141c1c80c0207410b0301008450b04080b00000d505940315422034801302d03203004030b540b0941da1190003040464606072015140351030b80c4055011141c21900441c000901d00348000c0d4910302d0030325200200702c0b03d05100106030030415280e03100b02030382230f1a800c1000f01c1541128082c90742400c0040b4001c11000781e0484050082c0303d81914194040c0c401d4608035012519200d14040101103035100c60407140510000c1c1540e10003010514907000049240510321940c1d01e6817140c2814203028110001c20240035100e01820000801c04200440040b070300141070208488554690b0b200c02401c0002e18610f0b81d8200d031a02a00144500c00c940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 270285134 1250 270283884 270283903
    0x21201030503030615120f0606040b04080105040203190302150a02070c0806060406172e050403020d0201050c071109040f0816110f03032a03040609080d08090d031107050a0302 77
    0x20382c1044034111401e54204240544840306d800b070008840002d1080c1d00d006039090703002000400385c6280984401c0400d0341078115402c480c603660355407410401141000c01c0b000f810204a1030203401001120359000b5035030b1240002e80401c800398240440c14841150301691209903000c00c0e801d20742e0b074550526640c3d0300e904650080c490350901d0000034618540d15a0001188070760740140c21b81d240e1000e0b1502022401b400402c01c6000404d507407400701909442002d001c1d52082c2d000c5c000301ca40c0454000d080d2040600f02c01d036030b00303000c1203120001482e4400410f05440b05880d4120281d68600700010280d201c1c131006480c03e2030004d02e40605249945154080e5807003448144c03103030f004010030b0219a4802001d801d8140c0d108020f000180003a00c10803812001003d200000c41c0b0090300019130840d003040c0d200c180840d4804e0024840d4000a001c140600d911610302040c6501d440034000396201000c00580d814596546200150800c0c54000c603004650408115030144e0034620b00250f03207802c0d84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 270286384 1250 270285134 270285139
    0x203070203070e06011d010807030c0905030607050403031710300305190e0306041e0512040f05030d0e0108090118080a0f0813060b0d02030d11061302060403080d0212010305030306 79
    0x641c4071b551140c040d10520718680603500c0a0080d030340d0a0303081e801818901a58000d10440750030005590707a0804c90381c1c3c86a050f13940c2c3c003038496240d4038014203001c800383c0c20101e252020b03408015541500010380000c5550800140f05400825120451007248040c44007880302c0070340205c40141a0003500800a86241d050407803004e9501c01c1c3c0450f00180c00c03220720796141d080302c0040387c0443c103002c100d80500000e4031281c08050200369159032904000349a81d880e03001d00442c080005078100c3c8640e00007050250003902c0388040ca1407000700300b8005000c4403814030224001090745a1025400350300021a10001601216540d0610807a907401010100000074151a1329084440c81225054041c490709aa20f8120058036541d243c090034080b00800d40102d9880348010160b941003042c800142c42c141c907404071086229000b2410003000806141007a096000f2900060300c07580101c1d02243c0c2c0002440380c846d20505086c6c4040d10a11034841c400441c100004001d1040110041d400354804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 270287634 1250 270286384 270286397
    0x303040302210c1c0e0607230c03030301060806040f0b030309100504090213050406051504120314030a05090d020607021e01020904021903150509040f1a010807080f160b0a0203070203070e0601 84
    0x3400200186e40c420304400400201e10500050810082d002c0c0100b00050400207440004100c000442c4c03441d0001da1004002400c980c0600a290505200d018410642c1c0101403005c00c81c3d81c0042541c034481c42c184c076070017086a050241d0340c0038071071010f48001c1c003801c80c001d40d40c4100665411440e4142c50184610032031404a000809103460180304050010b00c280243c1000c1c6417045484400c3d06040c019814002e000c14902410138034007000350f2258407110800600783c01e06450081c94030240301c04680a542c485020b2007011500001c40c000081c42c54499240c01501454940b806409494285034100e070010a41240036807800201d03c00c1445c0070783d03080000c142c001500c0c10341c1c0102d03440b4080e000f8111a0200e40802c4554000c0f0507050f0040080071008003002c5101c541800003688004c020742c224171024842840d05021024901544100030004440b60350f40c0a1420443c5210f40c00b400d035400559940554024415510810340081c2a0b400c1c440c0c1d00c5192290b0340d03a040b15144d001400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 270288884 1250 270287634 270287657
    0x915050c0105160c02130908040b07051b0102100f0e060a091a04080a03020304022403011a07120c020d29070201140f0a0f050a0207060c020303040302210c1c 69
    0x3c150840c0c582404650f81c01848003c00c2c1c091003401d642203c001030505d500d501d110b8012411780d0004000510b0009078482d0340d82001d00b07086040900320700380703040301191401e154040c83c0c1e8009a00c0d200d1241c0381800180748203103106102c0042034401c805559034042e56003000301d040314560102541e140a02102002025030928484a0b09001c54000345002024062100524803903405903500503c0600b0b020710500d6102c5d503201c401ea1003000080c82c1408000700500c4100d204503008038040c181100500d0403e81c0340d03030700d144009a000070903508010703404084005640d20103404803c0c054202500c4c048480c4140d00d00c02d00340694011503a01c031401c04000c00e2000b0300c1482000840020800c202c2000c0c2c07501107141c0501c29010745805203140c1c5845680444d81414032899000d13030b03040d80c00182e4403405450301e4019691008941340c207640090013003001180c0c01113a4030b46001070200035070200f0743c00c0c09e1030906240070301e020842c410320078003d004041e0829100213511881c4207882c4d418040307a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 270290134 1250 270288884 270288901
    0x901020c0c0a060c08030a1811010f02011e0207050a150606080105060304150c020120192f10050103050d081b16020a081915090b0402060306010915050c0105 69
    0x119a485103000081c13404a04001040046000c0c6802c011050350101d01c80e691041c01c0c0c10502c01400003174035003158215a0303520546e00169600c41c2e603002400244078800d01c05080c1c0107058181c5008502098000461074204602405101c1030a6802120020540c40000340040104100d014580104540c1000480c0c0c0785400c205881c4070300d50001700a240c4e003041600c603001a203100320f12941550749954211300541007115070b0459103140c0d01c4001d0345625074920600007142400b4203960500c480313140040703100c4001025000c1e4414503a00d0021103a00c4280750146000303555680d41c501c0c80d2400f0001310410002180c3c42061a180fa0b8503031103907440342817a651211500c000a002214003c10080c82a991100351408105000a109203191036483e455503091850f41169010400c1441898000300655043c6089180d002d007041000404001c1c0c0d03428441880250001e03118040100c00174507580e206d142c1400c040c1003420490706510040b000094110340082d600b2000039400c210005a510b07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 270291384 1250 270290134 270290149
    0x519031a041b120204090c0308030705130e1605180406030f020f01080c1e0c0f0d1e08040201031a0a0605040801110c0c010e2701090b09092508060901020c0c 69
    0x45070010919038018203144d08203c024507100000715400c5450b5a00040400d01c500e015605c90303031940d1502681d8641070300165100f1003464120480f00c0340040217000c0d50246c0c50680c00300901260406d0fa9650601d1100803140541503600d9a6100d0b08110011040184030780c0040300b2588281c6100906815100042d181140111144020b211082c00b1401000b8910716401e00445207000000c3d15081300804580d041a04000b0400c0d000d0340508815807403154419510541c1416a1f1000301309503246003001401008050301c06810180c035203007541e41c00f000c200c1640e109014000d017150b0315255501000b0f002e40d00325106800b10741d442e0140c55402d034007048040700c030251505005400307100c080e1070042d41e584c005000b00c903421400c0c1c0c013911b0003500301400b5012042440d000344041c0941c0340100a6054584c1e62981501519025003800f200590025680c0a00d40c002c549078180c501980ca0041c0c1981075135445690548540d2060204c08201980104214012001503c00c1c4020103002d100343c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 270292634 1250 270291384 270291389
    0x1605040e0d0806040c09030b0c070201020d0c030909020d0f0e010e0d030204030213050c07080a090e10032112090303050609150a0b0c0a0209160f02070503070519031a041b 75
    0x4140c50742d0010f00c45203891380c08106140308030705002060903140c2d103c1d829181022626680040400100641550b8040200090f001d10500d089000c1000780c0d036005100c0041e922030b03071032855004500f800c1e4105e0560018400d0b150701030000c00c5035a045081d00c0b8045c040d00c4032020400c0c05140d1003c1603440c441d0007104c4c2a243c01030321403c84504002007003c01800014122141520148500c4000840c0d28000700702c1ca08055030740c3c4401d641020200840304401a26001c0a2010500c040000481c103c0030310221400c600c42d4038035091404a0142c0d00c0c01d0f101e14100c10407074a490240000c140e09075021a0180005a0310303a005a43c0703460a03410000e032012106607100520440400c5030440501c0101b058100361000c2d640e100b240d0754046150320780c0c1542d0030811005045442a03000343e000448440e240010710081070028070741000f0a40340d9041d070240f107000e019100b000341389004800c0300d080e00860b40159031082c2c2041031503200c45095020742d41200c91a0401080d000c00d071001e40783c2c1c1400d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 270293884 1250 270292634 270292637
    0x120604060312020307060509120f0d020f040b13080102120f060d0b10081908070b0c090d030903020f0415330f021e060118180b07030f05040804030209181605040e0d 72
    0x4ad000c40161403103c0ea800219105007441d808010ba40b82040001000d0300c020a920b1142c5502c50101c0000011030046035041000c1e285e00c103110f01e074074640800c014907170003014001c144405911080049109000640006484a01058244150f25844010b1001114a0f50301580c1c8100000c0400501414032464040c04001c402d020300e2022450080300144c005401280852030002c4840c0800c2c90304014420a90109601e10801c2055062099490035543c0c0112800c10003801c0c0c01070b202101e10068043d40341e048500c140404428001c010990000b0000111071342907210011000500300e022009143e00140112900c44010301104104106e00000001c0a40126802d08411040810b1280c040b210082c2c1c0320b88000d501100020080c619060045004450614004601500703481d02c081012012515210030003000c914410261001c0d00d034112801c41c00f54840c9110340d440b5614030002030104c0c0c02005000c075034800081c42c0300c1d4121803003a07030140f01c4071103000c08040d21036140105120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 270295134 1250 270293884 270293887
    0x10c080408040b030603190303050412050903071419121101090f0603110702060307021b030703050606040b0103020705070e160f0c241509050c0702030312060406031202030706050912 80
    0x2c2d10f041880616800300c0042c1c2190b80d15007252880c6a4249030805094003c240d40700c0500043c0a0300604280300e100040c1041d52a180c20a40440c0d0f41d2310351885008d503180c001449007812560785003000c1101c0030100049011443d03c6044400215540b0041125514020219042a9409000c65000301d40c02c2914041845180c030006801610010300c103602011020000031006980d0040510300503520b640c0109180e81114010441d2120f28441c8144a80d02c283c90070000207200040a40d80840282d9011900740a01801a030180c060b0303040c028a01e0241c20404140e82d80daa00029104500c81000c0d0342542c65001c2058804d2801c888041d40080c05c0b00d00034001140700d5204030171241501d482c80f20712156030031601c0d4080301c19404198a076554800350800c4030410074098240c01a02d00341c002442d00010780d00095980c410b02441009040c842c00010341d03e560799030300040007103400120404903040102002922544508811a00705103002d01013190600c00103514000c036600c0b0807031507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 270296384 1250 270295134 270295139
    0x310090504080301301b08160302010302180405071e03090f03080402221e0c0503041704030803151c0b07050705010b040216020a0914060f01032c010c08040804 70
    0x1d000d00c80062441e6100045c1c1c1c0c1040e015100340181c94240e54034021808000a40c0d05542510315500c407940c030044456000096408446088440b608200d039424200180c2d11600c03c4420400d00910354a003561103458030302040324403908016510340700040d5901104d00e60440c11400d9084034410400500718401400500001a01072070f02a40c0042c0001c183c0600c8409603906410440d400940c2e0590554075a0203040051000c9030302d80545c0c5221034801e210b000f603003940013086408005c3c0302822840d080c10415804001d82c030102c802031900840700e6a500d15200c0038548010700d0b451070040c02280034807403d601c06006500c10f400104d80c0081c0600301610785002c03c480396048800c05039195545c54101001c0c0f0303034881c4014011220040c0306400003003824010450108440d0b40200d031040c6c00c15407c6641014101c2e44181c0c020b404646408268000400480007080c180000703115400e03900c0d1003404814951110403040c00a104000d0000024a40d81120b0408058400030028182403006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 270297634 1250 270296384 270296399
    0x216080a1106090d03110c0301061d070917030a1d0108040602180d0b070306061d06070305070206030406050412030c0e04020a14030a050106140a0e01030e010209150310090504080301 80
    0x5203841d81d540100114201605000081c1c1c031003080460803404035100e07600b40100b0725024000d031140c0460031002000402e240207013180c03800d1049902d0017020072403000062103450007064200007506916003120b0028820300000f5030389e64000d02501010542ca110541d58085400e140c610303c410042e07640a183c0d444030f5603400041e400c00740481002407007460610b03020303488040c40114014020f007440051801c02da10b0160440c0c075244c02c90000c0101141380d03036070400f10310f51100350804025105159540e00a0408903068055000000d601040000c18041032044036007089000d0746c028121840d50f1024210154203d54107001807001194404000219626140e4003a180031181c60900e00700003000e0074503110b01c1360300407124020302d1a80e490040c480e140c0e008880c051980c80b5200311914100b2101b401902141c1820413032030404d0748414888983ca50290103607007a4aa025110840300d0340c2d5044d80340301a41084900140d03400700d0110000d14101d0754001d05000f13031b4200d05003c0c030356400d1401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 270298884 1250 270297634 270297653
    0xc0d080703020405030a05010b100314010e0618090307060b061804021303241506050405040c110111040513060506120a110315090f070504170a05100501060216080a 72
    0x142014190b082c00002480e032001d100f00c0c01054850800020f2007040101004030040003418070004040c80c1010705410042480509415945420140e207155960b910010707120024002540a00101c1c0e8028442e041c10000050801c9030300c20001070114107100070910459015003000324401c011040000c10560400d42d005102c1d98000c07250038007450740c403501e4000f1980060302d9240300300c162859010b200305003a4451a41e4049002c01040583da207415401401d0703010354040c0510443d651241a5140d5020345003600450b01e00f81c00a0140d803844000306c0200340c2062180d02c1c0202d0510307003034060000d12031140c542541c00003800300b410f10b905c40e2400405110300500c0c100030591b0761451141e00b5461075018501c00c2048004803800e41e0041002d001442c03101401d607603810780d45042802107482c2c100382a601564000000380004070b01d00315071103260104018005e0882d01850040d20942c204503040107050352a59000c407070a082d031903032030408403100d64825040aa00b10005000018003040d2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 270300134 1250 270298884 270298891
    0x5011e0e130902041b11010b090402041107020301090b0a23010303050a020703052a0105073809030c010c021b04020a090308031e1303021e07030b0408030613020c0d08 73
    0x3000241501c0964042000c0b10352000700c0c00854124400854001d076031046c1d503656601c000800030300c10401101c0200c4c10049020b08002e01c915125482c0d1017030055858140d40c8440d070000e0003031055000504002e1a1a40c1c195055035a003410300d292a140800c880341d064085c00c080c0340362400316a02e0b648085034140c00505400085001e918000000714008106003261403000700410341000003a985840e400e50054001c6505004c001c2c01481c01003036040038258070301914082501c0c40c000060301e591440100200f0204d50411041091040c80c000c0003001d08400c9451070000c01004500c3d070800c2c1d035103100d0820f14a403110300c00b40408640e42020340252580c00c1c2d0705d0078413400e415100c3d642c560090700111a034124400e200c0002d001812098001181c014001440c1464440c01c1520029200c580094841c0903650034a101008418401c00902006503040300061b076050070300d031601d00a02d91066a07154800c0004811403828245144210383c840c6054800a017035a201c442d10507100f004009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 270301384 1250 270300134 270300169
    0xc0906041a03011e0e040312021902031306020109020307030f03140f0c07060806010504030807020f06120f070215010e071806050901031103060a0320030d0905011e0e 73
    0x140400a45040718070003403040607180341d00c078036101c1d810304290741c1803211088800e0200d0b000280b0204610054070352840c0d0400e4161904402a17550143d00001a20503503551403042c4201410320300d007441d070210142011650500346c1c41155669040e0490a880902c1030107985504541c0c001c00c000b0f400707404c00f81880780c800e0400070032800e00320b00803c1076500300c1d410340501cbc544001a00ea5000c102405510068015410701400034140b80c00000d01e18021404002d0034000c1c0080c0910642d51184454000c070440244403503941c0304220039540c4400403d40d0f0b154004900c0780c01154039580041a00c080200b074910080c00c490303181c481c2814118030054070050034054002146002c002c0c410304018007070010f0fa2605a61138448000050450740c55121407200c0110078000e00c03145584084115046036088403100d18403401d043c0310190703008a900329850b85480b42d1540700980366000040c40701150004d88a101c40c03140031000501c0c00e10146105480010744a40c0340c02024540b504c400503014000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 270302634 1250 270301384 270301387
    0x106211401110409050f0114100e15040f0b040b07020108061206070809070501050705030f0f0f0c0705011d0108010e18010204140307060c1a190f2009090c0906 70
    0x44a900c507085a041038000e4481500014041c0a164400d000d196002518403013021709541c540b8178070390302400d41003003201c0c41803c881306508020740c45001807910341c00c8002c180351441e038501601c201c1a58820720544201450f0244006044503103002a0703003c4460041c01b072f92901400b40d00444001e5402001c560b0300c200e0480150401c0b070003c00c01e1500c034017004c1c0c030f400c0c400b4100031100d9880c100107640aa81080410000203000a00c00b20039121151003020041e901e900320400c6040060146080e0b1019401000c24104169000060075500701c0d0001c1e290034161451a1826040201c2d9503000c03180410751a10040002480c8000130980c005a13020308401c0b00e1414155040c02d99203e0381c00000040b070b4012800c14186400e00c440001405241008148403a90350b540c060712480303190740e01041182450000c0c07810038040454000782c8081c50001c02c01c071825120500001e0101048181810b100515030011110201044540f01d1900500710481c42ced0750800040e21079032000c412150403010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 270303884 1250 270302634 270302663
    0x605040b060f0711130905060604051014060c0f030708040315230c0405060a05041401110d080c040f0603020a08101a07050c18011401020d05090103150305030307020c090603010621 79
    0x5c1d01c68010414400c50280015080c032504220649401416508400070807003000c204040540d0005203040406840980d105c0c041e0118641c1400f90641085c00b00d07010002d114010410040c0041050700d10136000381c3c2ea050a6400044121115006160b01c44155461a0b08802e000c618080d5072281c1c0581482c0d14103501d074000725180b030304040e5061000c00c5000c102440b60107402c902141601d9020718000401416242c0d80703d903505012070042d81400388500104141144050485000c0d0100440c000c96155851130001d00942c008a0040001610340b0003040e0f42d0442d06c80c0740001c44100e413030300a030002c1081200c0701443d800404d044804e44100000c0d07114a456010f02c1d0000003441c20b6645220358503000141444045441007a81190856000c5e1002140c000056038506842884c0c00540e07041981030300f501c1c09019400241140c4000f108000c20241d000483e030008940c00e4800076081d48400080c0b600b664000c0c010301c500396201e41b400a800c1d01407034038194441170003038001c1121801c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 270305134 1250 270303884 270303919
    0xc0204150902070605060306040b0403120b030d050301030501141501030c0512040605040210210515150c010e0102042d0f120311030c0a170c030d0605040b060f0711 72
    0x2030296026074845030b0045284000d1060b039104181e03203d041900030b49141e146c9070382c0f220403100c00180014284000210440b811401c940c0c458603441d100034040340c01d500719020029141e070300b0904c8100d68540c00c240564249640040e4054085c1c2d08140c0780b0701454500700010f41c01b5046040c03000e410000c1c180030403007406400c03e4032980254090030b000101402d02e401031244142c10180000c0c10701481044021681c0c0454900808002e501440001d160311000309620030b030b285800100342c1c00740881a06900104400005190005180d0003c102030300028810900340c2c000d6200e8440c9540c960058040720100300000a041c103070707200c1551144a074441031410540449070b008902c98800d209501c0b0101500640d030b102107046200300950818594042c26950b40380c0180b001440400340c0102d01140840d01e07000e50b42c181203c074040d66161a07a200c06100103104e944101440380b420030305042880d05124007120130750100640004d01e080d0399501c4884000348580c0b060340c6c010f088a04030700100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 270306384 1250 270305134 270305171
    0xe0310020a050f070c30150603061509050601180b030a06031709040f1107200a2d0810020702060d0203241005040e04050a12020a05010608030414010c0204 68
    0xf02c0c4503c42121201c1d0900d07006003007902e01454252119050380300c03000e4407801e29052011006d648000301e40d10304100341c04958040c1100c3d500090095040400c41030122020141c681e003640c000d000304108960b110001141c40410703210002c00d0507960309005024100940b130045078032510b21fa40100307040e070fa683c0c0c6455840d10100108082160045041100392515001e0034000c18100b01c010700c05000140583d500a220305400200109030412200c494843e0b24041c242d4202c030005c0421510310342e00d80c640d2403071680303403040c104070350352804600c900398041c009030035064030401c60062043c80c05a0441d08000e500504080e41d11210502c079500c45054140000c0d40f040c26205400d10300660514031620b0500284400c0310f1045a48454030200d560303200058070212603400105480340d441c0c5043c1103040c071690070740140c150507030f000300c5800340c0b40c0014206010074410402008001d503240d0445840b40107030301800c1d040110a1661905c0c5600c1140640c0510340005c10015088803900380d00040c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 270307634 1250 270306384 270306397
    0x19080304030b0910060308160312020309010b0108160e10050d110c190809010e1203040801050105150c070e0613140610020f15190c1805010e0310020a050f 68
    0x2e080d0030800c81c5104041c0001e4a500c1c808440a000030fa00b0342e030711000309004011507d0041d60b090001081418071501803c01c6455604070115581d04220904e14068080921030342e003ca4070500218202d02030b0307a035000380720b0040e5540300305840b412041086050820340b001d00081000900030344134180d0307803882014082c0500f80a990b0351800524400d6003083c0351071440c15110311114111401054500703080390302400d02481e1030010300f5140350000d12154110101142648401b113408540380700c0c15072095050342c1003201c200740101410750f40e1800c0c5c0d10960b000221107800c944010030070f802c1114040754011400510354034403a0001046030046903481c00301035a20049034000e02c092410000405050701e010b500c050180c6003942242503698117005ea01c50014440d141001540707a500340d90340710f91013240e503a4040c0300d24050902c004056440101000300c0c00e429030303c030001f12507001e8020010a101d0150103000d10140843c82c90000350818580d4100384041001450141c1084c01d004050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 270308884 1250 270307634 270307643
    0xc0312062b1104090f0c0e1308040b0901120f09030e0a030309140a08030f07032006190204090e0307060e0127020d0b01030609020f0f0105091908030403 67
    0x61464044104491115140380305680d04540c603040c804110421020107540d540c200084000791440705020900803c21404060b181200c01707000714040000d55a4440121805c100c1610301540310700f601401c201510000081005204000400103010071b070018002d003040505002d00d04044100300e0105a500c90200d56036069a0380c07112404040c1c21502c1030f1200c240c20782c0c20000c12030a654020f08050610300560040700d000107610000c07a0380d010715400140c580802604d0312000c0c070000200b460b42005800700c010555181c0211800b42c480c4805804410010005021345d0300e50500c5c45404000c00002546540d400b0040400c2103e01c9001d84003020082c80000c5980707001c54100001101c541d04078004669050940c05240d0484900800171188400f09070448803907050310001c0c00000c14110001c00541d95000008240640c581c00600c2c6a4008e1b120f021403580701c00304005511304180109070120380288101c010904000500f80d2a604c40c84048046031500c400c00d42d440c0d134009900455 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 270310134 1250 270308884 270308917
    0x3060e010902040c0e01120b0d050a0b01080d03180b270f010f0506010903080a051e1b0601050a140a030b010902071a0408030a0c050904090804140105121b0c03 70
    0x1c11030030030b8460074101003031514040407201c140f800000c00c1030010700c3d04400000d84410702150f03565501d01074240400c2c0d00500b10752450020349003a00321100244500d482a010301e501d03040d00b40c3d00a0058911a51039035041305245009556121060f24024110024640e03410700c0040d0721002c0040b40e40307040240070b4000c12080454181040c01d4070548142c1c0c00c0554109801e010281e600440c0e01d40a4a620551460f00ca010038141112240502400001d840109480c0c803545041040c008285010304001c40f1400003001c1d414040d0b48010a2080c581c104150843c10028040c10583d10110300400420740f86142c1d0f501d07207030768200348401e0700b03e6150658001a01c0041084440d64854000850646034203035240c181c0301c1540d680001850001c184d034840d0b0082c03482620603c220394a0b014010402c000400e0740c0c1c02d000150b5045030244020433a07084030815100e6000300195846038541d500c90f480140d68004072041481001846500487c0040c00f91f0b86130084140007400c0b003541012400e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 270311384 1250 270310134 270310151
    0x90703030f1e031a012f10051518090d08070306080f0c040605030d0e01050306041b0f020f0c0a0b0c010204030519050606100c030309050c030d05071101111009020a03060e01 76
    0x2c09a11502c4d81d00034144100400c4901c0302504c15010911100c0841e41a0380800340625566410418850301d0103002c1841c007010448030030031200003002c3c0c2a07001c0d11005054007541390600f00a071000d584850107075020321001105948102803150740081249030205825503140c01d00c40c90448014800c0c1072070b4100d0480e0840504281c440c4400030201100200585021154050304c48451401014108440000001d0f032640703032908165401034014240c801c000d5400c1e100240400c0c0c60303a190300010f000309818100350300740008160348504d070002e101d107401d00c1c500300a0264550103451002c040303540920000001c00d03400c2c06404000d1140d5100103000c3d00a070b162050500500410040c070808401c2d01c207a610300d6102c14010003150785420001000c01850410a140c0b07104009915414811040400318075076120000e054500c0c81100e50f0b00c084d0614000554841d4284100c0210035444100c038548800003d40005d0030050000e015240a036490361039000c241c074a03c00c910b50302c503910b48005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 270312634 1250 270311384 270311411
    0xb01091d1503031309050a140c09010e09070f05031e0906011707030c0b070f02031002070b0105030a050d08070509060711011d09061003060e040c0f0e090703030f1e03 73
    0x15400380c980d04501442c0b900b41d1081005040390b04d90f0048500b03140c0e480c0c0001d030403c1c065500a0001580701c000314103052a2410601046501454100b40090501202d111440c180b0b4000707240246072544454200c64880101190795410007007507540a0181d0400480040c6c03c0004500d01420140002c0e106a6051403c0c44100018180d0700b091300f980418402c01c00715080321084025500304003680d9541d91124100448000c40030400039505005503501c0d411080c01d240d00410340e440c0b150b428541c3d40da0b41c034010161a030349805401341107904035040142100e442151066840003003800c15605011340c441c04030f0500c1c1c202070000c40300c598001c06007070050740c0c100120070344001c100d41e900305170101180045801c2e4503015006034010b5a01d4640301c017400e4040d4200d80c0240c030541c0040105e910b0641841c0d05890000e01c00d0780c2002d541c0c0140070600d6684030790600e00c1114510f0003400c4040c81d40e501180d07060900e0403a80d0410041c038030701d0f401c44404401e90444403031817079801141e85c8a282d0b10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 270313884 1250 270312634 270312661
    0x80c0103090f0c08070503160605040e04050a020a08160f120314130609030c15022508100212060a0303050f070204061d0109050106110a0f1e060f1409100b01091d 71
    0xa00000f81c8e03da0f00030801c0602d612100312402e6510256810002d0740b194a0f101749400801d060096001c2c03400000890a903400191071002c072030b11600040b140c1942c4403080c50421020f805442c5003601403094a9002c45d0003043c00b02400c0c10307001d500c9450705a900c442030880884a80044000076900f03d0100188940c52000401400b0088505452040c0c1c3c0306e00655110071340d0510444440b031010003011740c00d500303016034802041114280c4104045014100000b503000881c036210000003140400e00da03044c010880015203615860b482d161210b526010080b50b088070b0f0003207911945424010582050f1042c1c241010342c4d48034070700204d65041c1000c40d01651016049802004100c941d0700c41da180000a18505058000304600201c8000742485c5110759081d48410020350480200700c010003900d41d101440d4210f142404200540e950070310210701810607119906a54800a42e041e508030705640b10a0b00c942c4141020120f0701d982c0c001e580381c441d072042140e001d5000d10008000c100c4500c1c41c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 270315134 1250 270313884 270313903
    0x5b030e060c03090a17041508010503070e040f06020c010213120302011b050a030905011b050705070501080f040b0a090b0c090a05240d0902062b06080c0103090f0c08070503 75
    0x30461802c40c41d04540c0c0350740d251620300c00544a0700c0e148421207100d00f000300440d000b030412485501d0742860000343c040c05024080c4680b501a00c01d82c10002a41400000d5050086603c02c040b0030880e07619841d800041d40001c0c46203642c0f035508012100c0007600742c958800040002c4a202600301d101410040c1c01c4400701842c6602002c02a2000c8129030f903c502103c00845060a0004913050740781008c900501c1c4042e214000c0b0411040c4aa07400b54022000d011841d20400407140160b4a0300c00449a40806554445a15014401050006092080300e56201806150008404106480d1170f00107130f409580514090f40c000680a10f20f042640d021400b0344020350300b080d8030a03260b8990380000807518189100324200425040c07005150303034002140e11a0010180707070b04c4000720003800c61481004c1000c00886016608034851401e801e019020845241d03102a02007101444019400f42880040440b8900129070580001400e02501a0041e11000c0c1c02449254204400d161802c5901c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 270316384 1250 270315134 270315151
    0xf0306230606030a020a0504030b0117070902090901061101090210090513050c070b0601020f060108070f0501020a02030d050f210a0c020f070303140c060708065b030e06 74
    0x38020494a074031548120f0f0340101c0d114500590310382d00386d00700301d6180c01203070002410064040000108000384003152102e8000003010750754455a2040d0034803ca215600d2442d4000a03420010083e650142e988000401095000031815130a42c1c0e0009110300d0358245200d001c1443e2a8003070059050507403401140c03040b0140c0030009410f014002031068020840e00425851030740000582c503074420310a41103850f00c2c407801c407450b07561682c091030340b5215980242c4c0808440d0010018603907200088645800e174003e0090306a1407442030044501c0c3c1e01000d1711256200041080744100c80d0340422402d070202050316807803080e050a01038030b010340743c02e2550b440c00c5501c1100d03030301151000452044100c1303500d070810340c07080004620114541e00030300425441601900041000042d04000c00c607100b0002258406c0c06604070080a5042c2c450302008005041200300c0955200740144505000c0d81400d076500074015030020ba1a081c0401c003141501c0300080d10790200c00c041c07040800c440c90f00450507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 270317634 1250 270316384 270316451
    0x30e010c2706020a060209060408060a1b090e0f0405030f13030605090703020603010b0a170906040b0115050a05180406080a060501091407050315060c0f0f030a0e010c03090f0306 78
    0x800c00025075619603d0000350045d540001e05070003942d10101200c1c001c00142c0240d8095113400da0451000f4042e9601070310b100010591508405841342c44001c040d50201e25011a0320780380d800c921990303030b003009004a03a2403004000301c4a0341001640a480880790201001042c6819458040c2c160340010306030780e8595000c0d4205000580c0d4001c00d90341900c4000e1806038954461907412107660441314038916040818500340810a400031a02a01c80d07401250b00400c40c2c2d03030721070b0301c90740402c01c0703140381400940705119401c0018490001003400b0038500605444007104840000c007110070583c0f1040d001d900194400b02000140e000d00c42c010301e6400c108106041250b110120301030b00080040041040000010302201d42c2210703801c241d100d0240226032a001740d042c2c01030b0b4407a4110f5a00b02203110302200c0100840d000011a100c4145c0d42e071703e45d08040191001940d00e41208001201404607402010894590107845d178001140540e4000c55407054008109000c3c04481c40b01107845c40b0b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 270318884 1250 270317634 270317639
    0x2105090304260c010f05040b0a11010e06060108070c021807021e0a0507050103090201021609050a0e0102031009051e0403030225021005030c0717031b0a1707030e010c27 74
    0x5000ca1a2030348241d080c20b040d820181c4600048455107c0c82c0c0002c4110400411548102948a03070002d0144010a00800c8101100c0b54900c0d40c0c0c00c000c83d20340d400111560001113580348a041d1143c0c5c0c291026020103800e035032011081400a10480f0501c4c01640510700c2e42c1090302d10400700c480340a08141c090092030080b43c035104c0d04c814050154034141900c585502046900c00c004004806141c070944000d401c0d21504810080e02040c1c3d500c002e034904020501100d20418800c59005110f6a9580040380d45407120400103410024208201704040002c09005420f203440f00610451280e500141d413449049036403121038180c1041000c4040349144850010b0302c1d074031164565800c1a04250341c43e680d0748007007041203200f01c60009026a0001c4040b40000301841c02850040304646141c2c60050899a86009240038841030200041d0f400c6100c0200b44a1100000d0b820820344e01d8041503240c40026150b007501c2c0044207070ba000a01c40101c00c000e40c2902c04005000b640c0500600a0007403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 270320134 1250 270318884 270318959
    0x3070b1201060915230307020a0507080d0801090c03140907091a0303030a0f0b270a02070b0414101406130614040b041b080f010b030c0a2105090304 65
    0x2e078001103140902c2020100c046814085403a0b2442c170040d1018030340d94030314114100a445848082003125903100e044804a00c00c00082440a401d03aa03a990f40c42c41a07280c5001d032406064604021024161303203407003481900ca5601c1c4402c0c0300708100780040041d94601507104040b55200e43c0b07807a050704030040c20381c0c0d0140d03408412241c1002a880c1c0204049612069040040c200000119803181010380302145580d400380c0d10003c100000327000748132180c9d684801c520a910a81100804140e40c400c0080d0014000b50780c103550605200b0122100855140e2180e0101c0c0e100081c18100c505c117078810420300d403804980000395440000b005020030303803408c441c02001403c0d200b101c07071065850f07119012090706c460703102007521003c00300704500148080f0406004d1076070544600740c2a01200d000480c8030384040c021a80500701e140c3d0316501d40400c1101c11552a440c681121911030b051245141a880311809294000c00003103029541d104c0c501200001c1094403280c51400c0c202207a901e010005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 270321384 1250 270320134 270320159
    0x507090c140a021f150902070309060c080405041802120d2a08040608010e0c040b030109051f0f080c03070f1a0d0c020105222f03070b12010609 63
    0x3603204000d81d0340340e9840703030700c180d05081081d03d0300b10fa12240d02444440e100341c00d803c90078000c1d06250030070710615250f84454050f4400c065019000c661010f008001961152107090401805030b0462814992a000083c00b5112804c14170021208044880c40551415000d81081111200010601c448241c480a08004010b44040c54028201c00e011211500100c4107603154039446500035944a494a10107001d64030280603c0d1342d02e040030f6002815000f1810126000d807180f0030200c80c00c580c030f0120104040e00009040e04540180614000c0301041840c000001406e01c507030710103101310304148004d82ba00003000d2080c4c1c401c0d03000764820400200b0f505e082009445800c4042164541c121200c1c40c82881405000c50245242c0540150555819440180a92105540c0c2e42d24401000d03a03114031404aa08007a1a40746806841d190416074000c0070040c1a46c4480302d20070040140c0002400c040c2140e001844c150b50001e04240019038001280b40500710a041c1070100724100602d20921 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 270322634 1250 270321384 270321407
    0x601080103110303040b0d0608160305030f030709030807060b03010c031811010e060a0e09060d05100504031404030b0a0b04050403020703060e010b270f1b0708070f0f0507090c 77
    0x1902a50000c42c02c80d84041c01101c0c050070400390015582c00504502c8030081c0010703c00e2841ca401503054aa11002c500300b540012643c01400540c2000340d54400100a075102030090018000307800c2000000070462405003030103e0050b42c0004160714441c0a0600303541d80030b0003203810140b810144100b40e0a01d070100503455508084a40081c28400c401618408800314141d5400100030595a5010b640b103204003200d8181940d04002c42c3d00d4080600408903944030005080350402c10084441c1480ca521069001303000340340c4a50a80007039013007152154080e0300141c865804003002c00070164101d00800180480070785040120340b43c80c4d100291a0011404010490b940701c88047c0c100314825040038020302c03001000d07403811240c02c0b0f0955000540c0017059049200c1c289000034100035650341000c0c4030b401d20780d01c0c08001400c004100740203075001950481309020244030381d00c007003a5440448191948100d144d8919002d0034100945080c556600c10440c65040c44182c041309688170031348080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 270323741 1107 270322634 270322643
    0x21908270309090f16032a02070302060315010305010f0b041e03061b02010f05041e060603080c070f08030406020c0f041e0b0a0918120225140303030601080103 70
    0x2d0b0b072100f01150060b1226110b80081f000700c00ca1321180d48003180d10644115503201e40c0060f803d80c009642141c0184400003d08420396003500c03810707026145149032022694a00003d1810600c1203000300d1050f802e070b03225146c458000c207442c983c029540c8524244804501600c48480f00103901000400542c24008213007000141c92096034000c0e40c002d00d502546d8020b61700a04810030303124108483d0156a00c80c00004241d8480181a0640140d00508005c41c42c001e51301e540d002c80d40d0000147d03030f00f0400003044026000542c4050041c0b00740c1d90902031301d0b618000180109091845001c1203064494050703079054883c0d10207240300300c0c00ca5151013001d884492000485400b603026504502488512801140c55070104004000c5c1a104686d14044e410129006403601405400003184040b48180901406030102070f4440e0020350003181075113086000200b22030030620001c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 270143884 270323741 := by
  have h0 := BRFrame.cov_init 270143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 270143884 ≤ n) (h2 : n < 270323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
