-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0958
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:30:01.120293+00:00
-- url     : https://prove2.me/submissions/29166674-fa87-42a9-98df-6c8aa8b7320f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 172122302 ≤ n < 172302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 172123552 1250 172122302 172122359
    0x60f03110f0f071703070504030501060f1a0a11070602030406120504030212030a0207020a09020702040e060402060315060d02130602100204060504050f0f0d12030f020301030f020105160804 83
    0xe0410030921034000302030708100c801d0100b218040540c40290100c02d100740140140b0304180003609039982c100700c1c1e0364000111f00040900400000380103c00090210086202c013a6040c100b10360f014026010401000482c0411510380192055100c0b110b0390a4250503038181c5030305c611000f0344035071190207400301007840780c10000950005403107003910958042e4040c02d04140b0b442d8140380b0720360000d00b600c0f805c1d94081c041c0c0310160740c43d8208800100782c05180180c0d2060346105000c160f4030140806140d070b40100080001580f01c00040304c0d4400710200e4079074090103014002503220301400036650003040c401704411864850f00048034066841d69022222065800c00141d4240d100e54040c0e400011001d010400c894281140c2d0b0f5200c111004085013402e00342107001c110b2400c1c003440141d90740c0f0100d0b4682104d441d018465040361a11080c0203502d1981141c03920303000d000141800034104400043c276480c04032440c0100030030455001c401699241c0d0340d481d0307070358880703180c0c148009078508072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 172124802 1250 172123552 172123571
    0x30712030e01080a0209212104060f05250308090a0201080406021e1c0e1c2001020a020604020f040905120a020115030c3204050c09270a0e1504020d0606060f03 70
    0x155038103070032a0903003444023515203410164100c3e41028104082410300c03505000300700b0000c0000a000c840e401050b000d43c11480740500340208400c1c40900455001d810001c0d03c1c5026036071118400d54425003009015980d10415402c05606518600c00e4000303010001c40c01d0b00c0c1e000403032081810844c1101c44180078820701c218010f5114094001404513028251203003103409401400c0030b07507903601c030005000382d810303943c0307000c503081e42d1100c2d41140040c2c0089080104500c0d0010076440701c104140e5040110b40515a1840d41d0b0b00a40150401ca0329070116552000c94800d41000c0e0011a6040040c0f10081c3c0e20f1501c410003002500642212a0085203c05501441820b403000c0c003143e1626641012000c05041c0001484c003c1c04c4820503500400c1410016200d29144503031200143c4103800040c120810610304000020342410051401e01c8140c0060410002c2d03100703a008150035040100303840742c2c40000c10001e4030b0341004000f90308083c0c2c00103030386420a407044c209460702d88043c05403448 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 172126052 1250 172124802 172124833
    0x60207060c08130f050111030103081308030c070306020c01090c1514030c030103030c1103010516030b0d020102120d140a0e0607090305190501150b09030712030e01080a020921 77
    0x2003c030b0f00c0c900c00f11107441c41400410103054a02600d00c0c041d070000034101c0320300d0b1242d80740381c4c0c403d030010f842c0c42000140c0e51400f45038034114600103100500c0658104a400180c1c10f40310a010320014001da034001c940c803964042c00f0343c400a110f5600071240280d036a070792240e50014905004200001c1030fa0344061403615440c03031040781e01c5840703600011442c580c02e44c0d805413001068240140d42c0d09040001c04c580a44092080500884020000254002031960000c0031f841034200c81d50b0040c2404610f200040c1d8000402c800e040302d0982c11192a61255a021f1005080885a8001d409014418401400042c1d404407400e0010441900d42c25580e5180c141d4065a2500c001040c55114804030203400b4030b15441c205009100394004102c6010308102e000c150b9015405c224481e900020303e50140c3e2800300000b070010f008520891000c00c0098902070415401280c8a60520032440001040013071113a044407e50303100202800c0078020907050701c00c80031036000c070b0741043e0b403042c0d807041d440280303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 172127302 1250 172126052 172126067
    0x6010905040b0402060d0e0a06020316180e0601120f0204090c08090d1d0904050c190308090108040c2304050615030a0f06080f03191d210a060207060c 66
    0x5800640702c4406840326130a2061540c82000149003c40d50b90b814910507240a0050031070840c041e00015880c0d08105100803481c195001c414800e100d000902280341104544002080301d0780d01e80103c03403c0d900c0e1401a00c01d01c150705c0300c41c0c006a14201c924000c240d101d0340a08142d41b520b202c100000158144150382803c0c051311885610743c0300e50302e0a02441d2080f062010ba9400110210444045440c042100c00505640495154000e51651111030400452103403038000c40c41c407000c0301c17541f860700d40a040e8030034030408034108481100020f007444500d1541d507004050800d880004241071220344a04800300308221480b490034440850244d24200c0c00d44240b4001c420b401c145980c442d089201c00502d00054035014541c4c80d2040042d10007024010a40c5031801034010f19a25002d1101c4200c02c0d00d10800c2038018400d81c40071040c8100100510b00d44591030913034031602810b840300100c03a5030410070b02501c402403181e030010f10108021070b009400c2d032521440c410b0107080e41c82e40d8140e0308030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 172128552 1250 172127302 172127311
    0x3030c1015060e101412011508160806030a141b0105130905041b03080403050f011a060a030e0f0f0c040e060402090c0f040902222d0503100e06010905 66
    0x7004000c03c07000510b40900315001a100d181403005684e405003091250903000341a603588010420b000411440510002c10445108146006a05ca281c070b840075402030918040da0108210100b0005019910100580c903d01d80e00b01c2c0d1a42c080714413511181f903132111100c1983d2121848406e001b90503500420130758a18580c3c010300c0c00c0300d95061184138401010020002d455103440d007410340d014503181c50110b1001c1d5004080ca02c2d5030303c3c11810a245044140000d24807a80c0c50040c42c842510111480b0402403d01110601c0d80d1303800d81001100070b0039440c030051200e03002c1d03005c001d40c222074001180b08082d600380042c0d842c0821541c007007104031920352107000019084100020014070704003140d180d100c00980025810000d19122400382d0f6001a04110083c4d50700051710000304070790682070987d000d64405100c00c0c05e03050088a483c0d408044401030514101c41c09070800000c008200d60020305000340407582d01c0680c02c10343e94041c020400710801c0c3d0340140d04c00402c83e00741034010581706 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 172129802 1250 172128552 172128557
    0x1203090b190e120d1a1309021c080306040b04020d051501180806070f0513080606011e0207030201050f070512030a15080304031203020903010c0306090e0c090609090c03030c101506 79
    0x502281d0315001014040d0050740340f001d05100f45038002180e41b042d02e00921910382c1d0400042941091041c800c00b49a03814080c002e10265040700f80000b4491000ca07940f160b425280400d801e1400c0010a002c0e0190301074021741c1074100810411140c5202050b500c954000340d80e0001d0122848846094054a5000d1100f00b50001c1d00007501c90340c05041c00b42001c0c0c0329450903602c0d00152101545804040383c0140066030040710a004032507134015100c1030380000074503900011031407040c0003130b5070f602c410710002341031020220714148011400001c0e1440d030f82d0084140d41120725051010072860340111407006001e403611000642442070001d100703096801700c0d0300440c45d00d0306603298071403180200344000381016000c01a0f5207060f103081c054010084803580700450441c1c14030840c001610104080d80180744d126100309005650399405050300100141d0340c14805403520360301c0c40e09201c02040900c0c0c1511000030641c1d00b44400049154512540d4403003049400e207000c40c4490302510b18801d2500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 172131052 1250 172129802 172129807
    0xc040b0d031b020114030109060608070302090603042a080a020301050703140c2a0606030708030a0f030908090301020c1b0d02010f080a0b030f0102041a03040f1203090b190e12 77
    0x100c4541015050744581c3c0141000d803492059008001180d5100341c02650b80e80c1e4951104000c00c81d00018020742052a5003025814400b411011400c40d000003070028140d00b001524540c29016182e09469030040140f88440005444a0b082c554a80919404038025847c12000aa02034030901c0b4040c0198a486000365103038481054941c45a04442c00c8410206444510f03803440c0700c8008200203d040b032080c003902d03140c0b400c80d0405050031071070391280c0c2040c1c0040014030000366025003a00e0965025040005031111142800100e50040f44800c540540c40060420103a000c001060401440808141c134214030308030041c09103544241c1002400320b5041003150304064042c601160f44900c610400181d60760b101c0c80041e00c0d060f07160703502c080c0595000600b80100050311400550725900e2104040c5981401d0395420b40c1c6980c0d40380050000c2d05e001c894a000c052107504400c1d80240c114011141c07900b084d1040c0281c0140e102002c101d064a0f11040201d40b0b60041502d0001040311a921030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 172132302 1250 172131052 172131077
    0x15060315171e1018150c1e0306030602070b06130204060c080901050702040c05030712020c0c01181503021305040e0a031107030503162f010e0a0b07050c040b0d03 71
    0x26440503107052105240207071208102c0c2c289140c420a0001d942c001c1141031368003ca402c2c140c9103281c90140b2a2120380c202000160003c0d00320042d510350090b030550a4a00d06901e29040b00248080d820050405000040900500c04c0780c9200c0da00581003160403401170b281000f03c0c20204e106a1140300081000c40a40c0d0300807441000241040e0641814424a0082241c0c0028111121441c4034404158040f0070300c140c103980412419000c400070f2400b10301e0a182c1020275a50790a00303000c0f542c1080700721043c0e18040861080b10400800c05041c2c2e0b0520314606130800b44c040e400c428403100001c081340c000000c2604d01805441c01414411000e07004562603600c0c1101c2688602c510302c02c42e07108140c030000005c0c40c01c1004000ca000841c00030080420107141180b83d0952180c19607000001d5a101c40d01c5542249001407407080d0b0034200340760a00341d0000031984500255219140200e40030030b050090242c08a14000c07164400c844c2004401c6154080004003006076030041e00003080d05106c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 172133552 1250 172132302 172132333
    0x5011b030f170a0f1a09040b0403031d0106030533040503043309050303040b030a271401050705090607080c060c041401020309150306041506031517 65
    0x200e103540703800c00010b840900c0046222806807a03aa01040d580c0000060400d4184184441c1c0b50752404042c00480040c2c0001b03a400102070000740090507091301203001c142c041d0b030001e00142d100c456511136032059004124000c109030320081d2918082e01400001d250280e0501d141154500c0e103040e000400301344214a00e965008004994906c81004041a68a030303031455403110200030a400c01c0c4041c40240394954101c2034401c01d409001014400303003c150380120a0380c0682e24090384242d180c5d1394420800c40174081e400003064048140003100d5001f048804014005035005484640322a03090300d800c03601f20740007220810002402804618014034080e0005c014450089411030704081d078070000a41407801c19134204540100000e403c200500403422046d400580900245042c41c1601012807030300156800401100300001000500541c1d440e4084015080b05542c4c91190030344641c4045d00602c080380425803040381e091030000d240301505d0360318090942d40030b002c0c1c0550380e01d00042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 172134802 1250 172133552 172133567
    0x60926010905030313020406090b06040b0a022a1807050306120a08030a1509050603151e0106120b120c010c0305070b04051506030d02060f0c1b010b040605011b03 71
    0x50354a405400c408070ba01040614090189580042030310100f600c1004100c8616074082c0001900f8051054216034880c030a542c11600b8401c2a156250f2280c04100d081600322412034180e20a0017800318100c641d00e404908940d14203850514880c00704950070030900c101207500e80000b8808200065036400c00c40030030300d4403208410807244048100d43d01e2070b810b0b0b041180d80c001d0f015a211a584040c0c41030701d280c60010006100100034504140d400f10b0340768941c0158950030841000040f40c1c114104003041300d014010300e102103000c2e58403504010860704641100000311401d2039241e184901e420302030031010082a030014103884921000560321600f032520241c0600109002100c003044aa41105214600c0f42c40600380c3c00074020b4544d50710b5140030b8011802039000f00b01c540f000b41e03000215141c00c404409807100c0103a030b42d880240100d1051081c5030000e0700a4503080d120300321054109078020360040b1801d0011544440044a0403101c40402c404855208120000440c0c09845d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 172136052 1250 172134802 172134869
    0x50f070c050a02060c1e1b0a060c061d0f010b01080a0c080f04060e160305010c030c0804060b1f021b1f231206030705040b0604092307080f010609 64
    0x180c07403201080142602d0341804194581c101b540007049140480d40c1031000039040d1002c11100b00400c80e0078148014403041504800a2640b90740f6807611148011490703a601401140400301d854213011030400394044c240d1513689034081441d00000c14900103c501900c2a8032100c0c1e640e4200f9581c0e106440171707500c0009001500c0c001e9860284c080c1410007030100e82088592030039a50000c0c1d18618115003116045880a8105440d0014000401d03520500385070300160400408903800c0f1200d0f0001340722000ba40449240c0c00c60303820704140100e4010a0b42135400d940500b0183c542e8288000303028110310b0f0150000f00640703c0341e1450030268000c15070024040380c000d20340200744804d4070040003942c0c1320020003120010300c0b404200181c54208031250107003005171428083c1c9110303600170409a0184d805110302030703a290b10103441e001c820200035400742020781d095100b5074140154007412000041d6500e01074140301c03c0c008104140640c141c01c0860f940801c10419170340440803401500081103a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 172137302 1250 172136052 172136077
    0x30302070f020d050a031202040f1404060b0a090e06040603030c021011150916080c01031e051e15031b01020f0703030908070504180b131203050f070c050a0206 70
    0x403103041c09601c0c0c0503039221020b886003004100402c141d0402030040140503001d591341500420087c4030f800851411641150300d2803072154212541000090b000c3d00c01d41d04004031032b000110b0703030f049100d5004049200301e9442c5d14040102d03807215410710043e07440900002d8003080403100c0190060502044401c4503500604d40000c04991410f0140c0c1400030480c119a4104140d1091001800061140044068103130341c2d15011540303040c1ea019140c0100c20446030506a07550342e002e40c15920304050b422842282d0204118070310302043c41c800050f002140244102c030083e000a10a00185503e0901c0000c004001300850212120000210954604083d04601841c211030040300c008104940c0618840e4031101680c6081110003484c120890380010300c55400c000c40c00c1c4070741d105800d6003040350390002070204040e81d0300f1003031421400c1340e40001442003104049403102d071a41a4880703401000c4004105481d80c4900808450100c400c000103030a60f00007840b02c038010b1400c40c00600c000a03820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 172138552 1250 172137302 172137323
    0x509061206010603020304021c121202040b030406020c0d1404090908040801090606080f070303090e1b0a02150a02030f130311070324090b0a0c020307140318090603030703030207 78
    0x40c158142480d00c01e80c001c1011940202c144011450000c94035008881d01a401c10084403040e00c0310301d048130032080c1120600100b55001e41016401d50115000b8081102c0c041d1380d00d083c2850514000c3d4006c02c0f43c04840d000b601410110140300e00b42d00854881b8010403075043c542000c802c4002487d000c002159182000c20000400c0c45081c05000b00e6607015000c00100545400101418015034000b0402203411803202400040e4100040000f540c000c103031337000e2655079130588045c81c03841c0c0c0340d2240c0306445010860000b034036400154040c0c2208400c082150a450b0300003108282d000c00e803500e000b00e1102c00002000080c8a42412404c80d002e49441003503a00e10503140d5003015409d810a80c3c680c4141a00c0c0c00c2d000544514805188200c46400c100006003034a0701c140f10180a0407005d4034917102c1c450955803a00c00c10a032500d807074004a940c001440c61f07940b0316640fa4840c00d5140c1c0045d80c032030800620381c580050050f10680740034024514000c29960110020340c4030010480381d100c00e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 172139802 1250 172138552 172138579
    0x20106050409030e09010501091a030603070b1603020c09010531150f050f06030403200106090c03050610021b0105190507020111010e0d0e18090c0109050103060f050906 74
    0x11030140c0c40500d8001e81310302c40700d80d0143c0244203103c88140c024030705019065204120218003141000c1c451138542d90400d84a80350040081d0400001d40d10a41d0100e601040350035203452555a4000e03400d00c29000c842950526406200c00c0c00c40034807a29520030707000d101d4a94504001045d80841e03441800b200120f840130068240c08444070001101031101d0b2400050000b0600740340c43c8800fa00c001c441200c0c508034a02c000841e28407000b00700904100d1501060380441c0540c0d413010301c502c94a82e0007446616182c0012000030020074000c000024148804600317103040a00e084c03006e490840d40541000800b0510700c480101c1c01301c803458100803041110000360303201e64003c88004403540e83c2d1195544140d00006107030005170f2112031180c1e407510b128810b12000029a43c0c8001c945d03801c00c00414071416000521120200034001d800d04035102c204400c03000d01042240111400342c881c101d0807511400110300700c4410f400703620a030109081c000d004500d8010811075202400074540b41071540c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 172141052 1250 172139802 172139809
    0x90c0301050903040f090203011a131d15092406131d0601050c0a0f0809040903030603020a170303010b0c01061a0d2d0504030302040f0e060a0b0c1002090102010605 72
    0x2c9800b80901d800100341401a038865031034220041c01c80350019400d41d4142410522542e00041040d4181500040d074000804034a41c4260000c0a03400960200c080400000d013210103c00c98a450122003003a8508800e41b4110010034082c41801210044040c2186c50500c6400300c5907104035032081c010b0002c040280030f031164140c040d01c1c03626840142a6030701040760032035800150443e03050140900c06000d00c0000010400c104980040440702494002c5c01c0c0740c0f00328813480c00704030707041030a0200040c03c2c150150040d1080301d1003651505000742d543c0402401110301f14000d0007143d0006c200400008208801900d80040c104000017851076842242c60140c041c400c00e2001c3c007140202d0104441050784c820303c800103403105140d00364031a40e489090400a862000070392003640d200045000d05101e641514050002c2c0644840c00503150f480c50300f9103801c11107503988070701d104010100751452440e05a52070704000070000e00a031000b03141c0c0500a500282d038070904540d41c0d00c01c0000c8540c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 172142302 1250 172141052 172141061
    0x30305060a0f08010e0d0c03050d050a02070c092c0c24030708100f060e09070c02060c0f241303030e15190c021213031406100801140c03090c0301 64
    0x240f0b4100006410401e000c8550509244009000a1041704010362012980003c1140d01030100c410002405a407080800c900034058440c0182c41002c42400220307801c01c19a00000f5900d50a000f0008604a80000c0b820117100c1c04c80400d8242e00042d07035184450a203445021400d0214035000c115101840c7c00c0061642c10480e80301001508400900a004002d012507102804403d219a603055040000241c1303844440041c035070080e200c100000b05210300c40e0300e01c10344141d070080c0340036941d00c000080395607a40d100031b120800c03600450580c40c10465081c2100040b44030800c015030410343d00e4805100305001401c1c802e906140e15810311000b2400c00780001503510551000c4000c050604a84d4a1010443c00f03200317094582c40d040e11115520340024550300c032540010840350b503580c2145103103025201030703a0008084084101001d02c01000210b05075114100701091403291640da443c070103080e210070010300c19841003000c01081c1e5011420b4008c582c05084501121403e04056020a0845 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 172143552 1250 172142302 172142309
    0x307031a01050909030307020d0822030503011e050f010f11061303081f09020a0e0405090a060509070b07020906210610060201110f071103071d0601030204030807030305060a0f 77
    0x1140c00c0040c402442e00c6803489030008000001582589404c14000c2d50310302c11107600d1024061101300103400481d02c658003c850301a1803140c04000c030f0750380ca00945103410a0086803100d896004021441c0c852540026040b980000c02402004200c1d40040d100304100016010030060319803542c402d442c004125a5010b404408946007402a050500820844000d0603e090400b04a130440d890f401c0e5620400050782c6500f0300050346e9807000c4000b50341c10010500043c2e0841d00342001c01040d02c60201d202e61609000c0c0e141401641d607615061a100e900c94054400341e41401d00c1004003606204401070707031080000d04044d4114070bc070201001d81d5404ca030300445156002c2001c024ad00c0b1081e6144d6401050240000d0000410048405802d03000d1142e840424110201c0c03400140132021010603844500581070740c00300d0b62034032003a10400e0040c00f0541c1004040401207079042d440380c421541140e8219508a08144581d98101c5c06404c4c0503040a6000c01d0300140801c0210081c00380c1e0006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 172144802 1250 172143552 172143593
    0xa0816020d0c1409090c120304080706080a0c020304060f080a0f09060b010e0405070e06090307150206070314040218060a0e0705090406120503160303020d0603060c021b0109090b030703 81
    0x29185410351125007000f5049089000c0c0e0040002d204078220009400401650b08403602c058a210020029195014941c040589032150550010700c0e150130018a9015401c4024144148140c4580a90703503480f071072203040006480c0c40303160450f00d48120070858100c82550070125441d001c4441c1c42d402d0707404454041e01c4003540c0c0d200c640000d41e00300080c0000c256081c0c401b84031902d4842c801801e00c035a11688640213181c0000c10b100079940078005a0082c05100521550800c440c5500039a60b50f003c4071010f005c41d107098507454054514240091040e41d0003040c16440c1c501d50030000900303840151025820040035100400c541d00102d15a500c90b039150b5940300d441303100210401c070503a0300650100807820f000d15a00408548080203d9100580a041ca170300100110b2504030b0007071060b210003807805403915a003c01000025042100200f0a9500304d0320581418200980c681040d544080e000c00d13660390040ac1145c2da581c0103504212001815200d0682c0d60392144070505c440303c41100c80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 172146052 1250 172144802 172144823
    0x90509070504170304120312050709030506150607060203040c06141903020f07050a08091305090a0605041407140a14010206041e0204020706020903061003050a0f06062c0603010b030a0816020d 84
    0xc101c2351446070b00d074090100e19000e5901072960311241d480351130291800504031101d00101e000c2c2d44448044410056008401315680c5ca40741c103115005c0740f50360040000040f03016400e100c5100d00f100036922500320380340e140500c1c01c01c914026802035000e10341121981c0028059440071510901c81c3c84200c0d40600c410702c0c0d4604400c0b00b001070b0a0903900ba00e2851302c1c50502480132003c1300041c80c3c0380d0640d01c4037001815895a007800204500701a02c0c1c007196104030311011508203064595004507120940c0c44101850302e4850429003c40101e0404d8010380c003100009001c185e91030071500c1072007848040780a8100c0302c0d4010409030b900640701503d00d660005600c00f207500b0300b001362960050611003010041030640d0348060b103440314941c1c042c1081500e0140d8606001c2d243d80444010b05501103190340f814008188100c14400c101c43c41e4070605201c0c00001c3c035504060158080440c00100a0078501d5034070303aa408a03581104000403400c01415040c0340050700c481100c0301505016448480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 172147302 1250 172146052 172146077
    0xf19112706060f0d0914030304062a020c0904060e10061d01061202030603070e040f1110020c1203130612060b090a090203250c030905090705041703041203 68
    0x4128001e45228080c2c40200101e88031100050161101e803544a00086000c003201e080190b811802061414140d00000040c882000a2071b8884510240004140704209030b1801d00d419034180380d5041000581c2020b214819286406184607a0282c810f48002401c903481c0888640303040c2503031404c13000d4075544140600000c02043c000c03503510140d40d00300004e19814810010308180e071088480050710303004000b00c1d0300c540c2c040c000c0d03201512aa0101403020b14250500c45440c40c1d80041c1580c491680c1d41500003182030502d040c0c178441d40c81c0e070014a10f801c0e680f403d201e07501c40180d0000a407800180002c001e0380021071070b00e100a11180d0354031001c540e0000c004c0c0c000c030f80c582e90141484010401029075291141c40e2800101c07681c0e03001c0141c40750345141c0c1c5103444a10b00a541807001e800c00c0880506950040c41c10080540280e0f00c40061325161810f02c8031101080e070709080480e000303102c10042920750099501d880c00000701500d04250707841010101c1c03110240800c44c0851b0240302040e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 172148552 1250 172147302 172147369
    0xc120f020609060714070309050301150920090118030605040f12051204030c0311070b18010302030f04080903160801200a09050906011b06060e090f1911 67
    0xa9402c00e044602410035030030140f0028001c1c244424202003210404500401403502a5403101c000b404080c00034440c400006070580b14044241c0101403800b45040e02c0a0b816080700d42c000b10003071100906040c42d0100c43c03401924030b900c00c02212240d101300b1107001b000094007801214080c030b108000e103403100c20851400c40d22010349814080708000050201402280e850011a90016003505042d240715400d030404941c003421440c2c402c9500d04c80c017040015424800030061005403020343c54041c45258110045060740b100303a440014070480200407402282c607010040505520040840c0d0f811644429007041d2800d459000300c0c201e035134070456006049900c0386070028102c0e2102d4072034501003445ea4081d000380d41c20300605000e0b40a4800086059004600128a61311180d80c692607004403840c2a8014110500031b0307440009112010803241c03c2c0c00641d007140e8a0b03203207019040303190741c0c0e403107810450100d01016121070a04600b61034181c7c41c0d4401500080710300d09141441c2141c2c8000d034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 172149802 1250 172148552 172148563
    0x80c1b1005060102060411090c041e03020112060506180d1203050610030c050a08070909060b040513050f0408210a09020a0e0c0f0c01062c0709050d0803070c120f02 72
    0x1190564121700c0c00c00001819183d02e4181d0b44c1412200c440a1303440c1e0740b205056a000e11f03005004024130069034040548201e550113001c07207201341d0300c0640494003007110000365841c074403585070001310601c291a00307000103081010035203030041c0001d501d85641c0c0c1c035441c41e055080c817007520110746d03503005005444c20801c0d40d41005403900c0c103051084000c4040010030b28420381d40a9000c010030000400c40e8a4031411411000f01101c003411710520352200d4400c4c48540c814405c0c10311070f1403a00989031808a8030300805100e41d581d051100403659503078690302c2c0c84d80d01c0350b4001d54880d00380e002c501e403010507517007070907130144100d4540010070f900c0900c1484103112242d00043c9000844903704070404998008407803444203040318064030390400281d403501420040e00b2010102e464101d204000d400004100e1184c5010690f103004e041d15003003800c1d41c0b2029140142034101e0800450740d400b14109900454105040f40f5120004078140d4407003416500300e034003035440042c0c4001125500316904000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 172151052 1250 172149802 172149811
    0x90705040e0901110906030a060806070f0815010203040303110a1e060b0312090d030315030807050601060e0a03060b061201080610081515030f01020a0e0411120601080c1b1005 77
    0x801501c0b080c13060b010054020450001c2c4590400400100d007030116800c00c00092140104a8483d814051000b030b00c018894020344c000501c40400061500c91500c03090034501c0010780145190070b003952400c6400c140000741c0510b603413061500190024118030644d039480000001501985611880e04400b90b0303e2004103030317219a2101c0d0301d01c0403800811048445083d02180c80c010a40c3d0301d07141c19409000101e8149083c0b07106400e0020501021074000d2800d82d101d00d0646002d42e0f03d950059030300301032a0340d14035040f0f51108802d0000035195803003113018000041541d4104840c451004290400036001003072183c0003c014171802480c600300b030b00b0291591802610310848128401d50141c03200804d0b008100555001a22072924284070840f81c4c0301d8040000d554406101c64003800c02c1b807a00c1d011034001c0f8034100281321345101600648100003e094000d4096440301401141c0b41d140142141da140e080400018403441800541c4501c43c18440b0050b00a22a01d120302d0011654003c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 172152302 1250 172151052 172151071
    0x70302031b120705090d0b0a090302160807090c050408060403020d03060f05010e06130506070c050906010504050d23070e04020f06120a020c0a0816140304080304050d11090705040e 79
    0x140700b1007940d40c480410b030b100945241c13a0b0b44a01c5031a0004030030f542c3c00c20014100c071030210107124001c1807980017001c9140c0070790205c50340d42c5100c01094207031440d00c0c880c888040c0c01800003400905402d8106c01901c640b140780c124102502c0b9142a82440d606840032000740c0d00c8101c50542c400d07018001c1c0c000800300c448030400e0f60351a00c0000b030701d0088404552885070000003640c00c000c400486026015000c040d08154494645141929184002c3d000d19071044881c01c00269807580700b40100c2d001d40d00c002c0c0c070741c121070f400c13682c1c541c241d0102030141e480004102d0f0058203002032003000940000c01c0b410700e00024500305070052000c00c034008050607004410812104881c00301e083c082c690407200c941c2c40141c3e54282140010300304000d80100811010300000c0300c004800e001042101482c0c0101a80c28002c50141d181640d43c2c441c9210704000341d0400e210410035458240ca112541c640990603500307582c4190b100142201008803944400f02e403001c00d043c0140694010120760120820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 172153552 1250 172152302 172152307
    0xc1c05070819030c151e060801090317040f0b09030d050603030301030f020d0f17030105120f07060e0303040909050607120b0a0506030402060714060109151a1b0303070302031b 77
    0x960030108000b5069074003405110321840c0c010100041c1800c2e15100118028040089a0400d04d0400c44170494199044186013410380104a2020621810581ca58151078410744a90182c4402e04440b41c0208107881c0701c28012029000f19090503c2d1a10a01404001d15a1603107241003081c21034002070100c81c020360050005000090586110703207680b036011500c19841340f1162402c44200d00c1e5480740100700c141e8801c41692285552030266050ba00d04441c04a1444e03070102d1025074030900000e4025a0f980840000c10540f0f021300121445600060f060320315103a2103015a4081e00c09000e02215103038485410407003200c0d0b0003c10034400b01558082032045003a0000091001603060160a00c83e0000001280c1150346000484880a5200c002d034818907044c05000c0780c40d00c609114512040382001d00511030401f5980035142640c0015141000280001030348500326000525002c030281c0c40604400c0c500f002c1000914401c50f1141d401690b03901d081c01c6102802454110220340d0308d20103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 172154802 1250 172153552 172153573
    0x253009080106120611160f1118153601442a01180b0309030903031801020709050115080601120207030c0b2a0a020c1c050708 55
    0x11410f0600c15036009000885c9103c2800c0c13000849200700038604094640c0581c3c0a0100050203031004919401030148070300304080030301840b22056580c0b04207481c0c2540600002c10700e120407181c0c44012407000d8540c6c000c5944040034000d010307100440010003600501c00162078540b007000b007d030150111207030845ca214a605a003010a90400070180042c0303081c0c415154070350f01f09816100242c801c07001250106006041c031880d0380701d11490152100c441e000b007401e00039401814002a01000741c280c440051345072100101c1150000f4008444d0790000300414035880d58100087c2111985180714134000394003110019207006025484001317083e040100400403003c450000070395030340701400e02c19042d6070b8520040326070000d1141c089d0722203840828003005242d805904400028803801d500000d6464258891003403000442e40e41486a01d0304906084a0500c0c41c00340c15840401d0045460014510340000c490740c0e45403802c103040262000c40c400a00604024a0005111480203031000c50074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 172156052 1250 172154802 172154819
    0x11030105010501142523010c0306080a080309070506070506190b0108060906180a020409060906031e15020a08150a03020f0d0c211502253009080106 65
    0x5414410210a01107480d02a4140ba0b101c4181c0009038440000400301c807a40c01c11b0115034009a80c003038207035803828011016070341c001d119000070b40e6100e40080500c88403035a10000e840d0700c000c7c52204107008110300012261a0000600000341c458009840c0d80d00d4400e0800c2c201400f0b0003d0002000c0c1003503800b01e140d03608900060b40000d0141c5540e9013a030b443c4404200c1040c0f401c1150b01550b49460100300c0400c0c0c65502510940740a03040c14025583c0c0d0b400a00c06807551800040d02c0e40d6803070904440c4100300c0d01d808601491241004402d02c81540c2d1440c402c90b0803a075038440c00700d11020104446000c3d40520b110070344500300c0359082c01c40d0843d0089001c840041141d00d025041e194596014812826249070042401c0d40840001c0094615100742440800b0021100b4011443e055400a0101c0c026544406440c0e030402040050040c0d501c03c0322080250240c070350310000400d56203042d6000f4165070280502c01200001e41c5007e84008051004a5000b449140d00d462000d1003c2030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 172157302 1250 172156052 172156057
    0x50315150d030302072406120b070e0109031212050105040912111005090106060e06040810020906041806030b060d02030604060c1107060c020a0617061e0d1103010501050114 76
    0x103001e64090060780990302c2d05030000e116140780034200c80e050708101031000300700e0610004e0020804a00748016681c41e030700700c0142c5c040303d00001d00004443d800120180d00c10310001c00c60540514007058030b1540d0740c498940f01d40490311030800280319170040c51602c10950280b5401040c0644040084e8083c5443e1903040a2075408210100005c2d074000c0b00b03c7c09400c000ca0301d14030540c80010410341c10b140300000d000344114482c040108203c81445030366031806400b981c08403407400d03028201400c1518080d900a500100c10359038441400e002c08100a46002410300181040d0207002880c1411410001840359000305098460211460a10010780b4049405c98000703510080c0410b4a03401d840c030644a40c0c200d6092000c41e846071410004010784e000e0841c120040c02690b8880325140c865008485100002d03561071240110a03012803410b003016031440707810819450080014800100005202e4075043c0c0083d900794110007164005c0d407030284181d40c0184401d0810303c43c07140280a45002c10f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 172158552 1250 172157302 172157341
    0x1060e121c1206090e0f06070903110d0f0b060915060d0f060902070c030b060102031204030f2c010914030c0909210304030807020708030409020c03040b0c0304050315 73
    0x2100c400d1040c0012601900030000d1254510105002c40d940320b022090017403400c040c801c0c160344240d8503d01d290420100d03000d401040390f039451011007411521240e250b00c03640c3d2005600981c010340e101020a034030840e011402c910070300046205003809400c21140840152110501224005035000c0a95809088486c800e11403c40800d0000304c1688050041800d58400e030005800001c3d49010451000c598200f41c03441900d0511306512002d004a030f40f80204040b0310600326005000c038010a01421030b408410b201c0d403914001c0c0701039120000040900511028845140034a00394440750b81000020014180c0790385000d80c600a18030000c2da441a2207651680588a11004104075503024070000c40449024112000356031124041e000c0c1a0740110340c294000351350340d004201070307920203d001011070716018020350a0600f44540d2030000d5000c00604602d030f1000308000038a145a40025100c003241d410302541d00c8614010515080490421903101c0740c210150800c01d5616070b064440152 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 172159802 1250 172158552 172158583
    0x1c0c1a030414282307090b1c030302030910090507060302032e05180f07050a020a08030106020d12140123041409010c0212040b0a030204090212010302120a050606060306011709030301060e12 83
    0x203004208000c150044050f0234518800601200703140c090681503001140620642d600700c0e00321554000b0011308a5003c800000e00a8008030010030601e8840c1d0003458000e00401c81d107032a4031808080c1051242d06104c40c1c040b00380c003604000c00c510700e04401200210045110b80025601d803a8950500381c5030020220000e02c040820319400781d41c820805442030a42c0201c03403d540e03584804000c1d40d1040701290480002d6860301002261318502d0140d14086002d490104e00264200030340f030611041d42c0100304400403c83d04101c03250355520301815510914580c4803101506111140b07600356503444040070700b90342c4400d04a019030200c81b01181c0403501001c8549454040e03440f811070292145a004803402800424410307101000d450030746048901c00c80315043d000b0b2101c045503840d07213902c09004d800c98101c180050310f24200040215400041403504003042d540c0d90201c009584010350346600030f90320101c014004d0315000080702526010844031211a00f004150f1075036a2507010240915 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 172161052 1250 172159802 172159811
    0xa020c09040c1701060e010f03020d0201080606090a03060605090604060f030f0201120c02030c1e0c01030e0a051e010b0306010e01030f050c1c0c1a03041428230709 72
    0x24080d842c1c0c03520025000120342450b51520300840f5a029007500d02881c803804202400000c0d000c0740508035001143d9000e403400d00714003c240c00640d0004802031607035401c520100046100303a560701201d03001440c03140341c00044d03080c1031806000d038000c0c00514542c066413500c0e40500c0824404c801c01e00450382c0c40f034800f14a1508501c012680c1c0c1c1c1540003501d050b20700b8178526100440e0040041c100e00c068402c11941101440b1400e6019910214000c100d242c100c6641c4283e00d51282c4c009840703030421042104c50b03440035030b03503003510b881034003100d2001462000c0c0700b0840c502400c3c010001003110440040c007030755043c45841c0d0070664040c440140070f01501d1803c841000000d1200c0c40d00182b004000000c1c041020803880c1410310610001c441d03501d00751201103015503d002000f0302d1003180301e102d40d0466031269542d000524076083c69000e0ba100d44428042070200c58281e209030b90b01100401600e5041c58940b14082e50611701600000b882c4a0416000380c2c84009100c20071640d4050001c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 172162302 1250 172161052 172161061
    0x1207170a030b0405010e0105100c0c05060706020c060a02040e01120503030601120e060708070f080c03070f020f0d0504140906030a2306090106060828050c0f0d0b01020708030a020c09 80
    0x10700a002810241e9002414440001580f07801464480d040754008d0342d0a0907418900342044070030960b8074100a00c0000703044014002401d100028103080351041d1001894082c1c1165840d01e8100111083c2d04140d4000506201e0694070458a50041c00c032441032031600d208a03900c0e02d4480c00001c04203410003c521070b0004800050350006501400c0001c00d40e840340c149004020560300d000c071900701c04070740c0084130850400d11a00c1d010340320f49900b0721442c2c21500c03950302c21114a590224070800314031510115040e6103409000c07103070341512680c4683e40e40d60320744440e5440c84400c86a4061003402120200304807130f1000708902e40301903403000b40c0b041030080c105941d82c10305229004200c3c10748a87d90401091440540c090010340e0710644440304a03959900c40d100120780320344141c0343c190420880b0407904107200e800c5940c10100d2004494200b01e02c0380c074400c0141d04a42c84030000944c4503016000d003941c0620400c009041c54202941c030b002d51541307029680c0c43e40d5001c1d150007004500d0004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 172163552 1250 172162302 172162307
    0x140111070905070309151b0c051207050f030c060109060e0903030604090206190302130e0705070f060609020a0509010f0302090a0e040213020c06151009090e010b0a171207170a 77
    0x7442e5855000c46800035842c1c0c814858802400c41981e005107c1031007440c1250b0312801040e400f00b1241d4410010300340301c680744180c04074a401c1984100c0700c0e48110f00c501d1060900610142c900e28040384020411356242407042c00aa91180d0301c881000100442401b0084002204980c2d2111040c9d4002c2000742c801d1012402e03510500d080881184c3d40c3c59040141198150014565000d5070054414204d488414000708507009403142400b08808011940c001169003154049003802542c1c0059441c0d40c07062600d06990041403908001a40000c822480c0d40c0c12140c9092900841c2c5030450404c0310943c00300302d101005000340045081108009400c641c1d6103030210502000e03845c03095403690301c0e03061816075505c070507941210346001d00f840003009414021680e2000a4041d55006611841c00c0c50540003428400300d022142e540720702a1002039180c00f00d10701c0007040840a40300d0f144c04120189400d00d20b0420399181420020011f00001c91050311b10031050b1012001c003260b550740d02c0d9805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 172164802 1250 172163552 172163561
    0x206040b160509120a021c0212070803090d15050c0403200109060c11030a0303050414011406010309020120030a0905010819020309030d060b04030308060d0b01030b0c130f1401110709050703 83
    0x2c1d8000e000c0d072502c03064164040306c07c940350391003178460b8104580420500da48404140c018040700da0f2003440754415510300303a0300d80050140100c82e400103200c0e9207002d80080d07500844031203540a0b0001400c008014003000e85110320101c10704522014a40480000c1041400340310341001c1001a104c0070040c400e0000820710121001001c59441141c58a0060090142220103440b0f1070300d002c205046401c018050f04402c140011400e64a590b16031005400600210405070f0402036403500c114107000c180114203440300c2c0d00c0c6004549901540e00c000f0081506130f001541080f0f280c038180540303003443c030f4601300c0790f400e0000b000350f00c9075215490145103011302c540305000c16082140000394001da0300d00500c241da0181d540c0e081a55940010f010f00300204030001070690501000400c08a19120b82842c1c02c0b506c0160460701d0a102540300035a410310641210103000d646960800102c1e00c40c6175000e0341c0c2c030710a080c501d5103681d40c101c0c052340315601807041600054030b820000740c03000e219501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 172166052 1250 172164802 172164823
    0x3030610080610140d06170111042106091e020906010201091e031815021501030b040b0603011d0303061206040f1b050d030e040b061608070f120206040b16050912 71
    0x10001d00740e503445001d07c2200c50030224842546054020080e94840c0c0b030898080c0c500928a139601c43c03400c5441030111414507003081c0c800503585c0080707000266024001200c0c80c00700d03c0c0c45000100a0f801084030590002d80410305580c500040d1000044140d010086208101002d03405c00107050f00303050b2040d0781d43c0c2407848880c8084400205030040c0300166203000000030703800c0354580881c0d62020440e0b48002c1c040500f8003070304d2200160004039900c5420780d201001900200740075034035030380030300e00500a88080491034001204105160a025044403103484260340109001d06140e140d603010005454009071101c00081c1d010390040440c02d03d002e004140150900128801a00b0001c0c00242c0d13064640744218248020069207140210545410000c4402d0708942c403142642d0300e0700540d0005004459a05142e5000b0b00031440c0560400340001c0990040d01c518682440c0040614000030701c1e12915020000311202c09580c04401d54560010980710f404400e42c0d050601894051407e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 172167302 1250 172166052 172166077
    0x51809040804060908010b010519030e011104210201080c0717040321090308040603090314130e070c050304060e1f120605010201090b06040b01050d0e0303061008061014 74
    0x818002001038072002401107401d181d6804603e00d4941612038269074401940300e000074000d03ca00c001c02c1c0949903c0c841d0030070042c00d0025100c00110745071402d4404803548190000000b1408101f160403600f0314005c843d0100d408544942c04603800648481c001620b41e03110304a000ca42c42080002e071150708030000000080003926103075646002080301042e009188054001110a521518050b040380c1041e2680103035403d05160826404070700400850340d06508014520704110520903443c002800c00c0b2007030040414071541005110f4052300b601900203410001c170b401000c00400c07408020790302070343c40514192802810b40710015054001d42ea03140e00e00c0c45100d004400c0f2080c7c0040346070042c0386c080c2e1000d21a0b60340d12401a4201c8501a00280c000741108000514603e05507208480c0c04805040071410100036007802011a9080da114600c1540000140111881c003034980403103042d440c1c0303054244c2d0300c1c00d4404280b1409074078441d00144848a40307440c0c050080d2800780d600050201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 172168552 1250 172167302 172167319
    0x1401120212070806040c120209060405090c041a03010b100905060901110f01050103050606061303080307050c030c06070305060604180c0302090631061e0203120103030309140118030518 81
    0x4140f525210307403065034210750000842000048400500c0c03407610000e60010f10204245d40d80301d0500003c0c010041c5101030342c0c0140007000d01c080d41d031886000c1c00d40d0306804078110200241801d0508681c04810060311400000c007204032a41e5007c00c0304010360b0415150300c0d03103440746600141c3c1c40210041d004c003154004c6040784d0710203450542c00306040701d0043c0100c0d259500c40300b044c85000e1080002c07089108a00140500c04280d1210056800020900d44a45031007070035044581940c200c1038000d816a0070400500515585c5405a545c01ca0b00c111005460140f07001481c071a881c118607010b007150b40d00d07071140328401802907054441c5081d0290401c1d98411f2504001c00d00940750100d10f0380c101d01030455a41500b2903000c2d188099030b08688030343d0050740d00c840c07521590003600090f010031803204110034100a05620310090081d84280c40c041510050380c503090b1300c40510032070090100e07850a003288a0100b0617400c084c02d804e4140c24140e54488441110f0504012020700e119040041c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 172169802 1250 172168552 172168559
    0x2060f030c0904110307050909042636010e04241d04050c0d0503040b040b19030c0f1d0409080c1207120509130507021f140112021207 59
    0x7038000030614210308440030400c560b0703c04440b40c100e020a80340080050818445080503003010b1002c1070708140a0700300508118504c140002d000140403032402441c14012421341a11900008840c0399a201e0300408006000900300303103a946414841098100008c80b0401c09440c0c0b070355844491102851140484181c400403902c075001500e40c4240c0c810703000759031110f00c0c001c4885102d08d8000c1d0746c000c000e440840303501400c1010f0100c0b10202a0340c6400b04210019071038404100400050002c80917094441c43e000404207168101c40000400303041c00d00a01070030065011007845202d0440e0302b0316810400103aa1118408102c1c858120340151910520000b4480c000018026101c4200c003260904100606015260b000d80d0900030401c01c03880d0a50f092150180f005480270303143c00ba14130b0b01e00c0446895045c0644a0982e41c000140e041212520745ea802040c40e4841d110070309190500021901c00383c4c41040c0c103014460024450b401451900455545000580c14819054101c5150703945 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 172171052 1250 172169802 172169821
    0x402041d010501090c020c01020312060f1c0303090309060507020904030503070201020d1505090106090b250501050a0504050c060a050f030405070312030b0a12050309010e0a090c210b0d0f02060f03 86
    0x1175440d041c0c400751044800708401c0758400012130310700440c0100c2d8800b99440f210b003400115141c0e1a01c040d03002c2c500c004264980d0380400c45181d0740901950b008140301055040240c142c5050350840b0f010407c0c2001500d01684a0a042a42003545450040e43e00c0d519454100c0c024040c004074125860300f40201c2d06520b2800c0900d000c29140c4c2100c1380c1c80309990750a81a20110498404d0040c0a201444034409080120b017030960800710400c04007030a5110384d542c603404c450084403859103642d40d80c810301007802001c009001342d2450030b076491071501c940e940029029005840700101031000020004003003000612a5000541c0c2c0a19035444445400f06d007c0c024040071042c0c0390203820489000129440810307510240507800c60301640c50075080c0d0004407400303000303c060560000c0c0030a60003d1101078038030605407104820ba440f40041503000e507004003441e03000c5800c85840307410b0028480140c0c0d10310000906c400ea11502c640b90300c00803440400d42c1401010a04521001c0200c1006200003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 172172302 1250 172171052 172171061
    0xc02011b230708121b04170c04021c090317130c050103050903120624031b09062703030a030f0b0909060f0403020a0b100501120603151107020616140105040b0402041d01050109 77
    0x28000c4180d404448e1010244030407030060358002410401041442c5065030616448071802c20b0191800b00c0a0750305014092032120001c4e101c001500942d0f4400009101d8040d0600c00908824a01400a420650182c40c0e5900800c00154180e803200004030302a50f0318041c120111911403403140c0d00d400071401001555410480b41100c820290400c0302c0400c0c0030500c110b51380c0703101c01440306007028801031032201d903a844c3c9200440c0114001e1480e0b20b0580d810030140803c0308041c2e40102e0340c4018000c1c04005d80e131545030380c0341c02140c3c8030f0284101000b01056055101c000c1c2158001c41b50794505080b8030344041e4090141045d030300d280910401d200b41c3c10030182941d4080c0c9402e0504000d240102c011a119880007034800b031154002907001103016000b00c007039101440a52420080d0540020b030140d0722100a030915650740c201c0c80303810000c42c07554008100d490300700204050b180c141c03540f8030118001040244030b2552031104103100580c00e841075a0180181c80200495030711840444000e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 172173552 1250 172172302 172172339
    0x1b3702030903060f04020603150f0307080f01150503060a0e16060c02090603150c030702030423040509060c09040b010c060c021510050d060c02011b230708121b04 71
    0x3401204009204c42c10115003141c0295400303003a0b9465035468200c259803001d003803103d40341c0c040c5203d600e400300c0d69010800d0304080e0000343c01801030201d04100450864007504000003032103052803010061a50302181095020311541c6012480e003054122580c00e1286584540c066020401d101044076076200411000d100c7c4244d4541e919915414105a91a44800a48250024000300041858240d00301841d088425030041320b0034103445100080069950000300105540c080300c0e0310780989040d00a90b9000301c1c40c000505014117024801c960b0901c40e034012076012381d484008003900740e485401200070441e00300380d0802480c84075140c02034032100e030011341c0403181024034003103450b99100090240807500010105002204542e4900015290303181d80c0c00c0c259503a41c0c0c0000c040f031001110880041815503241c1507900356031056030480701e207200e00007815041305100724000582600c084484840c1c41e041d00300d84030790f11a040700b80c5103d00032220b0a5100d2003c1000524102901e00781c1100c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 172174802 1250 172173552 172173559
    0xf08060901060b0c25180b03060a09021005030c040302090106080603062401080910020415090801060b04030201030510081209090109141603020c0607050a081b37020309 74
    0x31661825244514080c5480000300350f00411500d0003d050008002545c032518640c040007000d640f107501200101d10fa40d00d6082c40b58071086114004d28007404070b5036100300382040820440d603240c3c021850703034508a000c1034140580040451394010499003902c0c0215401000b401c407941e107408008003004402d4175400c3c0a03106010102d010444642103102c6850b00034111000e0b10306401c401112604030140c0402c4ca5409200c038183c601d05002d0000348082c1c1603c0e140381c01d032208040e00c000c1c4407054550210085915201d01409004900360442e01100e40900e004a1703151186000e0701c04030807a6501207c1c0d43d2140f4072141c400703055040080c000d480e00443c4d07072034001e82c5c7c2c4000b506c064401e10408d4601410442c0009450300c050380101584618552500504001c6075505891802c01d040c0c803800b0200d81c000c030340700180c1c0f80c0c000d800540c0180c4040f02480810b4003005c0c0801c460240005510104206540b270300700340f40d01c10702f00c00482d800107480710b81c01d801c00c0312019459600c01c1d12a68003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 172176052 1250 172174802 172174811
    0x1602090f01030206090409060f06031b0e0903030f0402030c0307030b011809020a06030921170a0c0c030e0f0904080306090c03011206021b030a08070318080d0908040f08060901 77
    0x41054240d100e103048940103800345203031080010800000342185601112955070f91000458003d80c5846070302c001e14401c00481c03031804c0c420b4900c0450b22440e0362045010031100700410120034030220683e41c01c1081d0101404082e202e5100003801c0001d0402c4003038061068074400010b11118011a034100e904280c6a10104088a04003100342c03640d140d000f941040450310100003c2d886944144c01039400340c8aca069520862085c0c81c8480d20380c0d952a9800030725007004c4c54100090241d641900801501010410380310480b10107800c021540b02c0240c00d11035260308810341512004d80400b91000028076800c510714192a16030354581007030b6103031800341100c003002520740c3e03800008807410ba541000842e8551807142ea502e0000c0c6d03000e05621401d110500281010b030520400207004281c28984684032203241030240103049588200810881e00410400d0001241e08402141d001c814000c1c1d0208061445050007146071046a1114040d00c43d64180015149408035082c4d01918001c0000e02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 172177302 1250 172176052 172176061
    0x6190206011809110f01140a02010902031009030815040f0f05010f0e0405030f03100905090f0c01080c160501140108030a0801060e0108010915031b1a0f071e08160209 73
    0x1001c40340e00103c0100800b01aa0980c46149051411614600c10524141d21040340000801da4940c109240710000350303440f80503003011490144a8045900c962100811000f912502c00510711b0401a140c0340c252014003045a00d951036580200142c1300c1074450521680380e0940c001c070028142480b50b54002c503122880810200380c9064410300540d0440011401e200c810f01d02d041c3c1075840680f1407105240d0b1810300042240d02e90050300c4c070402c079220143c20740c1e07041c0002907410003907000c41c914100302c45da40801007041503a000f5288002c400e4100e40308010401e1500e640100f9800c4c00748101890303440000502660000002d00c030800850b91407542c943da988000390380700000d4515643c003141c0c5200040c0b120442c203a0006a0311181100241c110680d00d0b00c0d9640d4090740741d81070121a10705c4040902403551211406546280891012850000d9408240c1d2040c02950340051060320000b041c03062004d480030944403d01c0c5c020641c207948070035400c80e000c1700c48a4860100e0043c44641c0c00503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 172178552 1250 172177302 172177349
    0x1308270a0608010501050a051c050a0f05010b0a1d1e01141204110f0409060b0301110f070b06010c0b010914060301090f0b07140f030a27020409020619020601 69
    0x410441c1d00984955100b6400e00d0010340d8503412517030401702086401d100d9031140e102d03601d4450f411801e0f00c0700b00042c1c50400030790003810386034009422003040d810007004002d541002c1c02182e210038000d02e80b110094141200030840702040500035a40984c2c0b0500308880300d91018061102c0c040262208601c01c1d070b02c440c42d2903480c09100c00d042070041c5c3d00e10003c0d0100e8404001c2c4000d81400030080c80034170b00014002001c540d07030850285c500c26501c1f2405042420244200b902a104465256082c0b03550706458030054812540000d100641c82c1010403116401565200c180c2503112a210f0300d95071b141c0600600030300c03030004002d054a030541c0201c0d00500301841990282604030204205100b031135100c0784011180588198100904801c00c00b400c0d031511406000000484403030182e9030f04203107050030155100108002c5601d01c880e034010420302101c0c60380e00600c41c1d0645001c16290507900004855025100e04101e4468007022404000341e80840c60605a640701e00014801c0103070b10000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 172179802 1250 172178552 172178569
    0x40e1608070206041e2909070501020309090a0207062703080a050903161110020a110301180f05070b19110d020327060705210304120305130827 63
    0x1d040241c4031101e14803005e24a0000b50300140c011070040040b000f159055440c45550201000e0307a80b240c0c1d20510801c114140403007001040240300030f42c02c003107440f40000c081d01e80c041d01418140e5400604541080342d40c1d00a001c00714010310488a00540400d00c421000704060300840008802d000040c48071a028810107004860920085052456082903000d0346e0320001c000f03440440c0c01c0924104160344a0b07e5014251b4011b901411802d4820315000744500d144500043c481d904182c1800f041180c8040d05140741e0360040e5449806c0401810681c1c201100c64020940400001404003014210b0b15142d0403400300d2a61000e280005036071402e600c4100c20b03000100143c20400204a00941c0d408221400640d00c0ca00c0c03060703143e0264001100b9500440c8111401d07004003580303140321822a6801c0d840740c203d4034507007131840c07030036580d007820a5540e140d000090580d20400f00d2002240c5e643c1c80f200643d03205c00115500c0740d0740091801c91921120041c046500ba60706400d02c0c2d03040003240d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172181052 1250 172179802 172179811
    0xa02061b030f070f110607090509010801020901021f230f0a0b15070c0806090a05070b04060905040207080714031804020f070b22080306010306050103020a0806040b06040e1608070206 80
    0x80810083c0c903840d404489489507082c4d10030803c4141201c1111a003402e0100500421240d01e42040151600c0c0c244401d41078140c2c4169102d900c181319400181e40c010a4000c00910f10740900c411070000380700c03050002e00c40c81d0071076024014040e1442781d5030485001c0c2c40d07000701609209802c481c1c2d26103000d141541c500070f0000e030300301e02c60300d0794642d991080034040d0203d03074401c5001c10f407041e8440e48c80d41d203070110840340455994004500300043c04402c1c09000007400880031082d1030a03044c0310025001f1010761082c40c1c010b0782d000070b0800c2804082c005807845203501540b00561030564102d00303030307403500201d204030004119004285254680362003101c80f4902e503507014a080c0300380b0362524400d940e40100b008000c142e10540c05201c4040c2c1a0f007559545100c0d0a0880c5c807424060b000604555807508804e0515104100c5840003d0b0000f00d09035200328100d5000c41c4102c0024040707400c500072980b040c03001c1001d000030303c03810660901c1c100124103040d40c1c42c44900e550700318003241c0da44001d0b207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172182302 1250 172181052 172181071
    0x22080604020a080a1a130807080304030801080615061b030a09060e0105040e0103110d02090405010912050901051e090a0303030212150d06020306180f040209010509070f050304050a06020a02061b03 86
    0x2074061103100c04005d94000c004180042c680122511002c80650149208a481103000001c220806410100c143d001d400034400901040c41e20802180004040c0c040083c41800040381089003040929640300d08600d0b280150303a11585082e101038480003441c0074040104111203c90949544644103440071500b03400101070550340780d81c40d540c0080203004206a0409800c0300c60101503107803121610b018612600001400003a0b508180b00c0d080c0c01d0440c004100102040003e140340c1e44001603c0c08501007080380d002801c51580141114841d043c10f5a030085110319002060541546c064207d1100304030748645103a5a42c41072094843c44040e4942c1c0c06180980010b010a000f5805140d21a0000e0640d03140801500d601da011180700310340901401450000300402c606000042c1401460155109031480c10824409030040c00c00064480800502100040601008205000c4020303080304045650302c3c054100203443c0c80086598401c8905c0b28501c0e28001110301085038407806085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172183552 1250 172182302 172182323
    0x9020a020d050d02040806071d010e210a02270606130303050a020102041a0a02010c11071a04050a150906050f0d09150f0b1002010603020307050622080604020a080a 72
    0x3210580300c43d00252a405003483d07081c8000f24031200304000586c0106165191001c0e003c0400b02e41101e18802c20502e54104940d000524180e5240d10500388a042401d02c5501030701000000610f1a100811601a600521260305065103103503030304002030345208255075840c080e9a13000c18440940705032030303055400340881401040880d10440c0601100440e610001d40350a540b880703041c26444001e10021040603000440121a0b41c091060b0324441c041e074104094021403003107916494460500c00e11441d402c0f100f524030062444030b003c0360060070004108600a0f900d0710f2040c035540c145680f00a0102d00d00120128120340554140c131125140e07a4100c910704511440031502414855404072080050280b41c000c0c1c80000b40900a5010b440d440f001851421060800c84000c50080f440c00c156450a1402d002503103001c1280d01c1501c000340e5001e541d4079845000c0c694014000f45614141c000c0101001c2036170840810300c6030089000700c50ba10310103a180d1071085d03110380c00c000e002400039884 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172184802 1250 172183552 172183573
    0x40f02040c02150108011a1909020a02030c01140a060e010b030c0d1107060b031605060403080a171302031608061303030204090c08040218010302010507060b04022b0609020a02 77
    0x103074001e103020030401e01c19164210804001c250000030281c001c03012994480c00000400c00600981c20a09002114030210340841e2118288480d41030340980070481c1d030000b038040f614900030412a40c8900142001b041034442104000810400580d0020b8000d401e0090000711043c102d0000c9058a600f0600c00d807079034440358008421503100ca00e058185030f1f1601107000c6064840c501801000c0e006010200c0c12308100002c0509002d07150041c2d1140c5100305a0901460700c03031005485c15aa4089000d0790b071100d00e070100b500e442086043e208001d07030b401300800081e1b501b090b0039031000c90b10a400300c5601d8000c40c101e404500c821402100d445030b00240000e00c6625103403c10a50103070003404e006280584521484081d03c3c10b014040d0041410442803008505000c0065000311494010780052541103038002400c500c41c0920180005444140703502082da00d9a04444540300c010742d200900c00030307607503c0e240310a880d0b01c481820a803501000091116480c005c0391500d013103980c040c0c881c0554 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172186052 1250 172184802 172184809
    0x2030606240c0c090403120b100f1d3001020f0304060903090314010e070f030c0b03040c0e0a050403080f010303080711070b0a03090c09090503122a1908040f02 70
    0x1c200c0900c103081c0302e80001030b03d843e02c5120365640114000e90720100d5140000a410b819549200c00d042d0042410f40940e540440d840402c0f96442d400c00c0c031345042c0010000032031344107410700085041e52080d0050352180314213500040311509030804180a84689030700c1000d00b8203c2c010b43d01c000492513001c00001d40010150b0744621442c51113810481c1095807607484480000b4104a05c20310281e6441446203001e001c02c1140364000c0c0403407061040e0050440c0e48106405545200d0f2042c200c40c0403012404000c0d40740000f0018004031548807541c2c1c80c00e00701c01c201411042d901500880c0f070a10100755110002c181c4c090617685c150329802c0d62a01c80316011182e1150f920940c3c1c695000c1c0f101c01261202c80031009040c4006680e40100e924001418609440134447c0d0040e910a0301e0100b60200144011065455401c20b0208584450307441c0880c1000031481c0404400e031540802d030280d400103a454019061950103100e507055055000c80c03056410380f00a031005001d268201030b0240040c034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172187302 1250 172186052 172186057
    0x3030c0714030d050c030105011b02060f0f0c030c011505010810030222020705070f0b04030b06010c080708070c1e080601090f02130612050a02030c0304031103040b04030308040203060624 82
    0x40720001c403841e0401ca000302d98116101a01c14402104000004104a6070b02404040002c072001107006001201507001171664405e0f104500c0407000b020601c400c030b0003491415501070314440001e499551f8180c0035018001d10705107074010400e02480c8030104031541302d518214820b803005803c81903407500716000c10003507100540c00c04c0020654144000d028440f94000391100c5803082000345403940c141011004800d01c0c54020760b111072000d210805c081040885010741182c02820000321205050a0440c001e21421001404803100090407504110038654000d08496140703034442c1c0c14082c4010b2150f0031905920030b28805500c240014000c00c0096844814181d00c5100c00502c2c213801603507092081c0b240c941c408004100400031642e400d00840c051681d101c41c01c001c0031441c62815081030001800094000f82c02c10280300410655943c0c20001c0314041c241c941040e0b51030f0380e030ba482c0c010072051046030102d000b0f02864012030210706086070b22140741002e2101d02945146400d0078101f0a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172188552 1250 172187302 172187333
    0x80d0b04020d060305060f06010c05250509070809100605060403060b0d0b0c1e0306090103030f03090804122604030b1306090303020903010c1e0f050c0d0f1103030c07 73
    0x15801c2040541d4940c4030f11400c0002e41c440c9024040910305a0000060502c00411581c140404407400d0300001c2d001149441100b448041403074400c524091949903100ca50381c10164000b034038001488071180d08040d841d03126507226000c9a6840700011841c60544581d44501d50b00b03c58180018400030b001e42c1c000905250014062215101503501c401262140c1655541c541001c0020746002701103040b054407061440300c01c3c10600e18103205000c103001042c1448082d04120300d001000c400d092080e044285a6900030b00c41c1900c403512107000d070295401c0d03148200c80d0107801c00e4100102080c0b4a0003071000340c0c0c00388176990a291540c0c4072042d541100500c0c40020034404210500024024816211010302a0f0790058446a0f80410305086807a118145d2341401141e076206240b11004a46507038031000d0b10301e03000592a404031011f0343d15001e0480140d013140144003401d0a001d44c00307009800c12550703e5130ad50b800c800c01c0c58816901c91109940e1031000100400800c1c0202d0404880000302c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172189802 1250 172188552 172188559
    0x100e01110706080601080c09060405040c020f0f011a0123090607080301060201060e13020f0f04021b0c04140124050903062701020405130b03070312030e0105070c080d0b 74
    0x5810204004608001c01a044800030a00d0700043c49044d5070310502e9160300c031b9035600c5002d107040a03060020343c16025900c50280b007140c5a000e24502c3e1842400400c50700149001200e10b0300c041c041c0c030140a002084403658500360410f0160f41d1035849100803440003110181c624041c0c48552a10540c1544031907803440d0016070030414440022140c0000314000c19031a4000a581ea0400c0480000c9007005024003040240303c42d0341c140940e41d401c0d40074008000031520840b2011f42200400d001e80101c2c5e03182c07488542040b02c202c14210020680b520380010848041021244240c01d45045140a0082408082c80c009240d07541d18490040c0c0d400384c00c400e0800e5400c1241000010b0320f4880201d420313407448100311919903c0b00005050601c000c025440c001d608042c1001d0109613410001c0003136402c204c4c0c8400715032880342c80a2158401542c0c010400f680441c400a9000d0007405259440d440150b29050000e031030345101d21300501c000356004501d1490612802c0d4100302800340e406d106a031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172191052 1250 172189802 172189817
    0x6120a0e1504120e060c1020040801020712020105010608070c060f061203030b0406060e010309300905010801240905130605090f1e0421032702100e01 66
    0x1404201c8501503485148225418803a22541c0710004011aa105441c240140001d003d481c4100501103450082a441c5440000304070100d15945a41d074010010500c442c4000020049008101034008040186c000d800301c0c081000d08020403400c8580900c9290001940700d80401c488900c51907440104600800001c00c000c074114001004aa02d96807103000c01c041707008140800c154050042a403609021242003000c0c9203441006040f584007501200c0c105640c8000000c01c1040c0000e0303910201d500d2480c819443c8800109208211103c503107500042040510f0000700e56109441540c141c601d00da100c860340199000c3c035119100080700b0300310b003800880200414a91250b2040e04c46071030103004049015403402040c4105c80b40e0281003c403141403010200001e284d0290b0407001c080100081140c0d150360b56042c8280b80c6841c800c030240c064054464625090f43e40350f001545220090600c40d03030700040304525101a11a58200203400c0001a00604941c070300941020403001e0381810f0021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172192302 1250 172191052 172191073
    0x40f030825081501020d140903010929010e010501230d0507020705190b030105060c07030f0b06040e010c0f0e011b2003060103051005040201050721030b06120a0e 71
    0xc04910304a03000007030941d0b042001004003540c0c60f00c800b4100780090300007014040c80c01481080282c522104084c40000c0c01180381d242544180940f58000b02422426283c2480602080b0112a041840a64020000700390031481818890413550140c40308900f500180c2c5569000ca420030300101141d40c820300c0351920207455400380c90300c950040d6000c0c110460401082145251000c10800301148402c2c000303201040e40d13002200d0640d00201c40c0641c40323a02c201c80a6181a402d0b800003006104000f10003020007010718801806032400310f806103c10407000c2c10107400c075014010100e001500303040d0b0418415028030742414880340c0601d031165550a03c0011a040d1900b130b50030440d0000022040710040c0040081d0039040000c00320042c1c41c0300d501d10744945031344901001805c1030869035900880c1c1168000ca04485030642d01403007003044005460b10781449440405034205c040381c1840714544c4a0f161170700c00c86001a141080d452050307110300408400420341070038900e115128598468 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172193552 1250 172192302 172192351
    0x7030f11061206090c070c0b0304061b08090c0409051f060902071b0509040b16230d0b0303030112060b0f061603020d050a0c06020c07030c0f03030215040f0308 70
    0x14010700b0182c0740e041c41c8606002050102020000b000d40d5072002050107030720005080301100078200c4040c801c2e019120386a81c00c207400101907104d242420092020344020340b0a0300080818400c8002605881042c5017800521040d101003032001840c6070041004050554a28000b410b0000346000c00021000d80b5401410100d9003c203000f500c0c5c00100a46000042034180c49520207000b00b0f446804150074070340d81c0c08441c4c01d000b4011a0b01c05581558901001d4800c1c4000c0390200c1c5182060483d4030055485e105481d403002980700b200703904044504200d42000800c5030304132020a80f0311410030031503882c0e500c000c040c60320a00d90700181c442034200b121783c1c4460142110100400403002c0145a41c54064a46000e400c191300c1880428480c600c446604800c40540a036000400984d480700c04000983c00c00f8015000180840e40080010981c8400c21240c40c003500e20903021110002c2e000030306040c10345000c6400a0019900c00c250707a000910a014050304150018a00c002d03107504078406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172194802 1250 172193552 172193557
    0xd0605032d030f191b0b01030605180d030903050918100f05011b0f0c0f15030203090a030c02030709021801030b09090d110c03060a02090108011707030f1106 69
    0x10a103034948003029180044010a42003410516100000c2d03180800c40c1261038240c0c0101000d80204c0050340400c5044240910f4075070401d8a01103e442000848500d072041c01e08500380804c0e100d8a18000001d90103030b144903248046650034200030064506100f2084001c0d1440c0e1104030208030050005035181d484802c041c0d583d41003c03e92501091520104031070300c0304019880302045003010300040090340d8000442e00304034816502091020003950500314080c001e4240024882200b5220000313850846a89200c01d94542c1c2044082194404e1821426800706480c0380385180c00c00000c100c00207000e00200f45006101900756080e8540d0750003440d00726042440c0d1441d00c8090250700b00081d6034940300382021400e04980c00d2072141000c0024954030032000d102c680074450841c0c000c4603242d07001c000c00700200100904941e81481d100ca07012011b500901c40c242c0c01300e24004000304100c1182a030000f1900144002001d0307844c81e6845218200710000c80980c3d5021a1701c440c898a078a03000e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172196052 1250 172194802 172194823
    0xc0907110f03090114031603090c0e04050c0405180c040c03060b070302011b1b15180c0302040513020102030a140d06090c02060c0309031b010e0303040b0405061605030a020d060503 79
    0x246880d010f001d000917001480741d101440c04034500308104940b13801040c580c2050f0b1981841d000580c0d004a00e4050f2810780c0d60f0704403083c0c600d0740404001c204500021203110041c2e003581c0600c0140c0390945a400c0d036030000d1310004c207a0f810550b4400c041e4100303940603da800b1202d10740400c000b907a6020780c00301640b10307c40940061b5107505106240b4102c0030780a800e0b02825241c1b10b1a020070480500c400c4d141eaa0380001d0180d8180d19014006068030707040403c00c540c1a41e0013943c035541518107032504d400140300803401582014005940500d251234110110b54041e00a10f1408000240c2111001401c4e01005020001801a0b1140c59000c0c42120068020035800285c01d85104501904d401030041c8100d0101600b0000c004201d1000b10a5803a008003110705080710148200e0440e003d0400d030b02117058544804401c04c0213110f18011280e008900a405031801c644a1042c041c1a0401c0310b240300001c01c00400100312451032907401407080000740600000e605403101c0021b400e2840419 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172197302 1250 172196052 172196083
    0x90203031902031210120f030201140a0f140403020a08070611030f01170604050d11010209040509010b090f0906040308180706030c03060b25020d0f050304060f0807020c090711 77
    0x1800e02d4a130302001c45098000519051000001c0c1c030300820f02040e081d031380307500508190300c43c01c4900c1094001d41050040f80c4000e580144e0a15101c440c81d4018505900302d502d6480c10011810384c034120b42400240190741580c05041c400c8140e07243c5680035400158119900781c4e83c1c1e050745990718030110285004400301c403030340d034250751618091030304400311200c550102d07800c08030038000001c00014081c0c20054080c24084840d9040300f207011700a000c0e0528013504a81008208000044c043d402540e4001e4201c4030501e80b5150142001d045805c2103504102c0d952002003c03c000c03900030205a544640700002e5860940c006142c0a414600c0560095000ca504d0b242001940d607094002c2030054101d0340542c900302401c201e500700001c488004402d4000c1040a48442952240480c0180c0035030800c110301c1070100149041c0740d4944c840e00c0754900181c10b084541141502c603140f40381c0205800e5005081e43d000403002c00003c5c00c40070301444140205050000524401806000010f81c880c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172198552 1250 172197302 172197307
    0x803030a0b010f090e0703060503010608010f0c0f0806090c041e0302010207050f03060417090d050a03090b030103081b0f070906031202070b030a20120709091e09020303190203 77
    0x9031440c1518201c00c00c50703040c0448802082c0781e20303510090303103c00c5410340d0740d803152103403aa070b00705500030b000a8000d1074055007010000306903024150403006420104aa0402c03030526405011102440c172240401c000410fa81e0102e00140362580d00c45800c40c003460003031880d0580e0f46000c00d0200d0455904403e95001c6444100259a0188100740c001c10056401c80415480b03940020f4440600400c010940310302e0080303440203480014142c07101e2240241c040b1400d032100b420301d6aa14090382074100c0000313211401c046440200d141c2900d0490b0b90180e10030741001944100c1c0d07640d50200039070001152040600981142a0400161000b8040910001000c505600785042c040c0400c07400c0074199801250f040202c4904d0500704c07540444100400640848069411880e00392505501e07404120041703408115001d0b5007584601940c02c03612080c1c40c07a50365103600c80a0f03c0c4066001070016000c0c600c0d15001ca000c03a00f0107085541b000f07060300c1c07030006100008540780c0d912803003140050340302 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172199802 1250 172198552 172198561
    0x130203070c080a3c14070816051614011e030207020d06051806060d0c15021903080f13020307060302220608010e0703050603070b0a03091a0912040b03010303050c0703050106080303 79
    0x554011810380d070110316040d1245007901e009401d4a00c200100100b410000043d0f1000603441c0480710450308d035001c42a6005142d00d007004501e2000c040c083c0304403602c40e1202002e15580281030100c1001c02c1c0d00c04030384c208081c0e4503040e002500403000690f0450385001d002c800003003684c841c0350b101d08410760b998913508524580542c50b001000f0012400745031100d08034800318425144200031180750305100020321a05020490405c400d600c10342081002a88819040682100c0c410340316030300780c8010030f10f2540c40c80101c0e9414100424041c1d05504050300c10b003c510301ca0340040011006140c020aa00400b900500341036151039484a0005940e171401440003103183e40000390824030354031341802503041c4100041d841c1c00e0a88501b41c04040002a2821803134040d03081203024903082040000016100e00241c404850101c451034000d000d60450070640329a002c003920250754098a2941c00c580c02c40d927059809911468181078540f05900b00003000801c02d00501010b00249405035031603041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172201052 1250 172199802 172199897
    0x4090309060f0810030f0201120207030c060b01050a12020a020f0a0b071704330504061b02030c07260307200913020405040629130203070c080a 63
    0x89000b0300204202c4600c0621440302003840b2076400340d80d002000380ca00d185141c80140c0c0c000c12000221005a4008207c0000380750b00444c0b8400164041d1f0424011680000011151841560315170b10100c0c54803981c01645000a50240988805c039004541c0f011880003003682c60b0049880040b41d52800320410082d03429440991070066051002000c140760409644002c00ca20071405841d5024112481c001d9290f83d0340042c025824103100c10410850034030f800e142002d0242e06005200d07804c00340507100d03401d910020454840c8400000074044082c00c0995880030060031009032042000c211070b4000005070180000c00700c2c07504ca005000c3c519021032859400d0034a10010f001e2081c994a41041110743c0509000104941d049500080310303a1186003078401802d100c00c03030100ea0800250032038030050f810031941001382c50468141303c01c4034991594106030b100440d50180081c0c185c800c1e081c0090075940140c00c00950703038200100c44440e00c50140100011801e15005150071901c1107813050b11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172202302 1250 172201052 172201067
    0x6050a091d0601150c0f08040b07020a08030c070e10050406080d120218131d1b0a0302010c030c05010207050312040318030203031e040302040203010b030f07020106120f0602090409030906 82
    0x202884041e210640c0341c80d10765484891001c2c0041d00748585c0c40141002c100d8140c0741c21030440d5101e80410740300d6881d60101403040e0804541280101032142c00462040d41c000b01341c2c2c0100b54403500902c403980c02d00400d611610b4015182d076841a14601d00450240d5460040c1009002548011304a241341200002c0291034030701d03201c40402c0c0c410486009140d24813017049411500680721480280080242d15000340315080c00805191142550000036030800302e00d0462404140001c00d11150900081100443c81803000074041807503040c4031000a801a1409000240544001030600416444803415a44003841003c415034103a4200020142c01418402d0b0080000083c0140c05040d640032980c0c03440b482e602c80007501c02d5064040c4056003a48119000b9650181040d51a0359440c04001c50a07001501c1025805c28070900140002d48140306040c1191402083d10800c00481e4545100006003001c090b01d060f9003c0000781c80544a50040e01c200910907030f9105e5003607151080080c0042c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172203552 1250 172202302 172202351
    0x21f0b03160608070516060c050301090b120d20010905060f090a050606120111040f030605061c020913051605031c140c0a02091003020f220c0306050a09 67
    0x201c2014006000c601d41c8003031119030098031410415903865214051140790031480a00408403802c1c0f04800f2062a4071001460490700070100c24408450781508002d02449841121321280d48183ca0384507030244a0440d119502010784900b00140d0144481a070031344030b842d201079071103912100034010b90350060400fa0b0761041d880742c058141984141d03a21602c9220242080d07100305510071038214000e50039480112101c0d10040ca12384d0b80d41e980d003101ca858141611058036000e14100008600d420010841000c0b01c2620400c0b070081c820a60802100040140c0400d01070361082e0074080c0001e13820007150a00e01e9200104148180c0703410101890410756035005591030032803150001100390400ca281070407015050710140c03150001f100d010301c1e1405441001c0d40c440380600c288108840c0c40b0840100340c9000b40e0f401c0702800c5c00001805029000e120b00c54500700b40f00c003607a0407060700c640c1c080d03003080340246404140309a440c4000351540c51640c001c0c1c14841d68034001d9413817803901c1000c0031011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172204802 1250 172203552 172203583
    0x1c350f09150403110d030c0204050c09040221090a0b010306020a0e040e1c020c030d0c060e03040f08010c0206070905010804053301090504030f080c1201030f020108101404090201021f0b03 82
    0x1611170b543d41c010610608014000e00680d107400116200c0e1014605840350b100c0080c004549911508403240c08000950700c50150314100383e004521401c4010401c000015081296041079074610750340d260003503100300c1404080010341c0b03c05c2001991240200240c0c014440028140702c20800e0405844084100c080b00c2558021a10746803580c90108020103040c100d401c01e044542c81c1030910501500e1200705803510340c0030005021a0380000860034009444500000300a035903007024040c0d98480d002c0d40c5c94000300b84502c0b401c1006611540c5030a601503c50f80a990122003c95a220052502e00c5a940340d44c110110b024510400076161281c018000303040140300c142030070303100500b006c0c1180e0584010068810b001400c101e000c00b048500492508103042e1483d80c2d60708025070328820502040380041c034030b180403446141d101d91b07210065030304c1094034190342240c513000c00c4014802400304074190301420342024443c0016010401a04203210804031b1030700340caa07080504150340201a0000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172206052 1250 172204802 172204819
    0xe09030c0712150923010b040203090d0210090c0512011803030b01030e0303060f06071b03030801090c02011b03020a02010e060f0405071a0a0f0e1c350f0915040311 72
    0xc1204034003e006070840d0040d005084510311000c5d540907007041c10304181c105000000b404520900040e202071507600a6094442000f000d40380002034459003000640340345256101032020b4a0000b071030080390176082000181c00d21401200441d06c2400c69000c0d0080317a0b965030180100d51b014050340d42140340a4000d18514a869400660304440584030f031801b070540859070200b0005044c00c038848e0f80a0700040000e44507660b141c000c00780202400745884113400d00d180542100d005000d0b10a44280480b842d46241c01c40c144224029040303d60b80f40300715900e9001c9c3c440c42960600950f0302503201084640700624180c00d2903132410860780c1c0304014400e000c403200203910703100320280d804103640e92404140c0015246000c94542c00c1524450b98003061a28841081032031103041c004244d4481c055034221040004d490840303401d1400c00194001c40c0d0f02c103140a031400004010320351034250320560750501089401041240c042250715400c01040004d0a0080c0406a900080300342e500711034507603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172207302 1250 172206052 172206071
    0xa06050312090a030b13080403050105010603110307081807170c031c090603181502030610020607020304060804051912030501080d0e0f04060e0a0207021f0503010e09030c071215 78
    0x4403401c0303c0d0b00c0082d0480d82842e0101e031b952040c902c1c201080c070f50032098440d1900d8503030400c24024402841010007091402028050002c0f1040580e403040205440300c0c0c10f00c2d41ca901c211031400354442d05203925401004400708901000541a01000080c480101410131041c0c041c0b601d010310b123104409a03454a000301000d5994040a1030066803154a00440c000e12813249092000c4800e09008210001e40040200400c0c07280c0d000c1e5104040c200c0e0310740c8181143d244281c8e2640016680032006800c108030910101c1d0040004a4000380700710b003100e06001e81104540c82130500050225000400102c05601c2d0356810b008490140c0303484030107080808040f60000d0007401207201594015104ea86c92600d817a503c641c4100c00500f00459030642c0c5142030301c0d0400003544103000892180303000190600c400040102010740380b0040b5210103186900380b080d004640e03c4000c003860418031040000d141318010a1000c00c00030030328020703028070812040c500020500013417080e15103c030b403508003500e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172208552 1250 172207302 172207309
    0x717131509120c0c05030706170f010806070f0e0d050307021305060618130f0605030d05030c030c2818090506030703060506030106030602120604060506071a070e090a0605031209 78
    0xb15040c0741541084506040d86140502d0181d0312503103c2641070081d440300080c400d030081c0d17181142c0300c91301c2000922681c4039400220440c0c820300510160740e1050001441541c0542c42ca170728007148034181700300103607070042c0001c000420b8603408880e0781c0c001080440840c01c00180c0c141c2d00002c8a0000c0c0102c0c5040404243e160040d0700700040020101c01580c0c255449088020750a240e10100a010000d022002680503010502c1100e000f403281450010a80f803264080e80e009a0422010034a103844032421560701e50401001d4095140f0446948920340c18500700c146088482602e07034545a60312500051070452030b07507010101050801040102e259400f0071b0600c19260300c502c0000b025200c0401090040605410082c13016100040c450304400c084400d162059408a4040c02410340311801c0c4000f5004025004120707050340e4103014011b40a003049503900900d00e00e0140e80303071583c200c00140008800c2c0d4240b030b08950b460368184070904007846031854402c0719950842c034080d0703601c011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172209802 1250 172208552 172208573
    0x18080f09010f09061d01030e030307020c1005070804030224040e0f070c0f0f060615200a03051c090f0609122f10060b040914060d0204050717131509 65
    0x554904103051171400890307001b648412080501d520440f6202d00e010711010b541c40016080003480f131100850f1100185204504076044103600500060405103507600b4411100868100d40d5407600402c9e08541243c48858040c200030200d51981c0e1505003000b41400c0c1545201030194010004810391000100c0c4401c040c12214a0b404902e407112a5902e080800c004c1800750000d031007502641c504118201e60080741400c201c000210030a0b0b45225a00c00c403075403039202900c0240823410a201d80c46401d82680c80882c107001d032070600400c44040399aa09807040c0d0000e001102c0d00c5079160345880c00c3c840c02e2048551600346a0528541235040c0880710152804001f454000c1e003101c0c1c10403018032000c148000e181c2c100c0d0340d80d4180652030303e9072800401a0010300602c2c3d003607442c005054403d01c5108034140d006450103028500d403000a6000d01016020040c5590144000082c1950400c030f2402c3c4050702c520700602e2002c14803400d80c038000496100d4a5001402c40c1d0400315280085554100e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172211052 1250 172209802 172209827
    0x20a03080a090806010f09060e0603062a0409050a050906061e0a030516030b09120a050304081606020a0e0108060901060c050717011d0316020418080f09010f0906 71
    0x100d41c9030200c600049881a105811908503070040c44000203101c05603221280c1925400b003001d00c81036480d203810030004801101d06592661102e004516800d0140805102441da400c1c82c041e0519a181c501c01d099501035485541e240f6034039410401840480e21411350012501c4c40545584e08001c00080c1d03c4130400b020300c100c0960940444c0300c59036115541c0100856001064808059414a080c01004030a100076a061415140001c8034800081a03584018002000040c00d08203040e20850b2540c10080c012281e4030340804c20300b01441445030121100c280320355005640e03805004d10041946010050140c1444130901c280103103640c40101c03450541e0080c2c500039401d0409402d090340380c0302440c1e000920601620100c61348114041d0882d0000090300c00d04000e034001e10754262540c2c3d100b9100e91003041c008181003000145400e03008801101544603d858010b10f19880c0d03400e155003c4118900e994900280300103595070803003036680c00c2c2c40b414100602414584000500a50311442 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172212302 1250 172211052 172211063
    0x30b0627040e0a06020702040b0a180903030b041e151d060d0803040b060901050a270e03040603020c060601030b0306072303011d01080105070f03110f03131a04020a03 73
    0x1950403155110703603108000c440c00503000c49a1103c0c6a00380741e00203512100f02070340180d0404100100904003011558120b0b00f2425012070301404c0302d44d003d8001c00c03501e4412002c00d602d580b10b96a013a90f55002c0d40c40c80080d4050052040c1780300b42c01c00da0840d0707410482c00d824484103801c01c100c00380c00003080d20070401c01c1c5402e282c0c4035a500c4000899448051a00605005010003400140300c1a1409184100300070350f02200300742d03298000c00c00c000855100d8103850107513001c07100000464000008070440c3c0000d4000c20013441c030b038540d1f60540c1c0142c0c2020340025404500507074100420040c041d044002030030104881180e0340c2c00300c0c0d124600100040c00380100c5a500c607040c05021003008100e0030702c1d0070550b81c507075864040300008411010603495500c41583c00200300b003941031103014020401074880c800e8560910100f9006084100107102581805000310314244401000841c81404250840346014210386062400241d0b102114084036003048100300040c0c45440b1448141c07074000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172213552 1250 172212302 172212367
    0xa1b020a080d06033e0d030302070302070f120b0f011415040b030a0e01051e01050f150309010e0f030403080405061602040c0e040b030123070c0602040e0403030b06 72
    0x10940c0b50180801d43d00c0140840161002403d000e20018a11008550150b64200c00c481100c95464514080005215030103040c2980c0400000d0003540105415403184c0151405a03680303030a0394000621703983c4a44011010150040f0401c5420008075622214500703468185505182e070b642034003800c560312140580c411301181d5098005800a550007010000b1160350b60385001d4403448058485480880443c1d820310022036842c5182002ea59082030a0445003019a840c040801c60303000000100f140d0000c1c0c000301d103d01501031080040d44110024000414040151500da038a0310094501844035900188000d00000319110304a40072036108031581c0c2d46409420010f541c4000856400035800f42c640326602102941050502c11b00b210211382c200f000c0240c1c03906260903a101c00307004030303c0c00c145465200b54812a1048194000341ea80c039000d00e010f0740b10742c1e0350300480e40550010132081100314100420543d1501409541c6002a112141810f1030900154226103940c2200700c03c07030111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172214802 1250 172213552 172213567
    0x30609070e1906090c080c16020907050c010f14070c0b150f030d02060a051f03060c0c02030d020105010e131511090d110f040603020607150207020a0602060a1b020a08 73
    0x411010403040c0c0150b0038200030295584250200602c0340d400a0000300d014000090401100d0078196103540c03114580b2140c05140070f50030850302c00d500400310030921030b060001c0d0b00c0c000b409101c0c828078205807110009410300300c2c41d6505041940140f01d0010409001803010010306401c0c0382580001d901d004800807102c06400054020b481803e1701509481002904056141d0024103280112031620f0100001e8540101007402c4440d9585135406464550b0000c000080c050b9100c3c0280340c009103001000c1100f5a40028100148101c0e03107c0140e4560300148400800d038803d2a4101c004400111031001d07440d1f03a6815a2440780b60401e040b940e03223aa0498101581030211a0300160043c00045200c240340350191044400070044d5006182483c0300c4000f50400c7d1007a6403d49030020241803c018583d83c800c2082240052000c490035002d01c83d4200688607210403d010300440d40150801e89080d44580c000c8840090300c1c0c11050b6641045c02c0034442c1c01044013002d80340c0080c00c09075030321031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172216052 1250 172214802 172214821
    0x1703011a030a0b0d050d0801090e030a0c020303160b010603110a0e0409030905040f0f0f02090306060907030906020a09060206100e0115051902010204031a07051c140906070e030609070e 81
    0xb83c2c101e079580c2001c840103110041050100358018085030b50380720118035988803201042120429021907400d80c1c4200075507072206015000b0b500182c2d1004040380d15001b000e002d40010f4ed98282070848889036800011b018140e05400744100d144850071b940e81c00e01155001c01400c499408141a004980c0c6002d090241440381c0c148401510001e0010300241006000e0040109800d08040c5102450b00b041ca0303991406600031120f4501c401402005292142c81c1000001c11020342100b042c07681d505616000034001d40042c00d07020005841c6e40040502d4142c3c00390401800800d070102189002009105101080300c61505540034a0101c0641e0100c4000c107032854440c0882d0a441c20a140ca542d25189505400030000d4a101d94400d000c030640c104250040d401081e24004045a01403000500c88070f0303d00c010f4001802c0070440403401070303031541c1200e40202003900d01542c542c1001d01007000d29900155280008141540200b04030300c0d05a50701d6803504824022503044080d41c6020518044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172217302 1250 172216052 172216061
    0xf160609140d020106171506031009050604020901120b040b062101050405070e070203040618030f111e01021b0f1008070801061b1b0807030b01031703011a030a 70
    0x75404900307941200180850750b07903a250900c840200542c00d06502099030700307124405000e056062030060040980010713039100000c0d802407405815203d00820380034582110700581d0001800341000d0510380c10720b401400b4080c40140c0102c6c0b50031000c1c14000b070000c0c281e01c46069001d03410415000e0a41c458500042202041841c5226400303840b040990100d02c0660000380903034070850855002e259120788240075690201c61140141e0003d01081026034000d1400c0030440340725001c105a0a500c0359600360b107038403061005540b091140302c80c5e10380700c0c20032940c10200400d1445000381a11190310000355529071440d40320310042d50000e4802100c0c1c41705105142ca5200003841150704c0d469180340101200c50484800d400540000000104a806050300340c6c5a560006151381e0001081e03143c14641002c0b1a004048074411001e0000d144803007808407802540c49141c40043c035514505051104042222440344030590030401000603101c1460880a5007904092894aa59070b10100e40d0080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172218552 1250 172217302 172217321
    0x1715040206130f08071d07030c0e0901030b06010806040b0a060311040b0406020a031d0d030c21020709060e06010503040b09030c19020414010308090607140f0102040312050f1606 78
    0x954901d2400304407640d903d030941003500d000d941100e4215907100511110042102c4103041c89000c4140414195407298020700d1105043d0305120380440701c00000305141d800709070301c1540c0206d503c2090020035a403058800741c0108049a0610040010034000b4480e50b49501c0b40505040d81c502c02440204036601c280c40003050250003981e115641c0303160103074450034414802c400044c0f109220f403a030a803041c1840c24200c2d4000d0006928400b0655043e00c1c8041103800544503141010a00c0211200d24000c80f2418086680900b150300c0c545030f05542541d1040c0c100c8145100c86500304201030340d0103429a44e0040d08588000076645803040c0c11411407040000d220494010079200c408800300021441303440314420385041059441e44140369000380d4080c0002444c501c0100002c1c00c451400b04040c24646019084145424040d00302d1146004108080041d543e500414200280201030040300c1c90715116041c410329107410300c05401007904c9000c071400c6140c0036551420050241c0350380039841d139 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172219802 1250 172218552 172218577
    0x1e0109180e1b03070e01080c1002190c0f08010204240c0605010b120603030a0c110307051206180d0f030c120213210503090405070c0b10030501061715040206 69
    0x2c02c0c0410100101240d542224600900c80c0803c00641d00d140c01980c00d04a03011040500700820301602000704281c442003c0e0821440344c41e1503810a00311000340f0788200fa1281d501d1504e1549402044915028241e01800d03242c1d2060000700000302e2190f6084080c2c3d416481814400c0308400004e482055902034083c1c021072070b000000c00d0103501100102880024040c03228210b03502c010806030740348201108000011184c03514400028500c0c0c0010b414490300401350323160a038072000070621202d00c04030b08451650060007031205130603148091588540e41031002c0c0081d44c02d41c0034041d01003030b207142d0180d003019036868042d801188240c15419203180030135015583c40c40d4105070007162a500380505849804143c40000340310042149441c0d040b98058061402d00c92004101300040070000c0080d001c0c41040340070390b00000c8128415601c55003110410306031460440c1030090843d409501f09910104034030924035402c010020318842424100d26080d02559a1840416013501a0010100a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172221052 1250 172219802 172219813
    0xe100c02150c030108160b122502070302101112130f060c02010f020c01090b0d0b06030403020a1b030f060519060603061e0b070f0507031505061e0109180e 68
    0xa03030b5a2180001c6049400303102c00c94460303190105a00044080520581d24444400c202407810003804c040c51075400130b5200c2900e2040c91041c0041c4c102180010003400068104038002d0045251a220001d5225154078061352220310020762a0b5a400305c82d8000000d110011840402d202c00c0c40d10098054071032507004c0405140d13102c102800b81c040e4640200d011800208181c030000d4030000c0e1120300c0540503034604000d00d145c465465000c0e817011700c405440b01e444050b074000382d44a403002540104d10036401003541e222141081c9118204a400c0300030b83d140044d00810200703040d05013031420729411100c0019291141c0305c40140751002803c940d560300f404d0400010740da9070594410300c122a110844a007501c0c41482024181041a01609202c05801c0c007404010030030800d0000c45d5584500b0440341d00701c0c1c484e100d00c00718a03039014426401c41c1d11103007004081c1c24041000d180e0441e210f02240904140c1c18006003c01c2054000c2540540c51006500312401706070700401840c00c162020740d030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172222302 1250 172221052 172221061
    0xd11030703120f022e1104290313031409041104151b11130f1505030a030c0602030a0b06070803070e061804090c09140405100e100c0215 60
    0x161603050784200340380841c1d0a034a0280c035440c008140700d0080310710864017001c804110304130b42250380c825114001c0100c0ea10880030756044001c000500c040d000c2c040ca00c441241048400c0c00e034502103064000c48040092050040142c0e004502c1072001c0c1e810300780710700003025040d41031215000340c0307028603449030402c42041010740d9202d00800079908851041280e400c1f030260103486440d611243c40c214031034108808404210400c884464102005110840f4003100e403140d0380a0354101c910382d485207541c80c0e080480c07031034210140d20010202070b8080d1843c0e0743c40f40c80161041c1c2107008090000e0b50004001040ca4019502040009400420007512003846040120140c3c00c21110607011480500070202e261505405a0380c0304120341c808000c5041ca2101404050040400211810b00d10b8401c00700d007685041c014905180039130309400c0c0c1d1070b190a007411440c080081c802014050301d400040100c80c40086495050026043c002080c9082461401c0745000c040200410321070304c080c000d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172223552 1250 172222302 172222313
    0x40b040f0509010b041503080a170c040609090c0807081807060206060f0d08070620030a02070308060402090f2202030702030d0c02060f0a1503080d0c0801091104050d11030703 77
    0x41d805450204002c1003869013420a10044909a2164088441c07503040104001030440c0000c110721411454500803001c02070912080680c026900110420030125091017002d5015400a006003a005410300c40860b82e2034001d012203402504a008000c1c81c0702c0050001c009034442c0301550318049084589050340c0700c0000b526621b00391381c45031144041c0e076129605891300148040f00b65802c40703441450881c160b0740703103c000c0c100d940c2c80940b0071440d01030b1040080d03141070145205024030807016a40340117078a001840800c00602242c412441845044255103401003220b40300502a14110380c4980c0d010310540800461040c80b40ea05800001000416035002c07010b403c91010301501480b0049444209907101d40c011100c0081003041c4030700003118506c80d60403034000c1da49a1302800c640162241c82d048000d034841c0d0f00e4100d405031104448400310b64000300040c010400c05008118007100115a50160300ca14440c0c01c1c0700d60462450382c1c0902c02e410804240258005040710884c503528a0103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172224802 1250 172223552 172223561
    0x1006140f12071404051803091c0b070f030e060118110706020304031e05040315050718090e0c040b100c1a0901090c0b03090a020405090a05161e0605030c09040b040f 72
    0x203c5015070b0910700072038084440c0006a072a200100b001440c14139000d1010320640e4100c00034551089503900326171001203101c401c0d00c24080d01440c0c0d1564020701342c2c10006421f60b000c201e80c21120f9030141004004440540d0001d040c0c24007210008a50750010340c0e0000e51a001d00c1001502d42d500c004180800c0541104915076200c60a19000c041059100d8050340e00340034600c0050321460740395950b80e08000c45540310030303882080d50030041e0382413080301190203080c80e503038024612544e51348640d509103200401091080034411142440909210300200301c2c1440003996040a102440c50548d04200390404bc0510303c0464040f094602d00d045502da41c042d0000210541d501c818000002c5116001d51045034402c4000e1001031504030400e41c2032000401008010100d00d000b000180000141c0a111041660440d00c940055040c00c0c66030a07104071040704400590425140400c02800c0e801505880d80044007401840e100d003030120220b070143c0781000b41c0c1c0c0e601603d0007664041440e0203901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172226052 1250 172224802 172224839
    0x30a0204030c060804050a020103020306120d020a020f04180b0406021207180617061201020c0a0b01082b03021806040b070606060908120309010b1f021006140f1207 72
    0x5201d0100c0e503203d005607021a42590f000d1301c1070304400445030241d4066001580c10450140012000e00b0b4000342c1c203410008089030307640040e004000e0140031742c50034940030102d481d400c540402c50030011700b2040c6140c1c400274500a00100070040003c0a1006642c1900c01c03060078820341c00307154681410020300041d214030407000b06030001c1d900410414406d02da20000280c0c40c81003464242c8424040004204a000c40025259000c1150350420501030080020261262210600c1541400402400c0245500c2030b03003001d07801c070112400000928041294071030494100107a454800c088070000f04000c0600840d0001400507001a0246810000745012809910b0821100381c4039041160190b1652040c600c080d4403070348151f28003a40c036000541e01300c10b800e400011912001c81c0414044408402a6080c03030100b00d140103002078050001d51815802803000f00000c030300b0266210043c66000e40554007a40d1700e000c00c0d1107280c55603180000409a01c504a400e11580d45442ca00303c10704050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172227302 1250 172226052 172226063
    0x302030604081306030213031e06060914060303250311070611300d1d030a02100902031515030106140109120b1b1e18031c0806040908030a020403 64
    0xa00044e00c92003403007a00c800500c01d9409804040c41d41c0c0303e1100f400500c000c0580f0406540d028180014200e110b0340c070081100e4080401e8000f440000b00c511110000d081c0d50180e0420008a05101c40f1030b0030010000b1507840b00310381400402e08044415807605000d546561140c3c04000c2003494100c1045551034000004540107090b1280c80c000c10003070713458140910000c02d940212000d24109014221400192034005549030900c807101204000c441c80f82c10494100156986200e0307814011503044075101304040c445000c0320342c0465030314444840460003000f1460302086005480700c040550145004009005940c7c0324070414189a400101c0540812255040010380141e01798462a106421214404459462244952a0f1700c1c06842c0d000308981d00300003108120308008503007034500498503005c940390703104032070303050010310303061305d14503c43d912000b14074585101048800024007001d1401030384c9919600c012401130814070a000f00301d8503000c0200074480700c1e00d034050000c8078003c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172228552 1250 172227302 172227337
    0x301090b0f030a020a0608071817120a0905042d050a1d07140a05060703020601030b0c0c0303280905060405070504050106170411060408210406090302010e0406030203060408 76
    0x426583c0c1c010080000d40002000400700b042178020402298480c4590910848107441c0e070f400c9070602c41c042d070410040383c0f050400604458030204a441c00c05000100c059140510036800500350b82100c3c8141c500c101d480e446a9461082c1000290201641c8503d08950580c0c1c040c1c5144090901294051002850302c00c0c40d800500d042000c60362850104009400550b0410303048000f004019a000c42d0003003418000091941c5a080041003118000e6014003602d50440c0351044d12144058040441403206000403119240044201e9401403e02204d090f8100c1200a001c15200205c0321130403010351908402c242841001701314584158440d0060302c00f81070301c5c0c030200412204280900400501440c2608109a40c04070f0499049400b40e400ca100c01060000051803a034890b4009180c80c0c8c0049400404211602c0c241c900c0c03d0220303080090a29051110081c10f6000b180f00207410048a150080c0c1d0a4407281c1c40000510f4001d420346200c1c0c81c0038104203040b58002c454000c510601d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172229802 1250 172228552 172228579
    0x603091506060f0c0f1a07030f0b1005070501110310050f04021911070b19020c010c05060a020f0d050109090302120c0a020f01021005090106050316031203020f07080301090b 76
    0x50340701d040c060360354648440e800d50300321540846200c414050100ca81150400509010035414510540f10b4542141e43c2c09061802003001410f80d044060300103d040c0c04c08403e0200c2e503680c13010001e1b10558514040d61150780c44d04010740940b1808080950444000081c00091081e034010b4400395030041d0f0f00900035241c52400d000480c400c0c1a42c00c1051060905c0c1c000d04507100355072120900070340750102d030080c61720343c5e408410991045003108440e4549541482600da010b21401741c02c54001d092a11218140d03443c0c05032201401082c1800315580056000c001a1005040c1c4d102e90300c000d01c08101940c0c4401c084001821115070517000341c81a17410020148030004121000014040302410444074260300740031000d4080c580142c154000d400c0382910301c8003c0e1141c1441101c3c2d0030008102213140c482452b0510b00000c0360f04c2c0201800010520104940864103d4454030910300142d071102080e05409442c000c58400418084000000040c55451a040307400100e008075004070001f0407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172231052 1250 172229802 172229843
    0x21e0c1801030f08090111100501090c05030402011d0a08120705060f01080c060a030902040906050103020f040e0c060a0201180803070314060108040b0c04080f070e0109050601091a0702060301060309 87
    0x40c00d2200402d60f00c41045550001200e52001e44402d24040c1003138040460040f20103404e144200c003c070000165510300400c1540c0040c00b5040380d0b46140c1c14a5459400c09030002000401e00068081c0c1c1004605001161522216021002060010700b620240c2405040c540b41d694429181911a03100e400082902c40c030b045185141255920001040c480880d541489001d4105298030020b0580e6940a407000d42c07200d000381001d9503c1808001101d60441c81040203002500210034017039450041c042c282e0703039400203155008860480700b558858100d240d04902502f400b0b04c040e001e03002c2c90b030541000c2014900c061070184150f618188101c81590051000000088441500203520304001c1000300d01d801c103841d600b00a0702c0551500d4a512840c20314136000d107240c030580903035200340c104000d078070b4406c0802805802c0c2924203004070304003080003c1c00c035061401814400342100c002c80c92800d8649003265922075010380701d2926580d43d810003030010041c15000769a08416862180b09010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172232302 1250 172231052 172231099
    0x1706211e07080a0b06130504050313080303060f0108091002070506010f09152112090306050606070b010509090703150506041a0108011716030b101401050403030f021e0c 74
    0x6100c100103000403d95611103003998403025100d15001040303420100e505028601900e44594010300045940d0620003c8244c045d42c03196001c464550014018001c1c6a659007402e0070f000d09007460542c2454a030200c01c1400c1a075409400c0c01030600c001144020800e022980c0c03412244480e9107802c10607586c60b106410383d0b0145010781c0d10a40016420301ca0510030f5500e000d01e54440c48011034031062145c0d80c90491014017807200c0c0114a05003410803c01c000c2d80280765010005940103410b0074442e5444280100c81030240c01e10601c031f11000103100c08030800c19680115081119401500d8190b400d010044c00166240340c00349042c45d021590501940c0600f201b03203041a51402d0144c1c0c81d28a4480c1d1102d8501880c0c145800399000e043c181401d910b0740030010358010640b0302d0542c00c2100d61803981d402c8680c04dc0b4054404040450543d0f80c00c0002d6030308a81d050b06200c000b0740001003040f0b0414203085c00c2c01161408000024185c2200001c03070b4030346034034103031002d404044103403a0502020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172233552 1250 172232302 172232309
    0x5040302061b0a230106050a0f050d05030c030a08071205040b150103110705010f0b090106050f0d0b1e1518040b0a03020a03062405011706211e07 64
    0x500100206580740065070381c00034024401c0c4095881c6038070f00d43c0d1440c40100614028950221250702c0803000c180082c8a00b50042204907042c3c040c032480c00003166400c1b401807003420f100b1440c031158081840418401c485140d41040256580d92000840c0584040c806503202e90000d8040081801c101c05144241030041c3c2c3c11032032640c8940c0c0c03880d07803112001d241da0580504054850b540b001c4845a61805000080e110705c00200700d080910209600b00d420711503031030b403040f0181c40040081329003000c2218115001100400c0e981c0ca55400703a14041c0c04d0919940e60840c0c151032002c40140c11009030040d042c0070885211380000c054402c4103000380a1000c044d920b9140310414945685001c0d0b029460114025012080142e50f0350001480d00842c4c0c0c0c419100180c45082069000300d80507200500c0703110101a8840a5081c0000204001c0c0e050410030340c918403449c049035540d0b46800444c20720700322000041410700d007842d0380c458403040300d904204040c40301c00211590003040860000143c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172234802 1250 172233552 172233559
    0x60f0601081302011107081c030b09010e0604060308030103111203250203010608190302010f150b07060b0a0b07111503060915030d0905090906070516031b1b0605040302 74
    0x1640c03182c0b54074000080c50200c081341800850201d0f6a00314000703005260041c03840e10050044d401000d0040000c1003c1d0441802c1003510706010b03000342d652480144d82c1540d800d5a031042e42552110040360041c0b289420207000701c200480000200882c00f0751b4018980c0040d05c5501020b40f003000d030b06075030340280180441c540415620203440c1e4414241038034100344c00180040340c5183d481584a041c01c9824510303907000c0780101329400c24960240100301107054031142c10004c000550041c10030708070050040d0860091f0025500081c407880741c2200b1040300000700000e2050b80d039800c00304500e604c00802115222a202061030051500008550b01d4420012802e4510b60710002045030201000f4010929841d66013401c0303c182d242045055000ca2050301c50612041c03d1404003d40100024200c81003a031001040012455000d000e0b2444c800c840d1070200d2000100345415202800f241e00d4030342c542c0f141810804107100310a403449420742441010014481d4803004c1c12940e034416400080e41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172236052 1250 172234802 172234817
    0x13060510121404050f0d110d080a020c01060f050a0b07080301090b0a09060e06040f0e07051011011515050c030f07020a0e0702070311060901020a060b01170406020c060f0601 76
    0x180e0900520345010241075011000601900504400707800707910584003035031154041c00178000342800c1040f030304900b0131140c1010f41d0050300001d0030503910082c946c06102040401c8011620301c1c000794040c1e60400007a00d000340800c0d40c03202064000d0024900c1003901c9580c0d006030000e2003c10171401c03079040d1a0400c0d80c051443c2e0800280c00054107509880d1900810302c081c00040c1d600d500c2c440c00c4050000d051000380903040180400040da40e02841c0440d0307142c42c2c510f85110303802000030600101c03070301640d4483ca05074018009651104111200c00065400c007181e4002c5e4002c014981c00035100340c00e540d00e02c2c095050b07500704c60301e008812100f8180c5d4410008128250f4041c1d001c1c015541c07004015044050f12110481c1a403034007903890b640564405039003802004202c403101c1c804038a055800d10b0508003e1030000399103a4418002810700d5580d06180f04860340b0440c14210001c80600ba541c11504240c40c00740000d42c0100e050003454002d14010882c00b664801e0801c0c007409050b56645c1c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172237302 1250 172236052 172236079
    0x1110412120e0604080a0209060a060206150105041827030c0f06060b0c06090601060e0d060f020f0c0a0b150a03060e0a0b0711060f06010207380405130605 68
    0x1980e5529081e01e0007800300350201c00b151556640000d00c06450340350003500d2a401903105200d800100a05241e11503914044244002e03640080e0007548505c10010303c1082e01c0417039005903007511031034000f800c211a00e02c58000101c0b00c0d64002c060000b4240584202a6031400003140c00d1200c0010014005188004110041422030350b89a50ba24040c580c0014482d07624242c00d10310b41d000801c2c0309a135401120130445a0381c0c060103a40c1c0101b8842c107000495041000001e00c40040b2010001c18150703a400010095041c503034103840c0b00041b5003024654407228900c2650f512003c0710000c07030f41c0b55200400070700c00402e02c400c03c4800240203001801009d045960700c40140003d00100003007031041003421004501500d00706806464a41c07115011420300c030ba216402c010004103880c04404e1548113018041e603000800340c3c00c880c0394075840b03201e1142d854040c0030a008000d00401442c00c1d56401c1054100303e0000520880d18204d41002400b48c4060480040c2c0c2c84d00d1041e16130101b0703540c1580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172238552 1250 172237302 172237313
    0x11e020c031903060905040605070e030c090106050a0306030210080402100e09010b07030c050a030e0a080303040b040305070203070b030103150501061d040513020a090c0f050f030a09080c031b01110412 88
    0x30720010443c20302040f016114282d0000700d810850b0b06441c1540c4400922003d5500a1415103003010150040c107001080a40440c903180b00603c0f0300b1081000c00200305403214400d500c013001440d4000c000007400303c50003000030b0540b94181c85c264401e0003040c4402d108076000f032400040f501006450070740c0d80da2034810b0f00c000395001803806400f44038441c0760010000d441031010f800d14500c82c1c1c403610308007540782c014000f1440060704402d100e039004000380710128559910b2ba550095051800d50b6546500d840803a042c500140c3c4020030001c0c000c0004410450b140481c601c541802a03010011684d88000442d45c1a6450080daa24000c2c648185000d601b4182c001f164462120114407821807496030100e0580240795102d2185076903540300d80c48445030300001c40c01c03590f00d01d894418100090070819041c544406054401590303a5400c0d100100020301003a80d4250404109a984030503c1c2c0c807400c8088040785c0502800d41d440c160710018210010002c1da4160303034404040781c81d801540c1c0c0c5c82 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172239802 1250 172238552 172238587
    0x60106050702040e010c1e0203040f050f060f18090f07080f04060e031b060105040b090a0b01020a14100e0d09062109080a080601030b0904060f110c011e020c03 70
    0x41e43c00540710424000d040c0c00902600080101c00c0da00c61200d160354008036031181d05080d01c044d0854104000c1000185114802c80c0c050b160308031203242a034860140042c00500c66103500420404000c10b44405040f036104609400321800d41d420a80e03503a91201c05407020070105c8000740070600740400f05032070843c00c110f13403980103105038400108006400080c034619044000d204d4180c02180e2070200080f1024030000f40148025101880103800103030001d0800d00c4000c0003046056640c2c8000d40890f8130800916220f20380024940c0c008814410f207003a00e83c62210300e40790b502c0341081e08038401060001581018028950740c3c0c00720550804404407002d50cc003040038010841d02d426140d40e4695684261112913110345c6106a595445410290459200404a5051600d01074481c0380135200d42a1003584254050b00000d00203215110450041211691179900500c002c50a1a2501c3e03055200200381c080b5081e032f4080303034264400e4040c10703803080c12410b403821b4202b404803400f8014140d61 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172241052 1250 172239802 172239817
    0x1a0c0a0305190e0a0c0906060503190f1503110a082a0315190b0a031205071a07140f041202031009060f0c170f220c05010e09040506010605 61
    0x80d18641c40811880340300fa51802000c1c00100e0304406800c408000c192072070078009003040b003400d003c01d503c1c090340034040b408002d20b0080ca240350425031503003121081d400301c601038482220070807865940d100104142200e50104031070041100c2144440751400c145588116580803008145041000d1207070b80030704d851080c101100c00f0414606080a54051202c1e01001402070400e15007480c258030080244a50190300d0368682e441c4c0702044819031179540e0480c0681340c100100003092041d040c4e0807034651054510140040221540d504c0c00462800c0b060303030103625a5660f480c6c070034003016500241c3d0300c20f5144546044078100300400060000081c0911403038002000e4542540c921102c10082d02c0c0340031003c070340180e035540200004d982c075882207003c0c8104500c1c1600148141d030103001071907407000c0c003c0c071445142c1c68002410300501c80c54068a07041004ea004800076854902018407650070700485001c5000290041c245041900c80940725540140c000d0925034a4182c0a5500750b0003030b00e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172242302 1250 172241052 172241071
    0x50705040e01021b0a020916050406031e090c08070609050603010e040c03020d030306090c0507030c11040b030d0e1507020901031e0206070f120815040b04060806070504031a0c0a0305 80
    0x45040c1010569180c0d0f559445004e00c00380c4400c0380544108681d0790f000030041e14032102c52680c0110015402010307038050759001d083c0001e4000100c0850449150034100b40880113042450010402c001c1a0140d030807a50a10f00f150401900d48a080da40088940070f550341103030b418030041000c00d203640759894016000d42403408001d0386940100701d81c0610700c40d0690200361104003c005001e0184140e0100020717a1030224101031181d40c0081080016141c00340c540c0341642e03805109590740354000002118001c2c101e854900450764080c0c001301050b035906104420400000010400c5503040700d004940c0105100c44c1030382160380300040040001860030828020610b106c0060719050020a419401240b0100da1500300e850300340000103203585c448042040381e100344800200c9004490003100b070b0440b80803840d4111000410010055030340001014880d0400744149140c1141c01081601d0050310760000c5c14000000c240045801600c0803418013008111040800d44030380d02c40381d04130b010203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172243552 1250 172242302 172242307
    0xd06080735030703110c0105070f1b08031303030e0a05100f0e061b06090a0b0a0b03160b030609150105070201030207060902030703080c010c03150b0c0a05011811010309050705040e0102 81
    0x55107807480d5800c0302104801080c00201d09842e0440c0410040200c02001d29005182c804155121503440e98040002842e035420710012828240c1c0016041c40542a6401104d8550010b003921000440240c8010707404540d504011031100d04200c4041021344070003802d40c10200784c0d080000c813816491402008100030007500104815540d110040200361340c02d61062800e0014020994200200902000c21a80c040012080007840e50781c5000c0d070010740b11000040d1801d0075030210b41041601039440c0c225408840c0c1c003042014900010714041e0b0000e5401c5801540c0340091038100340500302c0321a0218806100c030070010b62180d0000c144580c4a5800411403803030740c5c1d0200c3d00c0d140d16a0000c9600b14804611908110024030a00b204241d80d0300d01444003078140b1581400c12003880c0698120f011000841c442c035402c0421881031140e034090000c0100c1c1c943d801842c5081114500d0840e821007c1c12000d1005610a0040b66803a0b50443c1c05815420304c0c4c60f0800c0010a4400d41c2055255000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172244802 1250 172243552 172243649
    0xf0b010c2a0e0109060f140a17010608010504050d0f02030f0304060213120f03180f03061a06130807090507052d07080409110f07060903021608030d060807 68
    0x140b00d054004c120380030010070002d080441c4406070300c8180c0c2141350540d00441182c40e455880300916411034103078003c09010003403c40011405003403142c20950b4550300f007000f0b11080120000b041d00c4034695559400700e06450860040f80c0341c0c45a0301c04141040400c1c13001c00c021894540c010050b1140180300054560b1b6140300110060103106401c0d509890a20404030606d80c001400800000075581000c501c1c50520700800315501b00c901024100c07555890800315800c0d440354100541a100506040e100c04c80c1ca079403d0080119030190302d14500803d40c0020b10710b445409080e015032480d40b5a98200322044107480c501d040180428112203c94031344251904a00800415406000702c1020340d0b00c070b0414000703005540034115517020000e810410f009070f42d00c201050b5400703940d202c0004501c1c41c4030750900328908a02c2d10503650002403d1100040e05840000c0240030310440314000380b03c0640c0d1181c10a84408451284007802ca024400700110b1884030885c0c61044240e140c0c5080c55480c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172246052 1250 172244802 172244819
    0xa0b030a0c08030a0e01050406021018080c03070606140f0405130b0108030405190e06150903030a080603010c09080d050703030906020408031b06010614030a140a0f0b010c2a 76
    0x4990b00c400e01d079030000200102041e6210307813240c07442d100a080851809203020070080d0345111001100f1009540c0d4010314801e03440019020400e240c0207210380780c50b29205da00880d02d070f900084085940d146410000607000403680044188034200910b8a000440b00e0000c2c400600703402001c40c0006c201d422520360014085025560281603103000440e2038500708014007514580c80704051114000000080042c1165501382960041003641d072191100503001c10844207006112036180c0c107020200b4000c405a80c000d41d03040c4981c000324024001213101e090142c07603030b4900c2d000782e801941140914084442c003680050400c43d129180c0003509080944440e4201d0b040358001d0909034200040b10480030a00702031000181200300c01078202c1e545810005481810301c56048504201c0210010340000600d41c0907987c051428040840d8030325112280b0303001800441c4c5401d4915140451005035944102c092500c1e65030700000613000c800811280b1403080005100219500c07654140c0407034040b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172247302 1250 172246052 172246073
    0x5010e0a080c01060503061003060209120a0302150f062d06042c10090f0e030703080709080c01080105040504050f07030b09010501090b01050306010c05010f06030b15010302030f0a0b030a 82
    0x1401075400039103030b205591281e03007035a0090b44098070130380c44082400151640700f403d1200320b9900000c01a55001410003158080c0880c0c13110700ca40d409006110000d040c1c0101d51994402c03109640c000c815590350b0f01900500405035999030308000480014481080010803168000d0300040a00d2400060349000404940c07040d04800f00c0c112408043c507030485a42048100a0a60015582140d20704880880d5849400748542c018503500d40000706e503107001075809424859460402e8942d01c40310ba0a0152040f1001d85a1f1000184641070004042301c0226401402e14416511802140d00e880100800390202800c10381c0e06018014880600d100c08201000041d445010082003514141135140d0855034142c1c0106511400d0004035401c0b6a4040d04032540180c090803d4000c0891a040c07450040c00f955160715040b900e03000003c410320555014071803080c5203180c80c2c56181b0f41040011030580c00705403001804406004042221202103403c01611108080c0440340c0b4000c842d2034582202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172248552 1250 172247302 172247323
    0x150909191104180f110a0b042d0503030904050a020405030f0703120201230405120c0c0406050409170f0705030a080a0c09060e13020d0c020706020d0314040b0405010e 73
    0x10196407044080500301409041c0d030034002c0700000c040c0200261034001100041c081c0c002e0041c5e00c000785020840e44d0f64020700e0090b01000800c1c0f17407138a444040781928010502a007207820001c031220540c40034002c008103016514042c002d03609100d050401c2c00044c0038081c003000c103115002d00010540d520104050080203010390010701d850351641c185443c461201440c550111390410050703000c0210001018985003044141c0700301569110308001381401c0703440ac441c0980300000201c41040f181c000805411615044a0401c801690b400c1040100c5680400040560f07000441d05800300c468007000e010a1458032062528200f010703504c06045500c07804152010844400c140620300100d84101426640340b400c040140900323010010303000c2903000300000e200301c40300d84003070501d92023030f4066410380c840003a0140500500d0307100194440b032050040030014842d803245811054803d0107180c0c41c1c1e80c200700030000140c9a81d15960041c4c3d038010300030b503455900c03000c0107803a241c0c0400180c00d40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172249802 1250 172248552 172248563
    0xd0f0b1203070209010b0c060103170c010903030b0f1e060705071503050f09031204120c0506012408150409031b06050a051b09060a020f03040303050319020315090919 73
    0x181ca915104202c80c1000682081e0b50440060240b4247c2441c00a401819070342c10a01d04803e60036405c16007282880790820b038418035408d00c00071000305a01a0800d5103c0c0101b02c440c0d07084c0301003903c03d003c882658030000c2e07101c6400360f084076203060406000614441d4011425140182d4642d00d00d05080e0f10141030100c00241e80c0c80410043e000244980703a00500c0d03c030041e500c1c0182c11316214191300742c040c00181ca1824560a0030f6003090040c4049400700f81d00100b80c40b465070b510031501040c90f512410980203100240300340fa100ea440395882c02c3c495035403a4440180c1030a50024007008020013070086041c000f0b014035644503110440000500c40b445842d010482d8036040c60a2001c1c3c82001d07012040c003042412814014203400c00565480c918240ca4030303070b15000380c1c90007246450010941f182c040d0000080101c1810341c000300452090030030614107407090b103e907031808003203100413203003910441c401004001252410b0400c0ea500300c14840202c0c4c0d80e44d01c0300342c5185048c00e0b03060000c42e40e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172251052 1250 172249802 172249807
    0x105010f090e0603070512033006010e040e07080f010506040203090607141315020d0e0604090203041106031609060c030f0503070e0301051503060919171e03041b0302060d0f0b1203 79
    0x2710240300c0c0c0300100600500191440040c8680540040007040941150b045c840622100b51494032940c1c071141c2404040421140300680e25880e1035215403030b940226101c7c3d400c04000600c5810107000b01ca02455141c0010000740e69030310001c880d0b240d032001c0c403240b44a00800c01d9400340c0c040d107940040903101041c818200070302c1181c0040d00d406401c51080007030000501d4a0801d6680300010303681120340e42400541d41c0d0341c0718035083d510129180c00e040d42c0b001c404010f110041081c101c4030580c251711500d861508035100e13001918284071810b40280040d101e54003800c040381c440c03805150060700904050f009141240f000a0954504441080d04024150a5900d80b840d00300003040e000005540030f0458442c8403004000c0014007114003a01c2c2200f48108400c0602614003103c0302003118841c8284100c50100b00c2c4001c0390f005070b5090b03c2a102e03041040040b0482505000c08884d40100458a40708911300d5110142180c8280e0081459540c51484070b0381d240d461032888400445c0000c0c1d603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172252302 1250 172251052 172251067
    0x9090c0703120914190308010512011506020a03120509100b0409020306161d1003021b0a0b01030b070302120f0601020c03030c01020d060b0408070303030207020d1b06080105010f090e060307051203 86
    0x80c6844400d807440543d1900e05d182001c080f070740000ba11419100142d5000340869000319100340074100780d942c1c10404c03072106030000410660104440e400030b84642d4803c0c1500880b1a042070664500355203200142e0000640040410144d42c0b000130b613404080d001051a40030b03034001a0410ba0700711070ba045212914403401e149507921854010520410f03140c0101700064040102c5c0000c0f410f645507401381a40002c40d60005030541504485e402030b01c00c21501801841e282c040c102400030300c811128810a00045401c690190007950065150402c07100703003542c1d0f40021103100080143c0304a0550041c0c0102e03101c5034070140014542e50b0341034400981d4946014401c42c040390b0b003c1d4000800118240400c0c81090390104c0c450044a80610300035846420a0000a0351006c450030000c212107801c184d0380d4500c20b60162060221442c035110400f890381c2c0c0c0d00c01565050801e100b2000011040c01e0103102c003a1003858810780000c40074040703030507054403a0085801040c2a902840043d4004180c07031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172253552 1250 172252302 172252343
    0x40905010213031502070b0103080d061701060305010f0204080318270402100f20190311060702010606210e0d02030304200d06050703090213061a09090c07031209 71
    0xd802c4090b100404610f4007400b47c0311074860f0318040c000207000c0d280014046190800c44c0d0401c0780038007046070390040d4180400305006d0007055103200c111071550816402581b09280391003560100c0700004055850302c0781e0015081001803c804071203901608140b4841500d400058402c41c80e0b0550a144120605081c01003110b92240c4040c403400b00107581d0790740750381103520a00d00c40b0701c0b0b88480c40144030207040712412824032b40780100801e081300b4040c4070b100c00e06d40e000000700001d0400b1020b903040b90b166400100d00340d411500030613020031b02d586400d040454040f010702e0308000070460002000759500301034609005489401400581c4040184401e01a05091451a03140710a0000b141384400c034011511840c1801c13400f6000c030b903480c000108600d019800c0b40c05030644c010030203a20b01448811450080c07506020b5911a803400d0303502c4400c0084518211a00030600804450580d520039507a0b42d00c59020300412030401c0a040104401141c060180a101c544a140700840c0061283c404c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172254802 1250 172253552 172253573
    0x706050c03060109061d1e1314061002070305030315090901020405100e0d0b040506090c0603150904030c2f03010203060a1a0f040f0501030b060705070e040204090501021303 76
    0x98503480008105001c42603801444860403030300c5504103801310034004000070040010201100da003102282c440b6582c81c0c4000268410094000c6a111166481d04945601290686201038070601e00382c4000c90b1251518000544402c18280304946580d0344958580e42160015205444c0f01c0c640d400c4003004034501904820390100000008601b00f6103048005109000c101c9041800d22035050414003040c3c540c0e1000302881303900280416a20706040c0b5100e0b40d84c203030854140d40180a1428448400e10300781c01200d000c0c11200000040c00079510303007007221a40002e4001c605101d074100c034203000650020807018034052001407030001c80d842d0785030403000ca1003e400164400c1e48104100405980c40c40300d0303c410303500341c0d02e141b07168140207040c80c40043c8200303218031442c81804900000c0c003500101b105c03c10350b0401e80c0d0500841c81e006003402030900440d80010010380084005104466034181243d611500040003c1001185034071068220784c08a01480c0d24840c0000707042c002d0002c480310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172256052 1250 172254802 172254811
    0x60914010524121003060903020f1009020f121c02030d050a090816080903030705160b0c060703020a2309101b0602070807050312010f1e050f1305070302070605 70
    0x30942c1580001c580e1101640b28190b8100301c00030600d800700d200f80c4452001880a1684070710108002c030b4603420041d5a42004c41d1510145100f0504021420008d81c064442056805090840c0350b88400f010012000ea070401c0700e03840e0b4030801c14213a680303002d8101a40140091600516541c058114a0b40269580201841812800e0410100010310240104c0b075480d98460204051450340340b82c81200c43c4961b10005030305102c04699202407010202c3e46c2941c0381d100e42048120b903907454240600d0f03030007521070100303a81c1c00120004103a20300035001850400d0013480c0ca00c14151984e052001400c030352601c1030401420104030740086040c600e01708040001d8505200000a52591080501e034140420040080381c02103100010002a0710913604440e07841030540703895800c481c0c00302001c00403d00c9540c1e401ca145d0b00c030025410054034910f088020005070b03001c108038240401c0c0550080c0020441d0b4100e10195124070b10f411301c80c8145030240703a0a580260f070740c021500307045054440107807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172257302 1250 172256052 172256089
    0xf020105101809050109050105010f0504140f13110a06050d140103080f0903030717120703050c0406110c040c11010f02090306070e120109030801150e030a1103010609140105 76
    0x140070710003507102c115a0b08140800460119280c1158a0818050268041c00414035800c0500105d02a0503010b942019644142e40c04c00105440014a030030351300c0241d81003035070008803001003210400c10141e000e0805004e944940c100c000c00c0c50100310070700c0c010790000e80004c00200701c25400c0c4000707001d0090303084504014501e0550542d2682549803280d40c42d17200b135017000040d00140c01c0d01d090081e034000c1e03078004c1c1c40505d4101c8224080710141e40440207c402400124000440d00d501900c18103016101c0746442500b40345c14610199020b40c00318940f410031307120f03031a175801c101d41e00c90081211443c510f90b0b80c014060851036095082d2a41180303111141d40c010710000303886450018402d40d2150042c07030209041c628190100d41b5066040f90300418035401c202e260014580c21113180b5040f103400301440707035562088043c02c86a51005580003903143c2c010102003c00f080601c845044007500007400042e01d280d0700d01e43c25041301d414070131b0140080c0c1c1820040003e86803010206081300c0c0c400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172258552 1250 172257302 172257331
    0x5130201021015090203010b040303020c031b09130204090f0209060d150510080a0c0807060908030315150a090f0503030c061308190c0b06060a02030409020c0316030f020105 76
    0x1540081d445600320000c04502d00d036240103145100c12410211001000d10f40c1c821076a95850f040c1d2a80350350700901068004d40b0510030701c14118200050710400e1510b50414071800d0b40880d00c00c1002d0320001a001290314104010740340c0140e521071085550081c45421480c540162038410300c54661b500800140c403070031840c0c400c00081021420344000121202d0000a440c2e40d6101c0c2e138003941f2009402c41c916500c1407212036410407110b84444030545051030200c40d4030640e6001c040350020418000c061094200340040742c101c0008000340c50b0f10b164000c1000c136543c60300395030a003c0c86d08580d551000041d0030312010070112241c0032580015280960103185001c1c1d00000669852902800030001022004461410300c00c0d403800f034400b0010f0607211208112040c40000300aa007403924280c508000260120300580342500c00c440280095401460900703252085043c000e40104009824030f01042011b40d282c4440e600c5815009072003520b50740301040040344005d00310340d4010008000544403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172259802 1250 172258552 172258591
    0x10030b010c11040905060403020a0c0b0f1801020a02040f060e0906040c050111190320071802090d050f01020c15060a1a0c070e01150215060103091703130605 69
    0x30803074030600e508040c22004140020300424001c2c005424043c20070b014072020b1004144d401b254801c070150040002420964480c54506101e101c2c40322800821f001c100802c42d150034580e006e2152507041401030b2208020301d40c0200301622606520100110703074508050015114114480f0381004004005100300e00d4182d03a0007500c0340303107809a1414001381d090032a10b10101000307610220344074015800c640701d0143c540034000050760700c20f8504d244d200c0921b510f07035100e002480340101c0d40742c2410b2000b06c0e5100781e9075900951280d04615080f10302c50b420310000c11000c0240000c042241c1000587c0c6006209109080582240360300c030f01d40d0860f01c14401e45545800302901503802400d03084800503012070f051001441360000b083d4840c041c0a400040d90250280e0050480e4254a0341d001a02000b60080b1784231404154410b04444200c000b1900b1544298080e8000510803804805001460404580b075074000f1156200d019842060010800c040390240903044a02140030300c000803039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172261052 1250 172259802 172259807
    0x10906030b0d06020c07180b01030c050a0c030503071103040305070306060509010b120a0902031903120903080f04020604050a0b0a0e0a08100504050c1203030103050f03120411030703080f0910030b01 87
    0xa0302c0240c441c075008100c0c0d5941c00d134140b08502c000c0c8035843c0300002010b00218443c002c1c3c40288003440c0070a28180f201d10015005004840081c0c010f956000710082440d0342c1544d00f0f4001402d88003c00100500315174042900301700400c082c40c0500c0003803d01515615080301a20101c3e044079018400810040110031885003c0da0002c1c0034080d00c1700340f960b894280c0da500802c10418040d41c180314250007400310516503250301e6001170281e910100481032500c004400c0d20b4060a0040000724800d00103151803415944141e000340c0b0050a030303880c080d9180001207400710550040f0038071383c80020f9200340d03070b0b90040c40c10082c0c40340950707011500030310b040301303050b2140b03001c0003080200c41e100c400150400c80b00f0b00842d501e4a42c02001c0c45080040d01710720541d25082404100d070039125001c0380c850800e40001c2a58402401c168007071a940d655075842d110f140c005102d003160103100d588800300018007200301a104000700e05240c1c0f6102d441200800c10840d1450302c0e00b0043c18a010410300b203990703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172262302 1250 172261052 172261069
    0x7031e0515150a150f081501180806071d01090b04030b04020a0902030903090f060c0601060c060f06060507110103110a140f0703030504020901090509030306040504061e0209010906030b 81
    0x10041c40039a900703995101c503008015114510250b40500040408103d11003010840351500c0350795600d5504941e05c81c1d40a4903100d1050340d00d0000c07610246414811782d071190708141090401e09050300c0b1000c9d40c2d903441500c0c0482c180d070310901080440c0c4035541c07803407003040c800e110000007440d11180d19403501a004105203c0c502001d04040305000002382591924400d20000785000c0c0021543e9103442c0401c281c42e500940c200e0fa20807111025055801e10b011426601c0300b84600e0050141d591030600190360b084404402181c1070b6444030704030b4810380b246100b0800104200d0701c41b1030b9102c0c043d151000261184141c5941803516100c1c004030000120000d4801d96282c90400202407074511003003610a000321101e03d6611000040d50307204241d4160403c900407842516100e0880e41ca400c40138050359011a12070f80c6541c01400010541e28042d008103400c0342c002e00340000c05c00c0c40025223086002d4801c40f400101600010000e00e296400300c000c000801d002d180c200080401500001c01e442d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172263552 1250 172262302 172262323
    0x2150103060e01091202030406020d080f0601030203130606060305012402060f0601090503061512190f110306040b0702060106050901020a0f060608030a030608150601050306011206051207031e05 85
    0x503542c480e8440c502d004254805a40140c103e0304080300c0040e00c5000035520fa05c030780101401406884001007003175015810769402942d5030003030920156145001103000307410082c40040a10042868800400e1040c410741c4064007841d0b50125a66041121200802442d512044d20660b03030081207030202940810f4164001941705119641500c030f000040347c4030851608019418010b1500307210110280030001e082c01d40c07050b00c104200c0c0000319a1540c44030490052a450360a00c00d4010300003580000b040651140700f404035407820411000464075001c0222401c0310030700c0c142002d0007406c0382c040000c64010f05481c0381480c0340c4680500000e4484c0d00b20080181143e4504c0310b401c0820003a078000a0141040c207045940b00d00343d50000501070041442511000c1c018241c81120403a504656a4400d03441a1160351454562600448136400c1d44e4040d03500f116510b45010034550b464180520004c110386005060030350440c2002030304501a9894180840041c4220300005a400700d0041c014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172264802 1250 172263552 172263563
    0xd030f0e03030408120405030d02010e21160303050f0907080c09040807061503110d0c06050c0a060c0507030908060f010302061c0f0207050606010903080306060702030124031202150103 81
    0x202031803500440e145001d180c0202005002d40c5c181c80418105210140040728011011600e5804000300c041c7d00300c800702405400c0d660812040d0f0444c030308c0600400d01d0111181a4000d00d00000c0c014a217824000480301140001c2d03c03070b820701c00049101d520458100c0b944a002c2c05c981e6141c2412160b543c000c020505005181c881e00240038800c83c0e0303040e1907070150003907000e01c540c841c0d03400c4003e2100f21a01044074091420008180c503810404010200b00794481c01c410040b9003081000c0e6003580114440b9072182c8900300200d000100c0718000d483d00e0301e190351116919000c0a29010b1300c4044540c00c4060150f000c0c0041260380045030170210f04584c2c06076541996035418030015190b04849854561080c3d003480301d0a251400785900411615025005807a6151141c0c2c004483e215518840035006220602c040f4015140400080c07208620003000002c040c40070503121078481204a44ca41200410140304200340004401c080d200494544007805681d4a000103008910300180006040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172266052 1250 172264802 172264817
    0x50f010909080f03130311011407030e010e010e07140f030c01030902030f010e06010603061d01090c02010b13020403020306060d0b07050313140a03030c0f021f061809030e0d030f 78
    0x50000550849540c2403c82c0c90b215a645407112031100858170a003401c400080c1d942d1f141d0b502204040c4115031080412420a62490711141c0c402c8000e803004c2555910907540c1e900203d00811000d100310f0007610710000c0907007281ca1401200da0780d40c400096616000c0d0024245a10040d5000715024005250908000440018a001080c50321101d408501311562038100704070314105c030005206040340d13071581d1b09011054071209503070070a8003148940301e008204000140090042c3d034000010804851000140744062003000904041e91050074115a0764000350910a40c1020b03c207090f48400f0955540c2c1c6c54041c940d0f1015082c0c000203048004024010000c10030360184c0600400b46103402665070b2198150040240d92034010a0f0b0044000c41c0c80c1100742183e82d07026070094001021250060806240903480d40214001402101e0041c9036440101080c240303c40303036485141180d0203030005031500680ca009032841c2580c05000d840f82c5408041c80c80000c0d405607000500c0c0407140341061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172267302 1250 172266052 172266071
    0x5251706040209090408160c030807020906040c0816120c0917070f060c0501060909050303060405070e033301080d110307080304140703060f090b0c0702310c0c02010f03050f0109 78
    0xc003a1021450007c14848c07484c0d80000c24040103c01505080d402140c0c0c24005844800c10481110000390700c0d100450258000212900381c00c202420307030180c00c3c1c107060302d2605880703003160115503007003407414082041c0407420b101d622411444070351003451584c02000c00504003404000794403d10722600042200581d003100c100030f429009070000f020400c0c018022602146046a16078000701c581c54001c80c075010004200e10310070244081030450140245c14581d0404001d0808105d100c541c0b80c4003210309044040419801650550092440c10043d0003000300544004040c04005859840f61798001d1011002003042d41c41201e070401e501031801c0040e840d03010045c50424085900c054002d07440e2203c1810f01507060b07040181628442d5180c49580e65880b20260480d020300c50001e500a0844801500101e040078100e1081c1625041080c501041c0c900c03001050702c050406480002e01140300e10011541c0051048000061504040c449403608000e22005440d05102d40803209884c0c11084 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172268552 1250 172267302 172267327
    0x1b0306091f020f03040b06011106071e0207050d030f0f140d02071b180c08010815131202031e090d02010e06070c030809090106080709030605251706040209090408 71
    0x10343d1600203606045441e482d1504040c18580c10448181d40030518510007986201e01c01308042d44580c090740c450628400d50309030320752000b2040c000b040c020740c4034946000c20155902c860b2844401e110360346195003202002401492084104a100c06004c446000c18080451038815100c4608541c0001030300d441d0503007440c0705900c14001c001c2840d050203880200300c02c6003404000d20b0081c580103080c450728035244011100588248660740c6682c10440c03010481c80d103041034064100e81041002421b10019840b114680310412240c82c000d030b8000503111b000f84198201e01c0c0c1d482e2020020680c1051006004a040302d00304400007410002c800200001a5a40200b52080950400004010141c892a14034803503400764540500c55a01c0c0320000442c00e00c60320b40303984280080d0351038034140c503e15a1121b01602003d41910690b00d01d4000e0749805416100426840a0540d0384911a0090b44140c19500c084d0283c903517401280100f160a5250720745d1f01038035030415030007040141e0b208840081c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172269802 1250 172268552 172268557
    0x7030b1b0a0c0b27010f061a090409050a0c08031305040b0d14030417070e1b0d0c090b0d0f05010512150603010906020c0607080a02031303050a020a080c1b0306091f02 73
    0x1075807900040001c1d00d10b0310004c1540007000c1490025802c20809403101005800f01c0d82601c802d44d0000c0c810080b00c4400d040c203130405425540b080d011510008895a980910a00c1a42142c241940082101c1071003402031820940104001e54003005410175400c04074043c1c4002203009040031420200c0e1440c0110f0800845000300307600c2c140301002c052020303210394450200384158040c1040100120300c5150110741c3c42a40c42d103016000030b1030140d40c0700198000d0b003512050003080c01259070000030000d5000005154096440000040805102c0e4a0300102d5506801182c010740c403a1100034925040022140c200c0086844d52108582c1e481e80000c0c05080d020400428442c0041154840c0520000d0f0f1140607040079180d41c4015a01d480d0000100e000469043c00b1206050054001080c0501e00502244110b0710564000c02042c0e10f940100760b001c00b004180304d9002c0b141c00c11841403803012503c0c0003682100130309094244240202d0ba185110707288000e01840c1c10362040040d6109a04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172271052 1250 172269802 172269841
    0x30903020717030a18052206090f0603050d0f050307030b04180b01061106130803130218090c010302090609100c0b0906160203070b010b03071107030b1b0a0c0b 70
    0x128808010b42c01110607469402c2500800007062071200140c0c2d811807210082000d85402030607203400840b42001c141301800b01c90840145080d42e03180d0120b19618103009022082e01160070100e002031a500d800b0789484001c031810020080c40030f2103c0c85803980b1904a0340c0003081441c01080302c8140500040040c06120140816640c03074100300d00130041603448141c101c400f5901c0781d141d00308002e1222619404100c4a0f25a03a500d2140d41c0000180c5c24409181c20040324624445c055545a002c0740040800c1200759507141001000c0000540d000c201d041180003017840d096040c0b111110206400d8001c0b614824401c6180001060000d88600300050f020f80c1c001241101c0da040181d8401e40320b8006503050440c5d0300411080c00380c00382c0000200d03031615500510890040e840c110990f40f560304042e0400c010404041c02000410000f0085040a507004040d10007103400c0c01107024480c620206144900103509020f0008110703040f1b0f04021409401c44190416559140204000d0b041c0492 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172272302 1250 172271052 172271069
    0x20120c131509020409090308090d0207060c0602090d03090f050f09060402070611030c0904150b120a0204120c080c0d15020901140c010c0908030414120c030304030f031b0c060309030207 81
    0x18001550845c41d00b003404c0c09030094445004949403220450f840b509502c0510026030300188080150f18491492071041a0003180300500700302035080090240c20900f4030a40016030798400602200b10114203090040c60111503100041404030042000c400c0000c001c0e030b00c5964003040c00410b021282d041080d1400001c0c1d200e42e41d0f032610700325200d0740780c00c02c802c1580510328016a00c03c0724201c03504020190f03012a441c103420103030072800052901c440200f54810b40358080c40700040c5002024030b030300407240c42209a008240d06110405140501c110401031003000520490000718454800e040ca008c02d0000000d03a90b4500c05006032048454044255500c0303c000643c4c480d410380642c0508c90703001007a922580010b54a1503480e54a004038014001869081c0c8d848500c1c5103800c181d64505011100281c80c0f4542613000001e0454025074000d07500b1030403004840c0205139200c040d401581600003a6070303150784100d444040c10360700107000d000f09040e5160103030f030245070003044107000078480740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172273552 1250 172272302 172272307
    0x12150f2e12050105010905010e040f06080d03020c16140105031f0e01090506030109020625060e01050106090f06050301231005041a07020d02011b20120c13150902 71
    0xd0000600100c0340011000703140e0328102c0003107459072056980904a034816914000d034900d8031070070407005002c54054013000b50f665000000f030b01c0005102602c51408681c0703006894040c410b0a060403c450050f007580e410b01690824000b025041840347c0d0400000e18215031280c2e00c045aa50241158050030480d00010f02d2000904903115043c05045e24404a018400c40c3c5400e000d040c02d840003502c000713510007000d01c104101c40c403440d81d04504a40c03584610038000c10903500e034101103803031190546180d6516040103001e40d580214001c8002c02070703011f81050003031a2210040c064041030040a40700307080c200340015a18211400d8407002d01c0010840220792071114000b42040c1c0c410312030350704e04007102c85810052103e26026507492a8002e031603c01c00c09115401143c1a240180008046501003110040450800350600d107862448546000460f0410f42c1004400c14005140c01c085610001e400400d585035001500c21914880901240d02030b00030100c410000b0700354229500e840c0c4003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172274802 1250 172273552 172273639
    0x12061e0e010b041815020f071406060103270305030a02210105090a0905030301210b01140906041e09080c010e150c07020102072c01030812150f 63
    0x40d44002a50ba4044504004601030031051003058240204050700a13984092060700703002e4550020000400428012440d01031180c0d560044108451000c843e9540900104400d41d41c1503c510402c86201301d40048a035000046a1680d41c0c400c808020104080130000c11004680b980660740031000801d0290030144504e904443c199809220329071090403e05d000c00e1903400148210480c00ea085005146186c3c03c00500c280303100394880440791080507601701d0f000403c00195800d80039058060010300708442c20010031107002405040d00c2d100b0b602d000e41910201440b45044108404c4500c030120b00111103040034981400341e54204001e035400c1c004440bc1458004c80c4204c1500582c040c0c3c2c0006c1c1c2c40e01510400c8900484c54001e02507406540d050010a00000c0b920001d145242c0500e00a150341c01403591046500382d1080301c96400c0415200c1044c08030b0b05900e0790040d80841500f150540c09400202003d2040890600400c500800300500c400c00014040f9031880412000b11817000303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172276052 1250 172274802 172274831
    0x302120f13060302190c0512030c1809070507060507140406020f06090d080408030a090204090b010503060f07021b0a0b0a050301031a04030f030b031509010c020f010612061e 76
    0x1c81200d401440c0020810398064420f8400142c1043c01050a000640c0c200b0385552000041c00e45242c81921070760284405080000c3d80320b000c00d654120303100d4092466000320800401207051140c000a8100848035506c602520f44268000c2c01c00304064880d07240984042c08030300959802d2090029002c42c0503030b0005466001000d88108a0750340e40d039118400c0d5201d80750034508500013802d00b40410081030401c0003461300b0800741407001460000550004046403170a00c81242d030304545100400c494501800910391110440c0122901403401d180b0007511540d041c12a1400c00c4201c007540a0300c0d86501101802030440002001d40c0c0380464140034080c0d0704240b00c00c949404c1c1109540c5000110035024502480d03140d21a0602205441401d40141135804221071f014490100802e1030080c02c41105405910000d00005001002c10802410001d20a01c07001041c0c0c14014100604528200e22007001a00000001036800001c201c04280b008040368115a42c2d040441440340c805 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172277302 1250 172276052 172276057
    0x20d0e0a06061509080a110109210b0a0b0f10120212060a120302030a0503150616110d030212131707091a0603070e190f030605070c1203090302120f 65
    0x20441a0410601108501d0440b2828102c2c095100c11743c210b4031001c800202d040c07041f00d17001001410300319012626842c0c00c811040d4440c403690b8040da0841e100364140200c162080c0d800c100740301010f1003026580c1c07022074511184003c880b80a1a41542040e000a12800c071260500b080e0401c295520024004202c1c0610016102584a62854400005c088202c00c948144c0c1075030580155007405001a42912141c00090103409151403000302207040740d65000041070040c59981c83d100d40d5a2150802109078404a0991409500d420144d0b10100303800003620b9541c2c640007640e030740c1c0d1240f890105000b904180c0e0b0009450360602c2109143c01100481c0407010f40340e11002c208400100302403004e00410741068201d820443c01c10206aa9521030b125100b407621380507241010703503480c007a03d94200310783c2944980e10405240e5020310811005001b91500078100d8a098860f080c1c0075142c207109480341c90485018184c1c1c50620f401054000c1c44290900c1e00110350071622501040c03d52030b070b503a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172278552 1250 172277302 172277309
    0xe01170c0d0207050114090a1a070e060f03090f0d02100207020604050d2a030b01140a0b0c03040302010e04090809120f060115020c01080f01060324060519050319020d0e0a0606 77
    0x210028000502c0087c40000e1019103541c1201d11400702000d011400f45004034054424410403111026031041900d68000401100e400245090b44c3c0b403610149060614001003504542d42d0454040c0c1c2002960008a690410405501c01a52842c80d440002c46038800c07540003642112054205101b408a101403008444c81d80b0fa039801d403056580008241d40341920f000003030151f4002001440b11340c261103122100c120010b041707030304126200c150801c6a5040306410080b1540009028011540c2c0001c0b10b8500f400709540500c50300d152595410040c7c0170b207580d800e0040c0800001e14000e024204000341e0308005a00954103030f561141c0103102c206503481895805807041c0d03186400307554814011144551002c81d110142a420250102c010302a1641d42d13040c2c00401c2080200364060107203a04000b480540c403100c0da00c00c4140f4032034294402140c41c1c43c003031003000c1c01040110302404040c0390000780f681c03000503a00c0c0c00294500b4010020400700c05414494001e6060401c403255025070b058 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172279802 1250 172278552 172278581
    0x24020109020414160503060a141305040c0503070902030c040b0c030d0204140405011401080c0a03020427110a020a0f08040e0a09020901080f0a1103011e020711010e01170c0d02070501 80
    0x400048409817030610060b250f070358020103980ca0400690341c41d13000000503100010f16148100816080d12400d469050f1001e40f103490440d1000c011610302041800010254072806500750310300f000138640030f1b004601c1511305094000404035443e5905004035446c212581c0c000715262515200d04030b40600070395174098041d41c5054004070350307a040f0111550031120141d541070b8140d9960203034000d55070440c40310380017819000d00021900c3c00c1c0302c00100d0015031400c0307091401c20f04100e0141096806002203105481402c000310003d565000ca07004003000e81290344d0840e04140340c607010300a0b10440d401190303070780c403100140f01401c102a0449055680200c910b0a541c2e601d43c120315441e55861603117204154040c1d4906000912561044400108000d00002e959028400c2034283d5040d034807602902036500003001700810084500405000d2828600710006040c0c460010317110180101c0e080303101560407000100908000710031a400282c041b0415901d90f00f180c5000b5018001071440d0201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 172281052 1250 172279802 172279831
    0x405030115030506070c0309180203220b040b0405100e0c0a05030303060612061302030f0a1a090a0e010f0c1d0303070816030e04090803160924020109020414 69
    0x2142104090030700c2580c1c0c00801074055a12905400d07034050090301c0d01201800459a00001c2540420707031980180642e0321405a030f645041c20040d03402000740ba03450300c1e00414003550078010a00388808681c0c006c0c2e0002e4242c14a80387c40c1046881d0030706c0211a01c0e44a420301d005080b05010210700b01207441800d403240a41140c54004150300c074003088031256008107042c04800c0e088807801c540d90382c00000144c0403540c1d082e03415180c0d100382c1e48111100c0103500800710502030001410301c11040d41030031a0118245509400002848000014100c410f42030744816080070110402c1d031140038004241a410409083d428402420b84c9a81e0465403140c05c0035501c005905080120840e038000d9802018980750500308041d152100d80342c80c509804125400e001d03180300d620707544a900289800750403503580741d02c1c0c001c2c20b81040030325070305070701042101020080226540b00003401f092400e00d450020040d0b0103c138000ca0061045e000060360190400328005440500810444d00403200d894a140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 172282302 1250 172281052 172281071
    0x102070b0313080a2a0219080607050a0e04060602030306090903030103080316032a020d0201110304060e0f01110d050702010218130b1503040303050916030605100e091e0a0506040f0203030705070b04050301 90
    0x1c2031f0240c0b91061100035000500061030440c864001040c9454803414a10440e802e5440030808980b0380703810160141c1d000200b80512440d20880c0c1541c00305806005501c1c546c1143c5d2000c95030f00001e13200720b0600040307211807031030075010707130003520700403040e02c3c4103c01420070a07404c1142d03030307130100c0d1540058000c10780d070781e203c292041c0202c10b01000e0800c895807540e11280c0d52a0000c0c100f044a01d189030240800c6881005007c0c0500030605000001d541d4031225414404000c0b0b460260101c41903a204010802c000005841803250381c80e41243c00c801a4943c03d171002c400b80900340a1345a0200c08800c1440310300d6003a50285001c2c40c002d0780d00704001e540d5002e0740c03590358020300700741010300300c101d1401c0001403616040b069026006030b40d008400c80d40c90384040c821080564002d040703038100545000c42030300d4100000030035071400c8008165076107254683e940c58032000f070030291400e103070020003000b551010404ca552250380141124441903440c001580329402c1409140c1c403a500340498103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 172283552 1250 172282302 172282339
    0x7030b0303090906060705031e030703110c0d0c02060c0d030e0c090103021f05040905040807031701051c0804080a0b010905090a0209160c02041a0102070b0313080a2a02 74
    0xb00c070380e8240500049030f103490704002c00c903003900148806c540b184002c020700e0030304104965900c1525002c004046459080c0802d014083d5000e0010107040404148403c2480c0d4000040862403817981d820120a011020b002107907291040031804070241c402d00300c3c204402075041d403148555017154010360f084040c02d8010004160028800039502400d003480a11690740741840d003502000c038178244245170950300d04400317083c0d0300100d600361000c11340490204141038200b034004d18822a01e041c152015810100041d400c1030903040003004404a00030000d007040780301c80450340541400c00451320105117500c0c4c8011540800d00a03913900394142004150358410000d8401401036000b882c0d92041da031100900103004142c440440208041d01c020745015032124403400c242c00390342600700003003451154000781c90441144d20a0845650400070401e6203081e081c0415050303640585200e80d030344c4411404451a418107580001d40b07a1140b280d2010f5807403003100c8008140c1c070036203c2c0c140440c101400c0307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 172284802 1250 172283552 172283557
    0x2104030e01050c0a17090405150a090f0f050103060b100c05030702131d010f0c08060307090b060f040803030412050339130e0c0a120c090e040b07030b0303 68
    0x5000c2030890046421960184010740074406544085402480b0300f42c132202d05080c42403c004580c0200018892841d00f4580a032541c08400022000100c99500c0b0207d00807600c0341c414014101c0d07a03958044d40e04140c0c0e070070042c1d074000c0c402d20a01103540c40c4d05100c0000c1180d185494402c40c90301598811842c015086064000d4000d1b000c3d50410409800303000403481e2000c04015900d680d50006440380d0100003130141d003606a000009a80005142032508540f6040e03081414080b002c020800d042d500080c4280a968100c140425030714600c20108145020340c903048590318002180c04281d0050000155215030300070300c11071810b5001110181d40e280300c15031b680b061060640c6503000064140c644412000e148141c20a102c041029140840503008921903251880b04003008015500f03e41c0380c029042180c40d00000d14081310440e000c1c0c85101c4442421030140e4440c1c2550710003d0007101204014400040b044150745000d1410601c2090101d4140300403c2c505584010325090010a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 172286052 1250 172284802 172284811
    0x720030d02122205041409060907120f0516090903080109110706051803070606170706020d0f090512030a030510120605060402090a0608090c10050a050c01061a21 71
    0x76520724100400f0166040411150000322503809045400182da865030310510501340c0c0c40c2e644c0144141011841181424030203000c6082942c0070f1102800705d86c103604108200e555202050b6200c01c4602c0c9056420700d00840d950003100d800107000000e0710380041d080034001c03501c690350348200c036030300e03001ca65044405982544070303151424098403001401c503a1059402900e52aa04210484c40d81c080313514540c00104100d5015031119820030410840c03100400701c4209042c003400c002404d00e00008d6541404103590300801c00310764440d0287c0d602605a1070080e000c041d284005c2c45140088450b42c2754403d030841c00000e480c05000075081c0c0361003800042a240d8903c0d039048c03c01007070385171100507003c0500950303032140d030030007114280d50b565140250041c412038a9010661814404440c1044052042c00b802030b040850441c602d640c0c484201c900441d0720b0b0400a40700c00d00840c149004001c20b03004006280b1a50514225290072200035201940010101281042d030700350641c11816030954 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 172287302 1250 172286052 172286083
    0x9060b030711072d03060f02090405010e07050322021003020301180b01120f020d0504050f0d0203030c030402010f050d0914010f0e0d200304030f030e01050c070e06010201020720030d02 81
    0x8080080305404042131491400082c0000f26480d071a501c48000301e4aa01036080a040e600041d40412414540241c81c0100b4902c080c03031002d4501214003405510000f0040e04404d400c004e44201400100c1542150f1150003a00c03ca20b04501108040c009610078083da0a920241031400c1c5d224000b58024041c0d0800c0603901c5560940040c1004030207401c59080000c01c04e6002e0061020320b407102e110b9984034a002c0c0c801400b415110504a508000365400b000d021034000308208503e03940500c0850703401a030f0a02c0c101003456902c40c401c40c2c650107190200003041d400d00d0803140600a40310034010700100001c0081020041c1d0b54204400c8030030b00c100e2210070303400950b1500d1916004030380700d0002c811442140f4114035411690b05007164810303001140c40c003805c9a00b800501d136000c40d61009860342802c00c43e00c4d1013110004242d86140302e2080c4c41101540c140080e205034802c1d01541e07406a884141c1070319944080304501c1d8546336949406000348205108004100d10004440d82e02403c0c48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 172288552 1250 172287302 172287329
    0x6022b0c03050c070905160f080f010e19050a0504062403060b012d02070f05060304020d1e030c1104020301030822030f0b04110402250c09060b03071107 67
    0x7035038152119045030300c041d080b81c02515400118a0340390702800d40300343c80207500140d0040328540c004e8100070b14800306d801081405030400c80751000c01101c0340c0c19114004525070440c1d5078441d088041c02e5242c1c1d00c02c04000e0902c0c0502541070f0864000310b000341c2c8030340390600c032421030200d604007482101000240e1858003090100081011035200e452041c0042c540b0394014603c044200541d56440d41114901c02c4c60403a81c80001c60b0706208020150001407441040146880005501404050006441918103c100382c00308908256440d20800e070307840e040d041000d400c1c1000340602d4030540054403210303032044c2250001c1c9402d1085070705907684940140d007007002070141d990300210054002e504540d48a00080040351588003006145c0f44a04c2c040340031441c2600c0d00600704000c0014450040e40140f221101c000c08450590800140840300071200c4143ea041c40f802083d0582d003d881034528102d00440e400840400452191304192a131001a1b00c1c201d185d00e5455509226501509101d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 172289802 1250 172288552 172288577
    0x206041707090e0c040509150c0a090803360913030305091903081302030604111e0603010603150b0c01023c0304080d06080601080c091003020603040f0c06022b 70
    0x11b81c1c491600030080d201220380c02c600007109100441426140c4d110300c01c202003203405c5d505601c0020310000c0c2c9118805036041005800c105a40c0c1c2882d00b811440e403503042c0c054985540300075401c4440e080f030014122203090030a031020701342c4d46500342070982c002414100000c8040f000003500c494050040d9041101c3c070303005600c5c12a40c683d400307040350703441d0200f130969800580e5080140d02d00403805040c032004008160f8003041012b902c1d0b01c1c640705583c42e400381e1400e40b560320344050700c2c1141c04030300f00070981c400340310604003800c502504000e0740908081540c80c8019015405064840c0c0a200414148444030204004100c000138558800c400d00964100c401401e001c0910b40240c40ba803003071030401d65070215440648110390003240c0158480001040b25020400c4150111304040e50b035082a4181030700c1074a5100114000030b4001e880010100b420084820b200c0008540c000118401554440d1002500c0b81600034280100888003550000b08441801401c80c66141a8a880c082581d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 172291052 1250 172289802 172289809
    0x30318030e0109080c150f070b0405030a0305060d02030607030209040b1206041106030f06040b01050702040507020610270e0316060203060910051e010201060801110c010f15061101090206041707090e0c 88
    0x207c2025801424000d2113440006404418254041c43c400c5004d503460341000e1500400706d0701e00510061165130b12000060258902084080c1c00200920300503a94034480c5001ca000741000880c850f0300f104d00198461b503049408100315018038030504006640c4840003007041030f1408181d0342d09a04083c00008100c0754941940100d001400c1030401500385001600044d046490884254015030420000c00c0000c0003002d85900213016455030b842071030080340c04a800001141540404032030341d04c2d281c0c190004020400d954070450703d000c1100ca01011841c013600a0740041d00c05034017403050080030076000004503401d0025548054201100c0c80d9103070340d442521441002c00d10b41555a00c007000b14909200380128504851042e04080e0345811401c00182100d0b60a03005088551030500060590302c1d040400104958a62400d500081c030b21010050051041c1c02000b58451800140010b8403000841d002c80c07540410001d070760742a5581c1100700c1c1516040341a44140d0780060b83c03405640c0c174 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 172292302 1250 172291052 172291057
    0x40f0b0702031501090f240504050c04120c06090609050d0602090d021c0b0c0403050a080307030f050f0105011e02120711030114220c0909030318030e0109080c15 71
    0x40c00202102c074214038803e100c0361614003e0f0003001ea100e803140b82c0c1180307010050003190884d041a106c0780700074011446484005504500565204e56200c101151003e03083c0c2060b54058441c1c00c1c603c019a0100380340c041107018082c80790b0b501154400e4400180c80d40100802c1d0202c80740a05203030b01209141d51108000d502801c08654880c03000080c04015850300010107240c003458800c0000c3c0d54607642460446041c00a000f440820740800c014800500007050401a00f548100a542c40b500c0d1020282d000c0d22855040c0a01146440c0800042e081c461192030f04842003a241d8080c124980f030b1142e50002c210349100e40141e40301d039210b0044125948010308040380241d2041c0b02c12400f03c0002403d403000c103040070008400803014051581105840c0d1000f6940340507014021528942d070300c003020f120307a00c074460321a56100d14032428913000b030304854000115030b06e8082c03905c1440d107405420406980300320350000340d581001080e800d40016290401d141c00421412840d11040c0d080703001503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 172293552 1250 172292302 172292317
    0x8030c060103061107050709060501090905041214190810091506260f01060e0d12032a090806010b161101021603060608060604110d05180d030f11040f0b 67
    0x9040c10805d81021403070a002c140040c107501403010650764945400103000c130010350041c0e02e0707040c80c0800780800195140280907100071039003004224101c1f02e004000040c0588496120000701525290219a83c4055044c2c801d4014280d1241410389444048e000c071881c0c00c82076a000e000c110020f10209008044542084400344421030080f1101d00008004031703000d5481098001c00480184080b98202050181c5400140c1e0b05040c0a403241d02c0303481c0480e0412402c0d905160b507961420758901c0c411842c0400729a03940d807001e4030a003910000208191424413600d0028040c020004c0340318020401113450440048010132618101c645070307078210119203000d0030705510407000f80e11801526100c0700b01c01980103100001c0c0452400303c13254180040285420300c03462030000401000c2c5802d41c01e0300c0030340c1c18551001885598081d4040149801165011050721030504100c1215a154003d003045843c401e01c28412003042401c50725190203a401441c80710010345c1828000201a8000707000c26 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172294802 1250 172293552 172293581
    0x60f0a11092209080309120f0301121104020a0e09070f0e06030901060f23030d0f0e2b0501150e06010f051e0a080709030c0b070501020702120d020708030c06010306 72
    0x90241200d40504031503c40e030086440b00004410441c10180501800541e215140250340c40c180d04113821000e584414015910300400e5152400180100c0122501d204000034104644e100714040c405440c040036002c0f10703441166003d00281c0c055100d818040180b860503207030f0014080740c150030064076400040480d0410f43d80d40000240c1d03403600b0a208070081c940020016060313101c0003540b000c24060025514000d612090f981d08021341c1c405005440d0b0306080c58502c504002171800200100300f648114003049030519800000c1414203800424014815402000710b1401c400803c2c424107034920600d001802102e000542030350269424040850707040c500186000302c0703060b0b40b051a2800c541da12000350004155101c42a4010810075000311042c14030340e00d05851a9901418100e15000e561203816010851300c013004002d4040d00c1c02180c2c005c103801d5201e120140c00039582c00c00b40399484018810f515002400394000300c201d40a80c80484090122130f800c40d10b60a001c0c02d10240f01141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 172296052 1250 172294802 172294849
    0x503090301060303031b1701060e1c0303060f090e0c060318060c030117010506031b030a02131a0108011d06010c2102010515031903090b030108060f0a1109 68
    0x109540c0038454840a184292000500c3c0c80301d025a030010f10380c41c21105018040c9900e298108400c0090502c2d046034094900b020b08c104084000c610701600c0c15080a905d0b5010707200342001c040d0150000002c2c0c031034a1585402d0950f0b03d4030868144c1e8074007000c9580b143c008051b00c0d1b41ca410301000660740001da2035614907180106802581c50000205c810303442100010005202d469918800c1c5010b0089000003440903060401c0000e403100c2403222652540c01da104a21000c5807001d20510300b0081c0c009080200b0710800c404101c1c0502040c10400c8080d5884007501c031400d600590640d0305a072482104151641e030103e41c00b40750808003812803030601042c09007000c00500850700003005005101c5203030322680c0c1100d90203400e640003e8100f11500011102c080da4603203000a440d0442840b00d9680210303c64981400d5400c0740c040d41180300c0c14040040041024007002075214052400850b5420ba599500801041125480d9800b4254030340100003800051620340348410150095000561 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 172297302 1250 172296052 172296067
    0x50d0809060703020d020606310e0d0c0c06020a080a03020702030106030b010b280f05030a151d090307030905040f1407030e010e06010510050a030b061b0c012102070503 74
    0x700385400807801103006038011018004540e0341445a44e4101c0425120f460140c8081032080b0441003075220418600156001400480a150380110f40308042c03842c25030360035060b40c6030001c1601f51915019103408a034100000343d4584001504070a00340c04c4035089d4240198048110082d5002802c241d82c590740b1008007202280200710900d000b000600307502666040060106001c070082c08401c29404100d91070104070040c0c2000d15156655035610b050380c1c0c3d0b5520b1401007001041c03180c00d81c4107500e440040c00300c1c0f0b9002c540c1071798072501034440c800341c102d5441403a550307601d1080010003000a0340c1d01c04100020308094008181001c26100041502c1e402003101c1d642510342210901c00090310f9400e403a255800c28450300301e9043c80b15010340455810600440c2080c0751a808040c01c125001854102c614442c0d4001600b922006000c2a40d4203641c80c941000928a03017844550ba02444034207455a602030310242c0086d061003c0c101034039442030344904000350403482040d40c0c0740c0030800524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 172298552 1250 172297302 172297309
    0x120030301051c060c0e130608060a0c090801090b0613020f09040e1c1206061409060a020a0b0c030417030415020d1d0d020601082406011103030702010f0b0613050d0809 74
    0x4071a400020364840460058500810050f0340713424411031f503114500b2034240400c44003c15043c2d0300100308800403807200d4041c0c000f185c40c240160700901041d40307820310140c10041c00b8035420f130058504450041004c2e513041400390807845900240c903c0c0002c104806600c1d410a500072032003000c24203060f600c0a030080d07454129401548404500081d071100c1c180c12405484c0c0c4105c0015002601d4245410400751800840c60b108100540e4401d0340302180242c5d91074420002000307803d43c8414121000d040250403c21503400944080322088203401061103008101c8041d0fa110faa0000c0c0340c102c13036580619842000394031080c6581202034856251f0700c1502001a400e4a81c8a1890010183e0f0b46452400909160741030b044844903070465440c88a1540c202c0070190075810b15070000c0f480c19101c81d40144c030300248000103054507000c08000c02040c140c040d80550201e0120ba00b060292554034410807242d8407615040d2005000e0002d400e01c039078101000c0007403840340706000d00e038640300910000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 172299802 1250 172298552 172298561
    0x512030f040b06120d0801090c0306060804110a120335040f050709020c03040f06051c0506030102070b07050a0e0312042306040e19150506090f06040609050120030301051c06 76
    0x5d4101054410004108072130151240482d80b03016490200412070600b00002c04224000d41701801f5000800113443c2c060350351807520b0000b00340f003044c04010811a850041c2140d05034110b442c04954004c0006400030311141900d24603d0900c1c00d6500740e41c0d40f82c2d641e85a4100d04240b003602d80788030702d03007010552400b170340700034100c01e40c00400458503646441c0f40d00c0d24084e084e410400800c07400b4007106007410151417805845070503030b510208107079803028046402402500c1d0007038502a40c1c10140204030b6001b10050004444a03690126071038548418196500340401d500140c0d6403081200700034110b800520400c5035142c0c5490f05424100c0c80c00001c1d61604240c1008507491440400d0241c80781d1580701a134885141c0500078800c40c100014001460790845c0319490080d400090809043e40d80c0060585002e200185a44e03112526000f00808041c45401041d010810035020b41d20028805c0c900705581c00b941c40c00035031560f82444c06000c10040d81c011420002c0030089400c0000400324083e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 172301052 1250 172299802 172299823
    0x14160617010f171513020910140d1106040303111507140c16030605010807060e010c03120b1e03010f15060c03020709110d1a010206041707021203070512030f040b0612 73
    0x5004007140c003a00400c44c0201f000f900b1100704140711801041414044540404242800c4078810000f03449800c14000004004158551000d40001c01000301a08500d03526091040c000484262501e8019548201c030710a558400214040d070624441c0d040c44c940041c5035100c082010780b800450400c41c1c0c6210401035800c12262a034035500181304000d01088504028030756441d000046884840028000303414244001d010402c124070f95982003903ca410811121501804034242890355245001400c60881200c5100e5408e0080016145055000b0301e014804900507205107940740c01810b5503c1c4080301c0c0c1c1207007940903400002425861034421108288060300b1902c0d0b40342c0610315210201c035142401c01e203110055540412042c1d0340040c03855030040d8010b091408150007400c070a80c15024020000b940800c1610185a12030f0000c409801e0b441c1c4580c0c03c9409140c8903021601103400f048400409808e04003000030046a550101140c00032800340074000c0b42a03825400c1c41c1040d074100d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 172302158 1106 172301052 172301071
    0x906070c0e091f061805060f0603090115060906051b01020c030a0504051309080307030b040b060d090b010e2214160617010f1715 57
    0x603200160900540740c0e1450b142c0031060310755911107804085104074040c0e0810101c510140a00010795480143c0c0e50041c04200e2040c4000300b00044c0b815a02000c0c2c0003004815440d082c001303500503071005001003000030640505082061155005100f0440300c10000c200d4103a000f0151441101c00d0032420060b10350048a031170282c0100000c8012070301002070444030341b9030000000c0088440c26144003403010310706400707102203840148001d82040c404100041c0e84501c29482189001001000041c518440c1004220340303030030007642c01d1a02651104040c0501003109441401040d195103012902d10380129801d800000d001301c200310780910f0007010003c1002034502040364a2000e811a1200c90040c108128100f45038400d074400300d01c840f080c5003842d24040c01707058140e40c00140501d030b0061a20300d04094804120341008aa4014501c94005611100328654001c41045 = true := by decide +kernel

theorem cover : BRFrame.Cov 172122302 172302158 := by
  have h0 := BRFrame.cov_init 172122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 172122302 ≤ n) (h2 : n < 172302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
