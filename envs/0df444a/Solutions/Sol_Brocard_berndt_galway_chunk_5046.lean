-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:55.704129+00:00
-- url     : https://prove2.me/submissions/043e9828-6a51-4944-8843-6314bc1d7277

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907374100 ≤ n < 907553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907375350 1250 907374100 907374137
    0x40504210210050f010b1606150f0510080103030f120605120307050607022806201308150703090c0306020f280c29040b181b06031015 59
    0x150080111324401d078595141459001803406103035019005040d400203c94104901c0c3d42c8400c0c88405000c046000103551030000c03c1e04200c030f51140701e0060403241000281c0612401d14241a207a05807950380304c001d18190102d400c4820500c6510300b0300e03039401c03002c60555034004242c00740040750030049d40d590390b15141581c10054083c00071029548029050380080000d00076110f00c0da403144980d204840b00904140010f464100841e1007828000686044800056801800c104e80e4400f801c6540d55a5020503944d505100c10400d07040500c1c0c2408658000d12176045449824000c00c0c0d0344400c240c5070345610049900c0717142010203820000403180041210025030300da04200150041c41001e040b1200580844501c01000b0a0707501e03d07054242075148060303410001c4041c061442580c9261a00e4030303404480c0142c2e901c0c211840f0190301e202070602c0000313188003440d08040c94405009885014842d95400140608207442900940403899140482b520b81c0000c541e82c1e22444145850405907 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907376600 1250 907375350 907375361
    0x607080d0e160f05010f17090f06150108010302040209041d0a06060e09030a0f021204030c050301060b041d250206060109050a14060d09020904030203030415020a0806040504210210 79
    0x11508450042c104100c1e500c8030b42e05011110213092018500d51903000460f00200411007030200c0744044002d108940c00d0000d0501080c00403041281c010344c40e900691030040b9044c00e003950005070120011700050620390040e05040300c2c041d00108503070081308002c5601d02030540303202209070300542e015428024140140c01c020080000b8480c441e08014495986a1080c10031110034080400b1003084c8241c401c00c070f0540b48000c152295a200c980301d1506807030311501c40c80703050710a6007000d802140c0640708408a6044441c000441e03101548000711404e15904000c10180070b1469064000e081c0c422601c2401c01c82e403080b03501525051401030005001042c0c80d40205010b100004002d108074103200094503c00703030040b5149a1181024500e0101404c150480250001c4000e07060008054000000c2c5002d50300c28485d0341100d038070300c07507040049001f91245400044c0c0c00c48085407203400c01c0c2d40440d4202c1d0207031034007a0301d003044400008003240d090500440141e100880c070494075112031042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907377850 1250 907376600 907376623
    0xd020907080901140f0a0e0a02030d26071707020106091b080f0906150d060e160b07020105120604090501090308010503010c1b0209100f060c02010314070801090b0607080d0e 76
    0x100713413042c14502e201c01d001c118024001c3c078450f640d401c15405419020441110400c1c0d0090803185043c5045d50010203028501c04250000482c856611f9061900101d01a10450742070b51001c1106455041501c0054030240501096560300e000200e00a00d96000d9030101400f03102060722550861040141121030050081145480c810244030080c140803850030b400c200c02c544001440026000000d9043c110140004d24a0345050b100183c01d59021501d00344000b02c040403020195540d51104945118040f0003d00148082000100ea07140c3c0c4802980c04c0040900000b07181c0040303580d654212100e00c0c009134013080c1c2c590010401c6140074000c0d000c11300d4441c50000708411103c0e41016104204480007071050000c01c0018410000815500004207240d03040e8100050761030398040d00070011940242c0c00a420302081c5081d050048542e40d0183d5070035a500b07221a86400c444c00020100741c031010740c2c8890100305010110b0b10308401f038103440000c201c00143c1a07001c0c03024286850948500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907379100 1250 907377850 907377881
    0x9150605120c030c0c03030906010f0f08100c090b1201050f0a1a07020411040f080c01030e0d0806120d020c13050112080c0a21080702030f0d0207020d020907080901 72
    0x44001e0321030841500340c20141c1074010548139120113908440c0c60052901c0d160507403002004002d00741d6400a8140e040300d900207000414161108409082c0f00d4240c0150801503101c00f200180c4010b0b0742e4801300c800d10444c6000c100b840d44034034540c0400c2e4000c2c01102d2112881c94014013861034145a8031003210340072a92600c2661600d40703543c01005012011400c800d01c04035154055440d1500460440716a08165695032510b982a00a03c0e412a003e010001e114405075411913500912600440c07085100081030040396204d4110380c1094001c09564104419680c00003480d6070810001010600031707005054045001e070144078940c400f100301d0700c1150f818a0010041c1c20046081d84074655000b41c1c14541d18149a1042841e190000304001d0094246480003e0002504447c9144407943e80d940c02d2019103815000b03d03540c3c05214041245140104410803202949034000d1000320710140c100348102c074640d000501d41807021101d80c3c021504000401c584584207100e140c44103441c500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907380350 1250 907379100 907379107
    0x230d020c040c170618010f0f140603040b07170a1a0d08030f0c1e0913090c0b1318020c0706020118020f030a0b0106030c02160b2a0709150605 62
    0x22001000005000c00f00c0d900c14a091001c5207550312200c044048940929220041c02d507907813502104c0181d914851460381080b4028003140003031004190b803c115100a0565046440b240c48280190703101810702010301c4840310b0300001684040c0201d505c035a41c0d5a01c00250141200c1010410300302d905071042c4108410400c202c00900d040341641e1b0020001d403203500039070740d441c41d40207418880c45658500d200416841029843c0c1d001c00181466a819900001111512003240c41600c110b00c0008029003915002400b11940c0d41029103841880502c00d000d4240d56899401da140c11542400f00c03a0680003c0e0280c1140b108205c10802407040344000c0100c4040c3c80010380140c4901c0c00e0003071245551001c03002290f9001c02c0000116500450301b0001540d6035071004d40248007611040780580145030720301101071421011041298042c1140c94034240c0300820315040a104038400d8249480f6406002031861020411032010b040c03400400200d4461401d0420301d214556400f03c420400d040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907381600 1250 907380350 907380371
    0xd120b01180e070207081504110405150603060424060e0a030804120c05031f240504050a140708010810020405010c030c0302030d150504150b16230d020c04 68
    0x2070326410844901989441554540120890800003650320141d100d105080d10302444680e100707035460140d446060140701600ba21800d003c1038420845042c0068000b88a1540c41d50400f40e008580c0b12600500000b004242d801c1e03400180b0400030309084600303c21003002d10060360000e0aa0b80841c00c00c031004580e2900e19a01c20341c4d6449140950717020480d1010600e8100400c140d00c14014190090688044408400b40e0188044403451440840340c200364460200f009101003030b030100c544501c0700c40d00fa01d04050600000d801c0161250071026074822005501101e0b204048d0701410b000c1d5100748665150a0b0a9232903c19800c01f081141c83c41080200000c0c0c1e0488090280746901d41007440c0d1071205428182d0540c0245030135840a0350808283d840c004c6015441c9400b1794038200c0c0c00f00000541081a1004028503002d12000b0400070030280c002c09090034543c0c110a4130034001459841e070300d0425280c1ca0540c03044c854850f035103c40740072803007260180800c18810710b050b1010007010161 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907382850 1250 907381600 907381637
    0x605040c091e1112010806061e012a0206040305150c27130f091b0605040315020403050712050d0212030a0e070506031e1f0306020a020a02030d120b01 66
    0x1c0b4003444a00039600c1c25440c2c2610050030640da14940349181c950001e680d0303100d08644580f0103da65504c245003090704444a11030600d101c1c03000c9001a91840d280b40d41d0302c0c50100c1c0c201080c003840000d21b8103248140c801641c03070382d0082000e14826005804c4405010b0444940d0120203003c2004d95901401448092454100791800e5114840d4400941c4140c40c00481e0403a408110301c1a0340c0c1f81003c8030380743c0c91411a0415111035101d1358070400130b01108008203000c944a40280d1000030300c02c00080000c2406000d403140380c038003003010051802e60ba0343c0e1480d16058503540240f440d60703040420301060020a201c0c448000c5568005400b603525000304103003191000400400c04140c1d42c0000303108409080000704098100641500c1ea6800d04441811601c41413400c02c0e21288001c0e00001c24440c40880e00300c400d00848000c1c09965410b41d0343e004060340200303450204511a9072070380d20141c1d400301700f40101c0804a454141c03c00f5811000b039001c0e1640440da803818000b441b81100c024290 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907384100 1250 907382850 907382891
    0xf1b0a120c08160813150e0303180609060d0f051b090120031e030907060f08150f0d060e1b01020307061d0601030b0718141018030605040c09 62
    0xa0b00c10b40d0300ca2940d464034014080e80114801d0849584140d44040364003440b1b0700c85d21150350a640c03210b004e042044e90805942c0d208440b2817607a03038016820110100d0500c0d50180400e540c8c010506070806002d20a40b00c00c44410310a07558402e51200248011248101e1199a890160240c45403425a0010000e0180032440c40c480488102088440316000c00510a440d03aa4102c2d081031705c4000700070042c444854100f5a18856540140300c030008405004441c41c17854442182c032190f000f69620308484045060703514035542c028558090f180c41690b00c0d003011140d900e200c1c03440002c200380d108502d240f40c100184598401159003180101c1d0ba680c00205803600140c1c041e00118100d1105c0c03000c11148404440e0840c400d108040000c07040150020b400c80c4200f003195280120801101c95440811002e4461049111400e2181c01440d041c020110f26403030400d428460040f41030740e903034aa03000c1c020b0380c010744030142d884017072200708000e1030390180042621403800c1c0503515030000ea100c0c1c2003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907385350 1250 907384100 907384117
    0x2190f1703071101050c0706050c0c0402031308090a170d02010605061e07050708010501060507050c0a030f030c240209010e030a0b010b0a1e031d160b0f1b0a120c08 72
    0x11419040c605944e8455400c94103d08502410313200321595440c0050115084207046021501580509440504091003034034030504016200e04d40200103501e03038610980c00003000d103401440c040004900f50f1400c1d5043c0d0300c85840c840003401011403019009013110000c3c0c000030b00c5100c0c100001c0c6c072414101d0a010442d503d18590040d5222440d25159151a200c0e5200300305039400c03c400007983c0c64001d4090090300d40200182c1e540c5400c0d02c01000442c0d1524003004001a40d40303004840442e01c5030b80d41e0060240305d055007503c440401e00701c2d0021311000307100c1c1031940c640010307852549590140c203000c80b001c0150010302d00340185079910b1000300814090116040700224081d030216118028080324220301c1d0958018039503c040c00240601803e4003202e00205030110006800a0001030403004280d074100c0040801e41007000d1481140d100841c40030b00244207110030050310b0107004220703a00d416144020510b4504610700703048080308040d0044203009502d106100499410402c42da00390 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907386600 1250 907385350 907385363
    0x21c030e0a0617331309030503040c080604050a0b060f030f160806060303220f14151602090a0902031501060305070513090903050d0509061b0a05040509090a02190f170307 75
    0x140b20b191301040a1160482d000c000082c2001010428107411500650243c0d0049000251941d01d40c1c411030b5681c0801d80d8020090342c48040d030200802c07280d1528a8000000074201c641c01c40d03903d800245408060250580b164210030590a6203200f01000c00d4018114032029010a19205e400640c481c05840940c5068031000100d91a1084203121090042d000d4007409038000c94403020328584401a070003c4901411030444c58400441e041070170b490007080d0b480000034400407551300344071019001412000c1065214154100169400d101444003044d00103034010725585816002015204c020384040c05104041008401e0225140100f07401d8441041c1c0c0800c41b00186c1c5812142c07841850126811107180800b8003200000c041040c0f03000352000142c000e9500c0e44018070b07014510461040c00d01140c01080200420b050600c0700303687c011500c0c8143c0b00960501c7c1c001c2030701d441443c4180c2014819600c81440803050103a10300300900031024103052001e8000901d41e98a104840e80074151 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907387850 1250 907386600 907386691
    0xd0606180302012a1202061f0e0406090c080f0a0b13030503010902071704060c06050a0b0d0611160308040b010f05060304030813140a0203010b0d021c030e0a0617 71
    0x50300961215400c49070340403000c03588405140c08001d440307c000340d641c102c0c0c04801c00100461001d446201c86d003603078103c245080240d1601c1c2d8481008061000c0203e40200345200d00240c000d03020b2100000700034841024290410721031400031110300700140f8455880e81c520082d040444c0d032000c2500d055940d416001607a40115040c40c234540c6007d0071800070605030018010920551000403d96101d100703040910440d101c0340425404c0d9090340c03810715000300140d041140410180d4125010300044086003a1801c0d0000752400103104041c0c00a0740424941d41c00c0c00108106244c08500510260703008880c15400c19001401e03c0c480039001030300304006200400d0a9410200e503154480d540202000c1c01958041207940c0c590492043c00e0381720f9407070078800000f5800c0c001440305101b0750060070000a140b03200403c1d450b129140f0303010b508005042c500c62074a03403203074004403006d4038003500d501550b48000c20b5000016000201241448810002801041c1200380039088c6040990543e00b0744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907389100 1250 907387850 907387907
    0x501060509101707272d030204110d0c320d111e0316110f1c1b02060403021210051e07050a0e0103050619090608070f030c0b03070309080d060618030201 67
    0x410f903947d00042c2d0f0091910700c6044611541000801c4408400501801546942401620513504445c03051640c2c0703580e001844802c1400ca0089403103002d41030b00d2a8200116441c00c40221400b540f14042d60b4000041c40d5040110344030421607410460201d043d103107203004480c418503282d0725080c0205004540000b82100b400612200b07980395400421180160041c0c04401c00c0341060f0240580401e00004c1e02540d40c00c010101d400fa07040d005082d040c6800d00d10340c24894096480b107484100d901034042103200c521114060580a0a8451910100013a0000c01104440c001404800c10300c10104207071180d00350482040e45001e402400c0c0010151748800114011401e90b40b5400b0701d0b40d0000e040407511380c80551010003070301d03100001c0b00c0d81551101d1016050b440d00b0f010181110011110030440c40e00c103c80250360144841c42e0101e07140c8125520081150402c40855800eaa16901c042c1b240c44e500c1149448203907044180300c0841c1d4a9074002038061003900c0302144015918105800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907390350 1250 907389100 907389179
    0xf0f0f06170c04270c030e07180e030309100f0c0e0d0606120831092004080d030b0402090607020609030a1a1009050106050910170727 59
    0x80061054203131111680e1524945090940004038425008614100181c103480d40310784941c040410499000f448158103001c07a82041484000c41e0960071a1903400c0c080b12098240051030203503040701d0041c01a0340112000300c040d2804071000d140001d15000c180070080387c1c0800d9802c01c512003952500d0303150703803d81031440284c070f41c0d46c000d075004004007001101000900001064451030400c4044120758036601c40400d10740201c0700180300480c00b440144240c040907441090b841020080804134090015100810b0760410b5110000a80041c159240e0254060240424500046508500d4481054001000c9000d0107038040c0c054900801c0f0b080d610b0310308010403025290001c0c3d080075003e4080166008601e0122580c50008400c1c00000a1303101150095a06907505512013074102510032090003200c074141c1c151a0300b040740302d5940c01e00003448a400d443c004d44244d0389145580d101105402c00b028242241840c1c1100e2503101084007600b0030808100165200207840e000188074002c23030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907391600 1250 907390350 907390357
    0x1c0302091518090f0630070b0403061503050304090c170108070312140405091e0901020a030e0f0a030315080102030708040210020613080c01150f0f0f06170c 69
    0x419441c10004240e0114250605084204881154680c80c1c81d0b4a000e136000b0100816245c03036812804090f20010321000010016149803483d0162040c124104030b45940b910308070340d1150040c46c100107400d000703011560148888107884125007042c0da915503038903265a4401d40c03080d9108140e03201c0c56054800e02c1807008003000c6103503074081e58503940c4541040762100c015203c21500781c0e080c078136007403503481c06410300c0104030b500c56552505081c81c0c0010700c4400700b0014845446403035031112000c240214221040d004003030010005031203450505001e011964142e0712200e00f940040c1000f40700550018005100e01c0c2d240c40e01054800344407050b84074071401c0743c1081481d035001004118400e68801c21540c403c40c022514400602c0e6a48011707a100c1300d00349c0316510107400e444500b402046d841802003400c1040c44000051520706c01c000040c4094464010542c3c58050080801c490a000e000d244050810140400030080c074080000c1c180002f180d0004014445110000b01840c40b104141d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907392850 1250 907391600 907391629
    0x60106030c17161b0b0423010903020a050106050a030c0306020a0306181b1403070e060906040305070503060c13090e120d1d0708031c06050406030f050d021c030209 72
    0x405103c0c14246907100702a4211000c060010f80d41324280040d1804000d010f0310200d070480c1c09a061030b1215206c512a40c81510501420302c5400d40400e00c12010900ca00c400c054040c7c0d000d0b2840c040603160050a4600c00c0d840701d4450108070f00280b0120354a820300c5c204495011000503a94040104141d000e0f00031680604151042200c089038020720035080003218485400d001892050302d080166030b400160000e201c0c082c0000d20010303260380d006002681103003100508070360504000800080580e0720642040b1640d41201b0001c000504080040355002030092983d10f04190f40400d5148050841d803140d09409626660b00b10118481440190b101520018040c0d43c0c5030101c00010000d4103124648041c10020090603858941e4041011029a0b04100146150902600300420406c0d80980d200c0d81260340d62074000f03800d643ea413107440001e52103011003e03454100d900344542040040c806680554000540d410000300780c0b110351403042e94090a0060322142c000b0041210000d80030352 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907394100 1250 907392850 907392887
    0x501051b0c0913110109030c170c0a09060f080a030f1808010212072714130903030b1009060905090901020d0c050d06050f0d06050c070c030614060f03060106030c 71
    0x103208480070710b000740f071100318050704040303003107003140742c011036044080c0d110140c480b1000303400600c00a0101c1c2c6081c00c00490187c101d5460304c200d440040c94103d4568043e41f00503a81d8042045400700c0500102c0042074030901624000c00291400307044010781c10245010819402d0300b002c9401c14958000019154000c02151565010501200c000314281d9441c004900c0d08807846803201121481608030f0031a546903000c200b440c2c03031006903040d481a00007a601002c03844019003564014440d03860281c1c080c2d0f5011036000c41030f1080c018902401180082005590712060044a4001103100700301e030300170b4905000c01d80e90320310ba050090284c2e000300c115040c207220350017601c1c03644003020740741c0d55110030f004000700c0f075440713041100300c00000390055005075100f000b0101140c8076a000e2503020341007614403440c00c4040d50f64000c002030b040d002100c03504d645004401200041c00c1c000ca51205080e6100f80302440c1d80700000790f44090500c5130400f05511402e808031418440e07030032070401d407140c400d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907395350 1250 907394100 907394119
    0x203041404021e0d02090a08030a121d03070605010504180b04200310050601090b07150c050405090f01032006070f02032802121c11071d1e010501051b0c 67
    0x101c14046d41c0000740051044045810101d0030410203c01c4541c880c0701502c600b103481d50214031140240400034244000d031001459254864201400200440e0340308940020711503050004000031220b00f0b40840080b40c0a042c144030018007032a4601d604140c10055126011682c4040e8560007810820419014000c2180c4406ca01003149c1040f8002c050176218024030760b071562040c01240c01070403406000003200c6081401014020f50200c0d100e40c2543c90003038500f50f00c54010078160141551a0b00c1950003810040040c0074441c00441c206408000c218500d90040c0030004605006820010b040801425045411564200300461103000700d807400d000c0d00916030507a07020403a00e0f020240d01443c00080785851010000caa0007014400a0703030003040c9518400c4080b00c070181840301e5400c1b140305529010440b0707041038002c00c2c03030f00d904100042a68505039004a02c2c981698081e5000503404000600544c0e81104c152a03024007180309030b21507140a01c03412464500107511107600b01c9030b0342 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907396600 1250 907395350 907395367
    0x7170f0702150906040909052b0306051e090709150207030204050a0510270f0218011106070e04060e01030f0209011d060111010f1b020d0203041404021e 67
    0x1400c1128001c440803030101d11142c410750b8882c41501281d95203c102004248483c040750343c0710903841400340086030303013102003292480410b400e080a1311020550401407425500e9240c0140c0740075060039158285003081036102c4410038424904203502c0388130310b00c000481081c42004d015000700101840e00c6003501400300081d40340c42d828002640a1800d00b800601088403d004080c06a1110002d18404078038000340b5900c0030030002c0c9608100908400e10181000043c0078600d00701112841c01a614101c201400b21928058400203040c40100040d071800044080707075040e8030007514282154501b6903075002030024403d980040011240075130001c41404640f4030548a00c3e8801e5402042907601c0d8440d81d400da0141064909254014070005801944904400e041c4c044140002203580a82c2c51216810381d2140720300140e940713802481520441d50b040008208980303445c005507280070709101e0036180035062031414900840e00000c0c4481034810103651850700e850040d0203180c030b41580 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907397850 1250 907396600 907396627
    0x8120306030a064209021c06241706040c020a150b0405011d13020d0f030807030501060e09310803061302030114010c17120a1805030a050717 62
    0x10802c1d4910a080c0c000b050400001001c810041c1c4e0404440a44010b5151041190295001c0c011030103846141aa130f0321400e03c82c034000d907006032210540ba01c003d9281d40b400007907501c0e0a034001600f0030001e40c0180c481c450f5a56020360300f0020030340700410040f20014042c1d00e4641c1c8040b00504101350400e10002040700c0d03511910b04400100c4052120f41d0b6130f1a039107010640c51868001c64080c007440801d407112082d01c0c070390524503c05000b5800d074248a4a5210030315425182c180d0104005404001d0702c160b040c440c09000d0962428400c2803032144c04086000f0400007040186d210310510001c9036400e615800c0c24420102c03a045581542d801845c02c0e462580098420f5402510390b40742d000a48421030094078140c41441c81c14003912150741d00111101a10640c055450401c03010700652800149002071036003002071540b0080c2400d1440040703045448603421403601c04800703d1a400014000b104903a0030300005d1400c6500c03002c460500000c1840406019050342a0000d44503000308407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907399100 1250 907397850 907397891
    0xe0d15060b07050304121a010e15031606051b0f160801050115052208010b03150f07140d0903090302030d08011a0c010908030a090b090708120306030a06 67
    0x60000140111595141104001d0088040082c6650001c3c00140503500c44a031100341d01600592544e111401e01403a624008034080c1c10420503030101800704008100c00444070309000b00160010804200d41001c40504c0c20345a009000400c600000c45080038401c5184c8498440d100c0e00540e00ea01c0c030000a606c1d0f4500140a03810080315059600181c3c441040c41980e048481019060121030190794046031907038812240300d440881041d44d480e01c41d248840602016080d007000001d4240c155404062900100d0180c1281c1c002c191010400310315141c005241d0090540d04040414261003600c2540601840700b08941d0b040c50f1000035011f01d40d10200b2a000c9a00950a4481c4036400038030440380a0002d00940004042200080b00c040414400030080c60401c0000041c1c0b602e00c55460742c00d20341c800c1d00d07601c000320f031a802840180001106801d401450700c00040500c90302c1c24100e240c0b1580c0340340e0b01074202e070008000181c540e00c09000101455900c05010032031034011942a094112 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907400350 1250 907399100 907399133
    0x20705010f020d081611060c090a0b1e090310050c0d060b0c0714060c01110705120711010c060b03031605160609170c0915011b0f020f010e0d 62
    0x1c000d500956005800400c6900351201660b44401c2c2598a91040440422400b52480c041014003941c000015006120040c09000205901e554455105e020081700781120340001c508168100101002503803d9010705060b410b030841026103c08138040000d09010703d20011000a600b48000c101c0c503115040000e180c1c59040388000c000c8580c58810501c0c5a000d0310140c465254841081070061b035110a0411407141801040c8a2420131002c04150950f82d61400200a140c0c0118413001001010701000184004a0b04040d062503055120250030b980d2992a040c10701c0051030030312091201d0358102c01d00e590b0010701120b984020604181c0000c5150341d10580d8140200c203144050a00791190314070864969070345c1c4c4001d240c20481300f056140c03a4a08001c1003407240c2c0e9851042a181d821155104024840c2210b1500d400400050189030189102e80041c0c5801001400003914540e000c40c100c94050b9140480b69900d9401a61094804800f65030b02c0b220510455041040181c107581850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907401600 1250 907400350 907400357
    0x304061107080f0c1c08060909073f02090406090c0902070b06180105030a0b1f2d031a060d05011a01021903080f19060b0306030c09091905010e0d02070501 68
    0x4411310917104403581c0ca99241100054001010425500e0319000064209000406940700709982d102a0851821024a90040000318034806a00507140c41c00d461622544298504801360b12030740020b408a1303008000070301d20f507641e8040c0410b00c182107a1040150403c00301c00c540e00c0e01c141c102030301c030b0440c100c880c07078424138071048a200ca1404402e01107040311070140c01002c5601c441d51700c8a03010900109011000003080801c03840340408040c0041c014600f86c5200300035525202c0516601c01c2654010000030003601c04200005908089254015101c40c00d20041989901c400a0103060184401074506e6007400c4450013081c0e001c4001d0140c01900340c003110100c0c14802c0002078503900300703140a4081074000d0000354200c440d20b61041e9004904d08040c0308001424180301c0100d4074250070400c440117002c4100406410304101405000c1c004886d02c0c1014603003800544c1e42d40e2840c0d240c45490480081d100b00820009400078036030081c5010a407a182d0090300300080d9140618442d69001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907402850 1250 907401600 907401613
    0x1202040b04110405060c03120c09010f0305070c08070812070305060a0e043f0c1e11040b040b1201090b07050703090608070507021002071412030304061107080f0c 71
    0xd031600c0e208500034a2440d1a440342403915240412105030003692040b2520f02080003c02d00d0941c41d002024842c00d130f0031102e00c4d150711030b18000400d9070b5a41c00000090514003000e1180440d000800c400455a02c48d80c11070b554001441c09640d28001c40b04d40300e5480e0010024001c3c420303015042144104400e07140a144250f569800000d0042c00342d0303001e0b00f0303031080101d429800c01030407194070340300309401402c1044a00441c0b25031200622180602e4000340b41d8810440c1000a094400740000800141030b41c80180b080d1035020709142a190300ea4402c699454156101d5110b03500800d10b036103001020b400c2180b01e11007201c0e002e0301807581c040322860742003000070320000e000e10151140940c00d981c519124504156058400c0031001d0714074400c4c4501841510b00583d40c2100160380c0c4242070b405040014038140500d0040c90100d609184140652110504408000404e813540140c100c10042900309a161a01e5024465507101a1600c0000240e03000310940d4000142188402c0c030048580 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907404100 1250 907402850 907402871
    0x30915030b030d03090305090402031f080a020901240c03020705030a0f0605010504180602070201120516080c030c2208030f18040b0f091e1018020309191b120204 71
    0x101c5d80450130040210f481440b08030403604140d40955070002390300405038800c0d0312614050110000c0c1d0340c0a0f40381540b10f0f403500401c5003450701c1083d0050038004d044504402c294a0005080c80d40d00d800c0c1c104005214090320181842000140b006080250a80d40d80500790f003014103d41590480542d01c140c2001c00001e40341c1000c4c410100c0400400d10102c804c80078940d100c070041d60224506904000e00380314085404030403842010f01860090008044e503201c6404090280d24008040307a000007414802c11a081d810700d03003250412050311515a21040c0e402d90005000100e5401030300641c0300c0840c1d00c01000a805005043e03641c80c0048101241c003500c8204001e40e1215849542c000b000c2d1240f034103003030424091035034002c42c502c02c2c0190f43c5d5001900890901008480002a2000d0144c040001e0b6964003c6e21540d40c0400106520f10700c2c040e0303c6544d56a07480304c0000749492010015000b4444a1300d034412031918034901044c00c0c00d80d1a00c0107070108400d100c060f8400c2e4036100c00c410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907405350 1250 907404100 907404107
    0x120304060314060604031704030b010f080c0411191b03080906011e090c030f050f0610050c0d18030606030b01091a0901030206090f060c030a0206060303120103020d030915030b030d 79
    0x5106840043c10139150509641e940e032030303c81000716180203900c800d110100c0018400c01c0c00d14080c2244035403104480346000c4905245c1100544514080c6140100020201040c041221425250b1100108400748090403c82c2c140c0c1034201c03842e4203445046103400802d0350284040d805180860200c03923031743e604e0f02c00c0000144446020b000704000c03801e0040100c50619000f0400c404114180012007403403460b01c25041d00e04c211542c10000304030030100000362a249071604803640c030510b4410309103094480302c16170341d40c051046c0006001c8920114400019034a20360009564800c07070070f0003c0b07640ea191407800701c00e01b0701400c0d08250502c04610511203003078622960068005010030107d0f46503400784a0103501800c480c540000c00c03d10048a2901e42100a0142c41c40703c82c0115070f00d08110708000d0030920050042c501c2904200040166584020715450640303404480030b8a40b41304501d400e5521101e0b540c41825400f20034290803c0c0d1a030135920055500400f64191041d02c000100f048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907406600 1250 907405350 907405391
    0x31213030f09080d08040c05060c010b01020607031109190b070c080c062d0f071104050f0108070e1509070f1107060516020f0409080a030b04140106030213051203040603 74
    0x14903030b100103641c4c90510f101e03459240d0454002c80611059540baa40864803d51050002200030380d147d510300105035904005c0745070700840ca450308000d13001c22241e08038400d100300e0401e180301d05819110790b01d42c01c140d0520280109108110566100c202c1d2804603c503150b948902c050900030b40e02c04e10341c64148481200d45c0a16041c101181d910002d6035100300c10040e0321150700701c1c0340040c041c070181c0010b0310340102a02801039070404c00c01e400b0b8204010903200d0051a44030000d40c100c00403c001c80000500800b940c0000780d10303040d191348901d43c00850358100f020640e071044204042c0a03072290841e43c500c078503641d1030340e40c003040042411005d40c0d070344074600c655400118100500e0210000c0301c610205a244010014041e00200000040c26596400c1013a03400050000e0203c000701d0301032245601907101a24180a940f40040d90b6407803100051052405058002071000418140704040e40060b00000308071603000707214403001a54075045230150401003072500748003c541d0010f54592 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907407850 1250 907406600 907406609
    0x6050604020a050f030a060807060c060f230705090a0e15040c1d030a0503130e07031e090809040e030a11031602190806090606130b0306040204050603031213030f09 72
    0x80614240282480030020b40c0010500074486e607841c040814191400d01175540141003d82ea0a48400881e0030400b08582000c003406001502d0000d40c0c000b203034030f52807010349900c0406481141e44c2c2d0b03408006540910600d1941e940c0100842d40105103483c00070a8107008031542c04001e91001100c40c28081101c0d0714002460114140128440301c6801ea0048000c034404050b003500d4100401c1d698044c9903030014500402c0082180b0410311811002a0385554440520b2a040c005840c030f901c101d8508000340c000007241c0c1a1515018814006000c088a105c0c000181081240708201d8450517180d03013020380365400050074000200c250003070010503181c15254040303000c91a41e03a0b5500f0002d0f03864042c02c900320b008502410001d1603010520105104146210180c52107180c5001000b803417148603082c2035641898a0b0585c061920b0008142c0d5010346d040d41c0010f82d5460700d1002a1030b40c028003c4104402844404002a198461540e0101d05120761a4702d00e0f490010b00f0141e4a06d04503004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907409100 1250 907407850 907407857
    0xb100915150203162d060b040e190312110a0c0605060109051809150a0527100b01030b031207060506040209010c030509010909060312080106020601210c050a030f06050604020a 77
    0x420300c0841e291a840b00034600c403903200c5c8a500b0900d240e070480c0402da80c03c0e0a8564954070100310025040c0340c026082080b2480c2d024100b046502580704400b1781d40c0c06c5010303041045150f1549401c11a42d8030401030082d40144058503045403000003080c44440040031903019041c003011905950140b481c20741502c0000300710444c011509908141d1031400200b4030480b41c4206130051032103000b080301003030280700b19401c003044034541552021220100046c0500b9541c3c40a000d0a500080108030861008482c04000c14108e205200480103040c60480b410352500401c01501e04852100d0028a0000c1c840e000074806503444104210880c0030301102d02e03011a8042d286080082c1c0700e04010000d0318814181204040e4823003030514216845500212400c41c20054041c400c283c2125009006011510091900f03604003000a5008910b1440b240c5007540300c0105032081180d4104100040c20000e003004103011307138a0502d024081c10004c0d05079079007443c08000c51180d0070070307008a54160100c0d44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907410350 1250 907409100 907409137
    0x515010f060c05030405060310030b1510030b0117240d0f0f1712010602060f2505041a091018030f02121209012601030b100915150203 59
    0x3060b2240780403120103c0340d9020400001c0707040d5079206c1c040c0d80038403203c1c0002040e075401d5240c00f600950f005032041100a07600103502c1296034442615440407a410314000c81d41500079030041e12207680740212094a41d014808000c0c1008000884e452000003162a80da002840c200602050f521070310b40141000001800540101d00301101301982d26205040c1c0c100300404140710403000d5080301074078520130907030140100203a81d41040515000700a800d030080d01c1d41400681116125082c0c1c40c044059134041040b10000e81c021400c0e5401007000e91344244a00742c0100e00648a980803150041c4a404210400c241480c86138950150140030524546c02c4179080d13480340995440250310480c0d020400c08000220b4480030310a45451048400059440d00c01c414000340070128015074007031400350b010030403071f10101599a10707504607a0000c00c6185a501e0b140d51102c1d031030120703822036007441d41440c0140b954604c5c07811261040f1041e8071030b440c0e1003600060040f41c81c1d105d0200c0349600c1d9034514 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907411600 1250 907410350 907410359
    0x61e05032802030f0708090a020f0d0507032607080d090807020d0c0f14010203030a0e0c122a06031f0f0e1f060807080a180605040515010f 61
    0x560055401100c0004201d003150904200c4400407000e8121144449030044103201141a85103426900101c0324142a9141c2c64026030340d0f56140003d80c0c001e40305006040c101c2c0c40540350715139075000a94005060302c4e5000e40700d05010640019100c40e2103038010340011390110801d5080f054035183d03a0721480c05c614004440401c4030160200400c2501c0c0c800080006100581c1c070a2018803125200d1810380044903c3c01102540b80d0707013107501000d421404450b0341c500a030790102c1200d0b84078060360070001d00c00030707100d5504d807600c0010302d41680c1200a100c03444c148102d00040101102e05c0039041140d030350b401002c020911809401c4035540000d414808148008400120345103110300404030740d11420b940f80310300100b05c2a2079100041101110b420300642c00780c1410b6418008662400c00031401740380003001070040c0780c002c11050411866a022a0702d0085907007081d038090841c280c2034103228507076080000040070309480844480c410703004c407004608101c41b01541201d180c1d552a141d0285003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907412850 1250 907411600 907411607
    0xa170402010912031211040b0f1309090b150604050901030212150c0a032007032001020f210405031c0b03010609020702030615060f160209090115061e 66
    0x900120306001010801146019060740f007841d03054020b6542c01c40407a0358240301400c8824200780c044030303544200b00c01c1c00440140c1c030803a103200340705002e401c0d60f81c6c02c10703819001c0b02c0e14503401081c00c16050280020070702108141e402d000303003021042580e800b04010100030f1b00d44503e124080d0045110030040004d840c000d0303400e4290b40710401c16149042c2201040e03104106044856807003242011a0800c0810b41c140304910119042c01e940701c07a00000c1d8203582041e8000c4c4c010090030003a4025104403000701802d030300c40024803080020b5483d1500c1498108141d080040b42e00007004194103d011030340c01d05114039002d00c0d04200070f185000581034000c90f50740440e100004055881e2002c10300d0f03e0301c00f44601c4000340f01e14040103845020358410036080000103005440c4c415070102001c400d503a5407804039151000781d0004165a183d0743c590084104607813000103540482a042004107200064001c06040460722074122982c6032241e030203403168400b8680451143c01008000c2104600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907414100 1250 907412850 907412897
    0x70501030c20060916141504080303040c0e0f0f07031107051507030c050309120d140a06050307090e0a060c02011107050a050607210f0b04021308120a 66
    0x30035141030000c1580003071071035102d0603448a204400794002010000003040c05e0201a1500400c921204c40303a5203008103010390f0040034400180b06e690000080e400130b0b49507074200c900411400058948910380350038050240c91071845140300f82010240010a4003004a410030720441110004d9400d41d00d402c0c5d07044004203c0c007011940e010380c2c10010341c0c000c14420422900c0a001015816070180b90114004095528a100034000c0c08010f000f489110318000c19004030206403815410f0715110032041340000340400c2c22a1050f092800000c0c0038514031540c018500362841030702103501d2a50349071003c508885100c0f818540707541003200d031600000d0f015044002c03828081d20020480c21800180d00c80158402d00007100c2c2c80d401004508100b000900c0040d80c81211420903004d260503042d42c076040713103c040c0701d48003a203660b442141c44440300661207003000700c401410031512004c54440002480500303001d021102c0c818140c400b19103017081e07001c45090203d2070342da803540b84140700c04000c144003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907415350 1250 907414100 907414121
    0x5040b0d03140f07140f01060f060806041103010e070e01090b120c070210120c020601030221070f060e01082d04030509042918190207020301060f08061807050103 71
    0x640410000c40c240c050701003c1c25004e4080e0240250f40030106000500d0500c0c10303030f504101e0303904060041080c2044d00340070108680d50f905104500341d840c10009802802e20748006048a01d001c0000301c0c4507041d03107159602c0313902d083c0c69400c10110000d0040d140014a40705290322050100a1000c069054044458202506110b11b41c02c00441b4cd00150201c85a00d50396070005600c0c10f05440104098006c00005d580d00d030020705055411a0080b58503048114004d402a00d03500d04400c01e451820412900107044540c01020440d48500c40109400c5100310210700113001c0e0340204a08105944807a03000c1444034401d0480618170544000107405c0007001035041c001c0070301007114280c0300e6014108841c0182c400c204802c07405044080e400603100914540684072800c1c0b814410003816018070303000051030310030002002078181c04001070321504c0350082d05942050303000240356442000300d03825503030301d541502e44550311109080791a845c084a004400c0e0f0018004020650103a4040c103500c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907416600 1250 907415350 907415387
    0x10e15030c0d0503092806031d0708030a03060b030903160c0914040611311a070308070f17060d0f0b0609011202060304060509070f0f050a05040b0d03 66
    0x10003030140090b0300c0e80380180c0709840e07a0f0800195501780f4640f40c0441c42200d080801c0220b50480f07001000191510a030003590705160b91210040c00064150f009100020241021078041548481d075054507608000c1d1406c0c04203040c800041001c0c90301e042031ba0300c03880d810070040d81803030512254020b2015480e8000c1e41d07510020700010030080d000c1d0149210303544412070fa01c241030a25103009005c45400440b4801682d8080c0502814140428042c1021481e01105122680240c1d100c02c0d0b034500c6a5884429005000041c2054a00010000d00027650281c4c594400d0340d6180b1005450b041c8110341d10f11300265025841c50001c2207681540c42d00400050042c128110313240d03546040354007007150103454000e65001000889d24008905034054882d291034201c0e0107040741d0111300300c0d010142c8000c01072521100000c10494003081058002c000320078a806010395514074000401c00c003070040310b0084004080128084c1850b0064148590b0003400741010010141c03001c842e4000d003044030320349a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907417850 1250 907416600 907416613
    0xc022a0105251a060d0b09100f0e0f01141612050403020f070b0a12090503220806060607030923100e012a02061e07061a0306010e1503 59
    0x300309401192011401d944900b01218545810101043e18600308501c500707010800c03c100b0309444414410500640c00b0345580007640315004507505058261200035551803900c9120503800d4010b41100b40341c0742881007500d140c01c5070207122509032601ea4480118210391440451240c000c1e1603145565514145040b06040080501e4001a240191400d50042e8080010705042c94400e024500c0108942d51003149814a408405881d101e40c070010450101e95a04103001070103410b0048031a03501100d84804081c0420a10b00f40d000d040e03501034001c0d1845054009003003820050100d40159825460b41402c40c2d1400e4083c50340a4036400700c50b0780ea070b440d541d81034035103407940d140d070b040403151640b01d508510022400043c01800140e811102ca590250317500585249080203902a89405a411941d40d05c28a82001050489032000c100c9110000441d40c080c0180e40e400b482c941c07000c4a007407003618503400c003c05a80e0720088c0280d1401c40c1205001ca02c038030000600075604054040c058460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907419100 1250 907417850 907417867
    0xb040f022e0914040e0106050310020301080d020304030206090906030a120302030a0c030618020927072d0827060a0c021902060f1c09060c022a0105 65
    0x400d4a4800d070070241c81550a480300100186290201900c034905140c0606001d18200402200503400749945000d20359a81011342418000c1d0000f2001d0007026046500c820150000c24000b54824403402041d405a610380303c1c4080d03c08000ca800b160740040041d410003090000b00504648040d089a074180718404820340040c115100b0003004070300f03a490068481c071b848420801921303030304180b10040610380007041c0140020071002a92901e036400700103850711202c10103e07800e54582c0e46c006046070104902e100403c2007030b05411b481100f0656074948000d01028581445a8186070954285030007a00501140c5128803055a0710404840080d8611901c00030304a80e00c404220480039550800e00030840592914000c004025000f0301c002d1100351079501c04200f0300f464800000f03115200000d040d01c030100251082c1d4840310502009c0000c184001d000e071400828440008803022800c0c0030001d01540e00100d80c90400780000c410f4000801c80e2118807181c40d11f201551541409028041c065 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907420350 1250 907419100 907419109
    0x21302090409030809061302030a29090703030318031e050f0f043809010507021509010e0a0b07240510080c0301150509130b10140406030b01030b040f02 67
    0x4842c0c0c0c0252504641e50400d406800d040a40090588071400503452100c00180ca0014104404030303080100111060075660b01ca90308002c900d01c2d9102810a000d0030b00804920104a0104803803103500c0c1001980e4642d0540c410540c1320b400d014004c60180d10a1980300480c500c1c010900356a03515283d460481d1070900c4000c01d801c082c0d110510b600340810284060206003140c4403030b080c1d0820540301c1c090002c119008590342100d0b001500e000010450a503203034094401e0784c000580c004c1462114285040110507160070001c202800901486203d031031900382248080c0658040038165031916085445000114058007811001c160b08402c0c13021501046104150113001890b69424401c1e1801008e80e1600d480c60802611036450001021445402c405070340d000c0745e0096444142d2a41e034800030700308640c0010405000001c0d000d0030000d0030706c2c086003108140c0380241c41c014000d501031000d0004071803990100410804da03800050002c070b4130712008154014403440940e070a00c001540480c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907421600 1250 907420350 907420361
    0x602060127090627150b061c09021305092e11040e0f0711060c0414060c121c140a0510030503070606060809030a200a2127030213020904 60
    0x80e41d041000c00c0c0b1030f20401940800e02000c407091740034207000300743c070260000f1081c1c8030f001c000346c4054501c0009402c03a00d000d90001b601c8590010410700703101005850420140c602258860f203640941c0181d03255084042c0301c914a114040c5a041d1500c0c808580200300500620860f003010407014800041d80314140e555161207028521002600d509240c0070142c0382002800b204009500700d076040125401ca4074080d0307000c42e900203074a17124111030312020031058410781401400034061144103100b0700b0341ca040244082522841d21003030342119000714004941031041d0000e9a00d427540c010a80c1c516040d080396422540001040c80c1841d07490b900c0034a0f680c800d440c22104203840d07000403c8900d40083c2d880341c0c0852040044d61400907810001010400803c10b11800c0410b58880702c19040707010403d851100d91b1005e007280d80221b485020121407801c054420000460700000c00182a411140ca044080d2210480c501c1c0c3c45d04650802c960b07002201e0001204070b5091101251903070300c03401039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907422850 1250 907421600 907421651
    0x20a02091b070c0302030d170c0901140a0c0b0601111f1803020c0306130506190f020a030506090a020705070b3004061401080c011b0b0f0106020601270906 68
    0x2c408a01d0700c4c5106050510104140007400d00c401400800d591301102d0002c0b0b0b07803100034249d84c65641c00c4d040005131a06044191000b25991010502552458011025a04003405103215156507500c0c0001150f482c584806140071541040440000040010038a03102400c00c1040100e2070344110008031403000b000c00c1c41600140e10901003400c86040601105400c0660000c040c210b001d10340e20703101d0380e0f080e000d0250384644030b40206c0303500003075481d900c490b02e80607505005540d25004000000c025000543d01c41344a5100c03400428140c440c28800c80740d00960000140450030700c0c12804096582110b90b04a40d8001e80801d4011214a1380c01c8201c0c808280c1e501d00703815420141401811038070000c01040c2c00f00030144c0140083c20300051612045c50003442e00406581210819101d042c42110004110b0780c18902403011444030051640d05840c00c540c01c48500340e0b40e031020f07000124100d901c000d43c41c0462030080360306c403007180d04090000e500910021910305c1080c1044071044042210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907424100 1250 907422850 907422863
    0x2031e07180e060a030201050c0c09010b1b1b12160b0a020f0c010518040b10081801020a1b051f06090c02010e03030105012d0216080d020a02091b07 65
    0x201c0c403007000038510800010300100c1800003494079154000c43d070394480b83c0c00064140600030034503102682003044050881840a0185c0e04296901c00a42400ea00101d00d2568151030260301410000c07070001e00c0c08076421400e18410403131400281404248044a8070003006800346080100d21a95130000c0000189021030010380c5da0460480300a0a102c034800c00c0111603004030104c01001d070781c4502900c80341c003070801880c00c900148070005801440d040748056001000154140791b1640c008506030310070003071800300d408040e1207481a035080b0f1017040c100d01d01081110107103000d003090700703021411038604c140304441145c41004c00c00803a080c080307506503603410f0f181c2c1020b01028849006980da00421800203000d0041426000c03516400305006050421840e4644e0707001f14410391300c02503e1401e400c0204404400c0302c860003921005601c0d80d910003003d80000004007002c000038000114440d40c0c1c054000629280d080101010025146a802c40b8200c400710841500610060001034030a42 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907425350 1250 907424100 907424117
    0x22401030b060603040b0c0c030d23010b16060c03020c30042105030403170a030b2b150c11060f0702100b04061503050411031b0402031e07 61
    0x1e00200d0804004103070501504041c020700c0f000034071449106802c2a001e42005481d103016840003440d40c000c00e05174104041c24030301004040d41e20b030500549a2203110000c42039a130f0f00c509020140c1d200350400d90707080143c0e020004000ca401c503402005074501610340980f0300548401194540f940d40d441e07000050381c1d28a02c9110486540e14040011114044541e04003031800020258030b0100708030660080e4000080c0b07808000060080302c0c080c0d0341c403110342c2500300042d0702414a13035000729440e8000302e490b01880381254542405000b00c036020440c0c02c12082000b00c1e205c4001c9121003501241c007841c1818582000e05454021101864465500c031400317003212005061801001903c0900104641c0c4240025540d02240006814401d0600451230489000200d4001c001d03e5000d2007202000c50810744d41c041d80358200b94022402100700d10000d1030044200740d1102e04840301d11941942009001d000d50401c1d8003c0c650010011507980c0308004a8504c1000481003141c0b1200080c2924 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907426600 1250 907425350 907425353
    0x804050a090c091502030702040b03031201030b0f10031e0204060503030f0706050a0b030706081b1c1505090612071701020307110c130515040603470702240103 70
    0x1210070f0300148108040c0305004205150081e40303901c2141030281c003451b101e6142c642903440810454080700346d4942d0340c200640c2d607410840d22107102542c0d1101101c120f01d021801c82c0399924000e806807070b004009400d140800040701c0a0315030000c2c8089030800d40700c040c00a81d40d87c0a101429543c1001000640c0d00c08461800034215000184040d00842c0b4002c203801741606d000a1110540b01281080003040e10b4840c0361903801500007007030103152400042c890492003181c40c011603010b602084140032841c40280300d0402c250982c01000d40003580030340064624541428954210071592007030b5030065031a01a009529044101842403da40005c2400041ca502a1118201c1d16406024124031501d4400040341110300c41d07c0c01081584403004119140c9034040040c4aa5034010b04c1003286a6481c0341c030a480c250900c940301007142101840a5072840c0561041c0d01420707050980b50305004d0720f4541340101030030250072542144030301250049007580c540715601c0e43d400c00942d07501266146 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907427850 1250 907426600 907426607
    0x1015050a120513020d321506011e0f11031c0c0908030c06010611030310050405041104090f06050a15050d0602130e1504020a360609150203030108190804050a090c 71
    0x110b00000e0b003084801805a00c51b4021415070307040034161041d1b41194a4000c012100c03c0c40c0b03009482c03039041e810982c0e407410756008100340b110940140c0f41e6008000512a065499009002216161130400e05480040380c8070741c0d010b80322504081c2401c0c814544c80b54103403403440d00143c4002142c0c0d405000140462504a2110910204a0700085182d0b1402c101c6d11510180d261007828080c5032a5404101000010f40a1852094010340104048816403d00c8a001c0c0b04800040c0d424601c0c1101041030112940034050304040340b100135103480c1e45840c0900c4440325800ca800c3e00c4d00341d424000000b100e58841112001400040c4130303001e542c05e05501300d51400d9004075001c1d104500c1000031815a035084800c40c92a0a00c04904504001d07035528181a86154442c000100e44403411002c21141d40052142068828011515521a002203016696071000380601820707540041f02d150b1400c4180c240021160b0720580d4201e050075500c10101e54150700700d0b0051003138192a81001d000710b40d40b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907429100 1250 907427850 907427903
    0x6150a090f050301020a21060302042309031801050702030a0c0b03041e021c050703080d020d0501140f131811010305070c2609091015050a120513020d 66
    0x2c0840003140b0700061100041c1c4001071000000420036154144400f000490b43c1c0508001c6401501c2803001c80d403600007104400c540130070030219400c0742901055070304000000ba2012141c2203d1700c00700254020300103450981105000700e0303261140003501c00000f80780c02982c400415908050646a060926008018401400c00c061185d40c820240c540560f440240038140c07504a1009022615518100b980c10f00809800140002d58000b0700f6a01c1d58099134002c1080b01d0781c118042080e42d0702c882c68802e0b5009008101c0e40d11102601a0050700d20f0100116514900159000622650007182c000480c040760345068900800f00c0d00341940c80e58142c0142544020940f03000da051818036600c5455141c6d0032600c1034010100440e80040d50401c41040311005035009110800c01d00d0200030003401c5811070300820300049182040040f51600410035036a05541c5612030341210b00a0341e00d84030080c000208042004a02c0c1100c00000d07840341c80d1784101e02c600a0085903598010007600e4000d000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907430350 1250 907429100 907429109
    0x1609091401111204050307020a08070f09021303110d060e0703030807021903050d0915060f0510020607030504060605060304060e012708090a17010212131a06150a090f 73
    0x9040110b50808456400e0031214414029071441c00d6035119400d1080c514000d200307009400c07080740c84010804d0880041c801048038240c051981d001512503501c5416805505412500290f0200e82400019110300b040c3d400d119010b4140410140a610761005540d440801e121103030700400014000d26600180050f400f01e8075000a160b4000e0302c600c540181441c0d00d400ae000c05c500030442c040c40a406800614040380c01149020780d50156554a00051003075200d07644010188040001d00780c1000038006808200980142c2050358850000760701404006100312021130f650f18012456956500285014a0041c070f00001c070303201d0702008503027121010f000101c2c1b84440f6190802001c4151030041c0301d2030b640040e4540d100d10824000c103030419400c0e04440310500c440f1900d03440101055010384401c1c0d4240d800214203449a01d040c0000084001010744075020081741000f44c10b6950001b03540103107005e8444a801081d44c002c80d82c40350040c511410008038800010002d406207269100d0207031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907431600 1250 907430350 907430353
    0x50703140a0c11061b010605030c030c090411031504080d05070e0607060915020f18010c0f02100e03030d021305060909041202010e0106120224030c070516090914 71
    0x300c103510007404406a880700100fa003000c4080f201c0b20341d25a0310503101c6107010111030404602102d81418082c006901070a8060b108006500b05035107400184000008000343c0760040d951074540300d400114400280054051040130040c0b42000c01d180c0215100f40e001300c2202e82c0f00d150002c0e512003690000b23000302c400c201054a40f4046640c0301803c80e1011a4003100000e0540b1b80d51501080c017006e03034444001680d1002c034070025810070000003443c00c1da070500c1840c0c800003040c900540d00441e40e26000b80030480090782140c018100051100c2c03513000b05062500501081200192440d8045000c407110660003054802001403c1001d80340075003000c94500b0301b07042210001c110f038104010000382c2912a85402ea0720b00302d00079030004c988170300f040c002440002d46502ea02061468820000c0f0b00070425000f690b0000300c0300044042840c4a103014136440d603115800504034a8011200030b491601480c0c50034082180450001d40041101c824081181d80c903504007028400d40b5330b91495041d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907432850 1250 907431600 907431607
    0x1d0301090302062404111309110a050a0c050706050d11030402090c07031b2613290d0501030501050906040503030115050d2a05040b18010c050d05070314 67
    0xb03401080440c0c2c04a10300c61114011500c5070f0249034184951050030740c02c145069403840d150320b100001030a84001c03462014010560710040d00044944651620206100074414070980b03501c140c000308800082441c089500005eaa181d160601c0340f1070381700d400401c1c000207102c80c1c52031860094241000b0041909415850a0740210305840d0000f0020003142074001210381c201030051100f03414900c40c2c0c4009140416461505034150a8502c8810042d0251840c00f150038028a41c200c6241c1072400944501d62482c003a1018100152103104140071914240c0c180b10100d410000340400404030423000c20603500d0340c1045400c40b4409094410550095020400841c2002080301c4c115440e09651445a45541c40111034130700074804c490085900b4140742d20800c0e1a00c00069017480a1114400c440742000d940a40781840f6520941c03c020105124140d00f00c0c24417002c0001c0e481040c10601c50f10403550340c83d181012440285a80440c9011841c00107040e44040e4016001100c107030380920303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907434100 1250 907432850 907432853
    0x40c090b120c1201090906050a05010803120c190903060b0a12080a0c120c02030f06060a03030e03100c02030309100b0a0e0403110714090f0705270a061d030109 70
    0x200d8800c505401c1c540018050105084200075003c43c0c0000c030b51900e02140300e5864007400d50142c203103400169212070800d8040f035003c5025110b01c504035003090000394901a01d140c0c120700c040c10b00030000c1410000c24400410f9051083c0300030641ca004540d40e0140160542c60820300325980004020f000e00f040080c14010000c501d001c2070586504841c003d9100d051081d01210703189052800103003504209030040c1c1c41d076034001148041040c802c80c1950406555801c0459076040c0486016601403800076040000c06e014146032001e07450b014064500f00c1160107400b8080c3c4d28045a0354006a20000800c01d0000c01405201401c0c8400c1c4828804001e445001401006240c09242e1341000300c2004641054019542c03c8130001c010015210140d0b51114500e80c6410240c00c21406130301014000780d103a01a00c03482a1050100c0d4840303a007031201143c034646040041122075441410307254818206a03681c402400001d107191b0340ca045104603580842a40c4030681d0001c01c2c082c3e810265401c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907435350 1250 907434100 907434119
    0xc021e0609120d0b04110702040e0f03030703180803010e1801020c150703022701090e062808030c0c01030b030f0a030f0e0a0801050a0e0a031d040f0e0c040c09 70
    0x1078a15035021041030f00c3d503140d040300c64024032103514a41d61182ca480c60340e20182020b02c0107440345da8021101080480019019261036205109903142650400c000007010303c0c0c0660311140d4450f2506401e14040403240c0d66070a5540c5c000c0c0c100381014507840342001000f10b07002d4409030030380341580002c0d81446581300c11542c6d2441c4c0e1010204640303242400182ca040d10a506540018400d50f8004046480b00581e2150000d44600d6041c0003820320540400c0d00300c458180c480c06280043e01380c1da4070703410001c0c01d00001645d8011f02c498414028000003903c0c0d0042000d000d16488030700c007800141040f200090100c0c0c000d1a4081d0294101c0e078103240d1041d030046508450180c05042091255040c401c04407502c0c00011619503202d00342c1341002c661031205602252040945030b501b00001800d04504541d92140356000a001410380040c2d4a20440c10b031290880403400900007081207090100158162111843d01201c183d0000c04003800382d141c64000c4800058207400d01c0e0707508504002940 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907436600 1250 907435350 907435363
    0x180b13020910090f2304051311060f07081803030a050921030d0c11070f08010f02030c030a020c28150c09120c03060e0a03110607080a09060608010c021e0609 69
    0x510110104e082d00d2040d000314181203012203170004208110624005130060b0071031096800990f0b09007120308082ea81810b06804031f482d0250b02030b0318503081c04001d07680c42350151300c9000c1249a0040c6032404e088503460400c0074040600306512030300c0e10307a19080d040c4100540c151000c90041520032860301103585010045412240e0744440c04102e00140e10820381d95006075880f071082500c0341d5500090310b551a1001c15007a600242c0c0280149001c6024070b00503800b05807800700b9080000c001290340040650300030061140144180c440d020201c0c100c002c45981441850020078141006020401265942c010850200300c1001c12409a542500811403040c9002d80c18002d02d6080b020130a202600c9903080095500c01c8052110405507a5106d4481403080000c4010910030f441201c4004400700d0094843c142c2c60703039202565929030511401504200700140c1e5490f03070750100492041c1081c0110b04818100381c004000d0340c0c0e80301026648241311106012019008001449100e00c0c000c03500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907437850 1250 907436600 907436609
    0x1107031202160503040602011d16050d2402071203140106030b0a18061a180906040e070f050310050603070506030403051902060a140709180b13020910090f 68
    0x5031203000c0480b0920300411101000f50041c400030a002405d81e5054201c01030b00801050041825030012010b01d1344da5000c0c03103000e40384450a51040c41141010303103070000c041c0d008408170041d1003400340101c0c80000f41d0f100b501d80c1c0d642e0001100018416031004503507060002d8582081038030080001c225680300180902c40800d40c403041d00c484190390f40398002c0d01401c40880004044400407007035400820251084403107100807125064101d00c0f8000681d10920640c8040058844002040081810004104a07802640c0c7c42200ca04140100181c0025081c68101c8c80300c414181820035242c0700201d100300c040389040070204003542c1c901007088421200140c4500d0f844c0d44480c03409544a01803160708506001251407600000c80d8001040c074000d4000b50400c001d04a0b00c03400c5503d01405c102c0d10100447c07410030040040c2940948021441c401002001030051903813000112a00161030701c54600c00d030080341d641c3c1d0a1a1401010071040801c0c00c03d18140c903d0076103215078200d4940724 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907439100 1250 907437850 907437887
    0x503150415090203030d0c030606021507050d091407090605191202010201020715050f250c06150608041a0405070b03060102100903020604051608120c1002030118110703 74
    0x25089400d00c041d0030000903550f0090540e44c5404102c41d20130003e0a22044d044000b03070511500044241c0085130f0b0626026103002140a00e90740c00206852070f82c000c6060f041290750b950881400300754001c1300c01c1d14154001d0003a001d2245004003200c00e450042d00f0591080c256004800d00084640f481682106c2c040550b040c21204a800184d0090050140140903212801e04e900440d00d240d6001d280308002d004180c81c01d50700c8a555031940103e840303410b1000d60317034401c1c034580b441d80c041c10703150178014812040403501c2d4118a0080500d05108c0d4881c2000c04c0000c81070108004100803884076032451545041006d10302078030b40c542c1d240c034280704049800c000080800e034035134401c0c0f0410840701c0718020306200040b12480e000356520b00464040e501405003500105441603c0b552901c1164100c0008000f4100f0741c80c02401c003544a50341c0507406104e9250742ca039403500580081c41c0284072461511064100c1e250b007600589035240e86080c2c0c201d001b00104000260030404140001100d40c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907440350 1250 907439100 907439123
    0x2010c0804050d0b010801050a02030f240301020a11120702010e1c06020310091506020606061c0e06060114071a04021c0506071701050a03020d241505031504 69
    0xa1080040c4a10b40040e078102d0048042103003440440d806190480d00e014008220350780d1900706107030890106841040c0f0541c3c0803400b0400c9184044100b000c1981c0250790300c03610700800000282264080b05c0035001003000044d400d01c51041c18414041405508641d0a142100a0380000c1407020702c1000f4070320807148850140392284c0c040307424850b0a40c2c0903808640e00d0404400f00000403100d03110b111010350a08840d2001d9215901d100f20489180d034000742a075071a44e504202054010030022114088410f024220904141c080d4000070700c40b0002500719400c4c01c800061400c420364a00ca82d180c1c00c20404a03002640b83c0700d041c0703422506841010b08503141c6200013841c800000c0c441d035000c8001c481044040c000701040280c05240d06448500c802e0030145a9220b880c6400d1041e580c6c001d0300e00d001000582801c481c010000361090100c80081c0c0c40860314000d40d106442913079643c10355211305581492400c848440050f20301200101a200d02c0c01c1c4240c81001d0008000602c030142c0320 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907441600 1250 907440350 907440353
    0x150509010e0723041a120a05060d02031b0316060503010905180a0c09051503150402030307020a03050309090106030605090a2d091b0b03150a0b0c011a040c0c02010c 72
    0x141c0c120f4200c0e805451001c4a1191400da80300c00380d0300b042c0908640000c0c0b0031a900c03040a001002c5419610004101c205075076620001080244401800c00350880c010b47c44141c01a5014480020782803903c10020000c01c03101d0062500c2e107803104041e08207110340340030144802c40d00641540c4c119558006d000c9007a5984001800e046045402c204403d0710800d0700e60003c01282c1d000742c405480c09810104025915101c950080c1c840c901e1890f601138000d007140c1195456085001644940083d04880c60410503501040c0002007560042c0d07020340002ca100107c51600034041d50042006190030b005903824040002d200460145c520106c2503940c111080e0320140c0a0b0490102d040e51081400c1202c10032020100603004c85030003155125120301041c50103002c6a05090151021902c150741903030303a04006000c5440301c881010394080714010001900342100002400022200301c000300e403280451101d40e000c0790089101520840c04e01c151031840a5100c04d045410039024070708203088003000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907442850 1250 907441600 907441607
    0x1b0c030415090e0a1406010513140a0803030907090b01020703120809010908040803040f05060a02150a02070f0f020f010806030322080a030f02120304170702011101090b070201150509010e07 83
    0xb00d6001e064601d8500b41044410030071a03100d102c007404030100c1d174416541c80800464142c0300301481402004402002804400c1d407640340ca1003101d1018102038602074841804900d107070411141070045901c0131505004042807801035443c405002e000a007005401e540e1050280000e40c40e100040090f0900018003102d003d400c6402c1813a0401541c6035900e403606a12501d941c401e0140c0c0031181c0c104840000c00741030600c21201d00c0100350f0b010b08880204415000744001c8050903540509400f03114000c0030a0b01c5c0801d41c08118480c6008110b016094418000384c0c02c448500141402440d6003000b0444d1070100866110700000046407103212074494081e4129185504450321510610707025030f00700751300041c44aa51810360380803503040d2550030001400c14030049400070000e80c6285402c0e241c0b00703034a20140512601c141400403c0d15010014142101ea11140543d00404841c1c10301450300d40a01c244880600304003110a03816041c14045010760206118002104540c00d0000f44620320 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907444100 1250 907442850 907442867
    0x190f051b060703081e07030e160812070201120e0105100b07030206060f01031d06060a08060c0414010e062b0b0303161b0f0e0a0603050a0b0403180902031b0c030415 72
    0x41c0d029817240c5081c1910b004000b00464154508a031086400400c000c4280c100ba08080340c0d006401444204846070350b000c51900f101e081241400036445030034000180c0d501584c1e400500705800001c1038a070002e04c40030f03011115400350424580030014036012135808501150f1000d819104403140802040048008180300540030460858070000d4461141c000b107611405220210380b080c1d181074944c0d00303150701c90031b00740c1e04000109010441041081143d00044029850505020b10407000c14404580c03e640109906034039581a0b07070010340c0308030030700c5a0b80c82800b00701541007210200d0480030039560301c2207003140300854822201d00400c02402f401014064403e20501c8040e190b520f40c0720004c3d0302c90318080e04400002460000341d480b045032241d541202d403c08020b1411078819100c00003520740150066080280b403002040c094150818080010101d205d401030b41c030302e04021050412071011030740c0780040b40b0401113001101c0000055030161452022820700b084211502a00c6c0f400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907445350 1250 907444100 907444141
    0x30f0b010e1e10120506011803030e03150711010e061e092d07051009060c0c0e0106050703020f010504230c09100509180717190f051b06070308 63
    0x141d007220f0f00d0005600418020101e00c0e011020710540d02c821005584111104d540c0c8004a50b0340381042002c6031040513003000c204409001d5402c0603001c00140800100c0c129070317940200744900d901c41486602407280c07600814000c000740006040c00407080740c071200b960b581d000341e14402e00e0100782411424890400034002c690710208092a584818185080310301c1060559401203200024090416101c2300c488203c4c1641c2d030398021401c040058603071031032401064461502d40c4c800031602270490013030a80a826143c4841c0c2d00c4200d10b02d0000d1600380641c2001400780d052a00f44000140c40410520b5207500d018900030a02000300300340d07440c203848118529889010740c01404400c01903001d040d420f540050f201c0c081d466980c41040304980400790840c0c6150b80c0074050401c82c8200400748081c0c400c442e10705031000c21344210b0a403040c840c5403880070b903070b03415070002c000d070800104020301e4801d001e84450b03240031102943c000038400e00540c400a420f0001820008203040c0d0b142e0031019500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907446600 1250 907445350 907445359
    0x207020102100626070305030a031a15041701060b04260604150501050105031e0a0608071508180703031422140f0a03121106010312030f0b010e1e 64
    0x20340d4601401513042001ea050060204402d0310740450307038038003040c0201602d4004009616000e02c11034103e000f80451529007140100d080325519031740c1c0e81c1008440d186511900000c1c4c6450030080c1e0701d0019030810040150701c0e0f140080412104028409540c11240031a0003d1661000e407a00d035640c914828250403032902455040004001326001d111040e030b0f260141c10882e581c0ca520055506101c1941c10f4444d0007585050410101102410b0300ea111041a60120300c05684201c3d26240c4a0550018200400c04070507141c80c00d94006d520b0303603001c2140e110a00031880c8400049803600c5082c0405810800304114884003503c0b40c10440304850301d680841d04480004080c02c00c2c0038400d42c010100e03a60a050800821441e1100d0850300c050350007401ca0f110b1516540c2d481c4900a01d00c0131100070310507040610100c2c41402c2c45090b008601426003442c0311700d481d24000342151079880c0c44668040c40c24180a40766644550410800f003400e580c6404000404d05007800036500b40c800d0550320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907447850 1250 907446600 907446611
    0xe030d05120f131e031b0201081306060504090812070305130b040819050c150601140d060e0405250e01210204020408030919080c10110316140f0c0103020702010210 72
    0x841082084c03400c403690295460034030010079180d01070060401000068002491040800c01030780e20b540d0240c40b810b02c204400903607640e907030001c102950088242a00c13115800b0a490004860aa20265000b07040d031030b0030082490000803250038098040e20145c00300419800003801c114292044608001b0385105420000641ca03000621070f0344072041321240c6000d640c0400744001050500f05020316016150070416a541c412842c40340c1c1c004442c100c0129450b08000903011204121060140340100090058184003404d104107011450504c1c2400e0082110204629191198140e054994400c9542003800216070244031010f180717000a58041d100107000501c0310400001031007820020390f04260682141e00040f500e91049129451081c0c210030b065928914014072100c0714003400381440d03000c0501285d601072647d000352140f121480d840300b0801043c00020740b6140e101041d458001c10074948070035803ca440302e4080c4005414103801103031003011603000b40310700301c056003003810108032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907449100 1250 907447850 907447883
    0x8120306010f080c0f0702040b0d06061d01031109090a0b0f100503120d111c0c0e031902012f03181008041118070e030d05120f13 57
    0x10254400ea5619011030710712401c1811042c080c3e18000c1c0310707480440d00e4a041030781c03d4082402d16804004201c3c3e00c6540c910011419640301c0301d40030300c0c560241c20001380950a02128100245042c2400d44501002100410004010440c100c802107420303101d8200350b4441d00e0100345405900c2c80c0080c07044146500f0042c2084c040064a0310406810403c00c1d40159103906264480443c07460342001e0a0041107080340401d49500003104101d500b0034200e2501a4044110303000039008628802220380329001a4401540025810510780044020380554200d09108400c107000e040002070600c00741d0341d02c980e04840c405281030345000703058022a84003400e008555440c1da000c1050702940305207601c9401c01c00d0819040800da556901d886204154070355480c1c05950000c0451480d9119110b2842c000302024a00d4805010301a0740d15900d00340d0004104050505102d0b00480e420480d00744000c0c00c0c228400c98845402035004502800c0d9034403282c100c0403900b041084003910190f41002d50a8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907450350 1250 907449100 907449133
    0x15050603090a060c0c050616051c0603060b010509010c261309150302011706220905060127050901112a011119030e0f010b1507030807140408 62
    0x22910f00c680d00c00c20082d070201c0000e03150f4212410b0f01400c1c1780e00420010740084050052031000303204a0410390b0800c01003248039101551007500483c1600e803540010410410140100900f01c202401d055040c2604100002d203c02d0600f240604029100700c8254a0560802202182d0a50048140d55120920b036010909072046115062500746410300f4035071802103000e00e00c0180c07581651100d400948003510000210000707040d80ba8045605101d107804031104090803541813202040210f180313202421b00506056050380014101c10078400564a1554609160800401d81c0a400a15625283c0021b03005001c22418419101e400191140110f0300d40210107408050102042d8440c607014100d0600740d88420060089988081c05004d00220304610050b030703d60700c0782c500040e80c1d1642c8402903103441540b00103c40c00365900e400904cc0c40c142076049004178124179070500e01d064440c0d50010407081e4010001c00c100140f0100704c05c41805c14904640007001d81c0401c540616800c404040f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907451600 1250 907450350 907450363
    0x703020903060112121101140103060618060303090501110a02090903120a1e090f02030d05030601111203010303050a110a05010506040e0c0d0210050c1504020a1a0d1505060309 77
    0x1407003403207030200006032240d258015401d21a4044001d10885c0300214080da5440c0b10001d941915540303488080e80202d0501158070300075401a640882e0403442c00310001010300d1051102c41c07506040600c2800482e8210827450b0440f0020b00c1c000a0301c803c0c03802da00c2c0c1000d20300e00000b076000b1100b000780840b81900001400d904110700c0b16000c407544800c4050412503041c0b4141240380000702c843c1c0300d05215103a000508160240e2209103640b4105e03400242092011518003000c00c030003000740b12844d688000c42c1c640000303007400140b8000210088010310b40c00705220040400c04005178011000307100345207a4051460510481d2050506441c0141c040e240458450380150b181c185110300380900041c510040c50030240030701c13199a00c29002c2c80900c0c01e6280b004001d00004224050001c082000f010100903c2c040c0e140c000d07420180f0400034100241c2d40071540c10084000b01d10064503140f82111500e41465500142009006202c03071107070342803503001e6640050040100310030035401041c035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907452850 1250 907451600 907451617
    0x10605010801063209090a1a01020f070e15060408010c0201051e130201020c1306030212011413020406180926090108040c030b131407140103020d090b070302 69
    0x40c2036480e80c0b20f110444030a140004c0d0028444542600e1803407102288021215002400721118505210100490f45c00d840a480c0c41d8030b183e5964880401151110781c0c0149401400d10190001c00d04600c2200ea039031140b4058820200810000304d03c4a20210b0f003601e0f10b51401501243e103c035a165481350003000c2920940002d9400c0400248060484260043c05801d013a940b501041d124041508031452042500724103502c1500c0404d101507551419550400c140039602203009421481802811094503558202c00d0b03050985403ca130170742c0c002d4480d51002c848003540d47c0e50781d524000500904000c0c3d101001c1603070740141c1030a03000000c0d001703900094055081c00c00b041c10f61141800d0304162080462403400028030120341c03158410800146c026015071404445c180d120b03204da5801c01c00903640c1100070781c3d040a0000411880307020006a034912040500328880c9400d1031083e2420a4032440f81c101940025801841c040503071102040300c3d00301da400341e100e141031301c0060300a5024000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907454100 1250 907452850 907452857
    0x305030a0606051e030703090b100302040f02120f0912040e180708121e030702071518030f060f050711070f050a0605160f0305090918120a09080a0501060501 69
    0x70204500f40a88216032440c40303002495800e0040640c18980316800140c400e0042503100c54010021036240482903014942400d6508005899441000304641d691706040780010300512640300ca4810000c0d00c41d03400380605019400550f12001e490b428451016503000c14036501140104941c81240e001d24400e060b0038041c0400707040c0040d11990b6a0703055204040d01540f021500200c503071805c1c0c025085542c004540d440c01801005a004c45603001101c0190041e030054208004078140c5110004159505d0704204030b040020003903001c04094903001c054a1071020f07003050003c200c800e605c29411b01d4001c0c0d400f00028204000d000f80600342d91000da1480388a10300022070000d064520300300481e00c004010f400703414903001d810ba80680140f608120a2003501002001144021104a68061007a03441903035481416082110142d00541100184a210480c40d078000600117400000025100300c80344e04c1e440d07040e034212450349103900030308018010002d543c07007000340c15007118050380c1d02600c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907455350 1250 907454100 907454111
    0x120a0b011e120506060f1c0312020d09060f0b0604030503040603051801050a090209011a0409050703110301030308100f15030e1c051b0f0607050901120203040809030708240a090507030305030a 84
    0x404200c0c00203120041c7d031044464285400300028056201200126034816002d170030500000709480031070348201c9061703a840e0346808034014075100c0ca2060280c0c41c82c003200d80c2c2d42000d08640b1490b6483c00380740034080505607513a0219240349624490700450b2414040240058904120740303a0240c031201c00304a0060003440000b040e500c010640359440e00420600d03041c1814036148049000d000d0140018003072654420341c684071915454002c601860007500c1d5214107007800c07514101954510b500c0404203c401e1441031015281d03d9404001c040c0d09403070041000c0018980940c10291503503441100d5001038010600902d030004050100c9805540c6555900c1020f06050f40e154112104000b0303058002c48001070841d4001c83c0a44902d100624141c203840001c200c2c030b5004ca0b4001c0c0d8082d0340a80b40414102d40d00c3c5010040031004d004804054594034505158034060354101c1322244190300001400a80608c581303a01000a0035000400c4400555480c28003038120381c01581d07100d00d1a414034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907456600 1250 907455350 907455379
    0x9060304240b010c0303090c2d152c04021303170306030c0907030e060c04080d1e0c0f0b150307080714060d020c011a120a0b011e12050606 61
    0x344200140d070041030f11184d48001c0aa9000c40013003410890485004041403004207466284088180f900c1c10300104c0c501e880d01d500034504a002d100d0b540030b140598010582c4048040e4000c0501c000c24050140040c0d2280c116503c42c01240d502914035034025101003403107003510203103174002c000f145e0040b200620b010650600000e10b07480116003041d01580030003040d00050420301d507941d9220103240390000d01d0600c40080345090803406d0350101c0341ca50021070103000c110307028800710418803d2810030f01d0a0072914144488a616249403050a2142101d6104140080051b240f0030fa00d40c4010701c7c0b08545400030030417032024a40e50b10f2078002c0c07246d48000310314840c1c0007030b05405407240d403002d41084850200402590341d020365144c18800d502032100c43d0540b6024052100c60006102c66040864062028008880400840303a0102e9001c1c080d03142c0415000581d031815505400000a44e03404030301c0700290308408030350010154442d6549410107000010442032b019100803030f4040c0c60340c42e15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907457850 1250 907456600 907456673
    0x9030f170606070b0414030301120c0509070806120a080309030d0e060106080c09120f0a15060501120e070305060c07060b04090b060409050c030313090606030920030309060304 77
    0x1c4800c141c00610800c1040c01058640000aa20500c02c4070521825040416924290b81080e07000a103d90b403a10008400c01c801410700f0005000140d8841c0034514103200020001ca20182556003e00440008480481414400824016040100507076a0700b0078104180c0c0da54804c8400b80f003102e19169507600600e001041042c12a4815540c802c0c0d152030f00e0b240180540d100d4000c09a1026064801821011041c00b00300303000314402e0f000d09641d01203030810f0707031031003007801c8400441c01d00d861010700c07040c0e804c1058a060202c00c41c100050b802d0b082c1480c2490007035942c20142192140c88100081001110b0003483c0c140c1c400d0405204259140381400240c1e44803a0004003000030500002d983c43c01c007a48081e4031903004504881c41e072031400300402d04540c001c600305201100940818082c83c40302d40101e10040046107400c1198000d00d44842c000c228040c2c0e200c00359031541c1340c0c0c0003100360703000c00958604001c014640c540d01d050a20b000b452a44101d000a4403070949902d8407900f4000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907459100 1250 907457850 907457897
    0x1813091505070c02090708040605060f1507050109170705070506070809040e010915140603060103030e060a02070b0a030f0c09140d02030f10150b0a0c03120e0109030f 73
    0x900486114200c8003202150014040051184081003000005180036a1340c44416130b0280034a61901030807801d141c00e05405980004020300d00400203440d105e003180e25148400d045d40c0980c00445a12600c3c01d28280d03000d8840c2d81c8014001c80b403507001c406103045480f401440c440c1d10410455920540d00d00c18401c07140201440548001c02c00e000140050a05070400380d505280c00c03000081450b0030350b440c400d103881445100901141d64419903051035410804654000c2011401444190701d0350b5001048400301c8100d0ba40244008034078442c00a00800a400c042d003012003c0da40c0f500e6008500030020280351949d81005424194900c00083c018010407058410203415112100c1d0410188140611007007403c903014419030850301140d04092214035040320000c0400714400d0302d4050000a400c5058108540202e4100051110f60380c000701c6803100b0651604200c1901c400030107181e0001c00f40c0f03182c1101d4035400d1900003020158405142c0c0c04034099030b10398503942400f0804085070b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907460350 1250 907459100 907459103
    0x909170723390d030504180e10020a09030b0910240b1e040306150f080c0d230a14210d110c06010e0109020304020906150d02181309 58
    0x220380d001018144014442075005201d481d00c0202d001c000c0030008106035400002003980040c4012505004000034040c402421040b1600c0900c2140d0600e01826181c00300b00e86070251195000540d030300902e0150021310000d40d00203240f00031901d44924415201c1100d0079064811030300d040c0c400f078480711010707080c21814000d0401c10b125043c101000c8817225801651b4008400030917042e14071112040c00300400113188600400b01e20007044910990600c040c40e0030155074602c045009100000000400c001e0624040b2405403c09825041c806152540000821504201c4135005810301e80b00040d4021090f01c5035900b007008a40001110b51038114000024142d2041c02c405010008201400380c0500c04c402000040c0340e50703005e0070694480d0701c6141d074220140c00c0100108020b0f1503000880e401020006400c0d40b40d480e041c3d002072181c107001454a0701c190002070701e2001040c0110155102c6034080182190345105500b4111b00910302c034440f5130303c29078000c0c0d003410700820140241d07030055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 907461600 1250 907460350 907460383
    0xf06310b12070815100207080102041202040b04020a021b04110d050907090c0509010c1703090a05010b100503061309061a12070f061d040c0804060506190909170723 72
    0xc420804c00c1100c03801381c50350001d04610480c000819000740c07c1c401000203140014480444883c1403052000fa2028090300610441c4103001320312402c2d401040400f0107865024070303144444a81c2d00090020a036519050041c4500450502d04000b00760707200b1070042c8801340495207a95905c000c004261a6035103000e100041c001c4c0802c00195000d10400f06d03800d40f0406090307003010402580c0180c150021141d80b01540c0c4016030000070f1000c01e1044220030b01c000e440741c0803030201c5038030060b090348400b038106030084400008403d40f81074030f648540d040c0c0390b008405004040080fa04c14000b0b01507821564851400c0003100e2500440014500c412a403904180c4044c4a140071410740e17000d402512090009100e480c6001425030355071043c503606124503250400c4c603090034280182110401404507000300313692804980300560f80083c0724220f40c030f8080b020400d0600f614140c0903100180b488000710410119102c0100302c01d000141d10200111400d42c0c40e403044055040d90785000c0321300c0b1240340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 907462850 1250 907461600 907461631
    0x12070f03180f02043b0c10050703080121080c0c0a090501081902090711070308030c04140303180f0103150f030209130807021c0b0a0e0c0f06310b120708 67
    0x807a25501003006031708040e03009079510f003004040480d500600c40c071152800110005594010103402c444400e015090101c00e00d0515441c040f41b003040e45001c0c440280c03c0321004500f03480204000c20148007500406410300101c0769980b0400006400d003030249001c42c0c0112440401e840c5c20a0f8851407a90b90020021f050507224844292280c0d102515084214022400f020010a0301d01c0000c6028a0309011400c0e44c80b440c0000a401e03d01164024034070030b070001c1010381c440100380540745802075001c48084502000c107000580c006d0410b9a030500700c40300315180004550f0620030b8820201ca000355814a400e5440c10660070f0300d5100300700c0c02050200280030007009400d0414490540503a1341c0e10102d8a20b0950711500403c0f1011542c00c1040c40c2c40301400c0d100240140000c041c54541600c520b07181c01e0284d8001491402034142181080f0703240384c1510020340400d107092800c1d850b281503800c9880d4495070780c51741e1507000400103e00301c140710011030981840751410741c1c410b15108544024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 907464100 1250 907462850 907462931
    0x50c03070f0c0503030307050307030c0305010803070b0a0204091113082103090c0d0b100e07140313060207080310050a0302150304150606091a12070f03180f0204 71
    0x9100e01a280a5070b66040500010810351400c10055002c0e51594580315100e181418000702940d00400c41c520415040030010002084000b0a64150b50b900030844005581c1e80d480c12002030040781d01c00e03900241000085c03190210740303000070150508102a1f010020f5180c060241d40d940003442d0900954903280c4e0b526100c0c4480002854100503510705545420f0100380004000c4150361500395404c40e1094288200b01c001d501c085001010460b103802c0700c6140102014181b001182c182c40346507100040014100c0c14203461010000307a11800441d261800750624410381d0300211422003405040810220381340c03403c102074508480d801061503024840c1410403042c55000603100320b80a8142e01c544412800850003510003800c4076a0350f0382ca07494905000d07028072484c102c2c0c140a04040400050305c1004a108840364806d4180c10f010b07040840002040380100080034119505040590b0160204884c4104440390179000315820b120581803f0900e03041c2d9803a507289448034985c1d5124010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 907465350 1250 907464100 907464113
    0x714060306030114400f0c051005191106070c0c1703072f1c020436020901052403010e0f0601021c270e1806040309050d02120d02011506050c0307 64
    0x3001e01c1200c0056030596150f000c62700040d05120b1101c08a84041060043c50070302e0850740a04c540310349850b010303416003030514035116600503207110100f10741c0d140350300c0605c032101506100410790190b00340504070f51846180e860383c004c030000711203506d8800900e201048103580400002e1011a100d60100c442d0700d400c000200b80b24203803400440580b00711281c0035903554400c1d242c141505180607180b8140f0444108504074500b07841c0010240001400c4000d0b843c1c0e200034a0648106507488012950f41c54051208800c240f004444000c1d0b0000010072500f0390040d0003801444c3c003000e51a4292903860040e6212441e081c1e04c01100c0c1082d01d2008204c0784142e03580c00c2c8040300c0451113403400041d1040e40c0728812090304541e0322041e2203810b02240a1038054044c83c0541520040c20040c140307075500030440c000302d1161501c14980b0354160401d5503500c00320075490452800840e1a140c11400002c2c0c080c200c0e4003e1780c41041c9040c0e2000139040d004000b1100544401800f551502089640c0d45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 907466600 1250 907465350 907465373
    0x2060f0f0610140a2d0c06050406021603030605030705060a050307350105150319020c1905060f0c211305010509061008071406030603011440 62
    0x1901005882d4880045400103c030081503000025a10707002080801c4d50300a01030003d091815040001078001c807284035500c2807019500e65401030001c52181c8541c00c060020b406648500c1010030b441c554240200f58166000c001110b20540079503e050b13984104005040c00b030440c00901191003000000da01d81c1c4505020340b0b665034003c0d14008105000d808000c190f41030400107035107070451a8014401c030301d0007207080c040c0c2c0b10024568901d14036002c0c0c0181c0705889200c000110031a000305506800503028801c11a29851810740046090858108242c0d0382d0001d80d61801e08070780c03002c00b0440d00d40a540c2107a880240014001c0580c1103050320313888404200500b210800c680d510800c9000400a01a0320301a50508000342440d04000c01e607980358925a40c0f2158030750740401000c001c0c6452220700c200050008868180d12641d440020a01403c2c01443d242a400005010010f1400e05801c28500074800c203030382058180300c1e6411440703182c02e8100d07100640700031143d030440004540c0c0910 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 907467850 1250 907466600 907466629
    0x6060e250c020d02121e030403031112090d0312182616030c140d020d09050a09050a14040c0911090a030b061f0507120503070c0201031505061902060f0f06 68
    0x844000d450441200040c02d501103001c0c6c501a000007804205040d070165035a110001200080c216214407425160003078420884c40390301555896509c030061501440003240010010076003400350704007400e8501e00303030032401404407420303022080081c1018181886088422816180c800d2600140c48070b441010323284c10b28100c040001c3c441d0410002151900202c1441c1d0810004008d43c031040c1c080681425000f5a241e0108071524070204499502d070400c1104542122500140ea030301c42c3c0300300e0000b41c01c140035080c45c0075440c2400d1008104101ea5207000304c60103501c08124001c03002103181071238481d030150f1550081000b1000e0002c036440104c0b41e41c00c5180240174401120070030101900f6940c1d016011408200b0108025060100600d503500c0c0001d06490f01c1c03403a6190054001d01a1904050003a04066649507144c00d402c102c0543d41d0040c102c01030440d42c031591140d010388410002e405541c0014043c80004c00d00540b2003440c264012403a0317102c681d070543d4814040c0309554407030408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 907469100 1250 907467850 907467853
    0xe0702071a0a080a0903081f1d01080c0d150c270e0709120b0a14041a13151104080f03180604080d0f0e040507050304020901060206090307030c06060e250c020d0212 72
    0x100040c01b141080d400e0010040040271450141d0700d0b08484a0420301190400d0b401162215640300c0015081c0f8010500034805d507400291200b65903100f215000c0340c030841004103070b43d11401404401c41c80e402110484a420181031896924030100312214226440307803000e120040e840b20000918502d81260740610b107031074000381101524200080401c41960103035104a4048040000740c003007002c5641d031002032031f180084c01c009217a45441074200d0407201e05c815140d80d00c10341d0f40c10fa83e0312401c503401008031a044600103a41441602d490303910442c802c0080001610810350241000c00a03181219030020152a940b0b407505800d9075a0b590aa07245000c2203000f40540c50103036981e12842e0701407180d560b5642c0c1c03070b46800e1050000303040040e00b1110542d44000100000003400100321544942c1c1460400365541181c07030310802602064215148488002d0100420b84154150004884241504c03407154540c4880c403d650406170904081c3d08010345002d2031000d41400f10940c0000c0c00b03201b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 907470350 1250 907469100 907469161
    0xb0618041112010e09280512030a0b03060a091101080c0d021306020d020105011a161505041b050d020616020907020d0224010e0702071a0a080a090308 66
    0x81c1180859405050b4991103444041c005100005805100b00d81c0b00320510300510420701e20100444204d8003907100c03003403e004219074140400c4014090190001c00900342d0035200d0410f601da00b4003401e5070a9025000e41700d100c1c005a4100128003031306e204950003484100c0c04003080701c01100c130080000d01440201c03104100b00c8003c41a10300c01000c0e03000958596610550400700001e04180369440d19400310f83c10800140001000c4c15004c4001401194629682e14401d4030708040594410320090003241d8010f4600c1c200080540159210780d2156021801d02d61000000c0407081c029401741c1d0350480038a03918040142400c9000700003021660b2203000220020358005404454120780000068005092520205404204824070341d10114640c0c00407010b0010528908201449110300305c400d0700d408500424001e200c0e040c00340a1643e600222800184a806e40d0b55118100d00400295910b00107030304900d42d4420b0491840e03040e80c8942d811340754290b03503000684086184054081101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 907471600 1250 907470350 907470371
    0x219210203130e060901090917160b010e0f07052b060b030a0b010e0609090604090204020702100c020a150f0c0303020408150f0f0f0c2b0905010c030b061804 69
    0x81c035005008100c0c03807901000600d800400c5c0502c0a5060344030a22440c01c0c60041d0001400d208444280e5861503035034030713459440b02c01009081c906004000703401d6821000021581c3c01017000c19500c200c24404082c02d20b0707201d02904440910401d80820240c20144983c0c410340410040c1c10035030b0303c00c15a0301141154440e000c4c0d8855600c2074400074141d503500d001c110469600801c20403483e03002210702900740529080800c10380e2034010201c0d44195504d0240400310340d12079056540054020f0318440123200d0040c030150021414a2081c0d106007440c031030004500c0340901140481d034031155501c10040502d16003d441d241c4807040704506244c0c0a03c00030a5a220810040769041080c1044400a0405401d0144150700203030240709240500e20400042c0341c0030100140c2c110800c00400c0d5138079181e1000080006200e00381505c01004080c01c0b8441c40034168110302645802071000b0806002c9440c000c0d41110b542e0402c482c0c1000c014003152074400205080d2150342013000d4070200703c40400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 907472850 1250 907471600 907471627
    0x20a140304030c080d0f030e0c090604110a050c01050a05011d060111011a120102040506040302130e01022106030a0213022203060c0906020102090901170327010219210203 75
    0x1544c0280c801c035072181401814607136200340b0a1413504101c1c10200700e481e032645100c0e030b190744070140c003d400340e1100008580f01c0d4950360700400d003440c2c50501d91a02c940f80a50000c180f81d0108208110701e6007448007192603600d051103242d040760001030440700c80c4424001c2c9c0d52228040200005c0c1400661803032011114800c5c007420f25160010714000c401c42c159001003142c615404071011582d07030320600090060380c03960800c07107095070380499919482ca5511001000070b071407008806c0e4069400410301c250407112144c14840c0518840180200d66500c83c01070695503405080301079031110100303500f10b01c0d108541d4020b19400c40100d14100d1a4140c1034050701030b0752000e500484450703607110549030324140d010500390041c010510080d45030000380340000b90302e61018001e42e6512480c40b40d00c2c0c4900c0b0f204100f11621415084004800c0c9000c62041e03002203052808901d016000345031ba034403a01d02d40c58076507104995000f1500c103d2003041541d141c1c04082420800815440200510082c140380c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 907474100 1250 907472850 907472873
    0x180207061401051003060b0a05091207120201030e0d09090506010e12030a032009040f091b14010306080a080307210f1104081b06040f180c0c03020a14030403 69
    0x800ca03007000c0036940b401007405003e2104c91106820941b07401410302080d6295801c8507035000e080e00e02039172240b02e4400010951140f5004024040c852501c0024105001045a00382c25000742c0303080200d0507003409103645544404500c8000600210400c0c03010408035404030b40c00400c103140c1081801100c0010544101d40054080515032001c680000c0803685070281c00d4610390403a15480101c0644110f203a0540503602e4198070441e211000800d184001d0340c82100016001505403089201d0040b0501d5215007d000d0200000038142c840b00703041d40a0f0013240d0031a02610010800a08a40c41c2c0d402c0b945c2003e458502080b5100c0f01d01071501c0e200809400c6402026940000c1ca030060241030030844001e04400600c10b03005100411a0380004201001942c0e00003a21402084194000031071130b01c1250841e9031041842c4102003240a0007207442c07003c000301084100446000540103842eaa099481c0007001603002c42c4a000005102558116203c104241144d0429451b569500d42006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 907475350 1250 907474100 907474121
    0x14040b13080c060a080403140d020409091205340204051e01051005030105130b09090109030905030724020102070b0a0c0320190203130303090810050c030118020706 72
    0x21401500340001c80d01405101d01070082210700c0303072500910400203018010001c0001e003d1140c0c081c84480142501001c42e9507e40c0f4040046540382c1d01c0e89188401000100010b03500000362001100340c1600403002c0b1980c02080100345019440c91204401d0f004e071070500d5500b1410400000c16005840720300031302d4010b9584200c0c1162903403801180500c030840c141c1c0302a102d20b078240c10440c520380d082401c4070706407517094901504e11114038000d1005441050081c0d42c010006004008d043e050640c4140c0c4424801da442e07071800d0383d4a5081650b0b80d041801051f05001c1c940c1c1d540c40c00c0c0349100f001c2c0f43c00500c140c0005400c100311615038003c112400c071040c0f5681134580d00702c5d9090079418898202034a11f03c40b003070010510004c0304c030405030154280400140004ea907183c04e01500130000d99112084a841c000c52040c0c9a18004201c00d84a1203821503030310031059965010b81c5d40b40107081c4240d4800c00380a0035686444008004540c03c4522600e165a00708242008104140140c03003000c13 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 907476600 1250 907475350 907475377
    0x110c190b090f041802120705011d1c05071d0f0604020918190b1e040510172d190606031a04030e0d021309110904030201051605041514040b 61
    0x44d085005010359070b1454844120b603900004070074007650303810041810112014800b1241e80000d0703440807401100b603642401c001558084809010801c0005028055076201c004094140b9a40c81160600e00000d03180240b041c41c0d4a070001d0194100340c1c0c0a800c003281c00034415814100b000090141c4410103891a80701140d4041c10914140d00c0703800b90590311582598807004165428603500d4461007041c80d1144141c1c0c54001150782045407500302405440c08075092254910179101660f07864003994154075140940c000803081a600141e2003900481105c8003a224a11409442c01d00c000711102040396a11f59998020001c1142c101d00542d0200181e0b0102299007030509000e00761075045070055110302289210b10006840c1c0224020b000340a05002007441082441e00e07080086512500e10b411080c2e0400b00400d1540c1500b085005852800c1601001c0300d103000f04441500c2240100c40003403848205140240e88608070030120001119410740c20140c407a10310201607030110344080d040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 907477850 1250 907476600 907476641
    0xb0a03050702010c0c05060a09140106180501080705061209011401080a0606050609130e0109050109030203180a0608070813050106080a170403171b0d110c190b090f04 73
    0x42d80910070002c0075140e0f42030418141c212590386c140e50714002045043d0f00343d1200301c95420868669960307260554008001e2096130b80305d030754140b104000f03024007020301c1d8140070000a85000c041134150a0341c0c005400245040d01081541c0c0a00354007030048245990784000003003541d4a0256128041c00c1d103000645400501030030602c007524002d4200301d20400080110640541c1d40d4a00e002c0b6541c0140710100e4800b056140560040200001c003a00e00d50811001008041e404401000074083d0007103180000704100c4107101c2c280419002c0d00021800c08030205a20138041c500007580300c80303a0302c00500400b0380c5a46d40f038295160380e40f2241c650362007a200c0741e0401c80c016000c00307403442c0450504d6041c5442d580b21358507980c420001a001c001780004008440317048860f004090f03071205408450031412001802482c1c8448858009400d0041d01500c0c8001e20f049540103400d841c260340c4602c20b4900300701c2c003034441c3ea12840903213521a2001880c854030361182c1c01200c4c0720300e152103011080d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 907479100 1250 907477850 907477861
    0x307050613080a0c0510020d05030a0f090230030f0f07110a030501061401030e03090d020102151914040201021c05120a051b0f07031808034b0d060b0a0305 68
    0x981b0b40ba10072201507401880180051544c044140c980c070000b119804108900b401c4a5603005007585c1002941045020252060140d1a50505109001d40640361140d68801003200b68580c003440f5240325812000308501c40340c0301c50540240098900034002000d2400e8234400050030018243e0003194980d4685d5000c001c00141e10b0840504d808003800c1c284030400194a4582d101d204480754140f01c3d0340c030a9200030035a44200b20314119400405d0301d0001600b4104203640d18000c01840400149003030282c0c4000500b0322581d180d0050380d041e00101810034848680004140c1e13100044000c002c01840140c03014442440c0320f60003103494007800200f030b0400140c0050041048244401058402c01200ca402c902d56400c0f00c0780c3c00d03050300c0c00c66821141d0382205017003c001c560026a15120102d01030b0784407000c4120810042030b04d03142c0d040c4a42e1f46030032001c10038014401e008200d565092829041e00340000002c02003107035008000030303840d41c031000d42d80c0150700840c00610019507640c0c01c012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 907480350 1250 907479100 907479109
    0x906040209060406050105040911040b03010611061605070210140d0207020a080706050a030e010609020c01021314031207080d0e0616081015030e030301090c090b0403020307050613080a0c05 83
    0xa0b00101d0584051007220300303190020f86035100d03c0c403600d5645569914200000c0c0c2c885826500501011511031ba520750f0346d103400800642d00000100c001d40940c0303010403452010090044d181078015140c543c18406103400300040d814021510314284586c0140c201030004501d0000c1480020300d880058503403016005019804070070350000726a6510114040c0941c0340c0100544101880703c0c80c1c0030a1048000c213500d80074003065400003945600104092140043c10340203040519060b00102a5481c1c1d40c0020095180c000d058464064020200c281030b41c1440070b00501180c0d0280822900d0150840800000c407611103003d195650041c10030b1120642c1c1c4803040e015050041c0c504000603003043c225440501e9814482c0c0c00c0c1243c0700d60b00c0c0b00350301c47c060780050000300e4400040e65125079542003040b02034000c840d504e100187e6086008904201484140ca0030f90382c0150003404801d00382800e0009980c841402c40ca0a62003500001500002c100098001c444c070451826161510740001d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 907481600 1250 907480350 907480369
    0x51605070507261e030f030a06052e030b0616030212030408030709090902030c040902030f0601060228051b060f0d06090e060421030e011119090b032d09060402 70
    0x802c8548800d50080f03013404001007034442610001600a540307448903034120000b029143e1065070040380e92103590030401414803111000c5251030302c1411801006d41d078203c00301c5101c0360f507540c0c1c482c1c0306000c0e0540507185a8140003040b80700c0d00496000011121a240d20ba070030403101202e50a400001300144c440e44100031100500066509020041c010303800a903d03582c002e40060300469440d9000d20075986c080101c00002c401e4142a1985540c46035402901d411408281503050030760a580b64800e4800d81c5500301e14113400c03001800780c140e1100082d880074a041c00343c03280c1c0004240f03c1c155450080b4402040009081e000016415280c80c003001c05407100c3c0034031303171000350851010030002c6100112528042c4083c01c40c000204c052010b011f4004000c248941c0100750710b80b82d481d110035103050008090001007941c1c0d010f403103880c408c01200d840c0f8050081410703010060011401450398442c04a02200d100c1c20701d04941c00d07007000c05240081c030031580c66051b91300240030703c070030340c205003920b0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 907482850 1250 907481600 907481623
    0x111f0c0e010206040305030a1a13060504060623030a1d0a0201022a0f0102030f130314070b04061b06020c030d0608010e2d0d0f08070305160507050726 66
    0x161083e858103031000381042c000142050310f010340f6990b28404040103210108601c800040030011580000000c8000400b6a030181901440c6005070110341c4030b01600d0390300700000101298041d00700c0e03801107100c3c0c250400340c90388ac2d02c1c13602c0325044240d401c210000040c0340c065a00084c84c41824600009186c040345030b00210f009040001d07030b41c0c4490ba00409601c200c010035240e1a881c51040c0004034030310321945003070481c1e00314049001031480a90020700c000b02d074051110068090326940c1490307100c2d0114864909151810030003000683e02920b054808062069601c194a01840d12000c3c10303a8021400c2280c40e410018491241503101c0c410003024182900c0204288000030030416945c4015800c00702c404036000356068980f00b103072051000d045811400781d440701140b942c0c0190250b400402c00303002151901d030005080510a2054600c0f80d140e407010982013403020b00080d5002d030b2041c4030a40e41340c003c0e40e40106410410700f0728120500707152100c150003204010304103814424034500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 907484100 1250 907482850 907482853
    0xf0a151b030509010c0f02040e030a12051e150603151f1d22020a0f0e0919020c0609030c07050105070803010506130e0903091c020a06111f0c0e0102 65
    0x103120000c00d81c00000d8541d141c00a0070158031913030090901020b11454110001e61050804d01a075283d070a012000e4000b003029600c0340340c1c0c000700324180c0c0c00598204954400324401c00304045071602c001c10000b290440b1360268a01c1d4406a0b440100e880c2c1d9008440b00c5140711002c0c1154561403c2c0303409040101206440030541405454500401c042082183c07e030b42016004464881641c841c0c0c001c805400fa1f04c04200040c2c40c5404003840690449081c01000c145070307040301c0b20aa40141100e0180800080c0550740c0341c0d4410700481c081c403011980b5000056424416111010005c10080780101541b800654440550101c45e514240c8190030850402c1014400c0b0000102c103d07058a0549104071880c50f1103e074804482500c02030203038441c42c1020f9104062210316100403005104910007510403482c488000b0118504808452100940041a041c000c00046209071150f403070403150842641e4030400d034000c03c00800b05042401120140d55081d954a040341c0008004103000380a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 907485350 1250 907484100 907484147
    0xf06030f0c0318010f2f0a20030a08010302130c0207090e0a0507031113020406170702010209041a03150108060a0b130c0c05070504060b0a05090f0a15 66
    0x10200c004040e000303044800303540008000b055943d524041d015021481e03007402000740007940101c038000f6044d41843c0340a00300301c030100c0409022102028085c501e031400310040c03421454540845030f64400c000040300c4d09101c1107038044804402e02c01000b42100d1582c580f44903504500400c204071440c00b0256007854681a50a020240c01041000c1200c0c0327450f0002a2007a50b182d00c0304d0500b909608001c00c60f002d4500c0120030080c4035100300c0c0e031841c8251461000d1031480b483d008224412400340700c01003401100b44250800404100d60341c0a40c4620016003040303c4940450113a441c01542411002091204040c5908042041c2d11440f0007000700c201c03155140442c102c0d2541c0c0c01a04c888401c1d600c0700304c0034a4075150881504641210344000708503205411000400390360801000300c41030f025041000449180500400342900c010b1a4031030300d003890a18007901c0c1540704040480e0000c0f649140d400c1c40750b854009650052032600d0540b00080007600d0014501e5401086004c0076407684c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 907486600 1250 907485350 907485361
    0x150c17190e0d0f0203160612050901090f02270a060305100c1e050408120d1b0f11010f06080d080708090604150b0a09020a0e032a010909090507050f0603 67
    0x920010415904070604203401c0c1500c1c0017003420a03000c5201d00e0703200094a0000541c8a80c030202c010208061030303008202c00c1d00c03000042402e0700d40c03803603014115250b10902140036103040f165a41c0b018005034107080c94140d0f1401c1d121055601120086101a40e0744803c2041c0070003401b07840e550003002c11040207101c003d0310f0082c0921801c1e110b07801602111010110019000e08116409031288000b1200c0301032104410050713035031090700702c80300c1c05042158841100d02c030548100000310341925a040c29121501d400c032000d04103080384420940d04c80d45601440400362103180060600b24010b007003100180100944420006440d210030050240c0c00c00c00c1444000c280c1c2034000f40d015400d0009001c01502c0500902b1041180d140d00240020340040c44406503030040202d00056201d20070446500030806841e51050201d0015900690b2001c03d0020ba80c0020418186414106040030390348841c003200444800300c40c101d0311381e4010f03d418041d5203042d407800d12400c107048032001c3c95890170 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 907487850 1250 907486600 907486609
    0x91a06070305031b0403050705010e030a0302100e150406020702010e06070b0a0207390605120402150f130f21020409022b0c0b03040c150c17190e 64
    0x18034001504011010000c100c55800a100d00b02401c0c482c030300941c4d1100e459003041034650501e0312903e80890145584660a418013041080401d602354010340132101400203910060301307031010303240f2480c020241500a5100111241c0c1c0c000e40c001d8000584418180c4005008a1004601e184c429001400000000f6180c5603030254400c0c024100036031198205d2400911303000a043d18000640c2c0b82d141086e000140d0000d1220201400d03525014503280d40d0101a240741c0314915458000a120ba0005000340c01d0402a0f9003d26010790300d00d80c03406415080041c00341d00701c8019260b40110081d0b081042005400701d84d0040e00a4035222203500f2800308114000d8030214a0080c00b45032101d483e2019917030348461034421000340d51441000e41e03800082c0e640d413403809070300221541c040003200070641c60b8116040e070b446141d0110522080d41d040c0b030001988131021104c400100b08a42c21840f0020701d6149040c00010420050603031074002242a250304690301014170802c2120700007102c1e030325030354 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 907489100 1250 907487850 907487857
    0xb04060309020105070b040b070810050d0b0c040b040f140307061205041b090e0601170a260d0903030f0b0a05120c030f0724020607081f0306020301091a06 68
    0x1818140003469180a00c01038030305000703c0c84050b062406032401c110510103041d901c9440b6680981d41c0605d19600d0000c03010103208035000e11504540c1c0d400e43e14000822080d1601d4014002448490500d59282c24062180c0e00a810200b031103c1c4003582003140d0280051026a2a44120007411115084c4100188458900385c1e62030249a00c1300e02007000d012418500321120001d0210315000f041d110380502c40500390031111110300344140800080d000180b54055a50f540440300038102c140780c0c030b0703c0d5501050045e4203042c1380b5146030001502c403a0341c071000404010381c40030f00100b54010641800340881d40524080c0e011a428203505a03a00d9031008191000d48204071880c0c4290340280088503e8000c0c5003400980510901d5400401c04400180d0102220040200309030300d494100700300c044004403000c555001d42e1000b40032502d842d01540e5010f03800103450340405054004a110f007150344241e588155440344d800001804094064040d5124203600c40401103031034403020307001c03608512 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 907490350 1250 907489100 907489109
    0x31407030b030610031e1b09021b010e06010b070201090e0f0610030b01020a15061e0302031603030f080403170f0a060512190606030209040507060306090c0f0e1f030e06100b04 77
    0x2040b000c10501000041c000404c102014154803c1f207103074695282100950100c1c0e81000d8900030780c400003554403014041c508e0018001d4014024903440d000c141009500b0021040307060150f0548040f035050741e501c0d04544500d84134103600c2d00c94103102c000d019160040000704400c15042031311081140e600080c0320138043c0d601c40c01c042c03d00345c0754410741d000402c55a0881034101d40c40402088410112102850543c3d0084060b9050750029003010480d00006110007004180d05400c060666401111543d44c03060003420403090711004a941a08601e508444805409036054207002603506a4440e42016000a580c10800c908192101550b51010764180440860500a07103800b000034036003011000703540c050806007842c10145840c54603280300303000318000a864660300003100107160003800446d10040d1504100301d8001801160741c0014944201d8100d00403405407211221010007804d03134a11156000034404209803e42810f02c03002900c000c1e80d51650300000d006076003a010032141100e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 907491600 1250 907490350 907490393
    0x305181504051e01051e04020901092703020609070f060504050607110301051603051e0105040f24060908030f0a050a11070b030f06120c010f031407030b03061003 71
    0x25621403502d5440d00f200c08581e400405141c0c940703544043c0054000c03d014501c8058414207180d0100c0700741c0c18070b1008580c00b07036211340d60744010442d1a400ea881300740b10300c0c58040005000800c0c1c0000d0809808440c41c1100140d21100420181e00d400740300c40005042071202c90201c00d480e09a004001340101d000e213901ca100b00040d02c20800030007881004c540c16014000340030904d0080d075201c0198920000440129007440d00040c0e890684404c00c409442c5ca078500040d0990812081c00024044c0500b100c1c0b220755034030414001c031841c8520710341c103d10070054110030721424803a0041a0038600c0e48070f8440c40d40305000c0c00d2180c4c05071005440100301c2a280140c0c403440542000c55000e04424981040d5006807600810700d0b00b6144001c1d407041d1030803c0c800206032111b10a00c0b4a0560741c4094254541008407041b009621495100c004000c451401080700d04007007072445035102041e500351002c0f0703507603848211090809100c0243e01c400d15151b24207440d85591603408019040c9104c00901 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 907492850 1250 907491600 907491643
    0x80303011505210708090c03100b03030903120405150f070b07020717341514040e1816032d031101050108030a020307060c030605030a0b01030201030518 67
    0x21486a01030b520164692014043c07580740264808551034001c0d244030001845220000d00e120000003482505110041c004041d00308040082000400c01e0065159160004005041c45c2d55030070040321800c1c4c0200c01e0080d0b9240e1a040c200a0084042d20181e011403a05200890508071038000b40c0f410140c000c90700c8082a5a40c10041b4200503c42e00041815031604180e0003101700000b40914503101c405080680d00c101040c400c050b0420000804600ca0304000014401041034000c01810040d50341800200a1501c0300c03641d400c0d41154104284e2a0300c03005c200080444250300c182050000398003c0c04241c00030340d4030100740b90311502000d481941d01700c00c0b041802c0c821080200d00d0740c1a00300795441d90703040d518008040684185800381c05600f00000440e81100c084215102600550002e5103444010b0f507410001c3c000c0c94494005059403081c0004640d1401c1c008041113510600601a0641c1188000341c01c8400140c41c0b2403a0861260303074140c0381280002c080d01c06241400b803100d10b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 907494100 1250 907492850 907492889
    0x20a110609030114090a120809033108010e10090305040e0405070905040b040b071107090b0f0d08070c0b03100509090f030c0d0206010e041106030406150e040b1008030301 75
    0x1422050071880d1040c0410130070031920881c0030503a80c10346071051010026004d008032048402e100700b642c29440c140c00c1000031710458011440200494010701c01c220001040d5602a41203546e0142e10003011651100c0340300c14105003c0c019a00c03003401c0810b040040d034800d6180100030f80100c1c000c00c441030f209440030a060220402c004401003150640034455403406140c10f400c1c1060580d0f08840084066000c9607156000740c0101d50f4411400d001480f809103032614110241c50300c204a07903080a110032440030a522412480040240242c6a49550383c1980c43e0104d01c079030060f8014001d03c034050081c0040000d8001e150011104d0489420f58140c80c0d100030f00382041e1144000301c5151100250000003640003280ca8035910030a41c0030b03901183ea80e2010307454020000c8a00911250403518841400c1c64007401840d0064001d2354006066603128400c5000b40c659900a040d00f454214100010041d814422540c004844809041c44d18035080b00c8580c0c13400103000720440d1000703281c803001d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 907495350 1250 907494100 907494103
    0xd051005010303110c010f1b061103130c090605010c0609080d1b030c08131403191d0103020c0604020402030a09062a11120d091a06030706020a11060903 67
    0x28682000201041556034900d0050022521450300350418003075040400c001d07601902e40c003645d810a80d2180c2101003a1040c007511121000321049802e265184035580c560000c800255200b11000b100304c02070440542801c40c034482d0941d010f1070311641070103c14007080e40c0c404200c84005038061000300d000082071a0403806409250f1801e417000b460409c802d10009002010f032613a01c40c564804004c419946101102c200108480d00c40b152000302000100017000340f1450241c0c1c0001c0340070743e400e05031034400c06040c880c0301c58000c8001035080c541d8641120504141d4051102d002d003811803400a00720205a03e600c4d000b0070291050b64080000303401107002d41c000780c009641c49041001116520f140c40004200307402c1c00c1d040800f01d200c4940d0121400307065400c60140048000384007110010701e0280703441e801480410100c07500da6180308000f4011f641403031580d01c0808030810803803a101090502c0c2c00c030654403800441d400070345908041780b8070040e0310045a60558100b9519141078011a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 907496600 1250 907495350 907495363
    0x61501051b012c0304030b16090b030c030f0f0105090a111c020c0d081e06060d06060309030f02070605180a0b0c0a14012d090204061d240d05 62
    0x10880d508049441c5443d14801c00104107840c09003004581d40756402102c95a68011408014001004440400c2101e01d0001d01010005030340d180040300b454075140000159002a144d041c926503010080c098208040c4801603841201c18429108030761401c00010600d03080a44004c001540d1900960000d0f50824111400100e528400b007074103880003400c100082d807101c003100e6014041d0f0b80f4003003400c2c1c5c818cc0c51301d801824044d4841c0c19810324080c2403401e5020160009034001e2080003d030502400e10f000e4200100416100016189040d00b400340032002c80411080c11900004014048941c201040d2601003070000f580307250141410300442c1d400c94027500000401c803008100c00030300201c0043e400b00c3c86445021440d452001c0009218240e46481030740051080001c0000e200341c10035421003801c0c8003170304400070800c04450740100302124000e4115031400300c4140d41c5084075100300301402c0d40280a14080c400d094224844002e40c080403400c61622440c2000000b0b070a204041204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 907497850 1250 907496600 907496647
    0x32a0307030c12031107050102070e100f0b0414150a0e06040305070b0c0f010204080303010302130902130c02010c05040f1a190905040e0a0c09020c07080f03030609060306150105 78
    0x18070850316050100a4607001c034008400086080c000c0003a65a008260311b0308440d010f0b00100038681c01c1c0000c1d0b03110800014102d455510b00341500054081140021070001c0401c041459503883c10040c981854284044940303020303004400c188060044501c0c01c856501c4202d140c840e01c803080c600c000643c9442140e0024042d44500003010412034041e500901c0200000011514505003109110742030740114822400c1c42e400904c010005070400031028420609090b50000c1e0005050b40019070480c041c503003165000d66580060341c02076409110380e400344142800d19508141c50011110080c1106024140310300100c81683e404404150080c1c2d4000c0c05e41d024001219002c0e0800104540ca480c40703014030441c1400da6241c2c50707810201d45081055000289000c905040140d03802c069170220110405030702c07858070b0000d00e10301c061182181d2608844003542e03481c249071007000020600504058800d40000b030600200c049184034200c0b5449082c207201c1d8590640120b40303006610013004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 907499100 1250 907497850 907497863
    0x60c1a151201140a0606030b0d0c0e07050904020a030b0103060f0e190b0a03050a02090a05010b0a200f061503010516030e0a02040905031c0606020d050c0138032a030703 74
    0x504c210384926400c4103041e03401c651b90402000e0070070010001400420b180246c142110400240070031070308105540e51000c40c0b402c080b85800c0154000c03408980c0015400b6001039a0b414071400700350f905028407001803807060011641d2904001e28800b845c01c000c0d0400002554007404616041c0302a0401082e000380180407100040d581d04006895400c0560304900c14420400040c20640c0c484c801d49058030b65005c1100d0030445da0000517100000c04a81241c400d8020903844152405c04020b0b1081700d00c000c601034610f40c00c00e070700904072012400d000f0f244241d041c2410068003000c1400c48441e00710350385c40e02140d41c071101e040342420280d152030041c2d00075082c0501d0300c0c1030042c000014040000071a4034401502d200c03583c040d040b030b06a07011384001600030101c1c41101d41d110300c010342510800540002408600caa15030031900d517400281c24600403002000c1c10320403020302d900e00021042a00946601003440003c050720080e07401c440c11102d00c0116800b001130b01c1c2088071002a40e1f0060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 907500350 1250 907499100 907499141
    0x13050406030b010603051b03070f170a140a020a02030327060f220302071802040b0d090312200d0f06080c130b090403030c050c07060c1a151201 63
    0x180040d0040c400d0003070f003002c02c1c100b50100707280e100c0340c43c011400c0400300c191282c21602c520710111400f803040c24802c0200032f091041c3c015030503a514441401840703070110000340151091815160300b0350041070b40d44903d20500200440382d401000f00c030390048446034103043d400c4c1c10300892440e140c00c03030050b18102c0c4a5041001041c5c0780701d1030704070f006004120107083c043d130f424240901d0031026600c00074016080342104100f5415000d0301440040301c034032005410b1030307114018000181c0100302015051900c03814802d09041d00002d8050643c5240e203820700800040f00b00700d240740d600d00e4441c54a40c2e040010340f031030604050381c480c2e0441c2088910901038a5500c1918036511944403a00b03d00c034098842c4507040566851040c0000b415018205003910b90b9503841c1a001001191126424003404221800d81400e00344414030207425207441d90b0400314110304040d51203015041000781901482000c0c0200c103000350407940c200130412918607801100d041041400f4011314401e200060240c41c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 907501600 1250 907500350 907500353
    0x13030c0806011a07051b040207051903090f0602030a0e0a0905040f0b0606070b1b070f1a0c0301080c0d1b03080d0f0203010518130807080d0e060613021305040603 71
    0x10850504a0f031100c2e415442c3c48a4841900700103204020008219501c00c60720b2100c021290710854107a000000c2c0018203082075912240e040040311440c840c45d94144d68411410940c210141c00091312100c0103000b501e5041100103541c0e0300c10890410144644071035803c44c5596088a0702c0f010780f08010040c401c41c1810300d042000100c1c402012070314003100c0130000e02d49051501c02d44820b144c0080801c030054481c0c14980c1001c81c03010159030600343c4200714180104456908103800d1a1041c03288050000c0d035503100700c0020074042d001c0d2075183d108000400c01c11400281d00b0700c080d002150890000365a62034503810b47c0040c0758101142d074412070400001d0000c4000548510240b03c6018006c540c44840381d003089101c04d00450780e218640d081062504219440c1290b4041d8405084102c060303015101e901480d040807804640c3c00c480041c940107600154010350400711034840082040b82005030000742200c900071005101590301059002006c000c0d201040c0041070060402c1206030345a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 907502850 1250 907501600 907501603
    0xd1116080624060702091b0406050315030105160503100f0611071502060c180d12121a130b040906060509011203200a061a0f03070305060a0213030c08 66
    0x48440707000000e11140342c07034200c00b200c10058034079003030003000e00c0c1ca003080540c204001282c020340780302c4000c0400d0202c01c00e07020340340c0001c10103081c56403142030f2640b40a15503401460f03051120907010740d050405011a458820004802d01402401c040da00e0390703194225640c95034000d80c0038018110324031400089840d048030180c00100420003e80b52110b448940480c1c0c610209074008006900050029002401e2000640103411040405640091046000031104242c0e09030607141c482d500b13210300007001c0d0001314145582840007001d10441c0740044540d48075400c481401402103d80ea241011621150f500c00660310304000c02c104988015814207200400007030050030b004003640d00c004281d100078046450106541035980000c0c9001038400d5030401224050900c20512551b541c2200062090040c0814041d0304207074000d00140420404c0b01c94000c0c0441c0381e00941000400744081000412000c0d88603403810f074090b81d142d403800b00c0901c2c0840141e00c0034000d51964080881c0282c1c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 907504100 1250 907502850 907502863
    0xd090c1d0411012d0f02011a0603070915091d06180601020f0a0c090606020312070f050705012301060329121504120801050607020f0609040e01020d0c0807020d111608 73
    0x216a501c8401d0b8080c02c5046e030881e411464601b030305050a44150381189020401903500510074a800b0075403035540d048a20703040c0c2841c0000d41c04904407100c02d0119041c240303118000d100340c5500740101400e0400200d20901b409440c403a1810031020b00140e03e0340d00070042c1000c998085400c03151855142c0c181040844898061801c900741005800034100e480001511002024003403403140548a122040e0b17074061082c41c5180501009110030303130100f1002c0c49580c42c0d8008082080350662500002c52140c1078050f04050107061401c0c051034403c02480e90310341d403050554001c0850384140e00002403030030295410381e0ba00ba803141800600c5a6007181000c94051031044c2c4100d0720140040d0400d0f61100c0c4240500c9400031410300c007020161620200502200c0c00140c069464034101101140603100340c40c1084069070740009035508140164400c0044244a514280070a420508002034640307101024220402c1204400f014184030240419400e900d040c5040342802a0382d510360503101d50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 907505350 1250 907504100 907504187
    0x4303090305011a0a120609080a03050a0c1806030213080304030516050306061c15060f0f05060702010c020d0303020c030d0b01080906070807050a0e04020d090c1d041101 74
    0x500381038008070030824910407020343e104002c0240981e02d0400c02100c180301c2c020f2806441d1991030784081400300d25150010074440100395004241391500000d0300f410303242c81c40d5140080100c44501c1c00100030b114141c030415a125032601580d05c00600800104030341d801d07003201002d808009800010808c000a1000d000380300c4030101c18050b0f6454040503100e0748120303aa5604020300b40348400d402c158094401d034205203d60820542c1014080034803084403042d8100e461840b0920005002c02891743d0030805c010001118180d1030111950300081803c40c507024001d001d04540c092010426000c1d0301a0340a00c0d079030a00b100d03101c0410f112600c0c040c15509a0040c080359a400c045048000003060341441004191511425038465074000c13245607001005130820030400c0c00d80c1c020559224001031080142c008070100308801c0c982001c00300704200358424101012441003100c14000c4030045283c0c002d401a00381484421250010380e00780010b80410780d0ba0340740b4424040342c83d076020f07410511a003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 907506600 1250 907505350 907505353
    0x10801081e07081212150a03060209010c0c26010b030c2403040804030b060306070c0308090115091b081902030c07020402070b180c06030a110403080f0a144303090305 73
    0x50706c407085801c1ba07401c0721200d5150080c41241007480071607015001000503c1e010b140204210000341c03100d8540c15460b4020b409451070201503011b0017101000f103582da40081000800040200310006555075030385502d818043c88540c0603881c0c480d01300d903c0d0508030802008440383c1c0ca140c240342c031301000da1182c00704441c1e40300c1a001044260500203078592040450f6114605220300c2078038150783c01c0390001d05080c1c496490340004d5510342c0c0d040704803500409091201080240c1c00a0030320800c040031403040020402420104961841380141701500050f610303000681c4c0e520754004c8401241710303800c03000e900180002050420480c0701c610807480355000c03181c010716001009860546034260240d101703500c807a0502c04240000e81310b0b07102c081080f0030300348041d15082d9a951042d071182c000c02409481040049038881c00203402403050a03203d40031070100303031130401100316018031240d40030800389145030300310000d83c03d102d030b541c02c8a036124400c04442c1003076405d41d103002071820740c039400219030a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 907507850 1250 907506600 907506637
    0x120201020309161404110c011a040b10050a180e0c0705070911070206030907030605160e0306060a091505040f020c100902211c080114010801081e070812 67
    0xc1a600e206481d00707468149444c0e00e01d000f0b99600b0040507203070f070191041000904010300360144100744100d0088548202a50360206503160401c022a614440550301031588400d51804460b444801c40750b100807181812101403181c0440d40f2040c0301d10350002c035010780c03201080c0700e52298688068118148100c0403595402c0d00c0e801c0880a03507400d00c65500400405110000c014076101e400f41d94005081004c95100f29130326103a0901382d62040d2418184441d100524602d442d0348085420f40e1440c042d0010506401d02d00040303003041c2e029200d080340040d40c81c03504d03034440e40b400641c0c40001c01c070060050060541f07140d40b0500a521100364028148108521000040c1040c0601c0c03442d190010318180343d11085010000708850341441c4074485000d5043d07210ba2100003c1008101c02d00f640d42c6030f03542c03581803400b04645049a41960760500405800400000c200040e61140c110721192000050b20181200c1c240385c400f154000c1406030251040c4e10080c003090901a01c0e200c0c404400e042034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 907509100 1250 907507850 907507873
    0x80a0e04110c0105181b0315040b010302150a1209020f12010c0e0324071b0803011d060907030b010e04111315080105010309020f03011d0d050c0c1c120201020309 71
    0xc030194217240504090b084001408142201070101e40303801000981901ea5080d160010032141e40800c4408035040b0341c001c0c0043c015420041d803400c0e00070119074440d83c0307844400700003c0c1c20402c0ea81481c00310780d900e42d0140380464407103a0a00c1c03464040504034a20f410480507400e40038101d145800b1000a074040843d1103107140000700c1d50003a1441d50307501030030740300001c51003140d2000080240061040f0342259241d04112030072110034441c0210ba03155125414407501c3c0c01009800a00c00041d01106014041c007a0303500c1d2030701500700445090000c0d1040720300006030340c100314000c07159500c2858480c0c246001c03e8400002d00107aa80c0b2034016460304d403107200400c400359a4044c0c0e540002c07015401400154001c0e48007901180c001000001c4100c0d580e0300180c06e5401400c0000c021180f1618804281c2d030040100800384d00e690b0802e40e0a0121401c2080e40c1c170300440d803406215200b0320008040392446502c0405800f80c00080c140c110076105100a4040e51003035440c00d44034400c541c0c0b110b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 907510350 1250 907509100 907509121
    0xc040512010e01150e0a0509011b09030201020d052b0b031f0e060415150306091505070e1309080f0a111c120c0e0a1401090503030412080a0e04110c0105 67
    0x20580380c545444082c031ba1038810441c070061800500c403445139035a42c43d4004030f11100d4600840464501d54a8264441c21440020b0410000b4075400043c00b0003400310090096440c0d120011030321140c0302c017540d82d23460b40e07134001c0c06812000d0120303826024011481228240580c40c0c2003401c03280781c000707204403c02c100d03907240c1d6000c0446018024002d45d10450705160080d4001c0e640e042456614046000c0d240c1d02c07150216200d500701150100b07043c80d0001a14002d03401004d03404003990800b0359020010301c2c081150b401c2c021682400d42582d8198030300401c03e542c010388116141c0080425107941d10000f0241c0460001c98800b40c50740b01d140244a20601b20031010700f0026203035a0364090781c2d41000c1010f806094200b480c5014803001c0f0303480300d145d52141c000d079200034842c030b00ba030b075031070b031400a0005d89100090b4001900036001008240820841d801d0070081450b48588013580d51215007408482c11100301e860700c0e6110f0304140046051228a401078801c8a041c28000c0080f51910401340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 907511600 1250 907510350 907510391
    0x30c1e120c010e060d0e07060f0f0f09150504030605090307031209030e120f0a0c050109080a11101202040b070201030f02090a150c051c09050108010b030105090c040512010e01 77
    0x240c0040e803450079004042c240413010b4070b81c2c8248184c0c00b00d40c60706000f1038113007803400c25009040080c2d600c0070301407007156100405c403001507241c0c140318501d1484800003c0c004c4c0381e140664603200340d4a03052900c020780310303100311002075810802c20800381c20000c0645450341d0201030700b500000c0b90004106c40c441440c0c0718800d446c503890340301d074a96088420180112104081100b90140c01074409560000c0300a01070f010b04184a908010403003070801c2d0000d81201a2a00150410340c005101d080c0095101704015046079130885000c0c00d0205c00600440390f920862613625041800030030000f4001c0c0c0190301804d40141b01341c8060140344a29100030089000784544140d100500100c200465401c00074200d00c10003191408514619807502c602e4a82401c51009801e100444c4801d000d589622103100341c09803509103011003444d45000300e101021700046c01400c1c480c4407040c010401d42c0c8a0003080f28003c00014000070610710488400600178050001c030710039a03508ac6851799440e1864035101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 907512850 1250 907511600 907511623
    0x30c0d020c031b030a0c0b040f0501020d0e0609030c150603190804051806060d050c0910020a17120a020d02040e04030f110c060f090a080a05061009020a0507030e030c1e12 75
    0x910384e188005480d00b10747c0d814098419078a906420a640001c10820f00041ca458482c001c00031500310003d10340a441d04800a00c0f814907504184288038032100041407070383d4003405408910210b41c41d50340000b818201e1030f4140c02c2019500c1d0490301c003000800b01c090401c6441c101c1d07600035071502d6007481d5051090102d5801c1da101c4000c0280c0c880c810804d90001d5040509190300b68140890b0501080300ca50004043e2409648460350450812005d1503041000441605880f81010034202d0741c910343d6140941044e5140c1d0300441c0001020950303030b06660040c250050042214105820080c0c0940c8134240c074040001c0c1c50200004e1207020001c0e1800043c10050303d15842c0c1695503800e61019009206034941c0170402c0784002441110400c004040980500041d0109090040032003000c00c96550050641c680103200030005290000d058800c5a50542420303c41c1d10354510003c0e00b403010740c81d103644e807001d24541e506c0300d8011451100703c2080780644e12000071040d0300860a075184d0a1200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 907514100 1250 907512850 907512857
    0x100c050f090d0606091505090a1503030f0c060203070306061818090305090907022b0801060c02060d0c030b030c0108011203030b0a120b0621060606030c0d020c031b030a 74
    0x31001d414100010600345040c0160fa0004a164465002c6401e0780c0c020641c15014144600f02444649416100c4680103030f050790f000c00903002e08800f0b040c04095240f001409101c403541e02412036901644044203143d5103d00211b50b207180034a00600281184e0041394001a03214040040c0b10841c80f81e018161a0000e140302c090702c0900f50b00d030b0f02600700048210200041803041c134070141c03501d10b5854080c3c1c0300b580203010f40300c0d448408031280c074200400390403c00c0341e03802c88520241e400c0000c042c10344609180c011090801e07400454168070440402011070351504c204081e040780d25901c4922883c40840035600448848030046844402c01c0c041c1d104100325030b41c0040c0000b80a0783c04600c1c4a04064109002c00740c0c1c6611001c0604d17aa0007054901d10008020001140390000e08002202003a2090b030341c9000c90035690030350381c80000342102d00030700000001c200d080d2032102c00d6455000070080c041d5542c01800b82c600e506d83d001486881071511b80142d8910585c030b0040141e0381c60101555 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 907515350 1250 907514100 907514107
    0x7050114160e1e03030c100c0206101401120912030b03060a020c0601050f18010324050f07031a1005190503010503120a0311030c13170a02042408100c050f 68
    0x2010040001c1019022139251100704080b0501000601c44019180409800091800310185020382400c0c4014200f4600440c20402403201d0105c00001c040981002e10341391000e500b183e00054000d05244030043d099a01282d06006d400c2d40c90b80100803908800d03425203599440c2c0c3d030b150710164000c9101d61a42a0003480040c0300034105032084030600400202080d003607101000c0c1402d80101700f07800640344034503503050388604d4034a030030001c0c1111064688101303c039140c4036231503060700200508010308060b283c9082c001022000200c10b860301c1c10013008a981c4402c01000902590300800c0552401031008098030001c1c0c0c040c4094a04844010300900810b81034100032100700d611413602e0605066880c00c010010601800c0614400c0c090144855900c3c404038404298824066001540e141d00c0d14070804425031011a240300500d07410b03030f07000c01c1c800c1c01d070703d007001c806010701c2c071010a4640061400030307200f13200245502c41a01e460310100204202070b9001c41d002e12075072480444401082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 907516600 1250 907515350 907515379
    0x1b0803090a060e06070b041505130c14011206080a032d050714160302040f0504120e0f06030901022d070b1911040f0603150902030c07050114160e 64
    0x10340600d1440d20f00205028030f0644143d030350750000c41003070ba0700b501c05403640401c242044806126890300300102000e2600c031040c943d50740c5a11141e6501810300d1006a425003c42d10340d0040c00450101d10052f5401e010322602d5006041c0d0b00e090000054002030403882c166102c50060000050030300b4a8000300d100250b21416043e203a40d441200100c5401014261807010b03904140f22100e4110f000701d189070300d45032860041000340c0c0c002d020b801244a140409000010304141081080d21201c1d04280d4204050a40003a80b010034a45545401610020801991140640c004c00d401c98485002d05d84e8105105101c4824030f50a80403012800c0c01000b10740081400b0015417640000340d54246210b080c4200800c00981d120071516840c0003002240034440c5111403030200000d49500e24007044a1507400c414141c84800364461250340580c00004141c40c920364608960066130400004c1c009511000d071003c111041c1100c00850116050035201411440f54100425a00e002014140403d558 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 907517850 1250 907516600 907516607
    0x3050303071b020301420510170f15060a080a0c0302041d01030c0b120606030402120a150c02030c031b011b090305010612051c0908120304061524020102040f031b0803090a06 76
    0x494520000d0000381c0c40140c03c0081d160f049c1718800c003219421440682003550b800651402c0c18005130348600d00c180145008140d00401c0d0940c01900100d0102c0c90606c4c10744280c000388623540081015082103100d030203901c404008158100da03c1194403076039080d030344c0b80000d42078040d2920400c0701c07661000109200c1c2c030b00741010350f03000f6000401d4442d1380341864800c14a061200d190072501c2603032185409044004501c030700641280c480c0091494403107001c0500303443c1e20801c00d84094009420b0b454090840c025481004851544080c804081c140c120014180003003030311040303c6540c02e001001c160348000c03202d52989230341d20074010315099210317042c2c0c1c00c0c1d00c0720b80214001c10414400c500161040d0108a08510341c440903903175569904140c180382064a84100c0c80c4071684005c142c0400c04c140d040308205e60942924001660100b02d5600708a000e84100c3e44003c004600042c408414003c1504a08443c810344981d8003405035a2861100d48034000c0da030015920003910001003280500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 907519100 1250 907517850 907517869
    0x603110d0923010f0b0906300102040f09150b040b16051903080f011a070c0b040f14090105011209170c0303041a0103050303071b0203014205 62
    0x205400042e400b00c0c00c0c4542e4001c0c600c21101c102d485a448101070f9144044900c1694a0070700103542c800001d150810116010308031405252502c0c8000e4040c2500d00100000780d0191044a44c000b5565240d0721416160141094007401010a2800900c400c7d801d0541c3e58030422204103c031800d040c00e14100305090035401c030f01000003001e40e011150b100000c10a020100c29400700301b50856014189050052000b840101181c1c1180128401800000000d4050f084405a960700c01c554420240c5841c1d00d200f44140c0c443d90341d00030f0100e0b01046240e0703a040c200080d00d00e06001c5020713000143e02049140c40c0c082c49041c1c08244c0d170070030701c00880c0760355006200101e005d5000c480e218030030624002081d41c000195070403950404014001044a1a00c403120610b20009561805504640b10542c99101c0030700801b0500c140346403c2003006080380c90411500340c00a000300000c001d03410182041d108a0f11058680540001d0411203110900340d500d2883c102c144207881855081c031090202910 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 907520350 1250 907519100 907519103
    0x140a02030909010f1d040b0408090315010311090c03060d020103020f09030316020406151b020a081e060c0a02071202180108030c0607030b0108070f11071403070603110d09 75
    0xc10044107035582c03a684241802801e03010852611145490b0300c0e221a9031154440c180d059032580148000728040d0a410b64000ba0854841e41da150b00450001e03181c41c1100d603941d07400784d00398070001040c0000c01400714485801034640c80c0042d5101a01e503034142c0300441da065071118849440c0c5000d07502c070741e016280c00c500000c8040e180140d480c0c0001e2960308104d4041828461210b044000c50629004902c014940c55000010f042c12800003d840400d49502d440c258081d103040080956484485030b00040081c581625020401b00301252050007041103102041e215980c0071407504c6118404440e60b0000c298060300d6114182000c580080114080c266031041c40c2031640074404999189450082071740800031603850000315905400e0441c0282017100741441c0c4100b59009036044108a41d01031498074100d00001e205240c2038480341e00d03680144a1521850702e001c980c3d20440485101c84480c11021100180d503992002c0f0305643d4030b5502e00021070402c0c04003600d10a1650000d0f01d4a5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 907521600 1250 907520350 907520353
    0x403030f020d0f0615050703110c0a080a050c03160e190c0504031104050c031603110c0d020708030c03040312140a0306050f09150d02060903060703060305120a140a02 73
    0x2180348100081aa001060501c03281a9542c88610006a0501c10b03480180300c11111001444904440a0a03501800740040c0c00d01c084001640d01d143c505005c855000e10008240000e0f158698250542d14401030008503070a10502c1c4000c0090704c2d0009500041c80c0d000307280951035a0030f000c4050040320014100c6039480c4006010110204864043d10004400c95a03c054032240340d0304080b810041801e00d024090342c0f0740003d0004103940a000c0325448007021a61035121807500c4401c500400a5048a18560380045000030015501180c0180013084550884540640b10140d0799280c1c4901c1c2d00101307190340308100400005403801e40400c2c00485c035082941c10f40304147c3c06085154094a403820029564090078803281c5003940c2c11040d00034007030342d07603142525010303000c864031a001e514407500c5404c150050208542d140001c442c54841c0140a40d0750307504000101a0141002d0700013240e8030300030300300c418141c440303081c043e1031011006642c0c0700b500050302001c0c0ba4455012240ca042107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 907522850 1250 907521600 907521611
    0x41107050601241716022a150c030706090201110313061704030c020919021206090108061014130203040507090e0f030904020d0209270708130b040303 66
    0x8104103200c0c10340281461000c40c51143c004910a0280140d000d18110510002ca0b42400324035408001d029800744440f40780000b2020305410507072034200c0200c0120401041c2c3d594549400504103541c0a000d08103807425002095000612806801140000300b4158802e00420001c0380650f003140f2207075130041c1800b40c042003072424007608550050380001450840e8200030800749a21102810424140381c07004400c0b82407955005085442c03c2c030019202d845140c01148841280040d0501d082d07451441c215a1000c10601c81600ca820450ba0309100d030301c0007000018196000b00d10341e4402d480d034100301c41c00e4904024002c084110204030464100041c0c0300f1020168805100660003076010360b0062011303610780034840054481c0001218002d0300401030f40a000c007400820341c3c81c1e0f40d004072405038481410b00b400400038040c02040a0788040455818040d90401c8003031540d409580201c0c2c2020b40d0750381d01c41a100d440c01500d44243c40b078032040d85200423844401c039103070700f1510034036000c0345 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 907524100 1250 907522850 907522853
    0x5060c1b06010306150e090a02040903030f0903360b030c090402030f060a0506040501090611031e031609030812070e03010c0306080c0a140d0f060f02070b0603070b0405041107 77
    0x182500c03d800403a80250707616084c10641c0054020381006041c5110380d1252840c1811400342c94084001c0000e00554a815114003094020b401010700499880d404004880b0142402055040800840c04800c000f40070a24084010a60720b185110a4902002c2c0070302c3c030302905d20303040d68001402c204031050240043c0c00b0aa981d400250f004070b21038000c0740002d041c03030010030508111b81d80c0414424242000100300d182d030080b81c010200c0c0c80314280a550001c00c4442c81d8218070990030003600704548003001d082a0500000a9400390301c070120346a81c40b0000e84170a6a61003001d000250135540c00703000782404451440622540b0a0700c034a0892460703088003012a080d00c01440440e00481d460b00703010f02030381008024a240d02c00d011603404582c01c0c030700205144c149010410b0b450046100600c0c0c0f000740700810404640c81130f40a50304201c44041d000c0030340c0c025009408220744020341140814050310b800a44001074804080a880c0f4080c41c28041100a100340034200703080203000c1c4120f40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 907525350 1250 907524100 907524103
    0x702060619051c140106061d0a0e131a010b090402091809100b1512040804030503070503091c0218131b05040b01050c0a1b03151d010905060c1b 63
    0x1900310007004034160f6440441c50842c0a20303080414511880e0700d4414200038041d0700042010348a10012441c1070010b0041d808151400c0c01900400a0b00c50701034144881003100c50b20705003940703002d40d08aa4010b4440c02d90303441402028441e5a0540c1c00920008c05103245c035170300030404150b009000c44a910754600c80c80501540858000035203402c0ba841b401140300c15130044604141044800103010800391001107550f01540e41c4110286080b000042c0420040500711805190044110ba844101520700680da0b5800100b190703004280e007210307103c002202e0549580640381c4c0101004994200041c6214000c000144030084091038050a500410465003855403840000340c203e601d080d081400713203c2640cec01c0c0b144aa0401208015044513041c01017280740103203a00405c81c05c8082804c100c49a002d002c2900301078421404548505021038955200582d0b55100b04513100704104e11074074103800c0320720242001d040754000c4400500d0024910004082e44010002c1d51500d1029004041e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 907526600 1250 907525350 907525369
    0xb0913020a0602160b0901020106170a1142130f060c0c03030c030507230706180e061f020607120c050706021c0c0c1703070206061905 59
    0x125218290110120258142424072402030300d050700080c0003010051000c0c1159070307950b21400340912008103003c18268402c0d000a0000d0908581c034420b900aa00e41042d100c1d200341504030344890f03400c2e014040c2410400c01c580c04039414205040540300135400d4080007a042040081c11f0419a003c04858a801082c05001d04051f00300c1a802e00d14204450440b902003290811024090404580c10001e1041c440e0001900e500d4038042c1500201032600392020700030361078010000c480b005c56180c10704141c00c02001c104001101103551081d6907040c1560205550f81000003c0040b500c000d008110009000507080f0307202510400d06c2102145401d000c0304404c854080050704410705002001d41d105000d4404256040c008018040003030401420612501000621440d00455102034209110007244500c150b82d0b80b05201c5500d03010001081c0b1100104210703080000c4c446a440c8100b21311060380d00c82c610b550000c190301e07110381003009400714040228100b5841e000c5400b203400e8441e120f05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 907527850 1250 907526600 907526611
    0x30c0a140310030c1a09131509050a0c030920130c0e0306070216030f02040e0a0b0105011b0b070513080f01020a031b09141306080c10260a0b09 63
    0x1007500341d0943c6028500300e92690302c00000308001c0722050700f20204017002c581c2c1d041e5048510000840c0440003e80c040c0c002450382120010000400044514290300101e03c90001d01c401001610b0358141c06608130350040344d014000134502071045898030407192040d440e040c0000c00300d104030049600640d0584941d51030080008074078041c500c885003420022a0740001c0f5a0000e000d92588803034451a01d1080c601c40540250120540002907480707584c88494092084d4064407441200303030800b0000704000b841014001038600c2c0303045403480741c00d17219071018075880041c149c515240d0707400c04c0758150400308405810506c0c0d0ba20000755010104000844015100c00143e1600e501d1007010301185d1a000d905207001d400e035034148841c0e6074046140c0043d00e612801040c0d91071404808641c3c138058404c040382da600d01d802c50124071762100040c07181e07402d44201d900c0d50104180c41c0e01162802c00245040210070b911203030790540e8810141c5613542c80381c03600c5000a0102c1408002800c0e11006545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 907529100 1250 907527850 907527871
    0x4050c0901021207051c050f2805090603040b220c061e0e0d06060b0f070c0f0602101107060c080414031c09020406050d1a010812030c0a1403 62
    0x250003016580521006664403280c4001504018440c2ca0702d60701c481070051591075420805c0c00c0b00e000b640c091803e4481c485103004800d0384a150804034070b1100003e080f1145050001040b0031050144544100c98803171030003411b41030842d110f0369150601400302400c040b9038801522000d6030b10580c044090303c1e07618003925202e6141c03440d0100141900c0f803141203045200081078104402c1a030442d03500010f0f0760040ea584d01140c101350130b121005040765008024044400624a249102c0c3c0a01401c2601d02410054080036902c0000700d41440310313031082102507001456440f4140c103403640310a0190f001079480c82e1a01245030784000807501d040c038007000401d100400b030005120b00342038100b1790200b10034000e514100361240302c440d1320889984454421030700d46482c282152620740280c002000d01403d0200074200c14604a214041b4040e41c1c0f40280d0b400e40000905294005050303030801c079030f11042034039540300d01f101c484240c0c0c0700e429000184650349403481c05000441d401148541301e00071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 907530350 1250 907529100 907529107
    0xb060d18030e0301110924030702010e1e060c0a0306030629011d150705162d030b0a0213030305030a0c08010b0901230705030a030c02190602090f04050c 67
    0x10740508030203034101c0a507009a1500c44240e1301e040110f03040317450f0204100d480c0c01450444842142880318141c40360302813194040144003509405401c80303101d88041901350b13640f44882c0a58034201000b10031441ca91a80440041084018404021300b2210701500e0301081864898a0f0300b800c0e114030b80c03912000301c841c070030b48292034004c14141c545181c01c00f4070345049101803514080c066102c6000318503109502038013034110071680742400c540c6400d5100742038461011030351605410b24200d40c8540360f44110b5048001801900301e402807048c601416050500090564444040400000b42101d6485508011485c5c00e00312240740d22000314403e80d2840ea80385400c3d124035061300c803d1010071051202680051121000070001c0d109110f4007803801c1c10381d0300100440d619001b040081000524074000070914140a0084014080e003145524148840d00d6240b004aa03510500c0e90003881c294000810080051441c0e00140f200f00c8004242ca4080c1240400040841d181640c207114071002c0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 907531600 1250 907530350 907530353
    0x250503040302090601051c0509031213030f05250206040902120103260708030a2c010c09140d0501020c1906050a05072001150603020703090b18040b060d18 68
    0x980d00b42e00602c20710340305c0d0518440700700303901884420710a40700c087e07902ca10018000720310405c281c0e0600b0100034092105403e04500061000c0d4a0923419400141c0c0d51890403480e6004804442a01e41700130114441d50b500081c0103d070128420300300326403250b0204800140e44002e070010b00003c42c4050115885949185840020740703010510700c03d040c05402c903280c03169a040070180c0e00310303642115070a41c0d00d550300c4480000911100742050060160804403242c08000d12501c003e000c0c2500c0000c02480402e01c801343c4143d030a43c4503203000f1840718040c22000e414694035000382103202d20000341c00c1160520030349040581550200d031070b0401448a00302440301d140900394001e81424420842814030450080c000700119000b00d0030203030440380c0c0840f02e1f1001d5000f0502c44106010003210251503c01c020080d6010000036400640320b10740c003080314001101180c1001800000d5803100e1120a03050101428541400c0ca510510038014002580700c1030051000f00c4440c1c0340c4540005907503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 907532850 1250 907531600 907531609
    0x50f01060806031e1b011803060f02070501090503210610050d0e0303070c051c0c030c050c0d06230621012403050d050f09220903120e030f0f250503040302 68
    0x2480062410005040b2003408017041f40b20800c429207401810106a01c5045000800030b0301c50080010a60b61030010b0300828000048054510050358500818644602000340c514440c4142c803625030080c040070300c59031121700440042c880320580300390201d081c0e82d24811050554004451500128880021417800c001c0e044c40521003c4d054014081c00b0448001320080c408a82042d004003802012003040c800e116042024150312200106180c17004025454000081c00c00c060200d0003041502064040c103400c101a4103100304409440e030015600141030308660180703c00c9040610303540c2c8841398a08848140c07040d01a4049014402203a5446c1d8500245010780c0301445404100d0184103003990021200101c41c4180c1085401240010040c1035801440d90002c0c2c00b445030902e041010400c01d03410400c110454069080d040041c1c482c000d6282e0b4492040d04ca003600c80309410800f80d403804c0f030f100c8090700d0044480143c0140410756081d201c0d0080500403400d64890340046420002c603c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 907534100 1250 907532850 907532893
    0xc02120c1207030519030c060e031c0504050c190f0f031b0806151305100f0f030503070f0f02030706081009020405010512071b150f050f01060806031e 66
    0x19072001008240d107107488007904da4aa507100d1004092855101405240c030900303428055030703000201088221400c0c0380050381c0350b004042035001541c0b0074200f004620746034840c03584111340050107003a02034500d50030800e1007014005401d041410080700442e0507215018903201070410300d030380018440c0c11401d202000c490111061150b50400c0c4100b840030680110302c0541000d080781203440c3d100e0700407000404a100400c3c541c00070310b260004024407092091100d03030440343d020030450780d282e84903898403174061241e0101820310352040000740000f5032042c004140f824001c0000302155443c65002a09014840d407002000804000900051800e511025001050401d004504e0705141c600068002d0140070340b0040140350220001c1d64842c010201000003043c42442c40150b0a00703494404810090345800c2d090305840c060286000d1606481018081d2007101c6094a442e0700e0314504842c9018000d12043d01400307604071050050b0514100c0910307003c0c402001c0c5c071060900040c034140100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 907535350 1250 907534100 907534129
    0x80306030f0c2407060507270609030b090705100c030210090f0b0a140c13080105070504051219030f1d090a0209190b041e14010509010c02120c 63
    0x20800019648160b0f560020015100c054054000d504101d810380c0003024001d484000c5d1031281008200585168451084000340340410341c1c0c2c87c43c521891300c0d1040051854000d00e000705010701c0302403002c00ca8201c6000d030312210000c100c81c0320f25150408190550001446400440c00100c0c9000416405010100fa02c2e03005982c01c0049003610b440e400188003072404090424040030010400300551303500848103691442050141c9400d00f5007215503644d00602c1c1005c001c2040a00201d03003403c06008660190207a6a95941418140410443c00c154040c40118007482050929013036800400b487c40240c0b0b01948419100551105c409000004400c950244c6401c403069184101da450202d81034010585060058481c022032002c03070820181404a00128603801100103420400140104280d0340b2841d42c034902c002d0301784901c400c3c3c85100d006080384056a0841d044855200e0006000000d005150000d984160f980110301d11401a001682650700191342030102030403d40e100340c103c0c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 907536600 1250 907535350 907535353
    0x20301210308070509030109020301140a0f020f0d02090a150c0c170607050c070f080d03060510020a0206070602073e01020601030f020d0506090105012405030a0b120a080306030f 78
    0x1030150381d40080182030001c00300c20500102142882203510250f0040114607400350080140407070720800185000801c03901d444420381460f1500e6031060b82402034460000030800d480b030600340b00c03001c01c2d030294200c50300c00d079040990243c0002d5200c940920000d0f00619035250b50010540c1420303d80c8035858507070801c2e85034003110402c0072408200040c070346500c06120324140e900d074511481411b06100d4240d0001540d52081c01d00440d40c1800420981d080d4000da480c108101d030340d6102400500010340c2c0f0014056048a40c2c00c3c0302505045000382882e5105403401843c0000395501d0890804050381c142008504a107104018505d140042d205044140c03039011040001080000b59210b01c1400010050000d221100c1c08540704c051010765540d900005850710b83c80c0c01c151080c0288424480d5047c0c05046216184010310f1809070101001c0e400c0c0e6443d45140d81c3c8128000250200140c150780104208070034580c2d201041c01080c1d0410f2107184929500d0822804061804041c9000701019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 907537850 1250 907536600 907536659
    0xe09030421030c05190512180f040e011a09070807050714030409110a0806060f04120f080c03070303060f0e0411030a080c0f100501080a02090a110310050324060f0301090213020301 79
    0x1030b032032030400744100c40002c89c0c0d043e5505402d0004100a0302800784000701320b600b4811000700411040c040300c42c0f4032a09860805003566401022609810141d9042000c034000b04403220114030208400e03c200f00480003242c1c5170583e034040c0034045520b980200501030348042021940164490103031a0070103002c440c0b150503c4507180f5602914411882011082801014000104070480e48103a0741c83d60850350032070302d0f0002400c7c3c4030344a620452086000070324101000c02c0000721841403d081c5c8130101903240e40356a0b140d88a410415044034801e9040c13140c910b1490004400e0001400343c510080c002e0f089103200022603e1030660345020800d002e6041c84018050340d64005051002f15030100c07941c00c034036180c07012450001d004030300d1100c800a10000c104450000c091440500711030301542102c2141190701082d0b01e141105000a55011f0350040100310603240101e44a480484000d000292001e030340c1e8000b60400c59850809007003690007000403c0b01d484001402070b942d070060a04901c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 907539100 1250 907537850 907537867
    0x50a17280b0108012606070e03060c12070c03031803091404020f161a0103050d0f0201090b0f100504050f01061119150f050406060e09030421030c05190512 68
    0x81000f050003141c509002c010380c88a440e440f40c00c14940a2600303a4240c039690b041c1500028802141200601d00034403901000c0b5449a0450044814802e05032407042000d4480d000101c40395a0001003e80c1015290900c1c0d03841440000101c02c0365520907141e21020f0b40c5000742001a00c0c490001c41e510452041c402d05006070b0780707101140d058151a0441c020302050518000d580520585a00c5201c42c0c200d4002008000c4d001410b620381c0354480c0c403034003c84034103035104034280c070705d407400c0201020440400300e110700b1f1050201c940c02c10302e1612000c4415884030701140403100102e4540307880801b42801000601d07000540240e181000001810458441801e035040c06100c10f0401800303204101c01c8140c4550310742c1c0c401d2110000495042c4164186810041c000e04410300480400303461500c041408004008215012a845100d01058444a000711000c900010007010303014010b207003480300c0000c0d609000c0c00040300d1a81488410b0743d002401c11924260440540b00e005990411441a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907540350 1250 907539100 907539107
    0x70f030201051b0f0303160318030c110a080d0c0204200414010309021203190e030706030203040614090f060c0a12180c090209040e120a050a17280b01 66
    0x1502c01100d40c2e8a000c00c0034441c40c2151404c84481c1500c0303441c0c00007006222407540044613a82d0504043e9509114007135444004203405140e1303003c0200410000800e100002c1c16800781e00405070b10007009694084c0e540c0d01014149402400501c0001d04c44503903040461503e44900350140c1c042c12000c40038070031410044c15451007940209602100300e9151070b0741980c441c2d004901615400742465441b02e40609045030360f5000b20030340c2c0c0380c0c0b0344140001c02da607540304401e00441410014024881c1c503252503820f41c000d5101030300541e00952694968401c200302500614040d00b1004003d0080c0c03844a40c0035030420802421400801e202003012112050707008480e11054950000b000908011031310851440300000e48004120078561900014200302c0307603000d4100b000007518240540b94000d1141da4490300c03c1c00301c80d02811020300603610f42da88114064449150743d07060503030f1f40c95041c00c0e940e01d5002044070101207040e083c01d02d04808148440d4013806a00082900b07000b00c1c2035a40018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907541600 1250 907540350 907540357
    0x709091a0108060f0a09120302030106020f0607120c0c06020f0309070e090c09060d120206091216062018130207030c0b19021801180609061d03010f0905070f03020105 73
    0x1100c07103d1300700d010801803079840e480f002529070f001c113101000003072143e006800f82d003007482200e0242c001c9128070300210102051582c80740d40d070b03075580c0c1640314080f041c0ca80081c0740c40c030074050400080c4604000001d00078401002016003102c2d245441c2d1414100040c0380c0040f90304089001c07800748040c80030501c00000c0110340240222501082e9549400c081000c2c41003121f0040c002d11407070565082d0303642d008141c80b4001c20740003003990140407002c01c6601091140c10490049845c500d0307000e002148040d07011003151100c20f00c091542d01ca0344121041e2540048126403070714201040500e55a240420300101c0c01c0c58405015403c090f49034038051715003004001c0180280d01d41000088860101080019108021050443d100c041550a20010b00c04151348240450301c62028420078590050a01c0304803601c580d05c9035000d504102048821545448441c01801d2280380c2a65283d5000e0040500c1c81000d003030001035500702030602d1898160158071036401c01d142000d09002603644101103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907542850 1250 907541600 907541611
    0x102130f030b0a1d0613060501060c020d1707050d0806041d0613170d0e0c04140c0702061309092a170307020d030c05010515060a030e0c030709091a010806 68
    0x10110038104180c4c009500381401516a8060320041110b00c3c022170740303031040860051100b00400d80c1c0707841041d03078960700f0104003a5011081c05220800140c1f1410207012550320403a03150f05001c455561a8586580345000002058520041000b00d0030180700b43d04e910580009801c0d20070408090040c3c0303420025100c0c1c0c9801406003503660178040801004105d04041c410025641c400e514881c10040604482c210b100d8050314400f01d505203058000c00c450f90048070158071080c1c6903d15110032982c490802241c10040500400a4007114802c0e04c40c0181030021340441c5403a49813424000305501c1a03a00090020800203143c4a102c4400e04002034900001100000025580101c2c0c42c600400c1c100a42c010822800c001c10154041c000c1c4500c54030803002800b0f10307140c00c0c810722900720082d001190440320a01507800307203c0c420307080280c00a07504c200b40c441c1020406c010074100304c02a00006206521290180c1c1000a5881985803551409802402035410714901c580c40b018090719 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907544100 1250 907542850 907542871
    0xb0a0302061e0408030c0c0d0b1f05061201090507021614010c0804120213060311060702041d01021b0c1309081303120f0201050712110409020c0102130f030b 69
    0x72040110000d125603803007001c0b0310301c0c0580c1d11280d6035030f9416942d03803006600c090f10b40030b043c08009080c02c040b003014010980c808079681486ea01d001401800040201c030003600020181c60008103502c904c3d000740101007801e450800c956050880070000d98201030134004c1190700c410160700d41c0b00ba0703107143d09003640e01e0a0148216101518012100100c0801c0090b10542c1e001400080e480c80d15001004554800e072040d804180504081300c0c11200a88000303045490f03d0718000d07190749044401081c1103440140001002c091400d25605086401c0a8811490f980022800381800a40e91016028440300005180103048107010900502501180401c1640c03100340c040104603512003074400c228a0040000c60641d62414003e80a01014035880d002c1a250700071414400d206004540c8555595140c0c43c1c00c1e0a41020101c0040050302003c0344080b4003030201248102c2d1600080c0924603140c400941c8419209665180003601580142c094126211040000901c0040600ea120030440e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907545350 1250 907544100 907544107
    0x503070c1b09020d0b2e03180510050609010f0b0d15150207090612030c0209041b0321020d0212090316091d011112090a0f030206010303120b0a030206 66
    0x4202104a601e5070401c03100c4034000314035a1111a101d0780b021030080e030112040803055001061800c02c60561107400850740c0d10085501c40c005000350011240c4e4800341120b2050450540c40355410320541c0c40800321666101c0b0103110305031a21302c00c41c0303000d003078182050110145000ca0b002010701c103003c42c1c3c01480742c58000c01503541444c14403960007040f44030325a091005040c04000e48541c004d00500b0b040c14a40000450410741c0940c2c81d0713081c5e69040e103130701000300801d40802240d0380004200b00e0719041541202c580a80c180d5550340e00551080190b0303100499120034002520317100d00704c420110340c02560380c001150780c0000c07114070310380c6125100d85c0e40354001ca021034205803400c13400a80388240a207000034150803940c051a10010401d00c40b1051584400c1030b80c1c20380740a20740d801c001010174000c2d09a408003051000d900010741c1c0d0119504111641e90721ba001c020300c4401600540c00400c010018141c101002824840c0c40c1d44013040f00c0150540003440500507400b01900500021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907546600 1250 907545350 907545383
    0x2030702090c04080a0804150306150c1103010c020307140d020a02010f02010207170d180c0b0c0f01060b13080601050a030308070201020c07030c0503010f09200109120c060801060503070c 82
    0x98100c0f4064148241543c4403032a80d41440d9505038404c0c8039050041c8449843d0070f01a621910071032064420301a1810420380300e080c1d00310781136203035040140c80b10307030a284c01405c15070f400748203081040109401071034913810241480c1000858080203410203401942d000a580c4c0c0d404103040030341d00e60900340850351130340400c0f049009009034040101282051901c0024048a40300902072850115600344101c9026032002c01c40c7c131288040007050075244d00070603c03450000c40c0161489644690441c3d5299141014444c2034170708540c080005d0304c0e800113026080d00e50000d000405040010000c003899450100469075408103403001030100907091010400081c405c0d0110360310440102d0840700313450307200c0c00c0080ca40003c40c40362911962802a500040d9643e038000d0840154100603400c49010700c818210144403207130021141000080303000402da514400c803c5105050080d0305900d104c0307041c20300c0904010305c1a000724003444414010031040a40c0444514041a404400c5681208a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907547850 1250 907546600 907546621
    0x70b0f19020a03050f010602150a1805010f06032f04151d09160b0304110102070509130c0b12271015060302090a1a0904110307031b0203070209 63
    0x80c00010010301e000041044a955058104034000d41c03000041102599071a0781c10f07a076603c65569401070155580b8002024040258080c04585040c0b5040c0c034800e400607074580e401c40310046022016155a1003092061042d26240c1c5840d00f2401081c5844003c0003c40c241d80c100c910000f82441240c44a41d4104c1d1420301250901c004d10180000004c1494400610706c1c5141c070413140d400c981d00ca0100312450140b400ea07098001c888555800b18510b072115160030100c3c20a80120605600c83e0000002c0ca50702d880e10a944110022034a00b10010010715207030840d031003554000000c4180500445419110020303200b42c11400c440702d0440804a0361a807101000b800840c6000f541c02220f0710fa01042d50150008818a014421055903a5417201400d80807402002801e0f50050040c0340180510030885168a106242c6a0401810700417807900207010342e140d052039038606010120a0044054141c020101807141c400d403610b400c0101e62000943d00e000710300000e840b82c217495000c509812070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907549100 1250 907547850 907547881
    0x5251415090c0f03370f060b01091a1e03070f0e0307031a040f12050903010506040603170708040803040f050f0922080c01090305030124080403030e1603110312070b0f 73
    0x10132000d403c034408150526015000c80d0b00710a40e11f09041c84200342080d071241518506a8075010348800f170044501c9082e00540d04500790700400030042c803405080c1d0710065405544240c0080d40c548217045944500209480d1400d014180a40e010704030503c001802860030070010002d141e02c030302043d078480c102500442d84c110000b5100303a080702001240d2641c454010800c0c014160000d001e21348030b990a100c1210314622025004039080207015010107074000081c050346000e1000c940c10b25454440060540d0300550081c1c0c000d0000701e008029505100700c0344a170401040380d4880c3c8620b003145010099185003890881d4402c11603031f4050401152070103940d0002e0100c0000c022039000e0b0321300a130456100b8013a8005000341c0b4280d21010914106010038051156a2620a1500e407682e0035009042c040c8a0b03d640c81c001c41d54140102e00704400c401c0c000314058415401441a20000e15080404a419001c500882040814003080f400b401e003d80040c03020800101503525040401940d99 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907550350 1250 907549100 907549183
    0x60e0f0a230a211805030d0809031b0a300e031203010e150a03032c0d060c030e0c0a0e0402060f030901090606050105251415090c0f03 59
    0x1181c4081d00030440030151a107910f142d10b031169071145008401307100d0101c2d84107565150b8000102100420711805016030007807e002d0441341400d100300e00c250080e07040e000c481d01c0146d00c8004054180596003501c074440c1201888055800c401d40f4180c05e042400c10041d91090000ca44106606034504109640c12507000898058480d41c440814981ca50410784522417020a415104400c915025000c00212541034580003202c40c020344040c40100d000100545480e048540c042d40c0342d88607521580e002501c80c460010f244e0240150107022106007002d804100d511426000119845000c142e0090300c2d01604815502d0344c55200103003c91003505001d868120001c011300c82c0c0c6802c150004440c29205034010310042c0e480b0001180e060081d40070b003400020b201500c24100f010800000726800e0700034013401281844414106180c081100c0c0000b00c600070324410001072080c00d11400d20b0100c1e04036403d05c40c107042c60000960f600340e5118200b0200301e00b009003215500c003204403c4e9000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907551600 1250 907550350 907550363
    0x50403030f0c2a09150b03010e06190602030304020102100c2c03010204031b0e04021509120303070e12030304020a230a0e04030f030504020a12060b0d060e0f0a230a 72
    0x200080c01140e1103e69220b0305000c00d044c022118000044000440705807020b80c1001c6040d41e1130090131641d0b143c806400c080d0004c00207038041c070009a40750950800380240340c00540d901d040510009143c000342c481214141c901d00511a07078029840503180401203824852449039550a0440c00541070481e10700640c0766100190020400000c0444804d07802d1011034a805d00c01d0b0340d034203013800c3c0c420211402544000c41283c43d0460f51200c001038803c10314040d10340d4880820a1010380d1440c0d20039116100130490a21031342800d46040d50300b040070a00c00c3e034003850071400c1c5a804901117480301d024402038a40c190040808070b400c018a11845128014402e240165541c502e540320307031000f6a400c0d40040c40c0144000310540c000d0245600990380a8900c5054a1912172803060501c2c0301d12007200e0064844582540550740c60800007501805100d0010312000701c0c49500d8a440113000f10684940c1054051501240310035006100d514600d008034203005051100950818041501c01400c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907552850 1250 907551600 907551653
    0x1803050607021209091303111b030c1e040e160f03030905120d03240305010506180c0706091104020a020d020f12041a0714031207050403030f0c 63
    0x2885000910103014001e940c094651800c042c1c0b09040f01c41c81000300c240e8005d07041ca804a540440032071003c1c03110f0f500920382461034082020318642050801e0610000346280c2c400c0d811281e24040c13000a1080300100c8940031200101da0f0411130040f40c000030b1034421955051a0b0b0301032401404541080c401c06180c49450503100c0c1b00c0384059040a010a070b00103040b000c0c000c034890420040300d8070083c0c00200145410050380300c0c22800f8040c011002500e000c0030f8210341c21845100d20844018600c600d00202d402e1505505101c3d0f451511030091038030400791001d020b050201241107910382ea030403242c08140100d482c2003151226007400d03040358100d803001030078280150340440c100d41030780c070f240d1b0076a0a540d6008030074959078001400107d41c400c501700410015500c4103041d000c1092140c400c01d40c100b5400da12001c111186958500c40a9000021515003503a603005026901925506000707045c035095407001811240510030040500c00310700d80320005c0c00308003d203d03070301000c945204402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907553956 1106 907552850 907552853
    0x603240605060c0319030216060506011b0b0f0f160e030c120f06010509040b0103060525031505090c030619231306060813031803 57
    0x4116503128000900d5449820140041c0280c10340611745403044207680100750080c0040c102c080610410074102500030b500030022195402110000d410f9a91800582e9031140d09900030100102d5003034120704010b0400112440741c09011000c60b041d8481d040300204907442070f21021190b811380d103401e5695910402c2002e2802c4070013012a00441081030100b07220221001d02c41c0d00035005212608014941040b00c1070040005440700c6440d40b030981c4808440c0441130200074042a100c2021030102080b548048941d91000081100010a07810000d0020130050121000355407030b0101c006060701d00304048074445c081040da22442d5035907100c00c02c40500f42c0340d02602024000c054000c00d02d212541144511580c1210741107001500341000c100050810850100d41079040275000c0c1b103803d5102c3d8400350000401c1550720808138a0345002c0d1212700300001c1500942e518000c0010 = true := by decide +kernel

theorem cover : BRFrame.Cov 907374100 907553956 := by
  have h0 := BRFrame.cov_init 907374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907374100 ≤ n) (h2 : n < 907553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
