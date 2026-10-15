-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4789
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:43:51.747369+00:00
-- url     : https://prove2.me/submissions/aab3384d-cf86-409e-99f8-8d6f5076b496

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 861151079 ≤ n < 861330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 861152329 1250 861151079 861151097
    0x7091a27040617010e071a0702060319020a03020c060703052e051c02090709050a18090c030303050a140f01140d06051612091a06060f0c010603030908070b0a080403 72
    0x114280f03040b510f280140343d400000c2e8008034009441d0511200e81c012140c0c10080c610408100030802050b1481a601180d0b00c07a92500c440390425030201600000303035500c1c0d00200b400b644080e0503502030104041ca1105071441950307180360440485200301c80340c0c1c1620142541e480b20360307198048071440e041c14030364100d8078003500c9a0010710101012714004440c1c001c6003070504114100300701c161f500010b907800c21600741403cac00e0004040d84018000c0c1c56540014581351100d07824150008802241c1004250f07005581781d09009002d04821900d080f1401e003011039410028086440091103004103641200e07490f404c00d620042640600d0308807990289218204c0d002040c0148946809401c03444020f00c691903c64401401000c260152060500c0c80c00d50300f8000b00b800d00760345c0188101450080c06c1c0b1541c0b124001229409045402c0c44071500119100d40c4400055102800343c030f01076280e44903030760758680195981f294140501c81010b1424014172280e240200c440e19040f40c0719007451214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 861153579 1250 861152329 861152339
    0x7150e09040605010f05010828091509061d07140a0b040f240e04050403180f090f0902150307090902190807110d0503130b07091a270406 60
    0x40d854040d1400d0300d90a81c1c44004004148000c14803000070042820805441c2c0307001640180c4440c83e0014400e00c43c42680d180740342c00401580f004181c998003188144580c3c807100103c20080140f03d5044507000e08c0c02041d011090051480c401088000e20004c00c00181000c0761004020303d030400c40d035008104040f0110f08420100041e10251004220464225280020181005801c003448440111481e6000e40b021580a180e50002d9107041e180400c0750707100c1d46011940c40c081982445500702d80c0703010100300881c044603540d048551400d03090100046666580c0100d1b5203d0030020344c0305038800011064460b480002e103601581901700001d00c0ea41e07907914041a40d010702101c410506e0200d00070700c030058010107a160840c1d010f00d00103c144420440300c9a85002c1d80c113403a01482404400625501c0c41054220300490b40300305070840c00d0402d11000307820100f090242c50081380300c0841c25080742c00344505031781c80e550b00100c0000c1d80c40d05282c4802412503801010315045515130740b02180d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 861154829 1250 861153579 861153589
    0xc040b0d022a0106120b0612070302090705130e0702150a0b0a0b0910030515011b0203030c060912030702031206030102092d0604080c0105090a0e0403050d1d07150e 72
    0x5408501004141c00b0305059003160071100c0c0c41c0c11514000c0895846000468003007807869510000c103841103800c4070b900002d000c0c5813003200e81c0020751240302c040400c00c13460760043c082e00b051304c1035003030402006880710800e200001c012a214001a44080380d1300c0124482584010f07084200ca500c00105040d07210081802c15941d5040141e04d81c0c0d00080c8a07507a03040c040045d4852051310314003002242403580c001c2c6548010320079602e04100c032805410603029001c500c2001c0c8181d00404490751275058100740c0e5205c41c4c0484400c0703510301990603440d800f01101c0c4100c9115120036405586000c4c60400a0038510102410b5a43c0544d424003a03040651180c0001601c001700603a841040002c100541c070104040b003034800b50250304240010800d101d000200d0f142c0180c0242080d94031100300901140510354254011404000c0042c01d000030b043d003000062111800800c010300200542003121421303049451900001c03640010010003201c0341c10783e54410a6001840d06002038190040026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 861156079 1250 861154829 861154867
    0xf05060c0604352502010c0b10120501090605071e08070c12080f1b0d020f0f0f040305060703050f040b0c0f040b041502070b2d03130303050604050c040b0d02 69
    0x14075240400683d48011003180105a0300c4c202c20300da0550000180c9900081520801c0800200203120810115030044075194140d000741a03003c1c083c20100031541007941c003034800d003082035841c09d140c403022419080c8510700c0f00a0340d1183d21121348a0301a400000c0341ca1080003002d20080010308004a00040d915800d00035003040c80b641c81c0040c40c2001c0c4001c0201050242c21004100b510404e2850858810380640d509107441040040c5c4940320424041c0c80b034843c070320030306201040008181c40d46440c084003038000e681c010011600203944e8101c0030b03000c07070f002500c10304500300ca0b190001c1d000800c003e148540c07080104c203025040029002409640c0d81040d0488004508042014400d154031388107503041d8107501c1c0c0f004019441c50301e14105aa842004d003084003940c5031011ba05940c10005813030405c01e1108180c407990f01c0c9402c0211303c1c6e100f40300b8941240041d0030040030407030764034142c0101c074058130b07481010783c5ca01480d1010500c21940301c84205080103809000188403920060414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 861157329 1250 861156079 861156173
    0x180a1205090a0e07021203090a1209290702100c15060806060301151a220914012301110703080a09082e0b040609060f05060c0604 57
    0x5841e260703800d007081408000b6801040714000c0b004100409140d0000310005601da01c0051540d40e40c5030703038000c0e90a0059098010380300c403008840c143d400b05d51007a5180704580c0032000400402d4034988d54403103c0607000e00452500303841805a000580307480c1860150481c010301b82a04c0ca81c90560712400307003c2d442c410928440b82c4d9660104140c1c24144007560307100034114020440360b501031041c0c40c29401c0324003840403480c00700c1c4c0030103521080c15000c46500f64014158103008680303880d034143d032070700541c00380310302041c20203040f041818001082daa06940390a0140202040c0c40c0c0c2801c6c1d00290307111031075410007911804031000d8034401d0007440d0146000c1c01e4016507a00c19440701400d0398500b07903c1451154031041d04040c07001d04c04801c18448851000d80055200c4401c05110060240c1344425a40a8900b41000506d800c00d43d00c103004541010312142040d42e910800c00019001d8840200090340104000038001520840e21000c1d218440c00c04034400450f890a078408034050401c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 861158579 1250 861157329 861157337
    0x3080a14090f01270623100501090504140f0a0207060504050a060e031603050a0c150f0b030a05120d06080303011e12020d060c0905040f1a090c03180a12 67
    0x2c40402100203008084003c1c0c0070007000380c12051a1801c2c0c5030759814528000d00420340c0c2d516150200e02c074003150104170000031568031207030b820803d042002d24660342c442c1a0100c0d5040100081078146400703500d04200c2c002d0b0301d0352040d50b1600040981003000400300b0f03100b07603030030020900054000e101d03d90160740604014000c0c1e1850340b609070100c801c40300150542d40e00a0100442c1e03943c1050b0029019949490020b840d40503000040d210b81e459844003c2800c501d81128004842035030b4060380e6881d02d050002e101403584001450b445030941d81c009041da81000941e12500040d14006080c5080320320701c0010b085070b03510300c40e50468101380c0018071180d000a510411003117020303641c0310140c4003480d400001b1031f8507640012221071469000502c071944960300a482240500200001420054000d0041088840004004181d980203109151500042c03000141c200080e0180c461140b28100925680300c016040e00d854007881142c008038841c8031800400103e44000c0a0700001d49921 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 861159829 1250 861158579 861158593
    0x61b03040807030f060b06070506070c0f0c150f091505031e16080901230a0f1d060a0621050c0301020a0c02040b1f030216050a210509060703080a1409 66
    0x517000c0c0640301b00e07810030f51181e0740900004001c01d5011a04a0f08603516088c51482141c4501d0302c02e01103c404803029100d168000303000601b146002940d1440360360545c2d00c1d1030108200d10710540301d6450600a40304d00314041c21551800c40e0087c4000e5402c40300207072048585505140c00c400190004440300110406803001c18030050313800a54403a001100b400080c1b110b00c3c0c803815a0010580d03284031501c0740d07940c0d010120381c400e8840e82c440246000741501c207002032020740d1401101c1140d02c40085004c3d02ca480d000504a90413882030000740c424244004965038000055841042081601652240511384c1c03c410f00d42e600340b000706800e00319620380917002101801000100c0b080c6004160184061210008800c00340a4a0f50841041c6080042e10381015680403000901041001880f0348154401d035414007400c00c0c10401800c8040e01009103000d0580c2c421030782e41c000d4011050b0091b406000c0c0b6000a40107149007a408404600001090402200c003503008020503600c541c00f503000a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 861161079 1250 861159829 861159833
    0x30310060207060c020906060307030e07031118060307060c050313060309032a1e05070308070615060507080a030b041d0c0d0c051005070f0503030609010f0302061b03040807030f 78
    0x4801d202c000d00e0380f820281200a0160081151018000c00301c5100e60400000140614003e911042c6040b40440c22110003a80307a10380003c07268062900309125900c070b061a1140104184080d52003a480507000d46107642c0390110a035030303008400c0c600700c1d0240814003104526070500403400c1c006040c0c55902103400002414060246444140103040241880703100160004001c1c0d01c400103503500c4220038a8405800c801098030504680d001840750142d83c80000c14231001c02c1c0540740e098000c2074100864020040c83c4003024a09114038004074209014270700c08120404064140000b40d0b013804211900c1d0400090b080310072040b0714103000380c401d40080c4040c0000700140050403402359203505e1607004c5511981708880040c0729091180e0401c100c0810128403078815242c0907980012100284249450890f072260001c8954a004a41030030000031441070004001c02186c0d0081c0a5038640805800c00d1140134101d81200440303803108010000d640d01d003c0050f00020340c012840d020740c0740054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 861162329 1250 861161079 861161083
    0xc01061503050403080f04020f04180209010b07020112180b04030c170315041d030301030807050606090105010e0405090111040b0a181a071a10090f0c0e011107080303100602 76
    0x3020041050700d400b00304000240c118101c00d0b08143c4031074809503107584a00c0080d202d0305e482019a9000740c1030071501c4c2000940031408100191003120f580883e03a0701c9004044081c060300c28041d00040d884601401c1050096215419004808a4000207820720f610385a0000000742c0e811000100055011014403c1e1450100600d0701c030a500b00c0e1550a29801b0040f5507810044214443d558440c40400c4040c10b680c00c211800450360705490312036070340b420005155009690107640314081c00001407505d1a0454206043e1780d41619001c880e1025041404000d140050840285642e200a943c011403c00c00c0075100504201c1c550342c3c0c1e50200031800510710b103080c003103280400c00303034501c240040804440103400401002d5212529001035080c030200e66a44182c1821007090104140003c04880e4a00348068130f00b203030410720803200c0850b9001c04941c112a402c60010300c22610407030640d803080416030704004010b005c90380c031162500c02c40c508580c01514034110032210300c07904101032501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 861163579 1250 861162329 861162359
    0x8090d030f121b050901020109140703141504030507080702031e0c0306060a05121603030309020103050112110603090a1703010303081b040b0f0c030c0109060510080a020f0d080c0106 80
    0x1000c2e03820f004459909030802c03804240c269a40d41444004258013105034800d601030701c4100d03004a07580e4641d01585480e40c0d103a5402d400103030359074088154403214100340040c85104c20294040c0017036940d5581d81382110160465075040b01c900c5820008140940c0c3d0400c50081124603104240354071441051103985006844940345000e42c01c810f04001507551000d40100403180155003004c2605062106d56043c030b000341c2281079810103018404021315a0541c041000d851003a00c0803c0303140d88403501e4140122100d10000c02031240c2ca008042c450612034051904003d000080f106030880b280d6900300c1154104107102420300000c0010402d140d03010002c00d03008083d459a00e0749401201c403038034609100c3c2d0300072506007000001d2900383c61040c0c0b50440c0c010441e5217060360f0f00d9200180555006c1c144840041c0c40240c20240400c0800c1c5404604000329000c802c010103d001c3c0d95800e00c44032054551645034042c549800e4400411000401041900c141c6000010b0490800c020b40b401020307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 861164829 1250 861163579 861163607
    0xa1701050a05090a05060a080d090801050f0f07210c0c021f02031803150a0f0605030f1f2013141c14010e010b0a0b120c030408090d030f 60
    0x90207040400c115110410495040031415801007010341c0c0c0c68002c200880e1842c0d11140f010322070041c0c0c40300241da11298680903124601d000340b0840d00e8521070498155011345031a5107003030a00e40410070142c014508404901c00c007200c141807050700403805800301c0c1c0903c1c1c100400b1520240c42002103151840340740c4a041c280c00307074004040000c83e600070341d40d010f4a440e01716a030100e102101d9850303501f040300c00781c0225440000740c564076000c0740c10340140244001030394030355080180200d034a1a01046014180080c0c00041808160b1041d051014110000148403981d0303032407074007a0170902222002c2c038074908080c00459546654682c0244a00e1265102c007c4254903e400030005a42d86281c00c00442e12030403900344108aa0b0514100755400070381c04540d03a40c40c003a900b040740c07034041d00501000d4908481c13400320b0940e00e48071910305114880b0003a1084c00e01078005013a040d045030241d90050b01a00c402400c00038088045019080059000d40c08108401442442c1d580c0c050a10544e800c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 861166079 1250 861164829 861164839
    0x4090f0b0604080c19121203050906160c03120204061115010b0f0d0b032b05040503030d020a021e0307060b06091e0102190b0403141c090204110a170105 67
    0x80d24001c54513441d088558102842902d8480003c1006040f094140340a061b505d800c048a4584520700400400000032000d00071070706201c001002000c010500c6407207060300d021149000c0030001c42c02c85502040f82001c82c01c2c010040d007a0074000925201500107814140c8034081102c1400300407a1422000c0541c10b100c2a540c0001481081012030907246c0558070360021540350f11003044a40d0107440520381c1c00b501480b6028007440828000c9020035413100c0e882144003081110307070314101d039a440346010b00c45d050361041001204025141c1d0040070b00c00f00342d105450785840307102d10f0a10380c0f614118146403180e20108510041c444580309041806804940d80e5251207401e42c00704040781c961402c0090782c10304003400b441c401e90091001188140d5900c2a00c04500e46615005208000590f02500010700082c00c00901c010300904598070302d071a450f2031041240d80304400c034024144418089030880d444a60f4840d10144240203002140c240c1e40300e9031041d14220a509401080590002d8491 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 861167329 1250 861166079 861166087
    0x1003140304120201031805030738060f040b060a03090303110a1e05130b0309010e03030f0a11070c0e0603100c0f0302090a0b0a1d030a03090b130b04090f0b06 69
    0xb030340a001c1d04040d03820b00740800c040c0f14895102e03400100501001c1c03d2804001402400c0042c1e4012019041c42038584140381400200e070700541e0642d071291250701305404100411003030710300300e2484a0310132401000880c0f60010030000c01c2c0c0c56000100000702090309c1d50048020140c15010b00c14000300c22030212401c001750590001c00c22419a400314140e00c090009142030544944205c400d17402482d0301440800d5511407840150707910841712201a946414022010004040100d0380240500c101c00b03941900d03601340c0c0500800641d8100607424400700b19403130004211120395402040310082459a905c3c104042c50f080c09060041c13001940e1506000010320768004c50305110b211510300d0010b8079242f1080204098901e00d820079610340c2c00204510703800e02e5008488561008008003071500241002c0b042c56551690414020049012280240a1b01d60400c001e40a2a042020b0308004903640740048400c40d40140c02021060b0f0725240b07481d29200d03850041100f040020356a140ca4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 861168579 1250 861167329 861167339
    0x60e190b01080d0f0c0312060605040f080102090f10091a12070c08040920070c03050d0e0a171f0606020d0c05071a0706060608041a070c02040c050408061003140304 72
    0x701d52060790140184401e05d40c030801031500c2210a07188455846008208050703c401003d080c0740c001d48220a004441c407503010491a5040c0240d4064034005414840b42081e0b0004000c5c00d0f61f5650400c40401070326410015031400841003480744101c14803a0b03999640b0341e2a0352045000001405001444407a091b1240040c54802c200e80482d1242c0400003508074030b100850049a540300705101c80000081001414054096641c0c4200c0f44240e04035100e103c0f41d80c005564007021400500e9200e480d0b00d03c10460038004e2200c4a500d0a1504e05079545001c5092100019108400e1056004c6941d551f0500030b45804100014582d88c9034142006200700503581e807603603142ea50281080911000c00d60019101861094651055204005000c250348845c0002c01c0380004650603071701c07200c0100f601c02d1003c00c19544540220bc0703543d82c17164088000c0c0c0902001d40950024441000000c010010710590103000c113900036110034050500d101e01e1400c00d2481804692580c88140d0801c11007080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 861169829 1250 861168579 861168587
    0x6090a09121b053a0203092b060501080d030e0604020d0c03050a03020c0f0d1a042105031501031413080d0c0210290409060e190b01080d 60
    0x30342480500d441414201007400d0707031a0384000c00c2c0000b422840b801521000100c015144910809641d98614050140c0703801c1c00f244030f031140e10200004d0703001006842c2c090304040e485510302c1c82d442040080021503420200c0b074440a1400141c40c06540c46005010340301061001121484072450188001c1c0e00102c40181c803001d01800092007460304a9803c020000350500304001103400c0016228103140d1420003948030540610228491f1840d402c11544600e0a01c00d05410190442d20403400004844046002e000002d8410380345003125503c46a044103602188c941c4c09200c2c1d6507040d483e800c14130080c1d00005802d294030f905050511411008014149103081d03072140784411181c0208041e801c203c0e40e24801e080304900c501d41814170301c403552500082c900b401688180010030001c07590300c0b1000da0102100003040301041035602e81c0d204615080d000081c615008210008e110189521401e2030a5a440510031000d038003d03000b4800d0000c0944094018904a000f8260900310300c50010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 861171079 1250 861169829 861169853
    0x109180b270702061e0402030f0d0f0807170403030f0b03030a1d04180807060b0a140f0907120908120a0902011206060512040f02090f24060904021e1206090a09 70
    0x100e4107452550010b819990100120700004285402b50b0380000307003d020003460780c80ca4483c44000709022602240c0410300c940d904804c00d00310f0300c9425000f52036030755040f40138244220f440303c01c8546440300c10501c0d030303828001410490398644070184940501020070700c80c800c1c4503403140c0c45140b0f40034040c192042d02003401c0556980c00842113030fa42c00d440ca890300040003280ca0f00e40d04041060001b141c4110303909200c400e0b0303c404403055903061020034204142047d00311140b030001080648000601e04007900141003040c0300b808464102a400e241c00c403c50401150010284d0351180003175020365810072500314008200c0002440784900b040c0c406407107031182c0c0307414403400c2c08000001004e01500f211115075803a402030048020342084840104207540544103030980c03910030701c25440e142c40c500000b0f008551000d05880d09050008041000942142c1d080705015400000d030001001c0c4480b009103040e240c1c41c00c0700c0040d41440010300151040081440741c1c01440e00078141d0114540c40d4200b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 861172329 1250 861171079 861171121
    0xe0108030d0c02030d050907060905040926040b0d060e0702030a1d0d051009020f180f07090812071209180b06090a06020f100504020109180b27070206 66
    0xc2030601046400f00d14503c18090100100ba01d02001e000307131014045040b030105e600ca50b0b9918406921101003008851607403d0081511080360100100d5030b1603401c110f5416007450280744e007420780d074442e41c04090b4021400641195a100703c14040660b80d00032154020a1910055040504100010742201d16a9a0740d2605602044503a003096869003e40c01d0240d81c08400d5403058580c01000034050808910100c0c4107005003800c0e40c41f0b13400c00e41803511030b403100c02032040c2c05502c0e00704d901c01d4502c4001c1c00000801c28003000c0403030304680401406215251144216503108824202b80000f158418078050801c040f11908000540c1a500080410190910001046a81c042c00601b581c452804813942101038050300090540c0c02040c80c2200e064404140c61240f91000705540c22114100c130002c1c0450100b5400b8030850074800c1c1040700020340d862001490801d0200010010a442403031116400d030202c840f505042071034885160000060b000a1000e414070310001c0d40c0c0d010f001da40d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 861173579 1250 861172329 861172331
    0x907080901090c0b090f04180803090c03010e150714030f1e270a02030a0f030201090c0b0306180714090a150c020a0f21051c020f070e0108030d 63
    0x228154510030350000014540c0f015181451940c1e40c1e00a900320303049a0362051051024481403420350510740100841e402200803402c00c24001c0743d4460005410281510191348211081b80d1603a4401740310b011031411080004145218184241010000c401050305080010907200314030b20010342d805807a00030302c0188000c451543c860403410b143e889070b02000031203101351a00740010b0070700414240308040e045c000d03d02512180e0400c03403555082030000081d015030003143c3e0304c0d01044514101030700e0b4512a1001084c2d007602038891315042100c980140d145000c00000740603451402c00000720990050b9100c15102e40351030f1002403c0c1640c00d8180c0c0010640c001025212961408503070710140c09075031060200300405581c01021a43c00140490080c1544600030540b03100028060301260074001c00660001580c248000c1001d5815008a880340b18402000c0c002c081c00001d5081440f4041d03000740650b0043d011258900305142c1d100380d03080d06240005010f0b045020049600e140007100b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 861174829 1250 861173579 861173581
    0xc0801051513031209063e0312010501030506030a052121040303150e27010e010b040f0c020309121609060501030b09013602070606030506070e090708 66
    0x1010252611074050034402c1c1420500e808800c010010085000d000d060390380e190300142c5c88030780c141e840300c0b018000c0c1250060f2480e40003d0030031864804000c61460309000d43c01039905102614995006015103203c1142240d0044c442564548640355200800700d0042c03440c07004a841e0641c80c2c242481c08034041c03e24140341c8100c0d00b030203803040711503070307c14070502800031074024080f044114000e503404c0300041c0c03c3c0b48400060803543c00100c03054800c110720410f1180c8502c510000880103005d11540d00300d4510706000e01c40682881810050700980d0b0001c501c4c0c100c0c4000b00401c0300c074081d103c1c10402d881c0c01095220107070300005031200c50b4029100d421075043d0300e002003032a000c2c201c91000503901c0384550100340b02d849a0018030440300c080e01e042c808400040304000c1c40c040f090143c980a8415005451007615a01c80b036007441411030020440703041c0c080300380030080e41c2c030410040d00d83d261a074004104100c420400d0741d90100c0c0914281000414079000902c0c40d0380050041d00810508074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 861176079 1250 861174829 861174859
    0x20d1b02092a0408060415110a0305091e010b090115091404020c0d05130905060d030c060f0c1106010b1204020111070e1806090c030d0c080f030103050601050a090c080105 75
    0x4221959980c501c2c8403500c46540701c541c4c1d0f5540c84101c40407601c4009210a41e04000400e020f1400c8001c100300015060100011046005050040040c00c69200c0ea880001606004281d030541c0c0e052568000306840c5902001d01c6a0704006a00407080072215000c0c12a03110382c02b6071308000340c6110f943d80b20a5420008000303000390150701c1082d5043d004144080c1e1a49400c080240300404040d00b9507481c080d921000349045030001c907a102d812848031005503000a02c035080144802e8480c207000152001303080d151104641d84680100003207100250014545541008040d005000c070f20b00b0540741040648071228000800751009040c04841e49101e039802038144001c00190608280c851101d14041c241080c1b403000038001910071f4000c08012400c24074000c88c0d120070343c4d00081c0040c20750252540c0101e511000298043d500c0100a10512944d0015031000b580250302940c0144025410030040050b0400142d2100015900c1d000c40030400700c0c0c10040300f80c11102e08840f5000804040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 861177329 1250 861176079 861176131
    0x362090d0212160c05060c060402192301170135030904021b011410090c080c03100b030a0615081e15040c11010b0d0f060f020405030d020d1b0209 64
    0x150b0171880d4441c50124171400001000188284210b0084600700a2000f5044200f00340d4081401500c03105900d481450064480704981d0300340c000301c103250001d6500365070042800102004e8002c505130b4015030b41403041d90300601c00488040c21b008295040f2010601003003d54901c03075103492034000d50700410750200300156031040d103440c01d07071180080c4028048902d101e003071340a08561061000c451104003080709180d520a0002c0070010b5110403400303440d0314804030040d0308014560000403072107a8011035180700c0400035602412032100040b90040c140041c2c0c1c440300307007501262820070019008104140c10304520403445544000413a8189440b806c8100a820307010a08994000303050240c6901900e600c80c1002c9030100821008104441c41a401c21030139098114024011a402046050205041e070b80100c441a05c8580700500d05942c60001c41d06045000c102000580c0006c44844080c41d0408441e1492a0722080780c598400469400a044003001500304407091021013880074542c290 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 861178579 1250 861177329 861177353
    0x607090f1e090903050702100f1e020a03140d18050d1b110321070b070504080a301112190e030a020a080a0362090d021216 54
    0x1405011032030030141c01c050545400a44549c00007002c03225048001042404ea04a014007242c0c06005d0b40f1b0f0941e1421590401d01da074854600e40c0302085001d2030700c105032041c240c0200504d00c81c505a0441420014241051500d04038244440310315103035004045508510903003a400202d50341d0300070000c1d01291410310840012034140001d00403504281c200c80010b00f074800c0c4a0030041d44142d548101c100c885000f0762140d24090b034800002400064420644c903a841d96640300d140c0c400880444034a958036500004440200b10a031400c84030b034070300c10f21a00c40d9200701c40f082c0b949411010403141800040200780d0300c00b000100703c203030100c41e038051000030803035038000308410300301600e0b160420b86a101c1c4400c11008070f440d07500b810580c081c001a0480c06000600c5864020445d0003130408502484801460070640c40e107500c0b001411440e20428004404a45140c412440c1040d0801d10300360b0481401c10940d400300007900b6160b10801d003120002c1c0c1e10b4520a00800143d45818a08200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 861179829 1250 861178579 861178583
    0x2070308130e151003060b0d0e010207020d11011d091305030c0610051804021e0d0b090d03050702150412110a05010207030e190e070c050607090f1e0909030507 70
    0x1049205120b04052107580e0400300c400112018500000c10240c05c1e0b0459030745105100f004841840790b105404401ea002d6144203414200152515416500041c4002d20784901100c440349078003260021560f0040412080210b07a0012003918131064002400c0000000c01c49142c844150840034208401402518021144801100c80c18140a4010341901486004070360161070341c0071002c401000c030a02c06a01880d0064940e290810500d18402840014045a240c20648034103505000070003400419220301d000401810442e549401c0007000d948000d41001e0840d80312203036444241852107105074020351302150b003141e884070041043c1c0c4c0b0f44448130035883c100d004204002c014440190020200544666a43c60000300c034030b010001c4180140c0c045000d01040804280718050f0015607044e04003209041003041148203540d40d925100d42200d1441c005190118100494500c184c06c0c14064402509002d0364603152400020515000c1d01c207003141c064a450301481454011412910119 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861181079 1250 861179829 861179849
    0xe0a1104170c09100b18030307020604141302041d100b0f1b0d02070e060d08031504050c182701030b100902090117040c08011814010605010207030813 66
    0x4482100d80b200020300109004051103030014642c0c0d08036400401c20340e103015683d141030041d82600d4002c21741418000a80511080007040d01503038810001c3c00c0104500c0220544420b02d400a000e072000070f031014680e03060b005000900410110b1800c040354110410400f030580e81d142400b015a1f40303101d5201041c00e240001300c0c0b0320030005040c02404210711003950b0000d0040a81c815507550501203c0711401600705803018421284007034a03007a000940100041c8106e40c8585481410f0740c002e640f100003192130600140c05c5801c003030081c146e01400c0c98030424141000820303005407520420f0002c034800c240011b040d010408054103100080c034441100400345685900c0c14403203143c029100505100160b5500207440441d034021210010010ba5030140ba884042c66527100c01c01010780101c0704020008030208100209104402d400c5942c0c0380340080c0a40c150500c12080c1014100c8040300c2c0c2d040810078000359030009040412a44d00c1036840399100c141c0100700c4115171541d00120718103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861182329 1250 861181079 861181109
    0xc01080f0c0903210c01051608011509050a090605030f0109080d0b0301090b0a0b090903030603030f2d04060e0108060315071803110f060a080105100c06020c10050c040e0a1104 77
    0x290250406840c174040c00c0002081580c035410340da040d810101c4102c400c00035441c0c5005110000340d418140e5401c1403182000c0101a40750b02c00505401501c0e0042004240c0d120070406c0b0604d42004001c0030007120a00800040c0e0342038541001c1c0d88100014002c00710b031501101001510258000f68900350400c1c039400c5981400780c2500068408003080a100780c0c52000030034081b0b4804801c6130300410000300254500007401030360b600581c109403031140c0c8102c0c98000c2001580c2d00100406103500500945566440c10400081c15280c61900c01742d0400c0307115000c02c8002e0b180013404200d0310082000c04c56039556600411504072440b4013582e90300c2e5040030000400c0108582d00c0a2170714004542e461900c028060612565006818240b00016042c0004001c541040001900100780c24034044e40d5480303a0391141f0003a03910044004185130b00441a440030326801f4824140c216101070760340c070f00e01460301c42ea9171400311001e03141c1814540c1c0c40c02c409900c4c085140844000b01105407181d442 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861183579 1250 861182329 861182383
    0xb031b03160b0d0e150f070306030f050f120901050f0c0118080403050c01050307020a0f050c04140f011a071b21060c05160b0a0f110c0c01080f0c0903 66
    0x109410a003402080c060a1481c50610202d001c507200d82c02c02a04810304005c3ea0381c21100c64407072a80900b00740c00b8180d543c070780800070a2101c1c094800b02402100241488000c41c0c221500d8502200340c1110545028841181c0c9a0303802411540c201602e101303c2c0d500c80d030f8a8900c039801441d0f0410072042c02048003d09508114041c400340c000c580c0a80c043d92914683c1d0710042d1103501c001c441100058001d100400001031003010721014650241c0102c1d140f00c10140c01140440d40c1d5030719140c400c43e00740c00401800110307040d60f003800741904800001d1542022032003c0c3c00e5000d80b08000300301e080a001840152619815064001c00300249035000d40f40b031600b030a402800d000300050703404904214079694014040c004032890b0f40c800c12682c10f408041904c2e180c03225003000d001011030a0f2613100c81a600009805441c1501500c00306107a03595018460491500c1e245013003886c10302688404106a801c641c101d441d07401600240c2d1295200b8032040001d0410707200d008400090b1700e060f000e000b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861184829 1250 861183579 861183599
    0x121b0f060e0402040e0103080313020312180d03080103080c0307080d02030103020420030703020c15012403140105090606220513144c06030b031b0316 66
    0x12a461525000c25254040e001d02c820784c0700f0b5014910800101d0001000000c0030740004551040503100e510680d81e500b039000074185000151040c01601010402e81d6094507174001c1400b8181e001c40c4c0003030f05e2810035035010344110014440942503103408aa90340d05890180100c480311035200505d41d0343e8000c1c24181e18020340080c082640614640001e003028001d200290060306009143c801d411590b541c030080300694080a8481038500a602c034955045905c0c0054501a001d49038800c43c4c06030081c00400c90740160800760b8070400d0309007070ba24410700701003c01d2503040d01c1080e150180c1079900c041c082112449410000365054241c00801c0f000003100520b002d054410894503000e00e02a20380c41c5c44190b4218082d00c09036a966100800c40e400d0b4052402c10004143c040720300700c0302d60010040e01c05211440004c54a01d13450070301098185600c03070035500250070f007420101f0080c2c000201113540d03034441380500700310040d55034032025170341c1c0d020000d500b2548040b01010034120303214132002c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861186079 1250 861184829 861184859
    0x309031206010c230c09041406072c060408030a02010f0e0d05040e0a090203150106030b1e0d150e100606110d03021e040b090325121b 59
    0x6410340d480c000031400d15841000c014000d5600000318009000d4010700030f038111201c01078100c8861091801300300031625015500c80c031960196660442c08018078507a5414200000c181104202c0d02143c0032400c0052075540002d503004144d05541c50310440b00104501e44600d8014a00798400440d0700e0041d640c2c15084200c4c002c0c4005002c1c005c82400c03d4200d61f84281c03081c0750301e0110301c05200500481c00d146032500d62009900d0000305091101d5004241800b200c1060601c2d014207407001409080e4141c090100120001d4444280124413003420035034180c0110040c522981d01c00900000b403100880b015601d0000032030007080014140c5000907a038203100c1c05845091400c01c4070000300749014500e030401d42c0d1101000b500da0102a140200d0080d44041c4981589440310403503d4601c0708080c019002a00f04814100e5a80c040d410803d403810304460101c4403060090444201d412140200800840700e07031400d452420714907460103003440700084801045849000c2d40006100b12030708004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861187329 1250 861186079 861186097
    0xc0b040f170a17060604170a06020f070501050c071a04020117090d0e12060106050a050408061e1b0a0e0d0614070809010b09060d05100c0801080c03010e0c0d0309030503030903 77
    0x70b5503a00d44000400a110804442080d4410b5060004100052148804c2c1307c1b05040c1d60155a05050150b684500b280c00090003070100c640c0103e1204100b00b024420541c00010300300007641080440d5a500003d259120901ca9411202c000440c0869020303550480f402d00d034448444c43c6519021411382d036030b01c00043c01200050648890b488540c2441c07242d000d40d1003000c5000d010346a080c10003d558581c000901902042000c001c0040d48c0b0350140100760045104010030020200212410608039501900300b04102004a00d116403e002c40c408603400c1141e0350034080554844d550000d05031810228028000c2c0382800004c010301c00c2c0c0721000714411403082d12064a01d84601010a00b05c481c81d400a941011103140850514500840e00c5400503108008641c40030403406840c2c410317500818850320101380d5540050004010602420340032000c02e82c020080c10b48100c1455030394141e0180781300d00441e440301d02c510500d40b082840780b011b1604001105c0d601d080141040f980ca80c04071001d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861188579 1250 861187329 861187337
    0x20d1202010b06031603050402130608010f060503011505210f010c021c02060103030c020d06020c06010f152712140c010e0303190e0406080109020a05040b010c0b040f170a 75
    0x3084580d2501109890040c1d1710000e0980459079100000c0d001410044c0003a0703840f10f52049056003411041c0100c03006800b00500114544d9109840791040d50500c1e04040e21a0341031500809204000c00742600c200c80c030460311100b480032041c000690b0888101e141613240d02629020012000c415001416400501d81c21980c075403512a1502000c07030941001100181c0241e001040400d1040120340013443c002801a003c4c095655104007c990241039011030300d802c200010052002c81c1844500181001e0140c29500d1807403110090405071203e0303030000d518030641da480c0091344507003080d50044d1200180c030341064140c1d0f06100e81800c14040c45210360384070701c0c850114254464041e030088440080c0003035040a01e00c040341d550b01c180c0c020480741000b45090704402e59039503034021140101078802c000268800140140080035110360000e9000b1414410f2616040e41e00142c3ca4036219003100100d0800e8450b442c003054800b0030302501500011207280c02034000d500c0700c802040e8070102501c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861189829 1250 861188579 861188591
    0x60f0c1115131a0f070b07020c0619080106020715110c0a080304030c0801060b0a0c0f24140603060103030c061b12180809040e0708030a02070e0705032809020d120201 73
    0x4900300c41407003981c0059400844c00c1c0042d1000034003e81070150041000d00540310258003801c0400e00710740042c01c19171001c544030001245034075000a5014058129407026007401e60500d020070103144200b60b00750302000041c0141d220006024840e6030118140104a079000503910000c075a520f070840e020030b030348080d4140e4002803202ca051003048116641803e00d01d051180b90310307090b08d140b03c100d0300580344a1207040410001405641c0c4041c4816048003041656001c0e411424045030580d082001603032017036005018103998001022411a90701d4500310160b40711614200c0080c01300349207101d40301d40000c4200c4c0c1446805c21548a0708504e482c0040004904002c610210191104400350403100d007007181001a0510360450516a00c40e035080f60309003582d4400312480c56100007101c0300140c0100074203000d00b6003030310200c035000682450245d0031030902c41142009503015800b0100704404151226403240c81b1030b00010401c5800900300c0b8943c2c01107080410072500c280c0302d5900194a0304c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861191079 1250 861189829 861189869
    0x504060e12040311010c03030b090108030406140403020901120309081207031b0218151804020307060801080c0121020a110f010204030f02090c091207030c060f0c111513 74
    0x103029901143e1304030724001a5283c808006551b10f184036030081e0304154487c075804400341c513000d90541c002c007144001556580e15010b001495028503d5a410074030004100c100050303501e0003e02c0f415141c5001034000c030300003546020b0724400001d500c801410f000c0c078800302481b881c164018284082c0262034003600000740309d11000c251406c1c418001e42c040300407040380b104001d080000030390100043c01d0486221010800165101280515041461508500300411420103210b000018841070800340019410418250b8442145111090410941d0b00704982424603107a18000400882001103550792828180180030a041038801c00082c441c0f0703a02c03900074820500c00c403400c5079003018520300709000c0d50b400c1242044000e0208100808180150002a40c904604c44c441700d51000040012515503e010128000554070070070034480400503003043d96822590401c4103d43c403260305900d038441c000008100031041c14440304124004203480410ac0c100c180e0400c103451083d000a010700381d0781 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861192329 1250 861191079 861191113
    0x1021612110a180902031204030b04140d0f0f0504120308070f080907052710090f02091011011401060f09050a0501140c070905040c060f080402060307140d0504060e 72
    0xd84520725480c03e415001e0404140954000140d05200406a50140e00c128181c2c0005070055002a00c0c0600c001c405c0c00100000d080c80020b201c003011000e4000910300301c3c1c01030107074509821040300340512414080d40071803260080750081c2c0071000d0012140742c5541402821240700300c038014081a2542c0c102e4803a0760088088a100d000900002c040b8142400107006c00b0201801000a4244010601000740a000d400b014850181041807425243c41c101038a401c0e500403005140401c1d10400114a1503212118020315245241c1024042ca00113003508600520010380030f0198648243c0012500c2d9034055200c0322203001c1381d982c8000060b00d070340410a10341042c0c030845001c91202002e08920100c25406400000a4081a00c50300c1d1707501d440c100180c54080790105c96945844405004a40c0c0020108812a400346031400b1a4a0305a021036102c3c4000381051040c1300054074101085041c1ca82150001c0910036001e0129040c14580380703002d815003506260490250550124411070a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861193579 1250 861192329 861192349
    0x14130b12011d240105070c12150203060306010504051338010b04030201210903020a140d091404020903031b010c05120109021b010216031404050d08090102161211 71
    0x3c440c1e8107440808150f0003d140300003102500d41400f00c10320040c804a480c44001e10018024000b119840091034542400721525030604007400c50f01c14014002d1036240014150706468055600080e00d88030000742c0c00b103401c400b44c00180110a080c6080c100c14802c00c8161000c010404200c030240c0d5a4100c403010304002c01d0080000008040c802000550710a0a603204203c0ca4498999103884411408030190344401005501503846080400c040044035101c0070211030010300681203d210303898000303081c03d05c00d100d0350034054102c1c4142403a9176900c0e8100c0300e5491b0020216550b550004800c0740c481126803d240f04654a482c2000713072854058021110fa520743c94050903016820102c03444d0013501f1410b48040403004600d50040c07002c40034402000c1009040c03041c0f03907907403c4a00e00100f0380301082034240c901c0701007808104200d4072050030320020507600c085115224550b00380100c0c039042040c803080d50a0410804d000032040c104002c44104140180c64140840c0084000d0240d8041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861194829 1250 861193579 861193591
    0xc0102060a091e030c200906040b010908010c0810060839030f10210b150d0c0f06021c0305070e030105070908010b0a0614130b12011d 59
    0x1540052101c069990280c0203075032244580344036910f07024080144039521460118007003032601d003000c400c0c0712440100080d07280e2074100620402d460f01021a03552400945854000c9440320313020321140c3e0080c407561028105440003001040109280100b01d1901074030a4000d210682c4400310343c00340b00304901446a440b82e095801540c0782c0d04080c000c040340b81d400710003281440500031003112030020001d50241d1010556602a4100184142c20b04440b5a0000300c0c1000c066030510280d003985954802140d03004440038480c3e6032403070325400c40b42007101405a407110f07221a20404000500310110241c0c0c1010301544907058581406a0740ca4414102d103502c1e0440031410800303032500c2034001a511007564505400031f18800d5012a0039a0410303142c0d10301141e2407040501203808244900c001c1e0a000711a80b00110f8070304040900402140a5005070202000840985014900440d00d0040000300101c941e80d10180d91903004400082c01140e520482040c1c009880354816181580030341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861196079 1250 861194829 861194833
    0x3020a081603080d06080712050d02060405071a1c0c0828020903031b280803070e1f020d1409030c0f0f1e15271201051608090c0102 58
    0x181c216111610349410404c1c03100c00054490401049606040c0200c40c01400c403042c80340c01d5500d840c0380807414a00c900440004540c041c0d020000850b80c001112000c41340f040d000c0d4407148170324100c46802803050b030a00c02d564010000440054031115409211100c0690381d4003640380e240d66400e07460280195140740843c00700304540760014012a40140040710008080742d15040100e03909207003017148000241c415030041d0303040c0700441c00401d410f04500881c280e0020945003103030380c5012003070101402c48000c0228841c40f8130203541b9018411b4450504507800b4654030032008070001e695078500d04091000880e40ca0b2044613060b24481a07402d2140028003800070f07114401d09114200b442402c0459024100c1d503000115901c1e2420110341c050300c1110007400c4548000240404000c00105201c8580d02c100070000c221280b5000344540e0216512168034a01201400100e800d08134990b802129441d140c1071000003400202400244901c039140c00e61141d480c000f000343c0355a11412464056 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861197329 1250 861196079 861196123
    0x90a0b0a082205010f05010306050a0902011407050a0c080607022109240d020d063305280f090b0a08100e10030302060f04230709020a050403020a08 65
    0x24110b60780b0b10018940c112814a5008a503c5003400c2d80c154044004042da5520300500c1030210500600b5400725908100340031426680d40001c1c04001e042c0400900d5507004114a01040414800541d09a802c00445c103401074035000a55210b001c140d034010054810041c841486803149130b0014020254800501c0c1011707900b00600c010848001c4040e13480001003240222007124a50141c449a0400b80300140c40e0501a0302160494066400050740140101d0750b0f65806074511900100305484a01903030050441d036001030b92940150080e014109100a600c44007910520407118842141a0b0300e882598020b800b00b40c46900444c003580b084541700304409c0c11842d0160b044035030010342d07400c0a004041c0e070b40c06548400038410740309403005d050380034070400525030b041001c2c9400c0900e1541185143c04c1540c1d0702e01e01c2c50b20050b200700340803408a442d058001d2080c8052070040041e010295640c2002400c0100345501c5800200e100fa2a134170400f185e140720005070701419080d03000082c001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861198579 1250 861197329 861197341
    0x80f0106031109040f0f05010807170c09130606090c110606090c04140a0f030305040e180c12011506030b120109170f0c0307080a0e060a021e0c040e03090a0b0a08 71
    0xb17040f070245e0101c00d42d0f4549440c10005c10551294a0080c46041c0182c1445802c0210134050214100007002c40c0758401c180342e068550329982d4180d0001461820461815080d02e41000603084903071000c24601c0c90488000c80a030340001c07403500103d202d4810b44540e9078450080104654040d540a400e200f01400140260310803c03d200080040050020346419a40c4907003e540f1314007130304111300042010404101c00404615a16040842e80b12881e00d280c6a036817680356580e90340c0c0503482c410b5464960402008000f035001c0c1c2c0410303c0d118240e44405845d840058003902c2720f44400713030040504010360740d00c4000621641100c5588140280c9441d0309440801d00b10b608141c080303084207032003008202c0c020201003000f44041031083c0c48040e1911100400a01500201902d080c01401c04000da98903495000c079103c0046000d801d224215402090710051800c8c0c4203036103454005141000d415524a000005842ca0f00c808850000c80e140d1101d0300c242e820700074054280e01007404040070a803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861199829 1250 861198579 861198581
    0xb07050c0f2b05010b03030a0e10031d0a050c061305090916030303051f050907031d0109050c12010603390e06180126031207080f010603110904 63
    0x701c9040242807000c02c5146060412000c2100c1c0350386100544540d001c01c003000030a00814141043c02c90245042c03108408009d00119003c8842d24840d40504003e07180b03d0f8001d9000c4c49811002c9800140729400d1416400c0d541c1128000c25200740c4150425000c0a02e4040100d50855048990b0002514601780a103c9101009005400b0364040c5100240c0350580340001540194000e60740442d41d820001d5080c00c03c80040c11030285418040c01c070034021904c9021950b9002160351900160b00e101c500d84c3d1045e000880c01c10151103508241da99014401c0002d01c0030700d40c84003101d0700c410007a2010001400c0ba40b061000a006071001c0b00b484594120096000060020415070241c240c1a00d4159400620168001c5403450b240341c1c083c04040c0c00c00c8842207101030344c00c0c50100d01035410000c80b0400d540e02c1442421101a045010716588002401982c8955041034825032490604000180040304101c0c3c91901070109a400040c40d18030a01a0710422103124844a1030807801c0320500c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861201079 1250 861199829 861199849
    0x30705070b041404050a020f030c030f01081920060c1b0901080706110a06052e08030d181406060108090703020d120e0a06090602010e060910150b070b060a0b07050c 72
    0x10540d81d420b001102384001d2400045105902c5400260741c1e80c41c02094503d9522010307003001c503140d40441c1600ca01e940c00c940314006450307007084036100b10140402882001e0103491704456084100410f4030200c4020020301341c0456000200601c0318418402c0070702601c01024452416a40d0019030200308150040340b14140350f4281d201034884481c01c6443d001e050b2807003a40e410710b80b08044522461a0038030a81d8401091101c24410040280341400f19540c80c09039064054a00d6541c0c0381515400b200010045042c0380d0000308846296031704071009071200030459215001c5005030700007074040c0402241700000d42c0d50003000d031a41403040c0c3e1160206c081c2c008601100b0700241140a082d01c0d40c8480001008082c0b580c0c0d04102181000070003421345000c494100007542c070041c14080700e0040440e07202c0c00d030f80c01c000c800a4203103003450407000c200002e03901482d041d000c0080e940d010310807900e0000d8454501500c005d20304607a103a201610902c00d14402500c15004180d05031001d02e40480c00d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861202329 1250 861201079 861201091
    0x50402030307023c10050711010f0207120809031c09030308060f0402120610030c0c12020703170c1902090f040203010f0f0b12060c0d0519050702030705070b04140405 73
    0x50003081d4042c031084554000c1c0c90400e18242011802c4013501d1a00c080c89240c0d0403802e14120381000303029540c0e51111120400030905102c00703480030704030151080028100414203840e0001411016041c030040d40d80c404007006000c0d00403c0300d01d841740000c260116000c0581959103154052854404441d150400790846038001c040d10301000d4156910b00103060170741c0d581c9080c0a00c07800c2060801c5280740c08134215205141c201540140d082c0e821640d150400c91300f01d0003802c02c807d49a003089061101035003009280f000c0420f00594010107180c00380c05410800c1d02180c08007000a150425039008948009602c0070012000940007900703403040d41e03001440034001048000000700420b044e90480d400e006885a541c002204152902c0b00324020003000307000241c00c442c2001d4190085a22503090016141030700c40d80803c81d0030f0100d810740c0b0f03425488202d0800c414209140029160350001505503494410300700080b500700042003c90f0101c0b80c000d241071031259a0701d824000a00002026 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861203579 1250 861202329 861202369
    0xf030e0316060c0306050f100507020411190f081605090a050306092d0a120c0b04080a121a040c09030c090b0a0b0f090405271e0105040203030702 64
    0x241801a50340007220081c0e4801c00c408566000058001801c950b070386e070300452041c00448001400c0347c99030350201c2c3c0d000701c4030302d801e0395149402e00100d0050f018010f40c110303049030001860206001751940211940d04281c0c0c40344000307803050b0401c95180314180c0b06100c4440b01d206170b00300c00c203000714010010b014020701031110b00c1e17903110300107404e0200845001400da000f0411000e84003415202010040c0750001c14410024a40040a50340b10303810980100740c44c0c143c00784100d4540c0a400c1c0d64110940c80360707071b01d450340c5000d24001a8540100c4140f00c0840c048200343e030110030203402402106070f54800201c0b501c80c4000e00300000381a461040c8424049144004400b080c1c0e0700100c8009000300e480c0100b0303401c28403424020701c0c80d011b0b4000e98400c481440b00350340c006031b92011501081e0089070007082a48500b010001034180d0300c071120304201c01c00028441558000300700814503912102040c020741200b0751409099403001c0710000e502d504108403803001031408005450b014100169 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861204829 1250 861203579 861203587
    0x206060d0312090308011a041d07090308040b0d0e0c010212030c070b0a0c0e1509010302090f04020a110f0c1f0302091203040920070609080903010f0b040e030a0f030e03 74
    0x428a0b080b208060030640005d250382c0c0060100e8094815070003500000304440074505482c00c00e040c551400c404688080c0c0d11490400b01d0007562141c3c400d08007558100404654a558400070044207600c096803142078a0b04004044007683c6010910043e00c04068001e040c440c408507070100515800100b0884010006000c0903012034001c0814038440c0240c0d040001d00900b000d640600100d40341240fa030303c01e04610154200712640401602c109000a080142c0c9400f06400001c01000d840c070f5060750010320200d85100410741c095142400c0310030b0001a9202860014007648c0ca91032540740c655001003140329000d113003021600f22000d20341c10525005061100c1032001524044640318603481d241e1000c00c041c0304028041c41011101d01000c081c00c40c8103401028a0800c50003407100103052143d03506021802e1155410072100c0001d0006c00800c101200781c1001402880030ba07407194000c81c03400c032040c6840100001100c2c03a41400780c5a4a840d100c0500c0c0440c05803000c0c11001500d404284 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861206079 1250 861204829 861204857
    0x30e0303152b11240d180510050c0c0d1202040f030813060e090106030e01060305121309061d04050f030703030e0105070e100f1701031a070206070206060d03 69
    0x141a41c0c0b40e0054201c002080c80c1150800c1810040e6520f031540c0716405074a10764803003040e407101032034002600f900340b1500c1740c0600c28040d0041c008041411400300307a000990b0300b088000318015241c1c8884050402c05034230b4103402400a4041c1c617150050983c840007034520818014802c00240707039582500035141540341e51701d03428000a00d81c41100c0428010034117030081241c0b10700280c0039220503d810b90b412203014000595000c03040c4159414141e860620a1003a0000c0d008800076540002c00c4a48004608010821070362008841d03100d041c19802d40030070320220502800003242e104404480715201da000300d22440c03c402a1040f80e07540f05400301c0c0403110400780080d0a00d00d00a840008400e1551000f807401d54400034210302c10000349171841c1c406035558883c0001180708a00c6c1031091703113040d81415180d10a486405010000400000000b0891038a0004004403460169007101f07407a0110b050769101c405482041c0035801020001d081418001c0301210028007910349914001421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861207329 1250 861206079 861206119
    0x40b040f090503120a2c0114011707080109021e061309090605010e04030f080c1b0703061404170f12090127081b0102040b210106030e030315 62
    0x401c0c0200e070b00b80c001051076101a102115100d0b0321850005040c0042c0880300c14004031085101c0c100c4c00c00000444407000601400d510000c48105181c64081c13043d6142e03950b004400c1038004a00030f1a03c101003002c1220041030040d1081540d01405e03101d40500540e03400b1100300c940b40201c2d5009007050004c4424541c00428031001000003400000f030742801420490282c4034140c02030019042058103200c0000d0344030969031030220403450628456155000702c00407906c41c0d031601104c074804070728403441e01020109040c4100c86c0314000800c0000001aa43c12441900300c5028000701c0c0c034544004c080088280040080a8400402510704100c0310a110300d44c550546696a00c0c0c0e540d0203070f4400080c005403403040308170461300540007061071a9454003860310aa1030410071001980ca0111215503094050b80c016104400c409500e80c404c10040c02136540310504400b07848203074440002032003402849098808203000303000e14034613612800046c46084000e04425007000044658400180c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861208579 1250 861207329 861207341
    0xe03030a0305100b310503070e0603101401120303150308030405070602010209030a030302091206040f0b011a07110a050616111503160c05010504231b040b040f 70
    0x32a100018a03040c142c1e9240100c52864003c2c078030b0118108510708103000055115214000580004003690312480c17042d9114802c2a80050742501c1450000f06045039044c00c40e9208850079801c9980003d0340d03000c0c61061352090b58291b80c000e180c24005000700940d041400c03080b20f0023410081f54140c040c40030242203c80580c401e42d542071000c82031204100c010b1064200070900c600c000d50a00c070143c80000d403591130b544801000d040c0c4c001940720203500ca401548810100341003e840d4140741c00c0c103180c04000e860503000c8039042030400001c110f02440849004212840d000f1b235500b48031061762142003c0c038001404941c02040b0401c001040d941d040014440705228002c0c4120320034251400d8440c4402d20707280e4500c40c608500c2c1e0000d50f0401c0106807540842c4c1403080350700410310840705403000448400041d15070b509020800c4240009641c0c0c985150851003006980788500203c101e8913521080d065044507200f0703402c0c03d02c1510306600102c0d4280002400010381050004c407240407158 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861209829 1250 861208579 861208597
    0x7050f090c070507090c02010c0309082512030207050f0f0d140d05090f10020909040b0601140a0c0c0e06030a12020f070e0405120f041802070602070c0503060a0c17070e0303 76
    0x1b0311090385048850782070084483c458024142882003218582d00c0d404036001d0000221130340841d070104164587c0004031a1080b2a412104034091170f400544000c000c0e60004d0340544d1280304004480d22450340005071030f0000304019020307241e0110843c03800c441152645994860151007805000c07540c0c0394502c0b482e0300070781040c0003c09811014106040c2001c1040d40108940341c414018048103440b100002c3d070303109178400358610460b80e80780011388000c604e98a982442c640c0110f240c21481e40c00c00200808240200300000c0b0841da07a4070b2000c802e0000301d80d00e60f0036070000e403901c400040c00350405047c0f40700c00d8010341f00e048080500340c40c5000f42c10341c4445141c3d20307050144018054140540120807203800c010b2498800e070540c2049443c4501c1c0300d60740c20000c0302c0804110303820742d5906995246500100540d48da032501d00b070803c0038524074000d5500c203011381004100030654621404050200c0d0361a42400c4602100701c0548018008000c04244086001d54400381e680900003840081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861211079 1250 861209829 861209831
    0x8061306051e041103190305090910061e110f01051b090a140d0204051504050a0c021b150c070603391106010902180307050f090c07050709 61
    0x481141001400d840002c0d02d02c502424002c4289410320b600c070208294050740044030000301c84000030200346408003c01541144103500b5120104155101004007403000040340c151940341c4410303900c0710022455114036000308081c2841101621841d9059410300b841c5c41c207007007006100c82c0480e1420f00800b50464000c03030b5540c10070482c0b03059404030700041a08003408018200440348011401d803130018003c80803584030720704100e0016910380790403541e8298060020302690402d00302103840791203401c0026104508000002d02c1c1203840340306208442c66241d0090082c0b80044000d802c40c12070708001141c000d43d052450f04a00305034034001744490740303808008112541c07a00d0b0008048803003d0ba9112800500c0c450016000c0c51690343d10001100640d000340001300381d0742030079901c4044071814000c0c0e07030081400000e0494403503405000344003505224840458801010191500181e028003584140d2124103482d0f03034100940c3c0158003031180c43c45a031919413140ca41c0c034500115a03124200301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861212329 1250 861211079 861211111
    0x170a02040c050903060f130201180b0d020a1b020619030227012706082706010503070909050d0c030507050109050c0f040c0f051305123702010c08040806 67
    0x1404e04002d040d61012040040007414100030f5824601008110006030410154040c03942a0f00349410b0441c008085130440166281a114003c40c00f03904500201d90103e9680703003c80b40c0b101c040d840405011540144602d14004401c1c1d0a110981181885c110416034280605400c4480c03580420310884403a2411080480d24180010003406942000281020340000f0003040010070250384016603943c0e003441781c0c1e02c1d40c0e20201d0300300f15504a181c444207000b4802217040b80c5c03034002c110181a29800c1c0d0070f40c0c06250700e0300e034150159003003080c005080b0341c032011000e03466510448074040194403901d0010300c0c244c5582c40729425038600c407009803416040040c040205180028407104442d906542c18004040a40b0014141d00e9485000000340300d400506032501100c03503002c000c080c2c40014241086e41009480c0503503074240320f0410751301e2071441030305960301c0032001000c556002903800166009168154011a190b68040904861980d8103100114904a0910129101c1c0201003400c40d26 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861213579 1250 861212329 861212347
    0x306020c01110414010c17070b1b04260a15020d1805060a0905030d0905030d0e01020403050303011a07060f0e0d030c0905060304150216060f050709170a02040c05 71
    0x2124042d910980d100c0d40b08020030051000403508071090150242441c0400340a90300f884440e80070b03031036152180301800140c0031041151403601d090007251150349111425010a04401061181d8052211080311103036004001c11448800300c060706929400740d640b800001c3da034442d00030b505009a100310540214082d034082410703204082c00000e91504041c2d8806040d1a86034032040040c024030f0405403918410001d0240c00c004907003914000d03550802c0130540038144151a500031442268942c1d06200641004013014000d907000ea94110015501d103900e80401c007000c040840340380b400000820702c13100d000302d01e8601c10350b590780749041c0c8041900c030040c41410b400d08511030b8400c2c047c98604801040d005600000c91002d441c070545020784c2d2600c442c1000101049041001c80309039000041600303c07807030f000e041c03040381610604080c08641c4d40b080303142080c3c030310482e40702c030006034000390401c00500181a2403044000440550700703c01c416402040a03900c00741e000e00e01140e000589212 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861214829 1250 861213579 861213581
    0x40f1d0d030c05030f0f040c03050f03070302010b0306010509070f1103210f0c030714070f11090c030f070509060c0709021312021003110d0c0915021605120a020402040306020c01 78
    0xc101c031916083e4034520b03003841d00201500014100e182c40350034400008040003c004100b0020355086821900c2030500c10214660b41d50103032000310015402c1400440403400e0008401c4d06890340107007000c500341d9030040c08072032111040e1825803c000d400040c4100f0200140020305100809074030f804c0e401c9000000c000d0a90001800070b810541110040110918003a4196a0050840c2c60042c00300b030709500700c1102500800d030001d40581454124502001401e0320340d5054020103403030540c0c4a40d42c1e11a030364014042240c504081250b20b4000801d000d224000a24484000074056400c241c0403c100500e030040d1341d003000c9400c55000605554501300c030b80c02c44005080f048100980d4645941c08950b55120500c0000c0070705807103c0701c4e0b0104660f80b82c10f640707402001d00e8082104201a507001000724409215100e0b6561203000f4a4194501c0854588800005d41c2c41c14003001c1e1030708041c04454541c1c185001c49900a00f2414001681d5500090001b14010a4096100c00c030110a1034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861216079 1250 861214829 861214841
    0xf100b0121060f23010521010b0912060702250e0a0b0f190909020a170d0e01090e190608030a0810090c080c0c100501030f0308010608010b0405040f1d0d03 68
    0x140d039500780104c001c0c90f118041d5001c039091510a01c0d18940b1000318681c0e9000c00301c82d4805c41e000030f911041c0080381c04588000941084201250780301400514441c0c00b03030f204c580950b034000040e0070100c45441d243c2e980c0004580100b12400050300080d5465001c08614034040d076514042d0703270302d40c100e507401890051900d0450240880c0d42440d18480d81c12a05e501d42c10768420200b049860f20038000c203550f0303449044801818100c084010030f1055940842d100c071020690000442c50b003180b00b0b2201d500c2904040150788540ba100000c0d40c40326400400303a480311608800500b612141c02040040c0c00b8005440143c0d4540c90310300d10343c01d009101c480300c066150003804040d464807498005182e40203503030300e402403142240c25550310a9548000d0406060500810400b8100400042005810320014407002d0080d600d003105641c0b100f1b011039180c0d1082c402c03480c402c1418841804030b840c0ca07a00281141c0070350400015820b58000034030341c900d0b4103404400364a41020030b40041d820b03050b010744 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861217329 1250 861216079 861216089
    0x605090708070609090e01090602220902070b0c0304140313140330040306060b0a1e093b010501020609010b101413030b060307080f100b0121060f 64
    0x1600d8041d00f8518010201d500901c00c8525503a140c500742d9924030408c0d130200031400c2d044542907640b0740d01d52030242c4070301c070216a00851580d12180c0006501da501c1c425610305560001c4145407070b48030f1030801881c0d074001401c2603661544201c02c0d0b4203d02800c10041c02110700e052040310089141c50600000c840c1001d1101c1e019400a06060700c41c000e600c03150341d2400d0000c80c44580076000542c0255058007850700010242d502d000d40220309001038401610030022035503640d120040c0311030321244601c42b81002480105410150521821100115000603041e21286411559074904101e810b002060711706042c03c1e0786c4000c0180032710350303051101c25806007182e4005d028000e070f04004180401524071012041010107440550210031102c202c038905510044010405616030400c07900f07010051700c0790313803213407044040009040034089061816042002c01400c540303101802c02d0005002c07100d03041030421202031010741000402000f800d45521050031300207034a40c1408648882c0794565004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861218579 1250 861217329 861217333
    0x6090307030f1809150909150e120c032802100506010342030b01060804240b0f010306060914030c060a020d030513121d03032701090f03120210090605090708 69
    0x5080302041c82c0d080208e648006101000461000409030030f03080828240c00c10040020004441d1980400003001c0d1041404041c2e0f07184005140c07900d203000350f221096481d030160b00702c0300000307080d0a540c1d48103550019040c107010500501c2400c0c0840b20300d51540d500034419090b8525403e0b403810400e10b01800121407181040d0030707421600c4034030302201c05114207010400220009002c100819420320403400041c02840e00320300500344490003a2031010f803064000c1c80b018504280940c07190107108125155901d42603491070078582540c09001c0045c1000e41c00d0300c21200c2c4044a43c032003000074a0301074895400703001e0751196113400800365039001e0400414080021411000b0640c0f9496501c016041030030400d0004150484480c0309030f14410741140c0c540030109034442140c0701803e5a5081d904840d41c45010b000b00341d001512800c0050282c0e1040303003200c03142800018070700e46118001030164012030b00c81440c10700c091015105201411100c1a8580c42070021405040000300054442140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861219829 1250 861218579 861218591
    0x6120521161a07080c031603090204050a050402190b04051318032003180f030109021c03200a020618030318040c08060609040903110601080607080906090307030f18091509 75
    0x40c0170344140406416002866090510a0502402a40119611a0f0150013800b407407916040102c01824200e80503030107110aa01c01101501c1501c54a0b03064540701403140c1c1c200f9060005015034120b00c06038090945a50301c0c0c1d4080d05003040e5415018281c400e984080004410700b0100459482c010529201c0354018040d180e90702c000c00710501c5500200b9608400030b18102c2000a016184142020f50003200c80c1c004040da4403c003000c4803200a0094440645203945180e5036408500c04a001c000b89030060f0000d080113107822401850014003029041140032050700c0003e08540c07040f00a200e0031600c240050480d82407501a4002403070040c202410a0700d01000450a94828803a031184120360306c0303603542c017014059143d90105034099000c50b081580c5030701002e43d403a48240c80d103102007589540018801800010110711a80ea9a40618180003055500359500d00d400700303503442400700f0781038052401901d403031035800101940007000c100500e8410384050102040d0b0080500182004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861221079 1250 861219829 861219841
    0x906150102071a0c190c050103020d0219020309030d1d0d0f05010c030506042301031103030d02041202030f06160305041a09070603051003110d02041803080601020106120521161a0708 80
    0x4800c004490302820050f80d10049240d0300d8008dc450040321050709403450060300d12031075000014080b0a1002d508440400341c8612054030110007010155902449203200442c840c02c1610100f0340440c410312035091980d00c9996810300351005440c030b020000f555402082054542400b0701200324058a085600b00700441080301101141400050255103184031403039035940b800c0044504061000c241152030701d841d401c01c0301c100d4600074410b82c420320400c400040050340200c0c0b4107000d0050f541d01813800c18010f58080d8050310000b00151003801d4510f44035200c504024800921a085020190a00604011000d0202c510103066a000c8419a0b0340510000d980c80b18107811001c070449004214000610009003d85500e2014403445011509c6c144100f54102c0345003030041009030024003100d41c4a0f1290030880303000344806880c45c0d10945064000301c1c5082d02103ca000c1c40034481a00d041c0c07502500d612075440500081310117014400454040c6811034400942050151601807020b041c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861222329 1250 861221079 861221093
    0xd0810050d0b0f04050304050a080a170f03150a090627020a0207090b03190b01170102091e0f061902160821210a0f050906150102071a0c19 61
    0x141907050010180f400319090000803c152801041c0040804880e203440302080e076150300c0994800c86803110061103034a5028075040c02e40314088000c480c11810b5542d0b0400c14130180341c041e006c107500320407120300211740c5490a0069001614005400d42000c21070402c030886110031048181000781d1050080509166021a0010031107100c43d8010418080480c0060304100000e0fa07030b24145200b400c9294100200e0703440c51812141c0803c1420742c41104e025081c1c3c240d12030310101c03640c003800da4517006060040e041c2003184c2085000d0000f081e5294180b0209501c2c2d070103540d20181e466140c0346542000703981000740c0c6ca003a003925003035031584518142e41541d948076000003541842a03c00c0d106500040030805440c4103011300148604800481c07019a0b40420040c0c444001c502d061007007426280381980a4075001d42c0681c0c0081a40340d4480c04100099407458022a046001d6182e0015140d0083c202207201f460180010a50f50400383ca94240340440c0c802c00b45407001c84120300038001c5510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861223579 1250 861222329 861222331
    0x606090e0c1e0f060c0706030c1209080403030302030a0902040903181e060305090f01020414041b0c0b06040e01050405010f060e0f041716030305091002131203110d0810050d0b 77
    0x1c240c3d200740c80703203010303000080c4980503000007010903104080c0300249581c0d0582040c40c001149440340c0b009400d0450600381521450316014150312001c000c00c200080c402d42c02117a000d4209100000c003468198001020707200149800d07400502400e24a05620030b0101c0d5030b800401c1c0040342c4554203846442c1056070707084c051044000707055071078001522041c010312090000c2e012420085680d540c455251401c4c1c0407140105600607860010f0301e14502c1605031011a1401c0305440c1c800b0b030b49095075501e080401000348415000350301c864060021450074081c06000e18811400490310309040d0625000711559030340311501d020241e0050090212088843c0c9810540015082c14140c0c461060307034110b803003045805441c0c0c0d081c81101005143e41a400709000b001e00300d0a50b0b103103650501000c0300703034001d084070301c086c5080981c810091503021040d012003c3d44682001905c9460200d4400c0c1804403208507540030035171620400200345111010600500760451b00a101401c07151200002100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861224829 1250 861223579 861223639
    0x1120b031c03200408071403190606090c030501090c02070302010f0e010c0212032d09040917040e22031b110a27020f030705070f0606090e0c 62
    0x8003000700d5603040e500c2600304002c1000c91404a02032104416a100604e511521514103540240c140200300c85000003441c13980404001e00600c06600000740d030b2101c03c9074a04085030719a40c6e410000034034200d50b0107001c0403500542c40000c1c0f070b50314020b081d00659001d10320f03403c11500510000d00050783c0000322070746e0302c81c12072800f106a68001401039620161502010b90701c454170112821501c08000000d100f0600c2541e02c4071105410300c04404480e10180201c51440c11090041000d18140340d4400d002c41e40c001d8011250300402030140c82e42da035001d5084100b100307013800104030341491101c1803884d203040b410000842d5405191001800d0509111a01e0380d24181141010103000c0c081c0120301c070b0b0740c03801480062500d50703d03c1c40d03c2c001e0900184050801c4100503d10b400315450340b090310840010071007114030b10b03900d5603400c555130340c85184222000c0d0200045140030071441e2103840d01400f40010009a00c02101100500c1c12541105103072003011701d2044031290f4844d451132000440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861226079 1250 861224829 861224863
    0x301030515090304050a180c0806061918080c010f02060403080414010b040c0207170a08072312030109111306120914010b0108010614041806170c01120b03 68
    0x1d220302000d0b034154440d0703074000c65200c000002e000c5049042c1c01d4562800c0100c4000402114180c500d064030303e55402c44900d130340503200f4440d01c03c866404840d280f010a503d031900503040854421b2419512242d034003d620240d00444440000d940c2002e200b9003003481034001000c0c1803a007650010b101d0f08006000501e07402c00d85140c5000c2000035005464238aa000f030040c441e040b500340c40255100040e105903c0014a040c1c5080c01c400008201c503044c16812441d0031b4600413040d01c6900524040045200c0684402d07508032400304800d00c12448116101c6c10500d6980d45404041c00039110340350211b0341a08810061050360006600f40c52080b1000d07030803e80132424640c20010010016010090030b640751004442a102e001940700d01084402629807880d96602c030f81d01100e02030300c0382c07120207400c0500300001d1264201c0c4581006901402203404075010fa250b00e01c0410120010b004c0c03030900d40c40041000401d60308004203200b10340407004200300111041d0002980e030740400c0f003405154 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861227329 1250 861226079 861226081
    0x304020103111903050f2202060306030f120c10060501050a03051506040f032a06030509030f0c010509060106180b1b2b0e011e0915020c030f030301030515 68
    0x40c2902d100791000e03a5108070100481044950014015003811604000190a00d000044450545001401d60300900310710400b0750010030347c00c0c0b000701e900240c05d59615101e24505148001c804000603c80c92240c1042e00752200e4a2040c4d142c45d2109541e00d12007201d00300081801071340d074010306a901005013440c5c0420075803a995846002512410391842d040000082c002c240c44a1250705281140e00c10018904240411895240744814007805401440c0501d90b040010380e101c2d070081ea82009000061764903104880d40c182d503140d030000706807201a944410800c2480003041c040f0500501a0b4106030440c44d0000185200301c2000b80075443c041440810000c0c804890030401c04680483c3c0d40458420401e80851016914911246180000c4034a98650700e000d1003070195484042c0181c603100d030442d00c0070784544110340102240404004200b040000d0035000c4034542109050540c002c0c04010510009142c103043c0100c0200080c0d0b4410001000028400aa6072180015001c150304c81 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861228579 1250 861227329 861227351
    0x20601051f030b06160b09011427031201050f0906150c01020d060303050426070909140105040c1802030c03151201111213030e10091a070210140304020103 68
    0x500f280078403d03800900101e8042820000700c1034013100f40d4004c6181000756a10301c42d006003660040650801c4500300c400200c0d89009030281d00c5407401c0724044030b0b005109540b0410610316003090744202c0031049030720010800c6d41040c500f036881d0365205076042034980c608100810076010721549d4140302d45c00005940c540c6203800b94191080c00d80b1004040c403a2655074200145160400d00544084034030620199040050000341050b1072819000580056450920400c0091200b140f041d588030060007401c0a50000c207110b020320071881220a0b00c005420240d0a201c1d84021194608082c0d10410500c42c3c0b510300f1000707495028003001c13092000c1c507410b540810b00392000d030f501c5c03a050b9609210315031440810510103000f101c060034030b800e001c43d51103d8550074072070340701440a07005c00e00201c98082c007030810035411090320400d4140484402c0d81d51101001910041043c0e042315400401e40008510700b441c40c00b41c17014003601d44150000c0c4858a2043c4910020b0802814181d41d400900c4c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861229829 1250 861228579 861228581
    0x1706030c150a270911040303090b03220f03020705010c030c0b060a030506010308040515042409080d080411010908060f0901060b0c060702010b06030c160c0b0424020601051f03 77
    0x80036400340440e10980411112a441d250209000d40136640741820100c1d81803030741c0f10050b2800c613501561b50040240c9849401b0050354000f41401044144000d01034001d84403280b00d03030742c000d80300380d40d0380c00b00c0f1500e030500a080c4542a0006810401c1a41c400c00102c0e034001c4110034005e400080201c810340300c41001414280540d400248603020394400041844040c401400031a01d041c0c900000c041c1c000900b558641c0b0450041c0c90480d4820794407a4031040c01d000712903841002604040e00c40948400b441480c01c0d058078185c50029a1050402c010000d4144642240c03080a003000c03034030142030001d20707519510020301c41a22080e880c0c1c000b41034201c0942200006110350412140d8034844545e401d512140304a40a0b805503080c024168049c0c100b0a041f42d2045440b1304900c0c0c18000110340014904407005c3c4e00b0344115240078030201e1107400d18001040101041e55250441c0100c9802d032040c648180f04e410015504000300401c001d44408052a840ea45c0040500307100d4900c0310300580c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861231079 1250 861229829 861229847
    0x12050907090905030705010c080601050d051302040f020d1a0919110304060e0c03150a0b0d020909160905060303250b0f06011103180616121706030c150a 67
    0x9042642054202c1e81400307070202c02400c0325030181c0000d00031808010025104c11006407a03942c005070f020010350349045e16551006400070001400d100c40d0034401d400081c241ca616407440e61503d540010041100c1e02a88039104403540c0e420100880105c0c80f6001500c4001d0003406214651807100c44146181e0a5600041a0038544c00000d51a41080d007041c00003003040412581c041d08c907424030a1f2079481c0003e001c9040740c02c1700410f100280d87d010314034009801d0b4800b070b83c2e4000410f05050384c016075406134040e02c198609070092a10000d00c141e4007248401c1c1d070b800340304024a49818480c8589000c003c481d001c45401c0341c07000148030000e4000c130941003140c4001e081d00e0070103428071048445503a0240e001c1c80090303031190648803404d9101502c9100b0390500c001815085d0310005e0039420054046c000c0502c00644007248100c561b2614171000303051204c4000010002442480c4416281050130f81108040d801400f04482580101341175110403e41c260070729001198a1201501c150010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861232329 1250 861231079 861231089
    0x19030e06121e010801050603100c0e060c06090105070c080403060c0c020d23070530070b07050d0f0e010c02040e07140f0d020a03060c020115060507020102061612050907 74
    0x94055490007000c0c40d400c0408408038100396540c90302c000902d8000500aa50040000601910381100795040c44001440008404002e015480c00c20911036902c0384085c0040c00d14002c041c00c10b520b0900400c0e403c41d04020301d1841440440308450000c80c40250070395040d607911035000500621510019140065900b80082d030108800c4081402c001c00c2403001c00300240800c0380e000300c00341400d1109031600618000d481d04a148858402002d071080f64440004a5160b02d0100350103001e0790841d401e2060b2a080207012920015071501084401c200985800e80c203860b001841c00400342000b00710400e080019030400420f6024071043d562641d1080f111031300680c0c01c84582613995030750403c4200700c3e020800c3c8682c401120350104d038200183e1014070b00f0350041c110040c0c10b01310740d100c0008003401d4942004566880021005030783c0300c01c4c10000030705142d4541503194805c610009107031400090410130000c0003400a942c410350818664548802c1e4840041481d075280241a49008100d40c80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861233579 1250 861232329 861232357
    0x807031e0c06120606080c0711120319020708030307050d15090c02071d010501140307020a0605010b0405120705060414010e03010606050c07060f0c140c0d0b0a060819030e06 76
    0x2103050700288200c3c04000552001d0000b81d42d40d40e0150760388032044865074102d0301c0030071900001403904840400b09203801040200141c068042a5240d03400941d8511080079034549004134190701040504002d01c0040010752442c600b91710000c100f409407120b643c031802d0f00c841044140005880d26000507204086c0102b10728030b1080b00081d234616441c491403604424089038450b11201c1030250701d0580d003040c1c60740c0b10407148800c50003103194002450305c01180204100240081ea25005060080540500080e00c41e8206001c014248016420307510050380846400c0140c0c0d01c450080c0c804030f0b4038030040103000580c0c07140181c44040c0f40700780d80c0303030f140d40703403000c08076116070894007418072540b07407404407050300e91603550990b52041c2c140801d601113004800d0840018050302c030380304011034170702050794080c4860001088121030100b508a8142c0c03010010422146c07801d01ca103000400400c2d00030891000e404000c00d61324070105002400f00b001900c6001f115445007001c031a52001c800f00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861234829 1250 861233579 861233603
    0x240403020409240b10110c3006070e010809150c040b04080604030f090608060603220b250512040c0e0108010b100302030c0910021009050105010e0f010807031e 70
    0x10000080c130b0310342d400c11710075411030b42041c0b0744c54882e81e1040d52086a860060480c1080f52040012282d002c07030044051054040803503098400c0c92240141404c48180180501d040c07048020300400140901c0718108104c1504020600800080180901c4815903144110b42c803008001440d5110b2078029650200c00003c00040b046c1c0002280b0b4400c80c0260341e2010803580002080710202000e00c0f035000050384010200e200c070314082c1d00031078000c000340010035480d06240e45010b00a03040d60105030b0b080303500720082104c421104114035140d13050443c0342c0ca2000b6044100174005002e005080d54030b1034141c10008040000c0c0e00b1191028010b0b0710f01c106625070392900c0c258060205007508034013034801d20036503060060081c02524040c42c907984880781808248401d000300c1444029407001180300c0c00b03c11403032844052081c80d05050141c03002051940c14034035410050000a059414181310110040118410114820b02a40d5214600b034007081206664440048030f044009040f01d032042c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861236079 1250 861234829 861234893
    0xf051207051c03050c0406080a020d050a090311010216080306030c090916090b150a020a0b010b0909060f01050909150a0905040b0708090727020705010b240403020409 73
    0x5440042c200300c0c44051448040328400807002d0341c20548206514030401d11003440b11f103006400d125403001c2c0c1c0002c01810030b45031101c10800e0702c109480344945248e48454a00070305900c40207001c001084c441c001e40c0740c4018845620440217104101400c082004004100960350a0000d502d030444010086412070038211a199104e00864118108848000f4030005a000312405441c2c038000d402807a03d914060401070b0b186160340107445420450240c1c1c052040002d18000101c1d01a0100700176003621107261106004a6220260201d03100344820980e2008030703a40304040b00c07006501503410003603e403102c2c49081c0441e2844820310b82d00c86a0f020020408035410391002c0d21a07406940c0c00c07465a1966030b800c0d07072090341c2503c01a42c960040282446400c1101109150500b01c1007550f03030511000140704012038001180403142c40e51200d00180a5103040e81104d410400c407070a00001c0c04c0310181c002034051069101c003e00454448038240b050210741c0b07821849000c01410300c604003a65107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861237329 1250 861236079 861236083
    0x204020a0f0f1b15140a15050a12020607020a03050105130218040b1f0902180a0b0a1b02060705060a0b010908030702090c0c030c0d0801060905040203040206070f05120705 75
    0x14100e80000a219000362102ea81c1c4200032152002450401d1042404034684403e1041c00308070340184051070715900c100c1100c101d00155a48100f144000c006a106d60650f03540d0584c89499105c24820888890184219015030341440a09641100d80c0b030760b64a41c2e840030841884807580301420551900341000407010203083c2080c6c0700c0d4401c0310503043c14112115607560014040e1409420049090005020b0355080524041d1422509050f1031005655096001c140e07801072130203018904d040c1114104030b05010702d000c0b014000e200022800c0c00050741c401840d1114502d624030905071640150015900c51104840405400109652a070314080d0703840030191001c0396201c0d0000b80601000981c440c000f0003980d01c00c2d0750040041c14207498105c00c981c2c1c19081840700c40d910740810000008488001c2006103291780c0c0079200e100c00c43d0314101c07010300b40c1e15041d8401030003030f80108100401030340c6840850300040d902c85030025001f1803904205d40b82921091703c0b40a4200005a00000d0000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861238579 1250 861237329 861237347
    0x61315020a020a0f0317071a09070510090f090e122508120c03150d020a0b03090609010b030a02010e01050d15091d1501051512010b12060a0806130305070204020a 71
    0x71b900383e101000461915040324840d0100c09410708a01003020803000c405105681e411849102c2110a2243c4171400110144043c00e00107020581000e8100325070342543c00c0d2040202030309881081704c4010b00c0135040d00c400707882455a0400d6030000b54180e0001d5034106070364449611030034880e4071400d07030300e003c40d030035031180c2c032400c0300071076142d00040c0700c540d82c0d00480b8814968079000c1ca800310084814080a00303047d05089070300c1202000c0c041131031003140028510030fa1444004003c10300307010030a9800c454200001e14042e4016a0b04c100c0945d81000c0c159444110070300e000766559418907041d50003800c111800742580c02c00b0200005240034540c2101da0741410700b2110210858004200c642c0d904030310740a102e07502c61180300400c003502c2d140704105042c6000c1e000f001d140900856480c48111401d0f04881d08454000c5111004100c0708400c0c581c1c0039809840c07001a107400c01d0702d100d6840c0c00007400348800030f5403c262207042510820965000310760290003503443e490800000350440071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861239829 1250 861238579 861238583
    0x209220503030c07060e010b010918060302120a0312091101080405010f0f1e060f0e090a0803070c0c060e131104030c030606150504120b07110a061a061315020a020a0f03 74
    0xc204454006c0064061168054800e8140c4a0709003140c900030454030244a40301c800011a0b903540c0000002d41c071500441c11000c5003007000341c4041c2003103150191980c44814800500c86240506440c00101054441030000030b0034200070105684515065025100d040e40c10544141044030400265020750807012071000304182e24061075629403e900d00f221a40e03c140440a55094410090b40e002c1203080b58000384103030300b5201c50001684500c2040d500030307195200001c221045050901042c041d194014000904e000c0d91403103003210003c0c148044130044e01510541d107104c0d4880a130f1518003200c0040d9032100128040742d50380c3c142540100605d108007003c40c2e0b09107030781d403418074410f4088505030351019002c1302d40c50425444110055200500c00000d04c05007080342504024200004a0020f21920021801d0103d801180c0090301c64a010140119001d01c056502450207961980c10b94000c0c44400040e1072102c48202d281c0011550060342044000f100440c41224141c0e810040d40c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861241079 1250 861239829 861239831
    0x621060604110f0f070515041505100605090f2413120312050703090b01030609170f0421020619080603030f0a030b1203030907031106070209220503030c0706 69
    0x212a0b021906118071940c0c400c0342004500b00034001d9103005030409800600d00400c00c4500500d20200c014484520554056400400ba007825001c001a14040d850740015040700d50201140f030204041d00a01a00601c54400c884481c4102603a0300d0303c0030442180f40001c4401000002003c0c001e050540c007174103842d0301091483d04007180340e240d46103c400840b9816030328200515503440b00340740108006843c10b420035071207005180100d10403c2146000e0b40c080e80b030006041445182c60140c41e4144d009400450006000c0316481c20220020748044800c4003460205c81d00d124500d00b04904642c0e4002580000003054944180c8404000f0350001041e91b19030201d55103c1500301a40d0740103c108400114604000c540529840781c0c00c441c1d02c540d006440c12085905038580d007800c0d508221038000701580314041c10010702929405400c0d00e20340c1901c20b1751403d0201d4020a80c0d00c1001400b0040361810103100c03200201100c000c88008035009029a078503428182242c0180b0742c0030304400c0e10b02d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861242329 1250 861241079 861241091
    0xe03010b1f0e090f04080703021501060314060a0e0c07060915021e0c120f071a070e040207020609040e120406033306110708160302180c0702090621060604 68
    0xf0304100907010300500d11903104840c10b076901d030f90300c015562010008400714052881d8610036840700324001800382078541c801040a040e200d44040d06441c0090083d4429440000108500091411503540040041141640c0d13040c035030514030060109620000c00d0085c0c052640c4102440640c00f8100e00490045c580d106101c03003100345078903805243c0d0390302c078507410025a542e810003100005100340c08513544070030700701002c0f911041c0410302d901c000c680e00c2c0d0984408018071654000000007000703404480442c2003001c2a00032070b80178060f241c000341c0540d83e41c1d4031100c01c555040203100c64010070300180658498445d00024040c2c0183c030860b200f69406001304c40d500e0045060105a008407014002a08078a07200e411101c2c822400030021650003400d4000c6006142807000b400c0312400c039810140f080e031031841400041011010b14206441d0302506000315454a417084410080d011a1200303059101c0c0d40029900b440410803c810035408074402d900d0424000c81d01e14812a4211020449 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861243579 1250 861242329 861242357
    0x403020415030819031d0f070b0a09050906010219050a03090506030c0d1e06060207081e0307060903180303080a0f02090f0d0c21060f0603020d030e03010b1f 69
    0x1c05485800002c000f00018440300207680740c4c0000c044512115481e02080c004030101c40d07410100d0202034100100d400c0080001400300b41004524000c1c825503010500c0c0c8001d51100401d41c080500441d0700c1002c03c04042103c80e07208102201a40c1e800d03448a601e4002c151400ca40c2e07407030b000d40048022a40460307001507146091020b583c858013030428043d151000d4010458000e254002545c9011000c003e2310362030840d00c6204030300c082c252070f4004000090a1042441c500100f00c0042c00b6420907080190300781c4c0720044155188142e10150104100c031039841c094859491070200100804c6483c03400105055003c951103009000c0d01104004483c0e805410000303034403c8450320350304103041043c0f410300c60030008250003074035005003110b074412615900e000008000300c07000340e225643d800d202103044c0009031113800300c071140508080181600d1540400c18044541d44081c00303100031003014914a03182908203d080040042c68041c14504510442080b4000c1d1510a1b00168050700c8600c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861244829 1250 861243579 861243611
    0x3010b1801020706080c0a030617070812030103032f1002090405070e03072d030f020a091406040c0e03010510060306080f0304050d03090e0103081c1b0318021504030204 74
    0x1040d034404d95205001540c85035080f044c1940701000710010103540d602c0014001c814014035181c2017645101400c04d02c0c2c50f003c1003c2c5008904c9607000d1001404100400000b900614000e0f02c1410010b041c1140e1103100e80f001d80f88101031501e10540740074441c2c409500000c0c1c0c2d4024421050111000c0009407121303c8100d9001c10504203464041d40100380070300007503900801501240d09081c0f000000401c03401c0440755065800d60084400210720420745045180150440002d171a401c01d0400c00c2901e1181c4a910307184001c3c0080f80241e03507814200607014170942d5401c691050180090040e07040805007001100d03e00e10460307000038900400450002e40c041440e40141c0d040341c000350704190610040004400560a045042c41000d1400150800584200381d009502030303240ca540380e030f028012418030032124143d0001d160740750080c00b12285040040f540c504898924000502e440c100b0032500e88000711940c00b940c860300c81a500020340130341000a2050300d00c2990184070542d5103980c0c8030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861246079 1250 861244829 861244843
    0x305040c0303050c10020708030906060319240e0607030f060b0915091507060c1e0f021006321302090a0504020a030902041b0f11010f0203010b180102 66
    0x90a1220000d010404203200d90050000d4283c950141c0303d0760925001034a080741e005480441c0e080c80d0200400099140901c0b081c1e40c05002500580034650544600c11502481100f000303000513000c465482e24000d1110500034081c2e000300701000031201c00410150389500c01c44000000a041004881004803580200000c56601e40300c4030f0700789488203007003010408580701018281e5400f0322921405a4030400d87c011480c2e44560b8260b680c0e0341e1820f140054841400c903003824813007002c01045200b54038400041c06400e862a080010011807101241030440780d0000d58001801c01201181010b00e008028800c4620910112106070410403a4442601500a8a6031240340c48000c0300c1d0320b501c150014001140001e00b5030100f1515900000e0407078002c41ca0110001ea42d4000600c2141028400e1400302c2103003811140c1c0c0c410340b040780103003c140241c00400c10480204880b03058180d094018070f203151000d00d030075516983c48980e500d410350030140304081c5002540d01400303d07550000c0380034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861247329 1250 861246079 861246083
    0x15030611180f0607140f070e010e0601080115030b030f010c0201060e130302030a0c06140406050f091506060c070e040302250b04032316140906101b0c09090b07030504 73
    0x141071138413545600c0340207155810100c819001c2c0c8070007103a02050a1203640003824410425485039418040388501518001b000e50303040c030172100018401d48075210a03155100c8020718000c500c4a21940c0424186204491040441d42c20322034848102c035011b4000500386da050454483d0140da80f00c02400c0c01e010f8054001e000350b002080329048036445852480c400d10302442000c201220780d14402907108404039001e42c1c003141d0361418030400b01180c1541c143c104540c0001428120010f021100710840f0107080c03603200d680002012403440d030003400608001c0062107441000e41c035050038081d485089881c1a00ca40d11542e0700d46c25a0220760020020648001070445030415065135113103c80003040a40c401040114074501e08801203042101c41d8003034610b0b46284520b10706d040300d036000d481c540d80c100030f01c2551a00b003040340d15242d1210303646d1280d141d0720309282e10780381910300d0300caa01c0c2c200c180103881c40d12090401702d40d12102d40c00001529108528043c41c0b0ba840d00d070200c0c201c0300f040d600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861248579 1250 861247329 861247339
    0x91009050c0f03151b0c030301030317090a0c0b0a0c08070c050f370e0a1b0c0f150e0303070804050709140f0a020c010e0703020a0803120a15030611180f 67
    0x2c54500b80d04c1010010301945c14610151410110410107403554100b644110006500d0326240d26042441c10300a070b42040d0090000c11209095a41c2c24895a0782c6000320311048401144103805140315410079050b070340d00f180403e43d0315240b50a00b8030310b8071000e00034217005020707020b01c200c55401c01182802c0a90f443e840390117a01840590071902d006a11031040100c00c807810001300b21040b00d1001c02e401007005000c0001d1551500c07003201a442018206001488521244040401c00e10000207031000c0d800140c60b04401c0c08881c2d0080189485071380d10303200e88408020404000d401c101001d0150b80600226481c0a60702c98030b200640301100320180d070302c983c1803001c0b682c941c04650383d207900100104005401c0c0f180340e90b40303a421207821520341074560340040350420039401c006410a000c0c007040d0024524114002044105130707207010380b001450581e50707600c00e4007248100320620040c6034003007014000c42c80202c2c0703c03540039000070714080b42284018412107154600b440c0c4140c811000a04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861249829 1250 861248579 861248581
    0xe010b190f02030702060a1d030105011401050306040f1b0e0307061403150405190608161e05030a08090414010e1f0305070e070f0201020a020c0405091009050c0f0315 73
    0x400c0300c8003010040070600707620041c010400107950700700142032030002c155140345814800c0c5148410032901c0e07480300f0340280d01d0040140f00c00480c0c0403004c44442000c0c20290350343c0d15401d0100e0003c0c50034a0242c9042ca24000030848290581d0002180c20b4245075a008071420040d000c0540300d1506224640c0400c1f4000c00f441031004504020b10743c007909840220320004601c50210b020303070f04212401c0f580c1403e222a04100c40c04075100740070181408c18010708188010050010b05003070303a402601941c81e000301e4280d075081e0054880c00054075025042e01c001d034002d803501c2241500300300e480394800c50810f2a00510380c01521070850480c1c0380c5280d05c10326034440a802401c41c15900285030030500040c8404000b0410802c4144002c0540d0021079a42d41307000c0740b00811404100b824142113900400680b0116540080c10720030f2920101e41c0029107032a4240300c2031400b400c01d1400d542c02414000d08c3e10a008000c10000c070b25203803c0e2070403030302c50200c94101520790306031111040650079060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861251079 1250 861249829 861249877
    0xc07060f21050406021b0304061101270206130902040927082a030c01050f011514041511071d04080901021207060c0320031b09120105010e010b 63
    0x2420040d0804c3c02036034014502903c18a00c3c100c00e1007aa80321100d00c0c0e02c00901042102d503c8140e0200510f90782008105640e25441a10380c0c18a49141d9103900309400c0107035506540c1e51030100c1d80c40c00c00c0d00b101400c0380c1d82c3d1500480061340051141159880c600010f48240244094640c44180c03688001004589026a1640c4064100e03c0364144069400b1200c00c0410320715582180c04428010003c5898000d030003400c0e8251a8000d0949203140d4800d001040082840d0001c002d070341c14141825145040c2c6800d10119600565200c111121b05140c041542c481d040194018211003100c02c0c0d40300942c075a100d0364114040c0103e4002c0b0350345000c000401207120301c409040000c1e0148192010071440700540c401982042c13100b0380f080b5a031000380d5031040c0d40520079180a2078558203c0d403503204029410340001c2c04018219400750226080d0300c03120310168021500260001171140032604201d48a0600a00c800d020320454540e9800001c10494100300c144d42103080d400158201e856002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861252329 1250 861251079 861251081
    0x227040b0606040e070305091905060a05010b09061c021204110a091b030f022b06150804021c0507090c02061503030a0f020c1f02100b01050327030c07060f21 69
    0x701081781c180103270201d08032000c3d071211084201c40e020b40002c12440c20b0060088040b18130607032045003140c2040041c1c12181d01c9a00030707a5205200b04114032020300310a14004040c2c41481140b603994030300201004100030002c0c60b0300801507000d4a500442c0741d200d45070001110301e40c10022043d02100030740b00140521035001145800031500c1c01505000a405038000011032049a208608000c0d018001e4100d102c0d20610340113044080c1c880c04041003a40029115420141020b400340070300d94102149282c01d4801c003c01c11343d00c80c00321030500b40d96068840007004071210b90801409501d02040c0c11300c564a400596840b0700502862504009407010f0300c000b004501b0b5001075001d40c00054510f542e6074404012042c110100500000ac80c40a0081c20600e9004021100c3d51074410b00c4001c0c2e990100590f0f60014402c0903481c807820341c06840325480f40c030f03907084000307148000a14043c10420100d000021a01c1d01c1c0c840b40f0b1440c00c006019030700d101ca808808001c01c0c9450f8401c3d0385803501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861253579 1250 861252329 861252331
    0xa060f0905090a1e060614070f0503131508040c0509042f01021005010b0f0318060a0632040c0c14030d05280b37050604120f0227040b0606040e070305 66
    0x4207031034001041041e82cad2200d0940c1c00c040c0fa440721109800c4030801c052a8943c11700c080101603890103001c40e2500303a0f10000c9060740c501815024080f0200000d082140c4000ca02d800329074903252162203903d103841452083c9030103a0b207150050040040008000743e140c0a4070b810fa030400c040d402d0400c034044003440403c1d00018031400f0101c0281c0194541c1200c18403099000d01394030b02020407031501f00002d40d2440d9501484401d40d4202416018050703482c0c5042d00c5541180469001c00d800764205012104c0e4140b138000903000070000016008110b0000009015103a03410b0014070541c0d40305604105e142c944401003c510a441c0b2170745d98440c051075480814058001041e40142004074450703003c1514076200345d4540c072420480014085c910001c00b41c4c000708030460381185010300f8134070304000e02004154020001452401180115910350041481000c50341395099220f07c0c003991940000d20060364141d85402e20840840c002e814840300715016200710106010f4203407240c40f811130080c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861254829 1250 861253579 861253583
    0xc06070605061f23180d030908160f0501032a03091e0b01140f060705030409180c050102060c04030b0613020309010b0a090b0a060f0905090a1e06061407 67
    0x3503d080300c0d807040070108400000380000c2c1e84041d140d20398004d013140c0034925141308001e210014040c00d14200c0031241007001c1c0440559a003503810f503e61070300b0b0f10500c000750019803690040301e246d4441c504044d401c140480344e100301c199040310b076600015012544c05440d203140c0506440480c003007110301800801c846903800e02d800103550103513444070030035404a00116584004040074a506011408018502418440d0103001444842200055601000a84050103140041243d83c10301405005550040c46c4c21305050025540d0140030000300103d111b003c1300c1901961034042095440050742a10410009c400e9a28060950300e800440f0038000b04526807000054103402c0201c103181c0003071402280c5a5002041e40e030000702c00c0000000e800c0e0040400145400340c10b07805035603030f60b4a00e400c807010f60a0240400321241001c4907400041c0e04029080508074003481240c4504c0d40c1310002d8800f00b0311140e0014090720b450386003604c0442c401d090000386104800300ca4141d5034001011024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861256079 1250 861254829 861254839
    0x4030c120c08010507030504140f0601060c1506080a0b220b090a06110429030a0e0708120913050f06090a091a06030f0f070b1305060c0c0406080c0607060506 69
    0x1641c0c0b00c0c50a030035614101d0301d000c0040d885134244020800d040480790b0050a494000d802c040b9483c82c80b09986000c1441040c0411250ba0291028080078910900c02242030303d07414000c80703854103905540c034100300100300c8a080028000605002316a18005414101007105101402c46a202c1e142050005001d0301a140030711100400014082c1c400c2d600c801e100d07802c00c240c4031481c0ca901c0444800ca1503070107800180306491200d10f00b51080301105d50248030000300054032a9480e962a2404a2a42051045100d20741100126817681d001a1240320800c6801c00c0c5490a06426101598400e5645511521000300442c130380e86824240e05900c10149000000c02c0c05054442c815040c0101c07004030410340104062113a42c0c2818800c10255000078401413204401038482c407a036611062003164681000400d245003004607642c0004000c0c5002005c0035110b0513054820380e01c5020310803000c0c0c400c910340900000c03417010101d0500d0003058010111811f0403650b84414018090050940303a02c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861257329 1250 861256079 861256103
    0x101404020f040e04030315151e0306050303120412031a010f12020f0c071a040312090f090c030e0f07030204091110081509061516241104030c12 63
    0x2504800c0001c44c80350340a9580495003081e070503200c0c0380d0b172540c54000c0d07002440c081001540ca075410101c407159a0001c40c1c01500401c0c20b040c002c600410458201c56410300002489107001c071110701580b40182d0103180400f4a10380c022038141d0803140701280400c240d000c100e07000d01c4950b000f40c016101a840074100482c43c540c000201800702d80c00078002410f00c40d001b19400030305030170400241c0007510300c845d008580462111803090440c09907100082100340d81c207400c0d0995600c030b0701d840b0004020601c061803034252108584805400c0d0031100c1130000e850003443e4101d42e500052160100f0103414054100c41d41190248400b9055040c0142d0b2003a0500958000d40e8603281c40100c46001107175158101400c02c1004030448200101c54644134401000c10700c04560b9031b91400415070794810780140e65541d030a4001c0b072003c13600b442004d003540480a6102c2038140940030f40360441240072008100d0b4040c20445c101c001d003d64003004c0c180401740300040c0b01c0c48544500d15100b01d40a0101d401139 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861258579 1250 861257329 861257339
    0xb010e0411090115030f06140907050403020414090f0a0b240604120506181b03010f2a081005041805030418110a021005070302071b0e101404020f04 65
    0x220982c203074811350030441c4244115440651510800e0550301c030740c031018020689055006c640070700c46460503070322070300c020004030f20b006002d642120021a4060001d03ca0b01e1481408154250720844001c110b6000d00d5a041c1c59030000810101e6a0642c030940200d2642c0761440001800d40e01303001e1115440503407000c5103846944000180004051401c10941d0020342468200e007001005845040019802060614014004986518500341020303005503800411000a405030884002a0b04400e18290703910324110241544083c0080c13070ba8800f200d1a1448090443d24180700700c1e0001c52614001b481808145802c2e0810003100c1da00b08415a095880340d00c03442d0840d8410303409451251a07894031a104e0800034014543c1c47c01c0301d000c005040910803000a512205660100c290080c1c2c4c0700000391000c2d01990545000036007204164202c0c40900c006840709020900521110180c404005088000f002096200743c0c1d240c000c0440c3c0c0c0204110a11000e500541c0108410141c244804a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861259829 1250 861258579 861258589
    0xf120612050d14070f0308060a18050412140d0b0a170d020105160c02190b16020f03010e0a0803091c030b040c0801060c230f03190306030b010e0411 65
    0x146602074006024840d02461000c1d05246050080ca5804401801200003280b01840c2c410a169054105200306654000015550b040507030040401d06418500c4130303030310b8106544410f00c9140302d2107840d0006010f4010a540443e81d14010000c0e0300c0f0101b14501e458041604580500140507281040541e103d0058000b015010180c440c03540d0700030400600e40c2a424010b00d0340103172640407403014000c103d610003818802c40d200040e0007048005480780361116100042001040e4100e981340d140c0c1c164151076080c160b03071000103911414408407050001e180610841e041d40c4041030060a0305d00f41d43d5101c0305e864200401e120503501480c000d01c0072158040c00340894800e060307070340000c440d0907031420082119803003070f034800c20054110018000c65400175514484a82c010800410303619008011100e000c0c400c5d1b00a030603034040c011a0840100b800000303000091446154a942d00080c100e00b00d0445800e40f1020304021108001002515040e18a40e5002030091916040c051a2107002c50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861261079 1250 861259829 861259859
    0x902040b04110c06013f170702010e121906020903070e07081f060e0d021507020a121e050c0405040b1b12150111100b1509010f1206 58
    0x30030400c4000400d03d4548a042c40fa1602400e0b80c411001d42905650306443e031220001c01c80705440d0004054010414550f1184070318070b00d03078082d50035aa944107550032615150000a4228003064540c61220400d241003081c0658088200000746886ca9182646d9112300e0003000701034480660030021041c403910188404400340c03c120078403010300d05009400514440e0001e004100c0321859088065544000362a035100700c401a161180300184039500040d10400c41000c020350105c406001c00b002011903038090600f40c2c0c022242c0300f95140e1795041800a0074011341000313210300c4100b0502084800f040514030300b01070103001101c000740c803c0c0b0040b90840b08241e03001e46074200d5200401120300c0d600840c0840301081c0c0031080c0e0802d02d1101c0100c0241d00044e00ca4140b01141c0888109540d214414010040d110b180440312640c00841000c0010070216448901401203407500011003010442261013038901a502c00400c40c403242400c540c6850003000c80c204980d00c0d13103400201d5040340c1c01d0413 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861262329 1250 861261079 861261101
    0x180e0a12120e07052707080603100203090c0a060207060e0607030903080d0b030c030307050c060d022502010212041809020303090307030516150210020d060e01080120040f090902040b04 81
    0xf00290b6003000204080100e40b031625000982d04000303540c149a61010810390440b00d40d082c903040588070b40c0c2c000380c103108102e84408101440801005507482d0009140e607d010000c0e100006855102e5004a071030700b44500a400c041803107040d00541500300440140b250a01072b1070030010352620703030f9250486540715a03442880345840d10341c14000f1346424400c1d540e01402c224015454400c65542d6281c0711037102010718441c1d07c01180c030017902c02e0150101c1d40075403200c0c040c2d04690f059440c24118000c4806209030b00610400600c0c400303200e24a821941594902c0445480691034040d1602c00750615510898240c00b0501442449450030070000003d984541c0241c086a030848405005c0c10106900982012140c1e210b941c40003a00491900601405040c1c056950003041600d10003a00b26071388104d100380e41940000852000645c004442c1d0741c115031503440345d040c00c40c0c0144801e0080d4041c0d0301c00c4600440040140c030354280d20461446101402c00724646030402c0003d4203c4d03082e4100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861263579 1250 861262329 861262333
    0x90f120a0b01231e1804030e0a0f0e040c0905070917031201030206030c07020904110103150e0a0e010e15190e06040b04050a051204180e0a12120e 64
    0x4480d08100ca0401e1281c050300d81000c001c540c461014449110681003104443d0103a5901e110469020400d080d0303030a5481805428030440c413040d0444494044c80c2103a0640c000744405680c0d1150740703050f00c1050110b90305008041c0c00d441c2010312442005101400c125050144010700040410403070050510505542e181c40c00c0b954070740f11280095203105c070f0354841c20350802c0080c20307074441000407400d054a405895a6032203654410480c0c955128004d0060740c80381c20401080b040008802100c0b20985080e1ba0500c0340360a00c03205080039000c0341c0940c480c0040301030001b501d150b900307900c49200718000c100049109042d018580d0b060107076500c8101d0894034180200130000c103900b07000300700e8000414400c00c0106111240c0586905c00508010001c035a000040f40c14000d00300094004150004203407102c3c000c81c0c1f0001d1013030750322610441c0a2418414a01c40d5800340c40c2c13141481d210103580c0985400f4010b0790702c412a007070704081041c081c0000e64006082c40f90451113050440210440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861264829 1250 861263579 861263593
    0x311030f1507031a03071a07061401051305160503060a090213090b03032d1c09020102060109140604021e030403050703020705040902131121040c060c030212090f12 72
    0x40641d00880c4441c00740b000750001c1d0b0000c51700c0000d091400c4a1100c07503c011702c03059801038039210380b08061001c2c0416007007820103804030041c448054102d80e0121461003d035110184901d064420407903108803a030641c41c03d4000003502840041d540a01d00070a80303585180c48039000c20803a00081400a10800d0040c03081c00303c07003205c0c40703800c0c0f05c600220020740c142800010344004030144005400c10443d44450180c080003108429181e8268100e0340d00e0480b181803807400c4005001c08242640144260000050003441394480d000e10900d120004d101c00740d9410003800069804001c0c100ca4400c2e0307000044e664442280041c6015511a54070349644404c5410028941051504134070f21071440c08401d0350041c1d503407a4401ca141d08100c0710101e2010902d11078600f00307005001d0802e60703040d0108005404e505203080154400c91040d4903458034581c43d09006c40d00c441c880e003002401340c1e020030340102d00c116040028101c020002096405810301e5080230810200300d2880491041e03021007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861266079 1250 861264829 861264841
    0x1121d150a0917070609120e040f02040b042c04030f030e010b0d1e08040605073005030a0b180a14240f0d0503070c06030c02070311030f15 61
    0x340c006908202240c1c414007042055444600c5440e072400c000b4400a0300010f480401c10025400200b0b40fa504840510f4201d4000c000292201c048501c3c200d20403803030208041d2003502e440c0b00b900c01f0707600348504c07860406042a242080a4072950300c140e4103802e1784d800b2a15482d002541e00751103240310703590f074990003c0b11200140c02e0307070140c0000c000c039030f41003880e801c0c1c13103846442215511a800c285070045003410540e020001023171203800917091900004012581c01c1d0000b0091510078801c007120001721100301c440d0300045082e0444601130b405012103414000e440343d0061071700a14182e00000d080b03141d00e00050b042c54040074040441300c0c2804100b210301d01a6104405920825010110346490071411504c00c1c0b210410307500005071049e072042c15090322440504000ca0300c000d407040102e5041418280d90740d40002c0400c988500700000041a2035129005242e2441e0300c9070000c0c04541d0440e61800c0c3c04541d200000c40c0c1510410100c030309440780030010f046219100c002440c1c0c01c3d0600d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861267329 1250 861266079 861266113
    0xd05010902181b0d2004050f0301090f03140d0c0c1101112d0a0c090c09121e08070f03110c06031f18050601181401121d 53
    0x12010b0303200910b686401c102c8507000c41c0a80007115003810110a69510f00c001e540300003000300e01046180c5040d150030441d194444040104182c420813a450300701c3c8881601018240e0f007011100030440c140940c68030001a008a05200c0400d0440301c003941404045030300c03d0112511041001d0000c0c84a61001d02408400f0458800480080c44d181d504030598801d2150342d80a000c60340380c0c04070008060740c0c0d0a009042e5900440b0902202903c10100441c240184c40321800c0c0140b144091400c0070740c000c128006c24458089613034460700c0603084c032502d48401c0240801c54000000880e8280720038130004030321000500800b8800c13200e03040600c8641c2001010700c6180c2201c800d0590180307411307420a645090549a0111401854150340800e03c12a40648070856011940401000180d80ea1400441d00010311502081ea01d00e20309030b040c0d03000500c21801510a50801e101c0c0b1018242640d4030400c0c035000e001311f000c200801e1485044c41d440201103c81c116000d0950850141a6840c1400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861268579 1250 861267329 861267349
    0x10020717012a08070c1b1e060509010f0c080909130b0121112107030b06060a1d01200a0507080c01050909041e0803010602010e1b040f0b0d05010902 65
    0x149000c09902d07440380c1c001070103202d0041c03c0b0600f803040e02003003101007007008842c10250742d103240000142e850b659250341e080480442c0c00400c40304024100460340328421401e482d00c50405130349424941800e00800e58a49882c00b1080e5130b0240e08000d00400d07906c07002000390050b602a50052029a802e003060150401c06070003505903018241e006021801c0b1881079400c3c001e40002c00300d10301030010b02c00210518140c1c5058042070101059251482034040361850440b4000c44c191140d5554540800a040c4140718182d000f29144195101302d00040c0492034441c894103061411034090340f00600003d9030004590031146920041002c410090180569401022500000d2000034100c0380003810368002c0202007801000200c0004040c00071000704500c030307019800501e200c8007200c1c2c2001402e540c0309008031805517081c10a0000c1440000410341d9064031038904c030a809000070b90810000d0404e04007031425198031010038485555800c0110f0381203d106000005030b202e80c0e07105110300088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861269829 1250 861268579 861268631
    0xf0c0903050c010903021e03010b0405151806030604060c0201140901020a0216030b010e1e04061a090708040602031504020f0705070611070b0a0314180c060403030e1002071701 77
    0x11070b004c0810068941e0b001901301011084a071421003040480841c1c0100500c01c1da44d6480340c1448184030502c9103101441d100c5900560302969001c4090040c0d011114081d14a1030b0103511807c000f5000c201c241d440083c2c142c546100201d207864000290001e651403d48400000d42d5000510010094040004201c0710300a240c040600780c0c5162214008000e05110358030440d950307400003c90044041034025514101c01106802e82d0034941045801070400720004d01500d00580d140703c00c0382c5000c8014611540c3c050355035040355503895507240c011b5080582041411400380c1225651540c842c0040c08448100070000e549a01e85402c0c02c503d040b101c0e030b000c4424409889000ba810b40320101d050000d4986205c49580d50340d03a40c800c200d0040007400300a00c0725401850030711510b17802d004000720050801900300c07089000c0300340c108405880b543c030000300810f0101250003030030f042219444448900c0e60050310840c40c1c0c1c030414212425030314a00c100103030355a0564070904c00030000700340c44608 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861271079 1250 861269829 861269837
    0x9030908011a010f02010605030a02041a0d32370b0f01050603010b160302030f0c101410050415271802130906090c0605070302060c1812010f0c0903050c01 68
    0x82d1401c8d01103911081007080c083d0145840e8201500100501000c149030184094201d20106150741131030300c1080c000340701050a40b80fa000e01c3d10450740012008441c0c654002001d002502c80e5a5405080740d1114102d120956540d1920b03140740d00380701c104907811207016030711100f02450007005109034240140c102c181310340b90030300051100d12080026a000c03205400c80c501d88224441c101030740f442c000e0b001c07210300700c500000324034002c40c0700852050b41d83c1c20166014419021a205016050501190412110469a40100950300d07158200303148260007440303464101750706c450f042c8001542da1010140d01d2a515038070003c200304588100e010510605021050050450f80040c2d5494510b140c0e4543e241d440d61007040504c102540500600c0b544644d00581e02c954548014085800c460000c0c0c0143c000c1000181d940315401d0110340400400c0b48030400c200d41c20388100b103880d01840079a24003030366849401000c100c800e4403074a059841e41d9111010424070f1403800342e00d0642c12001141c100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861272329 1250 861271079 861271091
    0x206031512070b0714030d060b090f03070b0904020901260115050304020d030806310c230a11030c07170d080115051c091a04110409030908011a010f0201 67
    0x90b01000d800d844000d075020103503942e9075805e81d08103440c502440c0c48044800b8a031800001d80b544880c401005142015160b1810300110760f010076860710102d116003101d080e001c0015200301c1c42c013580240625081410030104d0348103030036031480d46011005040f0b1412862a001400740d18035155200e41d4060b064038080c0d21303516096002c201c01008040d4003c040c4403c100100d2240c1e9a116214240b014070140018140121403200b504100c00c0c00301d108003030038a449a0b00e10f6052250358100c0c0c8610f040c00c0e948500403034550034107500c1c0c1d10442c503039806c00c038200c2101448540d0a0008007821800100100300f203609141d624903000c803560a10007101c1e0700a100042100d600b1898050440c0c4800c00c6070307c0100c10030740c0b0a03510b40c49481c0c1c0034400c1c922003d01e280c520203941c0c2d022200c1540210425010607000c42458081c01d0b50544010344148089030140416191075041b403e9690700c240350174402c0c55500c155007429140f01d0202c024520300c0310820180d21b564041c3c034110600b1403620092001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861273579 1250 861272329 861272339
    0x8010e120a030203130b04120816050f0a021203190c03050609040b09100e0106090c0302070512030601140307080601022a060706110a02061801090b011e03020603151207 74
    0x581d10414070044145074010001481a104c48003030300c814290080315809152034540707400c429940717842003404049403408000c92407400c18840c0c19081000c09455003840c120030000c240c6002d4104d010520114840c52a20072000450b40c00070310300603c604403075184401c1035031010006950b6501c21450400d840d20080101c1f5a40e9403413000d0b080341d00581c0c0000f443e280c0841640c285032088019920250405000d00f42aa0f015405002180e5013400700300950401d40d8011000e03071150000182181d48860220086405070038000d54102c8814103140340c00d0b001c840d00c0040240c000700c400350701103802d1004201712941c0603c546100803a0038410140741606012840701c00d010004482402b403140415010700b084500d0b80000741c8010a1412151a020145002503039182e0489030220101002035030421100c1050080c1e000841d440b00e0161580d07070034004025402d0304d46090311011004060000001340e140d0308011030185821800390640b030700d0980300340865030308013904e0400240c0c408030040003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861274829 1250 861273579 861273613
    0x102011a100e060f0d0e0303091e0c0a0312180e13081c060f0e04080a030b01180620120901051b1f0f42090608010e 51
    0x6010004994040d07442841e000704032000e658070000d45030424000600c0032528005034014016045a0070420b00c071214050200c03e41724001952024010f5001c00c840b881c00e0300f18881e040c54040c010314129130144c00072800040411310307076a0050fa107407401843ca000d01a0b41c0501030805900e86154260041d6103031017166050158014020758075690306566101c10002c0289c200c5080300f04000003008a0034918084800070041807140c6008801100000203a01c01040000352069401407040c9081200360403050703000d85007030a000750400c0404120f01d2004c0c00f82d02c24200260400b980c1d0800f003491f5840c024000f42e6044442d41c0700300c0c0d21032230f41e203041003030100c044442040007840d04035101c0001004100070b0082c4800210541e0041e40030050b00004018403402c006003d1010a010300540185000108c890400c110151000c0042100d468060a201000281e0912412010b40031400401c01090050a508a00300c020340310b41080103a51405d0251a042103201405000011703603442e100310f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861276079 1250 861274829 861274871
    0x703060b1903020f13082808190e04050a050a05090a05100902040e030c03121623190203032e090b0a05041a09010e130323040f0f05010201 61
    0x44205500010701603180004030b401d07101e400c5180e0480300280b0f41c4030341c01b140e140c8800500e044407000221035802c030101070311b0a90703041c01600b02810700d00d80b04107820305600801c0d10782039480a01214040c0c3c0400c944903440307081d100d203e15000010f107074100811504142e800190109402c0d40c4104a1200482c102040100400420b0000001c96600d1407020901515420103848014000460140881000440142094080d00c8a2101d80783c1c2e4024002c01c912100e41410310000e0301e030030f80d41445c1c005282c40c1641689130b8103032400e00340815010b01c210707050b00b44658200180c1020007070003440003201c1c9403da00714840500f4858401d1a089403203814520070b12031010a95203490f20b032101520382c001500003402c0094410b00c020350b40d660b640142a103908825a000355220800011141d01d01000140100030180084020650740e40702290b0115004442121141e802180d01e85502d04038001000201944800d8034400761401c801501005c44036400300b410b690620403102c410300d407158006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861277329 1250 861276079 861276127
    0xf07020706050d060b0c030a0f141206120f0a030e1f1b06060609030b0a0c0914040e0a1202060c1206060a0c0501060b030a0c090806040b06270703060b 66
    0x103501c0c2c510098074600a00090b5001045200000a1b01d2411820100040c078068040f034071242e5280d100350034110b884070005444520b0000c3c0500c6190b401c5d0304a900e41c15000340300140305200356003083e40d01a0a00120300c2a168a40d48030004c42400c15400800104110000b100c4100d001904413a507400d404d00801100e00403c940c1191580e1414112100da0354403580003001001401d440310070180042005000c181c0c0c0440c040c00005101c6003080c01540c0c010b400654804003280d1030610880340b81c1044e030641503402034071126a800140410040c611042e030040c0503241300701500c0d90001c0c0c02d02c0700150006200500410142030010962403413160003100c151603c55503000b4403142107808030f08510b0014010350038070900245105600c00694056640f1500801065441500c250703a104694031500480350444030018020450036245136520841c0603040480c00641e007030032124290011122005102605401e101426515124a801422110300e11918041000d414040108642500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861278579 1250 861277329 861277337
    0x603070909141b011d030a080a2606102a060f05070206041101021504140307020306040b041a07170901020d09030905040b0102030a0c0b041e1a0f07020706 68
    0x141010000a010010520070b0250103907085107031401c600d0785015800403112030004070081400940c031282d8130b00d241c041c010014002c0c03509203140e0341ea120580c0c011407450002c0c004403400b2041e040c1107807441d80c061103503240d080da80d182c600a4100304d58005508014020003c010603a4170507405242104400c101c40c0441c45240000645486800f8101500070000442e0400c814801c240fa00099003e000e98459030742641c9078134100d40120380e02e10400c002039103d54850000700e00030420411300000540707142400c2c0ca04d800d55607004603190001c180c5080b580e00803408100800c0c4515480d1188000241c00080000c5080c0b00340700818640c0b10341e41244d44c400303041c004900346170300940c110341800d844440144480d0740380341000303005495144a420300860808640004540c070100855824901d5915019030309002034540603a030450040007201e042200720076244405078844010910076101c0c0515090704c0c10040c6000907206c10103040d00003010040030a010080b80c0105004040d0b80081c40c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861279829 1250 861278579 861278591
    0x305061e190311120303100501031a060301150905030a1212090b01140406150c12050c01020f07110301090201020d030b0f091f06090807051302071718060306030709 72
    0x241000400c54000d8140301d129240000030442004114a0324150480d80794102a41d404407564072480120f85030005d0100d58030b0140300c10340c082e43c1b08a4031200409000f80744205043c000c03401c46e510030b8001503003466140074000802c603402401e00d0043c10065000d402d41c2145982c3e00c180e911050040070082c0200910040e0554949900112800d50000384080440d40d540010500109141c80c01d02c0c015401c0c014045460741207002c0502c99003401ea030b540000b803911501c400741560000078403601003180030004501481d0090006e000c0c2c50303201014103660b1300b20b2403820078011420000d000d4040d905104104000d41e0f000310b210540c00358241800300b0f81116540c0010441d103d00303420f9070750000c0b201c0c0901011640b050921041c10302c1040b0413000c0162103880940f41d0000d9486600f055034426a0244694100b44103810f04120708100094100905030340ea50030050404055000d006c9004503c3d8260382102c41d128000344801520720314510700303009010a440e1002405016403d54980d9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 861281079 1250 861279829 861279889
    0x11401060804030e030d0908010f05010509011205160b03330415080708160f24030204080307031707092114060702010f051608240607050a060c030506 66
    0x801444c0261006007905d8041c51405009800c0000c507020381c000c19868040c0c00000c04446120b00c81c1a56402011070318643e02c2c0820102c1d00382d00140049506000723850f81d000d03080d0703500c03080d04000d0001c0c00103164592a166580c1800304003a6004824810071409204040c0b02ea4084002458042603902186a56401c1080d10490f903080d0b0107503806110740300000503586000b0407400ba50200703004051603140e0340c945240c01440154003d6180f0b504806090612481640d40d82c819000725506016041c0f603910a2001c2c15a080206c054001c1003280c07200000500407008400d034040081d05184d049241402880e6400349007130310000d04141491142d2400380300210b2000b00404101c8070882d801031502c044000d000c0d01ca030080c0d01340d209007040701188038003100003200c41e4000500d075180140e41c0e462048690040c0c40480c548010610803202040b041e071218001480b250740560000d2248913400e01e400000c80740d502c0144006c25241074180b098070741d10f03402d100d0102404c02c4096020041e07a2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 861282329 1250 861281079 861281087
    0x120105013609061508240c0313031707020d11030a09230901061706010305191505120a0b0f10050d050c1f0e091603110405030109060b030d0201140106080403 69
    0x1811800d60320034039013000010340f81000140382e410300c1d4600000141c4801035051044481d0300c2a220314010400600000f0b060085c403202c0ca5544034000d00d40b0110720310242009030000300301560050016042850607000c02c03030300050221003045190004500d44400380c00c000741070f03640c280103e6036070140c10010450b03602d549042c0c2040c2c0d0080200304a0155035550400b421810254508000401d0351800040300c560003407051034071600c03004bd02c0d40001009852a00000c25598040c22690341c0c01103c0410140c503054400d00146070348400820380c0010f10300b0300e928030b1031005001d09003907000e000030005009159800d200817100c05681d0a0001d1140b4503025060810300300303a140d000800c400e1b8550829100b40e8060943c42440d07128503106e00000c1c0d0501440c1e51040300c1d0000140500018885110301c02d5010301d00c0c0026080490b402c0a031102c00090075140b0300c580691300c003034586040001914040c80405101c00f058002000b44002c0d00c0c0c4030645024051084000740000400050240340c09 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 861283579 1250 861282329 861282341
    0x8160207080303010801090203120a0e060706200d06050a03170f0c0313030b0f15060904060b031e070c2409240623100201090212010501360906 63
    0x40301c01540d84943e103400d803660080c6002e0b00700b17030f10074482d5090940c0301c05480003c8071400000c0d0380c0c800b9952130241080c04403950260354100c4640f03584012010a03414884910520551100c0009544201c41117902c8169a806d4200360304c42d00f40080c0401c0000c014030380400c030407500e0707240064840501c8000c9880b140500ca940307080d03c1c00001004840b0014100358401901d2045981c000580c441c100780e003045902c12540c40001c0314007494010300034902840030300030b46a03009001040c2142c440520101c11340050b140c1c20789580d1a500c010031008503440782140d1110952804014072502a01c884601c0e840f1039071341c4c00c0b0103d1044040c00804445800122003950024040c44480791440150a2424400680c2c1c0610742d02d01140410031401031000d000801c4603208410f40c034060240c04000c6144c0541d40b1010556507110074590042e203411400c3c40780c850381c0c071000046640c0340010800c00f02054040c40003042036490320a03d50761404841c03543d4040480d50b000101001d00d0f241150041c90 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 861284829 1250 861283579 861283589
    0x290402190312080106031103090309120c04090c0e160f0305130c0e041104020c120f0d110711150403230709151403071a0d060311030d02060708160207 66
    0x8240b020030603a29000000c040c101c1c0c00d82d9600304221820500c18102500081e5000085508100024803080c03030208250036156030620240c480050720345001904a0703080020444818035842030070400c2d410900040740c1d00021030f100620261403200c0004006004d421011000d160f0780d04049007815a410360114803260784040a52103c2d030729080054040c000444d4116002c180090107180207007440e000b1358405044103001010805881100a05113030480d080020541d0300a0040c1c5624140078022146001039854074182d491030541401d038030580c0301d55417a500540741c080c1e010300400c40d0702c8100c034100c80d081702c000c07104602c0e02820304000382d00705080c0078010303c2819404103002c046540f2540e0046c9100002400c0d1961f2422101d1491052408c650383c1071b00072420412250b8030003400380982c4442407006600d0817481403407420480780c0c9070304251100313400081460300c7c5040c2004040c6103c1c40e9800100640c1c9840d0400401180c40180460071503403424207010f038010b000f0040007010b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 861286079 1250 861284829 861284843
    0x708091009060b030c03160501270b1902010b01050f0a2106050301270303050601050d062405070c180e0307120207170c09041a0907032904021903 64
    0x1516070030311101410340c00121a101707001d41c0503110b03200d180003c4c601400360200c0d080003018a16040040d215501e0f100030325034030f101404001c006401e11520014026000010459850720505015650f1090183c0c596800b503a14210b405d000503078102c0255540030340b030200c07615070300d500c421400c40d003186e01414280704034107541009001110541d00007505a0f401a4000c1100301900042900701070034140e40c5100c40300001016030003107071003504107030740c04141030600720315089500c002581101c905038031108411004040301605400700465004240316a440c026041c003185442d2204502014401c12000031500002d0101320501504000b900018881c00d8a858051a0030810480c038402030700140140100540400c00307181c04070008007003101c1034005003a40b0441109100d0768003005002903980c04c014200400c1c5401d003044004d8460b04220300a4a0b501e0f186290003d00951720728102203942e0308000c28003284840200031113070300c540c0480d0000c0c0d401d00e10040360394144a41b03401c060401b03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 861287329 1250 861286079 861286091
    0xd02040b130e060a0204060e0d02150c01051609050319110d140f01020c033c0a08060a1202060f040b030906041205040e010302131b0c03030608011407080910 69
    0xd80030590002c66590121815950f0035030720f103d02d050403031241e8007581c00802e84d4002c008140c0e0030401c040d00d004c10700c05809100641008503a05540d0f400c240e100000e07507919841080802042c45644416038011130a14010640c01d0000003a107600c3d0500303412003003074861048101805420800f040c0d0084020701407404520040c140403403503e0701c0c0c0d4100861449008001002c1d060148212914104940040e5040c450708110440c0303101450503604914a80b200c0280014a1040b030082ca2030a040945095a03140e10003005405403c0050803644601803211013081140b0351031651058292741110010b940e03807280e040c403840600444c1c00c000c03111480403007000860b0714005646401140180340c500c100d0701007583c088500f4801c0c0d00940c044115480010401410316040880748501c100c0e8000c6890002c00740c5035565521122280000141042010400d15800d4443ca02c00740c00030100920040c10504104000d068000d4245d00c10403840307800041002005000780391900303100002c14044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 861288579 1250 861287329 861287359
    0x1513031413050a120201080c1b030a0504050316230109030c030827031e1e160504140601050306060f07060c090e070e090c070501110301030c0f140d02040b 68
    0x3004400e00401e8041c43e00030401040f80f5034803c0c1c940d40307801d40c144c1d201e42d0107686000240280da0001c120004250400c0b00142051210a00103000c29407820398a858032640740004151514000004091003440740307220038804850204510007503520809070380c000f200350510040b2480c1059900292024404a00100821907000e004000307807c80201076007014000c982c203840d0003105414000b0b45c55400130f511440d4818090581c20b080b40164000c0d10840c1c1d40c0c1400b0500007001084060b07040e500a0011031b10026800f000c0b540c05848141c81c10848000c41c281c01e9034078410040c20070350600030040002030050382c5d00000c440d034003500c0000f1907403542d14a09c5c019019200c42c500340004075405003130210325082c2d01d402c0e40740700348420354400c14640d8003c0d0a1100821003d8001801d8801c100300300d1000c80c109000304a01c204209030015601d41c514100081b80c15255004a0501192608104045003840c55080c483e00c004450402c5c1c1c0900e507100047c0109184115070350014054410038035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 861289829 1250 861288579 861288607
    0x131b031a040b06061303033b03010c02030702060d1a0d080406031a130b06190915020d17060307270c0509011403040501020c0a120e010215130314 64
    0x40241d00c21003102c141500d0741c404000190213a028541300c580c0c0c80075000c00c04039204100026182d82e25880400c56205c51030501c1d40901000e02c0c60b42c441c021050340500703540c2001d00c00c065401406102840c00d0a883d540050320302d106113861010302e40d48440d80e130320805211560314002080000c201d0400e0070b0b001d14100c07400390080c2c460314010a107050318000602e5a043c244650b00040140305101d0321030740c0e81c24040100400d8926039005041484040300c1c045600c105800812100d4454030717680b81c94402c2ca814040080c0c110f004c21034000d4140b20002503042000300f600c88001380840c1900795100320100385403d58030b034000c24440c0c3d10078091440e0303400c4024070f40d200e800422a0a018811245006481c03034880c0d42100c60014a14100f20340c024490b07000070b960001e204070f00151604040b422441c1c5084c1c0c1b01c3c0c01c2070700c944215401e10420707507400c03d500f422811805e0029007101034821086038600100101112003100c032106c0f5500030584100108480c0701044a07900c2e407550f0380458404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 861291079 1250 861289829 861289831
    0x70215070c14060a080f101509181a010f0210090b041401050403020c130605060403061d070e070302030903220602011508030306010f210b0f09131b031a 67
    0x70115000000c4102d0306040640894035a850141c540340c815440e00409a6401c00c0001c0c0841d21880710701101096020070000d0040c0030740c2255840000490408020680d2001a50360074130314a40340100d95020500c141504142c041400d0030f0a0030301e48407030a000e07408c0c504070342114000a441e000c0b01008125040d0130303c07805640102c00c1d0080201d0204513180c22a14250f80103000b41c1e100c1c61030240035203000780051400700c90b4860045501595203004c1a007e40140d04100c0382c207a10f600c410023508800b030202e50842c108070801850300c10301c0c0c0194040d4500d405492601010303000000034004440400031100007207200c080d030159000040c400c400f100c2c0b406000d1103005500f4111451a100e040a81c44000e07106040059441c5032640b1006440c1c00c88a10090390510412031503c03100c0c4212640c00d0310800e00c584001144400141042041e52808410510710465220b030501c40d81030012010f05030840d5111409001d48944051013a000003010790004290181e05e0581c0344c8070141203903000f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 861292329 1250 861291079 861291089
    0x4090212010b0a021b0310050a022d03060f011b030806040f231e100305120406050720062209090302121c0905030c25050402070215070c 60
    0x102241c0d0302c41d03500d00c0b41841521015401640681180d0200c4000e44a60f040b0481d0000c0840300252484079030078090380c008072900610325901244803a80407422032024003101d100000d142400200070310400c185804054152401102c5880c40c5c41c030503074002c4a204a8200c1460401c80183c070a0b4500201461170443d0811301035401c0103c0000150468068107088900b01d14090744400c010811014030410010180020711010f00040c9031124034003030030540907041039514841703914110b081071450240076401301c09184000300001c006942e8018190382ca0345900003080000e032501d4140c8440450b50a400040d400b070710024490020052004030b45100b4804890070800c5660384d07403000c400700d442d900c0004d1f0158100c800030f014124079000042494680a400031000128240d213903100300c0d03120800c2180e03540c0c40041d07142c107a604100701c240e45d4140d01c44110740001103a0099400340740914440d0b280501d80100314403003159504180856413295514038151107441900b0206070303882d128864 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861293579 1250 861292329 861292357
    0x2070f0201230d022a06010807080a0309060305090705060a021b060c060f191518050c040b0c01060308070317010602030f07080a02160b13120c0524040902 68
    0x5401102e4000c07818076000144103120b0b00381001a040d41183c0a035000101c0104034240c0007407440084005103100546808815000302055814005064600880c54004400d6540924481000170b0b5202302c011040d9266443c01080a0710f42c2d034165440c00710745411040c0c3c08840410f020004c43da0002e0703508001b611201c1d0094220f840c084c18000076210b6040c0200007a002040043c548000d0801c2458104050041c0030308019a42c0001c242142c0482aa08024000d8042c0030001c5502150f2501c881e20035120041100342480c80380345000e841203204005401c0400b18008115a001790b011500842e04408126900c42e1185401000b0107802c01c990b0320700104034400811864400010340d403c91041e642201c1c50600c40362101c00e03054024058410442c4516212007400506000070380c402401544030b100e46444401d40c1d00c00d010140e64000450182d000202007001c208a211044100c0b841940c1c0341c0010318900074038804000000d15803500241c000540010000440d41c010010383d085100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 861294829 1250 861293579 861293597
    0xb0c0714030a140d2730060f0518060f0703020c06090c01030c0804050a02061303050102120a0b040b090402060d110f180406061e050904090c03020a050a0b180a0902070f0201 76
    0x1c041c2c8514a10301c401c84003041d622038170a00c165042624800c1c1c0030b40035514a900408050000b150148040e01c6044a00b10703200c03d06c0d0080c100740c6c1d01072590000345400c5250035081c44402440e5948900a00c2c1e81c1d580c031004404120002e000e54100c80d420804001503411524000140640d6a081c0f00719480c0040c3c54140e0180e012072041c80094020f55015002e001c0c40440c2d5002c005840e008400c0c11a20000c44a00000003d5801d20060100d4034000582107440d00d0b180000390200c0e4030102081c3d0080b03040424030200d5949008110390700c99411101c0a882e200d070798110710024801c6590041c400d01d00094100000b41c07000c1c026000041200301c11a0f034a11291013441f06480c0c442c4903050102e03141c10110308000c03024180d80e0780140c800d8540076051441c220000b80c29504090001e43d03810100840c240254201005a08040c04091714040402071800544440c2c0d8410000c100c100b034420140f100d0078594480c00018010503007107409540b19902400c1c8000400070504040b0b000ca25000c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 861296079 1250 861294829 861294857
    0x21303020307093e0c01090614130204180b0c0301170c0a0302040f0b041a0301230c131505122401052109060108070b0c0714030a140d 59
    0x2005a050071903080d0f004038844d801d484205191401c01030b00c0b15540c0e00b0b114200d2082c498008000c1c052250503100040395040850800308101c0e05070070004414585510108801003964040708044e682d8162000100c615000b160350308510f10955005044160780400e01203074003d904040e50503038140000c1e54003000da002203807070790303c02100d210140c0289403201d00700094500b83e8071080c0c02d803840c0e40e40440c201410350005030849120040c80070321941c2e46130004161703080034865499150007100c50320407900384142101c03042000080c0321002403000001c1e40c8c025640d001500d0001400f10521000c0c10056000020b44a45c100c14681050824800006022113200d00f42c0c51a03910009180b441031409840b00445d016413102c0c12220000111480703032000803038082c0e0910306c10001c517400f5102c954140b9400e64201a840e6005100c5880144400c03414103001069030021110350b03401e2001d600700c01b1004a41400a1050060001071500d101c0b948000001306090882c06030603901c2c610344900d04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 861297329 1250 861296079 861296081
    0x7120c120f0c0b07120e010609141308090a0315020d0f15051203280305010b0f030f06040e0d020c010201111201030605060a0b0a0320073302130302030709 68
    0x1401c92000101c50118002c0800c1c80c010f03032107800007500d00d05403100030705515081066070740d180403001c0c03180c2d5109010400031000784604c440e10040181e10000f58208400414010407d0010107801a200094080102d580b01c601305c00046601c2003180840180115400c8000d4002d07000d00342d052030a0001084410105128212018400c210b90048083c00d00c010303c2002d24a00f0303410030326403200308040c034138040c1d8404006940f0240041c1141100c01919002000d4a0040c4d012081a280500240000790f060348180c1c0d50091225194440e20341c0d4080c00038026203900740c00c0c00032901606410044055020030130740d1b5072000a03002481450801118540359101e124041901400700c1001803001803030703a4000581018004084d2401c0541700d01560480340d002080d5440469600c141d40c40a020019600060b00c0c4800204241072892507140c62031a080d0764004d20454a0040f0302d050302e00f02a1030400010342000030000c40d143d1940800541100d18030340410392180c810030400144001d21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 861298579 1250 861297329 861297347
    0x15010821070812101a03061002010e2a09010b190905030a0602160c0602030307030c09030c060f030f020d020904060b070f0b0c04050603040b18070e0c0703030207120c12 74
    0x200803111850300d10b10f201110381d800005000c1c8480c12250240000342d80724069900c83d9422030703070540c842d901d082c604108944484401020000d40e410040c41c400581c10105e44d01c018140d0891072003030b00107011400991b84c4901030f0401a4007803240c030000305088030b48001511559a80a2150040c0f5014070415203d0545911426034154004a09070f00014955005040d501a107041c90005916141d900e401c0e1100054101800581c008810030030841d03410300560400140b41d0921403000750641d00e4a45590080380105014000c2d00740b9a900018401d501940000384105021501c0348215200a0080c0d4490b80e0703014407803410800003048001c2d0420403a804181d00c03425002c12550107079546115002e00426002c0161400d1100241c00d44444009521591241c0c0c1c501c812442c0c070700c204040c4150003d00028880c0d000b1031041c0205491503001c25086120201400d031100d03860b103011400791041001c003c15000800c1040750805e038200c07141c5083c1502c07605ca0080a40c032100401c0b01e03034141e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 861299829 1250 861298579 861298583
    0x9061d062a060c030402190b0412080d060312091d010e06030316060506090c07031413080304031101022407051b0a03020703170c06181501082107 64
    0x20080100e504100c150940903040a0018505803010400340c1d107496050407400c0342d1029068200108020461601f500c00c240098150759118180c98106200e1034500d02540c0541918190303130607801da060202800c2940c8041811600900903e522403030b0210074412100e2912000c10180307e03010400c5034088031918030070046110b0785100d5078a4201d201c005408042c11294042c0000c0061070b403c850342003010241c0d680120400710710341c1058030611020400c0142a011001d00074401c40c80065406032440c00c40c80d004031045602c032200e100781007801c9030700359101c0c40036440b0000d4004108000290480c0c5401c000740c098502ca108110102c54084400030107007820340301d1900010303010078011030150034140c2c4002c0802d400f00451020980ca4250b5903202079015900104041080140108c48101c3d410800002310303040500003604243e4400e8090b20fa000070503090000404003100c200040004507010580b407100c1c030f50390703a00ac464072030494006040304e060340304009801d115400003c8070f810300e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 861301079 1250 861299829 861299839
    0x5010206061003061d01081b030d0c0c1d04060f02031b0703090302122a0d0609020d0609081306020a080a0f0903020a06020304080f0609210408030a09061d 68
    0x41d6458080001c00200c000120052580d6998007203101e5080f0000400c3d20031070310304011455410102003c0c035090b030580f00280482121241003040340c60104074041124010b0604400c808020f2a20480d15000d03600700d10b008001c2e8185801d0f0082c040c604150042d40505410000e81008803030400036072004803032007034220014240d54690111464001d24403140a440c02070182074403503000413078625100c41c0351310740e0f64400109540211a203c28000b4176103618680781c0c2d00416030340042031098102e40c001501c0b256a1b084038600350740380d10b1031240f01c1e941d02c0502048150f030b0918000030960451202144150131101001c0746190001500084c0c05030020106030512034124401c507a501241034620007002104440000144c03900c61001c4080c3c880798000d140c0f20b41c00c10103540d00d00b16440440074070541c80b81050000d007440114a9480d019480301e0031918140e0215a904503034483c60703102c1a814400040e10030401d030351102c00e10080d28003503610301e01e00c0d1482c520101408910500016809 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 861302329 1250 861301079 861301081
    0xa0909231929150409051503010507020a0308150402160503040e0718150e0d0825080406030c020f06010e18160b0c010608030403050a060b15300907051905010206 71
    0x1502d03081e03050503444880251010324242c5c031640350340709803242555098480f1807038141c100c0d030300d141c280101369001107079100034000083c075501c000781720600190071010401400010440d26031115011110030142c0090014200040e80c030f8055920381c00380c07203048002088400032039040da216082e20700185a600c204e0061060404501460490004040c0014001c8c0c0503103030a10b9484c0c00a04191160041c0b8a481d103654002c6c07034038081c00f800d44d9540c0130403216000c05400043e809005403016a2040d1400040c56414440243e10f0700e040c808000c52684204400010b01010901c41280702c1c080200c013041096405000d110303a11942c612040400c2c000701041403002d44c1c0302c0809043c9180d42c200001c00c4960b62510280e086500c1900160b6803904001214001c0c000c85000315510040b054903080145000381d51001c500c0e00400022403005c40381e041c1c200b000010301d465803000c0c1c240c09042c05145400c20074041540d9103c03038404c00d401082e00d10300d41d000d510340c013a10510842d04180c0141081e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 861303579 1250 861302329 861302411
    0x42c0c120a0c031d06150102010e071a040e0a0b0307060305040201171b0403030e100504120f110915040b03010b0a03110402070c06020d090b0a09092319 67
    0x24101e503003000003c040d6034500d04280455000700013084404210060a41401c0043c50f40702d807136840c1d03800c080c1503a0428a19244c4194005104002c440c03400564403003885070500d00100b1407055900400f0700c892001c0520840518a5000c40c100f41c4044003119403103682c1d40d90950a4400840303020340828000020030b0582d00780501c20992010101c00d00c2c518490288510b0300c140c0d04a60010b400042c50340c41030b04881d003824045039030207120364240340d410945002c200c40b5580c2da0b40e0314014400901c000355941001a45000c1c0010320800415070a9585072901449801c00c24450000384901d0600c5419000da0034181706515102c040503100001e03c82c00c0d80c0b42c0040c40e20803d800380d50840e5013048074102080607209440080c006030303400b9001d2040d041c034000f01030241070740003845000d008000b10804281c100e80031a0882d168054041005210900001c4041260b2240084415100030070010845524070340f403015040c0d002c0e41003010312034155035440c0e040f94041710490980c000d8595051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 861304829 1250 861303579 861303581
    0x7060b010c080a050705120325020a0227060117070e061312020109090204181a0909010203011d010b07020409211211090a1505042c0c120a 61
    0x180104103050140a0019075a581d400030ba00c00c500d03890005002040840401105115000040d540c0c10711135411401c1084100c0c1c5d00b101ea1521004a890751000c1042c5128000e00088900e5500103200c0703880043c089600d50311601c024080200c40c000000c002980c0c940c042e49541c12001e4540e038023450305d6500c0e0750041da2007084501946922840a001091510b0344a4407680007901c6507010103501100c01e44000340c0f000049801410100e8010700c030a029500880d2402200d0480300040400e210400500ca4048070071441c1510b07400c50810310800484c080e0540040d41207808110401654007686100030303101c0d40c42030142c40b500040030001e0f000545440c0e00714106850240001004410561481003500300402031640042902d09003422404541489090700d20f00481d5600d0313103000d004100040d146419800b44840501c00c0203551000a031103001030754060221003ca802a4841181504004100e881c2c24a800c0c06901000105015445419030b20600c0c1d241903020601e84409100030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 861306079 1250 861304829 861304841
    0x140604031202161e060c08070503071803020d0308010e0a06051503070306180606020d08040f0b0405071d01031e0503030408030a111206031005010501022d010c02100605150706 77
    0x900e1085200c0c43d510104030301812500403e07a015114510401c0c01e49000d00558810b40e81d8041400712010801040d2500311f0121b0f03910141520340344008500c102407000010900307800c0650090000d602e804205900010014142d500005501e840c43d9900064a41600d045004031900400480d41c1c017507142c12980081c0d078000000c2e0138081981070304d40080005240d807030680310400ba0b484400411501e60140b0503c20151021302c0c00d000c6038078207030300d03801300d0030342c130b405000f0a61104400010144403040c44080090165071881c000001004030030781e41071040a000a0700c03490300c0c9003000005617240003406440c0542c03120140d400c40d07846440741c50701d54000828032080720b9211300030030419043c1d520080c00300140040b0000002d003402003d05281000820081ca2201e107000014402c1d80e0700000d1004151072040340c3c580b118512420f0301d144204c510822001e1039801e060a88031160b4000c10030140e02002507074200682940d03042000341c0711038000d1441e500c4210802102c00802c3e000d42041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 861307329 1250 861306079 861306097
    0xa060b2d070f08180406050a170c0a06030b0102062a18040504030314090c130f0e0d020705010f0503060901181b12060518060928020403140604031202 66
    0x309040911640701e007101c86071038031812640c2c60000a40c690540d41c0140c0c40408426041d40d0030800d0b20704201c082208c07a45a80150030340b444c071f00e00302408100b03001c201150b421a00941085100d44da41c07000500074000d03464110780940a040005042c461400d95403005400c0c00300b41c07150070410103100c03001c191fa000400c1d0b010103011800c0c3d643e589860b02c0c0681070042d4407a84d40021218420030203c200100007408645068000c40380c215007554070620000484c001d8100c001071102d03801030302a030060056103c010000c1c01101d072101e0250343c001c07030620221102038950000c08104103c0c1200c29210444109510500640051003403290500050a0005010030002030a1100798090b0400b001c284040c140040c410380ca003041000312600a55008140036126003418440e2030702402d10903440100014000c0c0d000c43d00003640c0d8041d6690f4010540c07500c164450f00335100d0820580650311600083c4c0751040c1c40b20307142440304400070b0070912454240c0e0382c240080074a0784040d0041c3d071100c2380e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 861308579 1250 861307329 861307417
    0x613020d05070b030a0c0216050402090f150a0f0c0506010e131b0f080f0a1421030618060105091e12070807060903030503010e0c0f120a060b 62
    0x20000164200b0a00000d0a010403500c2c0c1c680c0303010204c04060b200b05003007003003c44d00728242c59207061420b04400f4081d510708941c0540c0b5004050003081038522642c005e690300c101c900744404034103419a0010407a1105581d244410489005c10503a051a81400c0042c56a0300c0b0b40010000f4140105a03d50081c0d41c0c500128030984842d00c031011484141d11a08406080b8403004014448031680480c00030603e910242036904081c5220644420035100080c02214941c00000300392141808410800230701110007208100e044581c0c0d04c49900122201400b90000c0340354000049040f03c820f521801c1e05a4035146031400c07030010301c121103501c4142114800040784051309a5941c684035000c00c510500b0043c003d0310724000d0405c0c0b4161450b489142030019000080c004258003101300c9064400103140140d0540301c0c403003c51000c0c41021041c02c18001e02154100c6481c0043e0801400760780345007002d21540c2e8441b58221040d204109003410001c8440d1180242c1800008980c11600d0036112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 861309829 1250 861308579 861308599
    0x40f0216080711061206090f070203041a04030b0f0403030b03010504020904080702031018061b020309010f2123011832040507090905070b070204090f08091c05061302 73
    0x804240c460f0172091030003101500207810026982841c01c8555481a000c03200340701541400d40000c0d4407480f46004420f541c884e215115200c40e8144411100203640c0031150001c28074001c86c803188d80000c10b03102140080d0911140d1605898140a01030240780c006240590b191150790b80c0c0140e41d444840200d030540034642120451552910515142042c505101802490249803500444d403000c508921029004214810010384c004165001c0b141c003800d08040204541009507401030030190003040715214032141c1340141a49400c07000c1042c180c01c2d03001500f860340c0d60030f094003401c0034050381003176464600da02c42248103203070000c4101606504401d001818071f0702151465080d07803200d90000c009400240300030400100440c1c00200750340b0704100304110b174640d5403948509180c1b003075062010f4041441c1c0250359407648604407142d444104d04200405034901144190001032500d80b00d1540304107440383c5132011805080407283e1007005044c00d5662880260400484103c050740c228001d03038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 861311079 1250 861309829 861309863
    0x150b0d05010f02031501020715081017010b040f020a2309120105160f020c090a020f130e130f0b0a0b030f070302030d0903150c14040b0405040f02160807 67
    0x1c45000b4094103503210250f0741e494510f540740300026011000504660041404004100789407038010210081440d0051041c0c890400c80c0300d200c0354039000014101000911048484015480504140410f8400788170f4010b0720010b290803805040c18a602060066130140c16000107507900e521440203031800c060034000c4070400318200c0c0d03103100c2aa0803e40e56960138400c600b0310030b1400f481c515090340303840e4103400310a5000a480c0c2c4050080107000d83c910b000425410030180e01034403d0000145d00030740d11800c07903030717900b00f60000c42d840303170368a81c410071404901c04404010b02e40a803035822102984a1300703000e13520000002030040490203480d07038130f29005180740e03000d0240810400d2800c00804055045004241c00c0810016002e410301ca400c82c01040010b84002c29102040410380c0b0004221940a00569540c07031071b410030218002c00050f01041107202480904140ca109a60401c40308402031411022840b5450300c00b060380c000c0418080001d20b00200409401d803154140c80d040704550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 861312329 1250 861311079 861311081
    0x606010f03060b131802031303050a021516030509032502061207091a030714070c0f080f0f0a0f0b0a1103010f030201080702010902010e1509100305160903150b0d0501 73
    0x680400500307003d201360802c084105502d40c41001c922030101149903080504400082400f071400040071707c240031030001e4140c1d009021049592034070924a003202d00e80b05180c1e010402c91907684001182c40c1402113441c2260010985850212034029000030343e060510f044500303504610101c1e8044800c01c000a04440740314880c0340100c8484e102c010b03100d0b040041c017042000f004042400101024000c11690a0344412080480002454440e549504a0410703010650702c98101d4641c084124000044840001842101c01c554240035100c40801d24080180c036801d144a001e4034200001020001043c1c5071141e480d00042c0e1307a1800104940c40300d00e102c0ca1380e0000d0340400800c84501d80200f084d075800c546030300d5000c0c0d40b40c802040741c000640d001816450000408501444611180f0003a0302c100004846c1c209800400080c11001485001005407404481e4250140b05000700c0c03104240c01307603083d1004d8941c404034068080c40706074107032001000b000c0c003400c6d40454540300303210120740c003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 861313579 1250 861312329 861312337
    0xf04060806150906030103030c021c23060903030a05091006090605010e01181415190e011107090b0402040b0c0c0a051804060f0b0a090608070b04080606010f03060b 72
    0x220389400e1568a820001c1145070050034050220b6810304020030740071540c5020850b41541d0341410b00000c41c0780103001142d09019001c603109c01c201c00f110854018800f040c11220130702050740c15038240180218003c80c2c0c68100c00d80b0b9045680d4070600104159608580020f5440041501211684800a04643d00b914003a900c0404c0045e56217109025550380011a01d075180d4081c00c044070341e22071002013510040d800384245040d0352110761100d102d6640d80c0e0a80c00b01e20f6010308219850311020380204240c12200740c0d00ca808901e000f082d075269940a512820300340e4902801810466103000440c00240c0400300d000c42d4131540c20000402c2c0d41291384041d00c41307030396140003e240705440d000900c403a068071504594411808a102074104000d1283c085a0141d840307071010459440214801c1d000c0d20500c1800c0340c1c0303c4861030001c200c5a200b68085000c41c0c0300e5000311010141d031017400820382c1c40789015003150742c0c01c6a03001406950240e0501c0b098a4210b01d030001d001c0390342c0c00c80994242c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 861314829 1250 861313579 861313589
    0x3070b070f09091404122303010518010302030a0b041a04061d0613060209061315031413060504050c060f0430021908120301080f2e020f04 61
    0x40514080e6038000d52100410300580f14483c02001040072040b00d00b003c02c100100020719450a4201d100031642c03060424a90b0b05005d00400c0400705010110f12141d90406d0281c540a003403282507c01040300e5040c03801d0304030b903006030150445041c43d40300ea41d0840300081040d15122040c401d4450a0b5050813a41c0344100e02078000050740c0340300d40c0100b15615030012441c80a0b540414188843c414040c002101d4040c0e0101c0c0050392549a04041100390181c0d00c46402071901418000900d440c06500c0340030400000d5400b0800e00e400800c0703d0821000958504c62700c954100c2c0c080300040e8166000540090183c0d00b11040e064680c0c0009040341d00c0240100c49000011500308851281170342280b40d54440320304800b103804284022990454402e00c000b82c4142d400c00d40c2c40700e80014280006d40a0f14140b000c1d074280300311403000c00704258800c1c82001001c1c865441503800c0300f240401c6000d00e81d40ca00500d000032002c1d0803030003c1c0c00380288124040d00c0c0c3d420090b251000d0864001080284 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 861316079 1250 861314829 861314837
    0x12040b070c030c030317130209190b040f0c0206070c03170402040b03010c0e010906020705130b06070609050105012309310f03020c2b080d051e060d08030103080c03070b07 75
    0x10946106c408020805403101038240003040d0020b00580d40c500903164041606030188442c2c0c1040518640641695803601d504a490a03001c05400c100035000300300701540319022190700351030b00c40080b545040654009000611911408240c44412164203600640001c0c004076070400d032440042d084a601c00040c41c0420390301600b082c007958100810380014002d500103010060f2410740032600b031202c5800c000101c0740c0d03900702580d141d940304c0080d15110768010804000a116502d0030390b000b40400c2c0250f0000c0c0f28111040c903402000303141111080d190240c1501e02c0780d203808404a02009001d480c101b03000f010654420044c03259440d4268440780150b08050004000e41030103030801e210b00c1c10503401404103000030000c1c003601108102d564a06105090202c8095040055035406036041d08005c3d94104400d100d01d00c26011200c0c1980211940c044803180ca880c410400f24818010004100050920041000c943da14007d81258000381c3d0507a46080c82a583c0c0c200440400c031100000b02d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 861317329 1250 861316079 861316097
    0x60405030d030f061d04021c0807050106091a010f03270c03021513150c2003100b240706060803040e06030c010e190305100207110312040b070c030c0303 67
    0x7000f1030151800030580c038480060503110740e5544c01c0c114140100068051000c2c0c94131040030403040060300c03d00c0381d040962161641c9062400c503010b020148140032110382808221941076035110100049914140c4070b000d151054401d040c0c0c0a04800c600e4503070000300030501c8490810751021600c150300e00c50b00e5205c403807504602c1044802d507000700d0480c030703080c506014500444000c401c0c10000d50300310520000b010a171a040460381112119401412050001d400c0140b8003456203031202502c42c00c60984d01c1403c070b00c0440768100c5200d0010280d20014003244196090a00d1444070081e06104034454075002e82611b802c01620682c0d80521541e030b000080030041e2466070f03c2c80d2030300702204501528a8800c0940000e2114040042d440c2c030410444001d03124034040c5000034002142c0c0034060307130314010f01050f1349802900b00c07203420b4a100901301e607500403e240218a030420003c0c80100f290401d402d00442d102c050f04081022186640791b01c40100105002c1d00856005500c260788400304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 861318579 1250 861317329 861317351
    0x3090706080a020703051e0712050304050c01022a0111031303050607080c03040b190e0c1207150c0201021e010617010203060a0302060f120f062d0f060405030d03 71
    0x10490700900c1030b24510310502c02c0307000080c1d001b0700710b400e01e111120f40641050810034078042d180c0b00c0d43d01c006126000c4141c103030001c90707002400307148107038040d00645000b00105401aa2100c00311039444403031085080c01550f0201d65894200c0c0030f400c040c501051141d0f02d100240340386500c14250000c42d220700700c00030030402400300901c81e4000340c02c0c075004000c2e08000c0340c9906a40009031004100840000005440501c800034219000180140074031071843c031281403039194039405c44034501a08a440c4032024000001031b540080300d11400a0b02d0303000c5a003c00031100e03850040c100300d045009921030840c048403140410760305c08070f1000002501c43d1500b030b50344038550780c00441800141d005004110160b0345008180e4103c0750103076002547c0e400c0bd0600c100d807910805040c2e49404003103034280510a80741d00c0000f445020152040c1c00c3c90468403400c00f8850311096404a50003d410309545454149200c0720025040b01500d8507040a0b110400079007010440303941d40d40065500c5000201c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 861319829 1250 861318579 861318587
    0x2d0b0f030c0102100f151d01170307060b0126010306061a090d0c1d0a15030b1f050a08100c05031b090d06020a05070c050a1401050f190c0c050406060e0d031403090706 73
    0x80184000701d2103510300031800c0701c180d42b24044c800303018103e5696080202c6031070b4054641058034880030200c54803003c444007806034000c0001c0c0419607240703142050100f07082085075042c49031507100d20091401c210004003004021141528201c41305e01004c0c5002905d1300481103103080d4401c0400c501030003464130f080040700b260700181050b0003204800b48108045a000402c0710f802030791030100b50103801000011901960000c2d40040d800c003003004ca0000c0c28240105110707041800358081800002c1c41c861088a9500040d107000f1243c1c3d05c0c11450300b4075801440010040f120001e804078019000f29166181241c204100380390100f0000a0004108a186003012001e01401c96240070180d00f8840202080c0f06900207075070500c500003c040a80100b5001941c038240b868103504c4150303d0003036000500c03411022808681103401e0420114551800d0302556050314850f6403402c6000400b07608004001c1c0c0050010380510900a40d1300100c26103d4008502c19601c6030001c0050a1038131800070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 861321079 1250 861319829 861319831
    0xb100504090b19030602030a1b02010c14070c0e130f0308010314010908031b090409060b180103030c0b041e030504061202040503030406032d0b0f030c0102100f151d 72
    0x191003014692003d09100c00d296050800b035941054006031240e490313080580042110003d0300e02c05015a05c60002103590540202161300425903510b046090140c200004602a26200400c02e030500302042c069100b9000e0445d500c400e0781840c0003c4400585c407010010303120f010064001800710750060042c170412803002c1c000401e485c0f0081110440b0358944e41624007015121858001e120200c0441b40c000c1401a1640350380020810032041505240c07000081c194031703288600500b901c00d800d205060041c0c04441c101c036055150046608402d50381d2070010000203100700d6000040341030a86a5902440841d224207110b41c036040d41e41c03070404001400c0d0060300485408901d004100a0045440c044251801c903074141c280800d611f100030360588070481001412041c0002d0b40344080a5403603864000502d540c20903103900c3e851400e120149034503050219400c901503071001085079491f40c00c0d43e10507969101c0d05c10001901100c001c1040c0c41050041e40f0000301d181c0500e6071000e10084200c401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 861322329 1250 861321079 861321101
    0x4031709010906020309030c0108180106080328141e0d050f0903252604091107022101060807080a050c180103080a0512090a05060f15090405010b10050409 68
    0x151b0409581200290750758401e00c01d024100000c00c808900e81c100ea0404a80d82d43d16010300032b10287d40c680070055980c5c0c00040105111001205a201c0b03140410030418510401e50b9454104ac292a0205035a040d40006122400886490002c0884c41e00080c00340004a01044d004940760034490f164401c0c84101420007003440e0002c0140400c009075031000c0c1c80509202110070800141c1e01d0074606c50030000c0600844c20590080785043c04003454000810540d142400e041010700031540f4021824080e00f2402034011003802030381e88803400610a41005c00c40e000001145072030b2610b031282e007413907a103501194140c0c0c415041141040300601c1402500141901c4015400180710701d4003011031018440902120400150203191034495801c0b903000000c01c034a505e0090400c540c1081d950b0740c1c104030549a50003500c000c161546d642410050154101000c8100d00020810801010480261085489642c0c40d0701400864840f01685440b40041c0e8403920388480c40d0031a04001e13a0052035a07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 861323579 1250 861322329 861322333
    0x2b090b010b0c0717010905010e07080d031109010c05010e01060b090f090c040605030907031208090d0f200a060f0e0f07050d06180b012d1401140403170901090602 71
    0xb250b031680390000f81c10b208a070400c03d1196407640d049003055004261041000d80254244020044120400141c0004851080003103a02ca0584d9800480844540398155205102d08000d0006c0c6913208245080031580110000150513841110081c00c5400790f6100346003c04020034401c41519102c1940c2c44031040035200c0c0e0203545000c021040d10792185008050078000c02201140210740200001005140e00020903074a1817010344c0041c140490031070b5160110311500c135a0300c244034850301c02e6000214841c5c80b6041c40504481d047c42c04000e103d1000901d51045007040400318400e80184069100050000030380002c0460a0f10708081084684408690240f5010446a183e60071003a003000d41003c1300050180c0c46490000d07081c020072801801d988400e40003c03882c0184000d8007001c008410080c0c0354400041201c01e0031116144c441c0101d02900301410040f01e501603565004207036480703c02c00d441c050f02c1e41e462841070725017500a000307030240c0031502c5000c558118103040007038142400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 861324829 1250 861323579 861323587
    0xf150f060702010f090308070c030b0c09030703243902060f040f050124080c0109090e0c0a090c0806150306150d0908091c172b090b010b 60
    0x8003180d440e120300e0000a0400115058800c1014490315a40c0080d5a004116554901241c2414920750710180020f032441c540002c00719a040b071280c41100c0180e400500500361041c07960311010000032500002c2000300407501d00d000a070100301d10455403e080844004950459210340d07035100325800c02e81600501501c05100311440390001080c80c0d00041e00103103129250303035502d800c0c440001888030082043d03003003a05041c07180c1c40e03440301440001c215610301407485a5070101696240d06c2082c100b800301d255218284040c02d019008010104c1c1c14404403100f110302c0d68086102c011043d8400d400c181e40d501d450440c02035004981e141c120008850081e4490012480071415200207000c0303c2c8a80c0283d1480e041d40005542521403501c07244600b00300345490b80c00d203071141c0d510050040c0d02c42d04141c410451102000d000800b000c80d0401c0d02104032015840080c610303684594020709803601040804050b44110743c4031582202e64a03040888c603131416161944a220040c1c1003906841e100348 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 861326079 1250 861324829 861324859
    0x50c0405041e08070b0405370318080a080d0c02070f17070302030d030e010f050108030a08041a0c040914240103140108030703021005100312020c090f15 67
    0x50341c030340742d104001d0402800002d1a403030461550301c10200000e00c049400c0c4100f02c24002c0c003080e6480300050b4850b800702c85810080307609140c0c102155504032440c20801038034010902c00c1c7c403c1c000c0240400b040020170b6803180a45442d20400941c1241c1c416030001d10000054001c1c050040440f03100c2c0010014a170404501920703000e000e004824011905900403240032200300a454011600501501d03910f4031942c90040c05441c1400701a10341e0f60808020046008052103001d0485000201031402e000c0711060460303082e08090003d0f0780170380c10036076412001c0c8100c03004c1c28001c00d450520156107519044000c0c1c2918142d20032208104000b004010301515a1b48215501200345c4904403046180240103030000c0002c07155648108201c4070000c0f43d045400001030107403078040d400b11511400c52005981c00d451f400c07a4000c5400c460780030108002010180c55245c0343d407003070042d200c1c12111306010922450301190070810314408034044c803a10803850301c0c05a8403244160340d071303550500e580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 861327329 1250 861326079 861326093
    0x6110a0b060126091020071b090e06160201090b0705030919050705090f07120c0c061505040513020303030f10030c060509011205060f09151903050c040504 68
    0x7084241030005841c01d1070000000c05405009000080c404102c80d0305206a00c15641d4181245080d07840b40b0f020a107a501080c80102c41110219500c0418502080c5540d80e62028035841400d504d018880140801d1194060088014400d01103008140b10f240c00090b65011170200300356074003036900d00303620070011030481c03080e0302e610040070f00b04540e60703843c1c1d80301d140d28101c1000c4140c0d244d02103151040d410070802042100c02c40e8003c4a54140b56101c1060340615140140c540401260814800c0f0100d40e00f107403c8503400303581390700780110901e46039100d400c181c580d40c8040c2120452001401c0c0400e14041c07013050380003808031000c100c1c0006d1300c1e40429035030700c009080c80d03071400b8502001074840390000307041801550744032402180050b03a0300000303041d0ba08418441c41c04503003001d10488a901480c400c291052000411544249600e03405010a0403000b0b4424281c94489002c0034910352169450850311031200c809504c0c480745581000e905109810407409c1c803403402c0009010204c0c4078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 861328579 1250 861327329 861327331
    0x120e0303131b06080f0702060f0106120209060a2d021231080106080a230c0915010207050301021603200d09050102010c090305030a1404030c030c06110a0b 68
    0x56800c003204003020b41401494541030030250450110391040118040740c0c40b440035070103040003004000854a4050080c0d8079641c00f280c1b80c00301d120303100d001045418132810040010111040005150403140f4000c100e25500043c5400b0201301086010845405450031a01d041d50074203502d20300c2c203080108025202c3c420341d094032060f2540404d120028146165240c8024400300b07034113100070074101020041a40f050300c5120119481c081c000150f482011800d01380e00c5a0040b908007031005e0280c4822643d8051100351007861143c4052100181c540c0480b0300c1c0a000d50740c10441c0c00c05107800c00203141520715003010340240d0042c080049001103903c5041203143e81810005114020043d815000390341508000c41c0ca40304160b1480c1034180c00440d060140c50303080c0c1c002d100b803065814041d25805400d110040c01580104401d00585228000f400c120000d0300c18003a1800d56a910340030105082500180ca0341480507804000c1d0680041c4800c41b1600c00d00701030082e624440d00c2e40304103450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 861329829 1250 861328579 861328591
    0x5060606090402090d03020a020316150503090118030e030d0507020f04020c10020d0203010303080c0c0604080a0e062709011401030906110a0305011404020f03060409081216120e0303 80
    0x300852051841e6032241c040c0d580110002e41410700c1051030f0b080017580e5401c0c0800581c0240541044110700d0f0406161040581c0d00c2107041e41823604800c0001c407a9944010000b140c195a80d49102c80344036004008055140d02a0790b401c1800d014950030581030124040c550018484100701703490042e11603000c58441000c04070740040c1c41e00b0551200c94103003084d062071160341a1000981000400103580070310306803030180e607503444540d480c1c0d01d60044500c206000303110164454000500080c0142c0014142040c9510707249000481100104445030081c1c8454007010400e40380c45041e8070f200400c107010009080b0388180c281d5140071061715188ae0b000c111a4109601c0741403103401c0c8440340e08160a071150682040d62b5a00c1a13110045c010482801280c0e40c0c91003810204a03249860b0081c0c8201c0b1076012540b03455504c40c18200002000681d00c01c40740744009115841c040d201000340e40f0b20070000030408028260601c10000c10310710051428081e81c500d801c1400b00301120000649078096 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 861330935 1106 861329829 861329839
    0xe131e0308011404020c060f0604110d090b2211010224040b0105041a0909121b06010f0b030f0402010908070b1c0b0d0308040303061805040203100603050606 69
    0x200c1126021b0700958040400306100388031804000c0e8005400a000160f08071504100618070703001100c2c0c01c09016030300c4003600244504051000c2d481000c2e50002002d028000310540d550081071800038040b52000301039000aa4001c01c01c40318428114802450380c060805041c084281d000ca80440308041c200000044604080c01804040904240c182a451404c00144161000300804000103407281024a02068803010020300d01c000c40308070007114046d50811460300e001c6c0181d018000c0c04000074420401c0b03801507010342e900f2040403000e00c051910341d400101c0b07000b0101d1b000001540100c407800035801e40124010000850100b805011107040440c40d08122031511144a4000075907910030300029100711610f0b5403103446803c00052807a1115415942c0043c80c0c08000401c0341c0d0740c3c05200030752400300140038218007011028807000d411580d400b070300c03003002400703040c064 = true := by decide +kernel

theorem cover : BRFrame.Cov 861151079 861330935 := by
  have h0 := BRFrame.cov_init 861151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 861151079 ≤ n) (h2 : n < 861330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
