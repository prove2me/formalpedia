-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3960
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:38.989631+00:00
-- url     : https://prove2.me/submissions/f1811d29-7d83-4bdf-8f04-49060571c172

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712050359 ≤ n < 712230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712051609 1250 712050359 712050397
    0x72d032001180602090102071a0711030616033308011505011e030603050f1f05010303020d0809030c0106170c040507090506070203330106020f0601060807030f090305 73
    0xc140201c0c8203000d04016000c008000755154500203401618505045004018000900c000e400d010b214460890b002d565a03240890300e498048143c0c280c2007180a5044101000649501c14000003e240200e003004a88841070004003002d581c3d011010030301400010b4a030602c002481160f2600b9501103c1c02007102340310300030070348219a155104503400650503c040348410f83c42c0340300c000e402402030704000c01c010b500c075502c060810500080a00c43e40d400314800300d500100e200212021601ca040e020849035045d502e000751504004000c14060180080100e903500404104480320400c1100082112310346903c0d041512080701340c60002103115038613500000f45008e10840b40140916290070100d98605000d001954114038400d9034075001d40c0d1b66150709a05883c0003820b140060030450040c842ca8010003401683d010b8002d0011544040840051188006040c5040d5001c40c00c05040c01e07610140d00310f01a08030303400180c0b032907410310103200c0415410a01610400d0b082110308521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712052859 1250 712051609 712051667
    0x9070518040c0303031d0106060201150609051302160803010602010606112b0909050a05010608090604080703140435030a0c080c010b090f060310060308072d03 70
    0x2400350036140a40b412940c0a0204000b9003e540701c1080c150044c042c464200c0e02102880d801c4174442d03409103000d03035140d1500c1c4000c800c034450f0382c00280c1040d040a4401c54101004030312180c0451002c0d2100e00c1e400122103a80303451200d41e00320069840141c00b90340e0b60711208004d001e041b01d0f21070b240100300c5030250781c42440004581040c5d1000c0c2c0d1012030482d621401100d14240400140440c1400485013010a2405150181a2007040545400320b00e952500b81c00400441d0014030041840c0c111006200000d000c88007100d080a805151428040d50030890101e0184620350045901e5a000c07030326681c1006d103214100148800416040200c0404038460070348a02c1410389000c0000d13244446200000d901c4000b42002c84110750001520700f914001194183c18155500c4014884e100108841850108913400320040010001d019107803550351031728258040d500c0001c0022404482c5050344d004140524207000c80c80d050b0920070303503070745040c0a4028000d07041820311900d05441e010b10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712054109 1250 712052859 712052899
    0x30c08120304080723070b03090606010215010905100f030f150b01020706080901060b0309060a0b1e2205130c0503010b01090b0c07080d050414010c0312150905090705 73
    0x71040b5040116980380005954806884105c0f840314041c40c58262400c0721307800c1d102001084003520380010110f03aa0f003010444a8a04000142103504642c44100d25002d0345442c42d1031681191800b50006c079154603400640704442c1042d80040107480a484000801d015008e00400302c102d001d022031101480034078074041c0503204012140d6026070f00000c800c0280a120740c21642c0e020b103546000250f820307101e440e05081a130040c1c4031000117602601c140107008210348a03074004007004550a190701c0070507441380c80c0c00c0308807568035a2151a410b40b40b800c101e04816496506015460b90821180c946080c005000410034681502c011184032004109030805200c2d010074010140c503480d41e03083c5003122004a56020000c0400140904040043e404104019510170684503840c0c117915941030850850250f003081e4031150411140c0c4541c000401d0b0411170400f90940b4100d80403d030341c3c4034014460b11008442d0700c488025403400040041c1c01e9408502c4c1c0b02501d0044a25580140e05022055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712055359 1250 712054109 712054111
    0xd0602040e1e130501020706090b0610050c1c0c02090405101113090e07030c0b03010e1e0103080c070807032111100903210e1015090b0105040b04030c081203 69
    0xa04260303004002c50603c1007101c083d420558407640c0003520380039280e5508070981389000740895031425954148205403a000ca440810040c01d8680b0a04140c800307581980e45840180c0c02c0c50b0041d40380b03096034004e184506014040aa009403454175141454904161f032000c0060182c6d040618180207041032031064402ca0340c3d103030380c0300ca0300d0f180d56818045200004d00c07030100170b0606881802c10000c0084c0c0450f102d84010074029800340c3d1250314240e0b20b0300e14098010011031030215036502080a9500482e802c5066a8201b06816282c62035000c29074030340750481e0801169407241c0d81c1d0010030407146904149558210301c0225100d60001d41d4190f03602002e02d00c03041441d810245844841a9256100004083c040e1170700702c0720440d00c10070502002031280c02c03107102540c446040c40c1c54800104050072842100050800080e20103881d81010a64540905e902d001c0c0c50398141c0f51aa0b100d1030a48020740102103803c2c0d43c4a03603901e01161040c20718441d0343c0c0d407402140705010560342d40e40113036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712056609 1250 712055359 712055401
    0xf0b06070209070918020306032803120e100b0a080c03030a0e040615030f140c120c09030322050d0305070204050a0e0105130605130c03080a0e0d0602040e 68
    0x9141051095801c011042c0c0c1c0c02001c50041041c032001c00910119010440714001c07035010380040e52814500103050078540142d00030705545003070b240a45079880c0300c455040b032800d4061030f240c00701c142d032421071001030700c008042030800740f0540784c28010703002080e404420310500885425184c40e40d45c2810945a81c01070a0850b4990000e110445556004020b10301d802b4400030800070f00305468030b41156108145180d48800a60b0751400703d00d41a4947c0300f040c0e5800c0381d03055400d00d0f510b82807000740c2c46485030341009014145c3c0c01e80410600400001136580b147d0004040da80c9480c008081c5020055034402c251400c0c0b100c42130001524245000d0220390142c16503070382441e0250507003e01010703110103032249520f80d99600002003003000a204044c007400d00483d00111022031401c00909442c009052000c8402858101c600090200d022a0040b0380d4445407080c0c5540090790192034000340c00500b150000c026803106070400005a0040c0241d480410000100e601e4031a07000c06001051840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712057859 1250 712056609 712056619
    0x1e1501090e0d0513091a011d0616020406090e0c0109061d1e04050403050d060824131713090507020c01030b0d0c120218040b150607050d0906030f0b 65
    0xb0414810f01c108010264a0740d00c40c9540b54182c0da460004040310380c2c44100600f42c4000349040980c035a48641340b00790030345003a91840400c1104400180306d034030038484d0b108900d8207401c0e5244115199500010300a0082c80c80c1003000340c029299058861031040e1074180025514000800c3c00d501400398131820207403424286d148051040103209603103901c2507c52008840300b000400907035840c1d02489109500c6a6141c0b0344940900344001f05403011904404981c0d04001441680d0412403901e066419400f031200c030800780c0302c4029160b600100140080d2484594401c429403c0c81490700404162545480b10455140d0b501c40240495070191008001600440c130501c43c2c80d80b00e40c01c801d140d10001041001700405698643c01101c0560b407101c41a409440000b400350301c1c010200344050402d8020082c114903040d40c80c6243c1520041c81c803094a014400e071340315151154400d4a4081c2c3d8803404489958041100c05031806480b807103503100081c03c2281900480d6164041c2800120014003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712059109 1250 712057859 712057873
    0xf0d080408030402012a03021204061b080c03040b120f0408030612100608010617010204120609050a02060d1a01050901022d0a0f0c0e0f13051e1501090e 67
    0x240709241ea6002400980c104a9418240c2c0c5011140310b8400c1130000709811402c0c20100d0920307000c0d00f03089031042e299441d00414001040a07a4000064400c2220000c500307894802c1c507450b10030058010392403421b0703191002003030204a500d050700007407801d1050260700320b00d01d07500c1c54482c002990003202c0082c041c401c2480883c045091020400400d07241d9101607030014035240c02c2e2181281c0d20b031b510215a980d10341d1006c104041c10320081c00308400e9580c2c003c0d890703e403c0003010241d60703500d003100512280c0d4440b610310134420240801a41070f5802007102d941c80d105040305d10b02034410012a90b404c0c4c070011601c0356042d0b0059046684500041c0c002d40803040e10000c20394a289141d101e015080c80400c2c010a050b998103121255034940300d80f6a8210710142810040314124040d04001d030101e542d9018004181000303800c180d8040040000f00d0600c0c00c480c03803d40c1c02c207400810500358440c21650321180144002c40e21903011050300e054901160382e118848003e81d4041c0b1400009504504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712060359 1250 712059109 712059113
    0x12060a050f0d03030e0d1205091b100e0904030302030f0a0911060d0b13060e010b040605040b25110f03030304080904051f0618080c01020c060a110f01060501020f0d0804 74
    0x3648000c1c040c0c02801c0000c0d151709100c00e011300f80f101c2ca2802c00001000000c0460f00d1500d00c1c40707610341003200000100240c0c02c5040d03124028180b4651268130420705d0510f410320240c482d80c840c07000200058400809820b1134500038010750801c0c2c4100a4600002c000150040c0c00c902c2140380c0e55410281011040c4580000c0c00129030080b00100c0c15951101c0c0c8280740354448020340e0080c0d13000d41d03d00140b0301d8603001082e072000206070090a9040c00c00c00c0100301311a440000d0381c0980c0c0c5050902503a032408140c41994881d1400b488143c0002c460240d8428042581c035075000210b41034800c810b4070720841d400c242d141d100440303000b031501d2010701c40d50382c0c542490752080e41d01000b6060003500c5090b4500d10b100a241da03541c8074100250018039070b00d21a400250703105000b05100d1000380641c0c010b50300040e48942d03102c1d508a001d100c010460301041841404500c550400300c8007a0b824041902d4000c1d030182c000f0340a2117002d131142d01800c1802100010300d40c6228400b9545080e00c58440d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712061609 1250 712060359 712060369
    0x6020c0f1314010e041b0b0a050f1b0c040f09020108010308070302010b090f04050706050a081b0f04080708070605040305101a0a0e0403090b0c1e010e03070812060a050f 74
    0x40801104440e5542c03021407a011103112807207010b4240c90040f00800d00d490302c1c0c0303070400390a143c0f003c80824110758000c1001111a205441b4140010704041ea100c10020000380d449018598002449002e0305280060317030080441d802040240564050003034541540c1c40e0415201c02520003800074065074010000f2980b03050251103400d21901c00410410200000100b421906481403040d40b20107006000030050100501002009242082814112500000b5040010080420005c001d400c0b03d481d1450384050200c03000074103668161500c5036103904450340d0314216402084007034481d400c1301198240c001c0c0191022a5804001030200c01c1100e00a2000740290411901c000c0c8510f42e40020140d070365011020140103250307040f154030324080c100240070000740d51011003a14000c03c1149800400440c4240c68014031500c0004003200c0d1181c001d0042500101c4482603020101c0d10300d080101c920000d11580c0848a008100c90b210070041100131384c180c0c400c1d5079000c40e02c00020300180c200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712062859 1250 712061609 712061629
    0x302090a05060705030c06100e0906061e0409050f010e0f0601140d060f0912030b0907050409110c01051e0a110d090819020601061103070b04081b030d1506020c0f 71
    0x1007401038030b00b007411b8261010b2500c8003c0d5500764a081000304241b00d40161041156400308040b0700401d60341c1044800b04034144c84081184054510000400a541e00d1715000b80c00c0745a4004c04481082412802d014001c241200840b080fa0196150b00074bd06107000030928180d078400c800750180250404100f01e40008500012503901d6111340751003912490030700c50310006502510682a44280c514401411102c810030520720ae50f403c28184002c1d254440c2c1520182c9410840019640b82090414110750003909810303440780d82000104040031051001c150b4114030320b0403802d0040d480340b600340d100741d4200041c1c0c401280400d00a9010610083c0c110040c2107029440061401320380c90f030b06030300f14140c1009020240e44424010005a648030b0080030000440101440c100001681e90345e4035001c000d03001412a01000c51440b1400e80210030740381201c3c00a00c11030741d07501984400314002e8030031503c00c17100030707550510001035013400420780105c4080002c0924010304450010040b45101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712064109 1250 712062859 712062863
    0x91f110f0c151e160c1104111c05090a0f060c0c050f07031104060f2607120c050105211b0408061512060a050403020a230106060302090a050607 63
    0xb103a080203210214003203801c2030240b507480c3c01100410011452001c8038900251404445920a03044000d406a11001000800d940140622585030070b840c0006c002e007101c00c1004120040c00500102030790303a070b28080401540070610902807962440000c0381c880845810290800f00c1100300d5400142c0c00b9032041854580070308100e100000c9580b00d83c0e1819014000c112491391001314140180810b0b0b00c002d400d01c0c1c1044400f03100321824034011803400c0100384904c42106c00c1c000e02c5404d110004280c0c2d008125015404c0380d451598031b2687e405074607600355080c4d8040c00303203e80100da01d5214008a404200ca40c40348004e03414820602109a040c00805800c6015600030031044400341c42c0008000410b008001054541032606103082504a0b0071040c5114210010300000c0d900008600b4943c4880702c20b00c0018160b0310303400d059042422811000b0691685802c107a480034605138151040140c461008205c019202c070344c15422486652000c507488441c0c03030820402440d1400c0240f820b64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712065359 1250 712064109 712064113
    0x30c09031609020c0f16051909020f071208150118050a0609081209030a29040f1109071e030212150118031226091f110f0c 54
    0x1041a080028450a40c00c5450b1241d0009403c91400301d007009185c1c04040c2e048050006202d059502c07011030a03943c4103c40c018003c0329080000501440c680c42c2c001c264010042d59100000c440d101c0c0a540b0140c02200c424850f80100402c1070311038980c3c544a42d41040600c0c5040ca040d100541c1c0c07000e12401c18442e105108080801d994958810300380003014145c42e00305856007460710190803c00e11071400d0b9008081800000c0c03080d80d0000c2c8000400d5003002003c80900b00308074020f01310010022030640c8082d240ca0922080003802400740c44920b000d054544103c0381ca560411451100698022001401001640c540e600e200f01c020b1040c055982401450f06a08400d9140d12000403901d034880e030000100440415608480aa0f030341042c062a10083c043c1180c0e00d0001243d1034130080410450800906500e000010048030381110481c05118202c0c5080d1300c1d0183d44020030b0900200d5a0030780115041040c140380103003141031801c1c0c050306050101074040701026811a1040782514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712066609 1250 712065359 712065373
    0x206090309010c0b0a1b03020315240319020f0d11090307090c0513121103070f060e1513050a23040207020f120304091401141509281a030c0903 63
    0x1041c441b011680d001c0f0044e40700581c480c500760340d003d120b6964055205005003211070b0300c103980508814480800c150303045180da03120f0f00c60901c0892950310900507040040e1000a0548a501e4140041c0c8418a50b0034810f000c110f11040032421b060080490880d0141d000c0300741801400b07a243c2020040031a43d10f042800e2940c5201442c8000c403050f401240300c0300b1905081c805002500089512061040e0000d01403549400f80700340c01c1c1a201c2c401c2c0701c1089920510840075564140c0b00f40400c0390000d000d5074680b0f8801d8a80b60010200744222445000c00300c000280c00c2c1e840d501ca40217040030034a03580c1540d1344040c0502001e0b6100c0c2004a90000354404e244001d99103044051004d0303050700c1c2c02180c41d0f0341840b83c83c104403074441140841c06980d8800411103070380c00d00c03405002141c00b43c601070b842c003400000c00160740c0102d011480d40320b4180a0001031a9401c2c02c8481c0050000c004105901652607040440314030009403200394954003003000840c0d80710240000e00da1100c0144c201ca0305c0e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712067859 1250 712066609 712066631
    0x2070519050d080a290307050906010c1202070e010905070e010e031906090605010602030a02060606070b0105012001110a0e1203030103031b061107050d09060203030a0905190309060206090309010c0b0a 88
    0x1406014900c100c0542e10303140f20305c2003581020401c1070301402054950351403a04140001070080c2e821100004e112242d20001400810700c00e12202008003a400c164400d956141c6040e8400b408003101d1840004980100d00c1416600c210344291800c540a00039100c0f0901038800b41d83c044040f9030090340c0c2140c5560079140080c3d09480307150700906c0345034095916a403d0b100000d003451070207400a40f0851051040e071002c02c02c44a819411201d00342404207114000303d40210202042a040400365480c01188000403d0644000c0030340100a5035850039403282c0e00c1c200000740c0c203034404070703551a031040c0010300020380103600085d000342c3d00d41a00c505022040d42c9440c1542c10742d03054200400b5000c20030301e04003c0108140319182e401818607294541c00c10b40029604e000040032080b9240e03d4451100901c54203100c0c03030543c030050400f030405c03401c081d00740685442c1d030398402d80005106860020301c8502012040d41c0e00307150146d44691782c485641c3c554011001010384045070302503a60300c1e440e034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712069109 1250 712067859 712067891
    0x60403120302040e010b070c053d0e04091a041509050c04050f090607050a260612060108070b2b0f05011d162102070519050d080a 57
    0xc4450350350700503a880f07040c01400c2c8500c1d401a40f01021007801803080c0000a40561030481c00d03030f54180e9030034030071960140b0050900c445100e0300140b90106181d00355803107403854510505400581d00e40d40706d013100002c144821034080701c0001d08040a41c43c0355503010300d02403100343e40103405580c4548103000315041c0340f41243d070032101c00c580070751080c1c441540304d0030a405581d900c01100740c03100050b464011115611a50001c05100401c40002a10b280304c5000e10310b048a1880141d0640000060220314240040301c03d94840d03214850007180443c6800300000c9113416102100c002c0c120315407610131000040c0e00014110504c903e4040035a00203120708400080307982440d100301040040e13840c803040040750010b070042100240b400c04c0c0d05a80d041c69482c10713a00505030490700d81550305640811100825000314000840d41c6a00d081c05a0507100c0d00540812401203007581d917104444001e00c0c0156041410060068103c8840c0c44941d40c05500070075442001b68001040d10555084248 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712070359 1250 712069109 712069133
    0xf010c1e020604170601060c030c1b1a040302040f0506030d18090c02011d03090f01050708070501090b04140105010509010510030f020c0706020105090a08090d0f050d030902031507090b09060403 85
    0x740e820702e002590304e602c018108510b0340181600d007803585401803a52801408444001c0300508191a406590408004499019030040c001000da503689401103200b4152568002d2000723901c164246a03c040005480b4031441d4005d1000800510402000000a50712a45561751503484603030b650400080400a0340180c410499403a400021a822451008248143c0100600e0070591041c081d490306502c1e5403c0040081c402403d04c141c80c0e80c61881c101c4160311900740010415401c101c03082c2c0400008554542c0694443c103603101504ad135118115088540c05d01c5020f900060140040000382410b200c4542400154600800c04021504046040c0da0003141148215030003483c0804c00d855081c81140c0d00045001c01400351076400780c41c2c2e04c201e8010313440c002e03100e00c4400000c0000c12410b030f40c8501c1e5942d80a8140d80b60310b0210721000d0010720905200f07031f010380141129040f0f080b03000c104940c811243d40d110b01420605110b12601550450200e0070b8204604000c04030100303618410103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712071609 1250 712070359 712070369
    0x10f150311041203020f060c09010c0c15050301170a150903260618010e0a1e050705030a0605040c0f26040b1f03080f13030212010e0c0f010c1e020604 66
    0x10350541c40b00e611300289400702004211b0001e4104c1001d0082810700300f000c0700d00e41e00c000d203000c3c3d8640788141810320001034203601ca5608502600301c3c8505068000000e14101d91003246080d00c007903588030304140c44644a060082c0788801e480aa60f001103195405150707000e000f0300d000c50288403102909030f4000002d01c1c45074100000302080060502d0100401c91940040b4940c4281b99407401c26094201ea0b005481128036584895243e00360b400ba05540a0f181c1100350340a000c0c500f45030502801a038810f58031039500b5403c10b240451035042c03501944071004440d81d500402210000001c0700c580c00c1d000b58164004401110030000a000320302c0c12409a1b0041141c0e4000d420907007440c842041d180c82c0b0720f40d03403995524400c00c04180f4000c10ba40c0c2c80e010015500d03548042d082039010108405403c020b50240741f401c0d1804a45034154825059020901c040740e1400030b148040095000c0b002c0d00d4140042c5000e030b140e0000034000c0000401e140b00c08e0b0265640807986500140280c1c12135003007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712072859 1250 712071609 712071629
    0x41d0d110d0903051e0115060302031005060a05090108101211030606030a0f24241a2203080c0303070f14041e0b0a0509040b09010f15031104 62
    0x162181550103000403a01041c207400c118002d01c1c51903a6103a19040b81c078910a2050750b5580c0c03200b80c0c220085d00580d09011f0301010f80742041d9111a0060300030340040c3c6404071002c0c0c00c0d060100c4d4600744a000c8030111907241d1030311410140900300440d08440c004000381000078802200040c12030320400c1303d50405118081c1c01c051800394000b814a04040146803d100c0e07841b65000c0000726107094004000c2e02d070400e050001c3c15848496401002e0703040d840740000245094480d201d60001c54640001074201100704c03030010395a0b2408080700364906445410703160006c0040540014051401125101403040c420701510303074039140e01006421070503003904d10340c00020410000644c001c602c3d00881c4191300b08107105480c00e8110440c1400349004100f882c003a051664106202e0480300318002f0a24491b109a0312279034224001e0141e044602c88900440c01c02e4811051072803c0c2c2d844034140c03490001201c181900c0c1140400c00b040040d2941c0c0c081c55a074178008001d0004500041024140044d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712074109 1250 712072859 712072877
    0x40b240402031003140304050603271902100f0203040b090109030602030403090e0c18090403030b0a030606140307031703070c0c03050109110303070201092904082d0c041d0d 76
    0xc1085c200e0041001c1c0c07010381e0f0010007050080d40d4408081e6500710140c44402c143c600e681001203408404c010401d881170b0301c20f01d006203d4500f0060412420903100b9154501c0d0700510103016260140c07508840400760308248424442803014802428112205140c910001d55482d03d5840880e401502c054002a0a40300113110344003600301c0094006842188551400c003582e5090050000e40040383c911801040000c40c0a00d44a900080382c01c9038002d00c1c559003942d03079181c1303080100800d10031a0300c04400c0300984441d5280c04546841100c8e0084c5443c4404030428a40071607d0344020040424001c1c980c40d100003140e000b0140002541c80f80000040602403400c0c490010441c056007540710341e1007000b0b50300050b41d006d00c00c0c100b00d92903520340d03500c40c0e0b1400d282514a050340c845621b84c0c0300d0b00403400050704400080c6481d0900b04c00b2100c0b031041c1301300808144002483e41600c1031380d41e000c21044150350810f175104280c1244501c0c5c0141020101520280c203022107071801400140d0f03125 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712075359 1250 712074109 712074113
    0x190f0f09120504080c0d0f060212060a29071e05030408100506010518030f0a0506100614041503020913050a0f0b030a0b090307020d1a0906040b240402031003 69
    0xc125411180603400c0503400c0c0f5141903001507448040980d40c0340600d442c060344104104a0145005096612038070a40d11240040403440360007030100c3d510380c0b050b0752003400028403060308510400c40e10383c0d0401181d00d1211681d02300450783d00003070046a00c3c6013681000708500180c200368503600d40c86180a541d5031840c01484620b40421444442c00b41c9180c5018840c50303a812008a07a45003039003205074425410403e0000741040d518440d000342e1409101c140c1010004007054040c031a85821440c0b80c0c580c0d464801c104c800c40656100112a00320810080c400402000b8110780303849400c1c500503240c9040e0360082010080b40100b415000c544800078845210401d001d01401e00581c242e003000501018000030307581ea0038044001d004c105102d40031400510080c001c07a44081d0b0041c100c129852903514012111210000a00c2c2d03500d90301c540462608540400c2076405660444c0002102c8e80b00c60072920001c8594114150220301c0040c50280140c0b924005035201c0c210003100310300310368654 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712076609 1250 712075359 712075373
    0x30801030c0603110405042f120a02030c030f2a0304120309120e040f061d010e1302090601022103060f04020f0a05030621011b0c0308190f0f09 63
    0x50340200040c1804c0001245000c940301d03060758100c03401140c0c0400c5183d1421300283e0302c1d510340100d000031520303081c40b82245000e04000510038084100003c00003982c40350203a108070f020581ea480030072030081000c41d50b0b0010003030b0380e10740102d0042c1e983c1803561031000d100c0d20420a41c0c18070140c21a00401080103014100b280056181000d040a00c2481201d07035030201c1c01f00c0c8403503450080c002c103000c107405561510350107000350100c04001004015110380d00f10303818000348002c00e031804544d0400400c1902d1011411801280d966580900312602c9070f003000301c4654010900c904500c00c0d000b104501d0080c00c40c2c17034154070200a0b041d5590342400b00134081045030780c3c50040d0059004025107182d01d1440400c489490200f07242c0035031291a80f81c0010400103220002140009648420030301449040d4440f030080080300d040309001d0041840c041d9a201d081c090f01801051111000505188803004e15a44142c84c0000c0001c40d44440503100c0100c6010040600c070013562020700d203080081c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712077859 1250 712076609 712076633
    0x70306080606030c10030e0313090507052701050f071208010501020a232d070504060302061603032301080c0102070f1802090a03050a0c05150d0e0f070303080103 71
    0x40001a0100d0b1500c0c8002c6980c9030141200704c0d00582c00c0102000c20340c1c1c425444880d9242e00c05040d65582d0b42004840321684400780140d215907450003000c103c0050048088403040e070301010604101d440c444008080d401c0c001c040c041c0c140300d4200000c00d200d0300700c10010440315100d0810100602c220800041000b001608514103642c4010501c3c000b08440c1c00202511026110680621581c20312855003004002c040e003044031a14424030f001c1c1040c10a02640b000a6030400700c9000c01c0e074400812055402d0307480041e400890402801d003413401c90000c030220050003030038041221002d14850794905068180058814007440d4010700698105101c0900410307000d1006100711340c20078071080c03041b1599208180c030803206000c10007840d101d6a0192000c102008241c004c4651b500e040041d00c4229a05d0101c4808620403000b0038107192400d4021284802e00e40c1107428215004c0783c40c002040c81c02c07400e4919110709074541488100412180b006184640e4641c46654514980301501d410707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712079109 1250 712077859 712077869
    0x60603020301060c1e2301050f0106050405040504020a0e10142e09091406041518020d0e121213020d030e0607140304060905030a020609191805070306 66
    0x40100010451298403012184c85150000d0391100c03000b51031031440f00084070241004101c0b40c1c0300c0b10801c09410040c0d520408003880d800090000d40d944003003a554545c1d003405080301181c4280004d0096080c158041c50b03100344013502c11040603440c1c01d9a81140541140c4003180c240d001e00081c841c2c4450040c14111800342624908100041c000740301c3c0c0404207005849508211900c00454080d110300c48403401020000400c00101c3c1080c0020b4420303201c1155100e000703904146407072020003103980c1c4072002c881000a2955004d2110000701c8041c0d0700c6951100c80081e15217074640719410084c0642c034426144d940c10350703a544015036035021b803031a0300801003550004404240d201680340c1c0809400c185900d07103048514040e4150014005000c1c0e4000504484c04941502e038070400c00000a2003a1a4186c035409100ba5980080680c2c0344d607000d0009412800c03d00040d41a418a1002603052500581624010320384440e03401c3d140340c5072100d00d2000e1035121014444419018450303c00540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712080359 1250 712079109 712079111
    0x50f090909011d07050f0d0206040b0a080403111f0e030d060f060e090411090406091217132307030816231519060e0f0c13090207030509060a050d060603 67
    0xa10b0200003400380c411b01c2003c5800f4078004600ca13000c5594440884024101d00800760f520303004401d50041a41c40102c401318045609025104000c420004100d40401658091007403549070b8a4a0317500908500e00d02c0e0075003440203000181c03014445010310b0018000d114a000c0c4443d2401600a05144000401038025240101400080348401c0240703100b0020a4402c09040d461742d18240340140b40c45000030700502040c01a04000d194441c404402030100b1102c0c00e03240d5102c001264203003181c558001030051040341506405042110b607151080c500071004e03200f0060352501c404c040c43e8410721150080354400c207800e004201d1843c1c08003100c00a1405c00c0b2003000603500c07010b036481a0703c46c030080c5030890403000640b24640c200481d000c90b8024440504c0750790b594606450150710103440c01c0355044910300000d440080b2200a8a50544000044c1d1090360301d0082c0038802580480c7c01502000703030803c00c00984d034844600a0041e1207aa6603540c2c0e58a1040c1d52240c2120400e4000360302b01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712081609 1250 712080359 712080373
    0x8040512032403071a030603060603120406030902060705060106120501080c0d031d130605030c040b0d0803100f06050705152a0c011a1c0302070303050f090909011d 72
    0x40001202c4044481200a051010501d4502c0081c3c94094581d0040c640301107102d100c0c4c00706180c40b10240d40130b51801c4d0b08450b03e50319400105510740000e20001002d0410610041040038401d400c84101e07a8000fa020320b2400c00a82c48841c2800000d070800000305444422180c002013940c4100d600500340340000d021000704e20780001c1c0494100c0b00002e8104402d4409069109100c1c00b48400300c49401002c00300701603130421520b805000c59106841c8a0f0203001101c251600302402803c03030420000740944203000081d0b44104982d00b000d0000d038414001e02902045410815100d18040d105a8942030b40314041c92402c103141081c05101d00d500d200341d4001344030840348011190001409022590041c44e007280e4040b0303902c1d0140b00d00d4201d0365800e121919103019086801005400c1060340c0c0c1800541a945040319120300411000b001a4001d80d000c0010074450800344c480c06490500491821005c40c0000c0c0d80e260041c0c40300300c1965921229100010101340036288204060b201030010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712082859 1250 712081609 712081621
    0xb1503070b04080604080d0e0d0206010f0b03040b0f070c05070801140a0911040b1306090617030403050d031d1c030f0b010c1205040b040906030c0608090a02010f1e0804051203 77
    0x1035840c0a0001048802c0215607440c2100b050382288e00035005240494030311214088000350b40e92001e20801c1406804118040b07940d90000040780d120700d410048a01c51520340150400c45004c00522001c10000380c0000200015810300c0b6407001800c40314004100900c00c08211038152001502082c03001e454160f0602c000792103a001c2070010720301102c00240703a07060320010404210740c00070545201480d0180224801d8540d0303001c0c0c0c0c103403010041c0d151740304441428955981d1249000162080d0301100f512110342d807094005040e0502d09464150020420702013080c580718020303020000c01b03800c0c40d030043d940030740c940b081c0040458030000902c0190807820010b805908128009003000300c800b036642902c1806041124004c1c2107400702d01d541d491307813242040000c101901080318211444100003030b0140c468101a4011109203014102c10340c550340c0190b422400044492040c1310b00c400c039013041d0036000f9115100005c0a5121300c1c5440c0b0303152821909007403080d5203500e4003841c14018851 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712084109 1250 712082859 712082863
    0x70b0c060124230f07030302120c131a0f0a05030411040203151915020a03020d0f0e0d231006050d0308010501050d020c0106090606020f060c1909030b1503070b0408 72
    0x100740d012480100b41c241c2c00c0000140a18410140d241c202c41d0701c00200c040405905070b0013010784120702d4000d40420f44662b51411264131070410514454000b450062000120a070141d03241d001e80c280c1090302e41601200f403011650440130745031020a40210801c424400a010001031101d0210750842c0f42d498010a08507500c140d00900c80d01460709003003030007040d05054103060090881107600718013284a4200081d950301c04043e080340180100001c0340c10060044001c0140445145c4841d05c3c00c8800c1000d21400715038500c8161644144040030180d82e06035074041004451094000d49514803810071504c0694032a50300050203500703c0c07082c610200c1c0e0f010541034103540302460070940ea0240c80003143c0180c0640c40000d2159481e00e035000401014a50200c070464403242c081d0f85020180c08919034440300c02b100d1b00795001504104020480c40d161454072122006424a107e01030b4881d02d54030781d0000c085450702c101070180c03540d0011610381042070354001c01c00110000d140078102140e5035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712085359 1250 712084109 712084127
    0x218040b100c0516090507120204030305160f0b1501110c0303181315030204061e150c08040e04020f060307020c011b15060608010501090b1803070b0c060124 69
    0x1010403812012000400900b40281004c1000070540300045945420500004100582d071752000f1801c1c05000318030031440da00070b580840e40c02d030f144e440c1004046204481310084c460411501074401419000006048030300540c000c0001d0980c0c08100341c0510005040d20341c80c904444004d5128042800d01d642e8004215655201d041140903400d00c03845020821180701c01720301501050904140d500ea480c00c180011701102d008580910070182c0d40c3e0700c00070104102e040d00c0c0c3c1400d1444041404074007031041d10841d00380c00c1031400300301c9030520352100f880eaa0841c1d0008083c004e000c074240010340c50204081c03071560f0b000700c178014614103001002075a03403504000c82505014582d00c1c1d00203080841d031126039209400603e5542c1180e400c086100090100780180400b2904e00c3c000480d195100d052100161800b0718583e510705503298084800000ba5401429498030401e03102048060082004e0042990804010941541000c2c0342e210a02c809002d000719410b46040c80012842d4007403401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712086609 1250 712085359 712085389
    0x803041e05030304180b09010e041101021c1815020a030c11040507020109031205010623040b0a050c0d0c08190c2405090604080a050309030c07090218040b 68
    0x1120030818a0820406149a56110395454000441c1c001440c0717406110341003034480d1000003084201c4450f4104103851a0a0040c2c14807000f140c800039000401d05020201174175414011214413001022942441c01040140d0b24000303400ca0406807103500201004001030201c0c0c2c12940307115000d21500950328088074a01074108402e201c195418811075a030b03880342d2254050300c1401145803c3c50081d0203407802400840005580da0b150303010700c0c41d95116a45c180e800b103a45107414801ba81c00c007e115024402c1c56000d00400400000450300720000081810f04055111981c880c003102c1c00b55818031030502c2590040c810b51144032000551170381d044960070a0040c024020a07818050226070740c0c0080c000003003c000c0c100741e03520840c45001c1c0c14001014a8030708140a940d480755145600c503407007a10022f040f00d0f02440a806051f00440c0516400f034406800c890500ca190b40910346840300070351081c01c0d40da42c00504000181c0115275441d1760710209490030310081030f490380442c4444213200c101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712087859 1250 712086609 712086629
    0x50306161407060f15050f031606051804090c1a1e07080c10020d0612050a0f020d0c2402011806020309010b04110405090123041d0307140610080304 65
    0x1c01c0041140c19400140048041c030020042c5548200f124417001a260041d14410703d01180b1929480ca400900808000250014030440340d207010020340741604210b0b1702c506001800d204142070394a842c0f04401c6500c0c081c031824040213140110200340c80c005003d6180030060f080012040c603040e0b4004044101c000d103248183d884049040403d07042c003901d0102109401807405090052000d9006889a25040c140400c00c0341d0f510f03138202c180711810381001442a040281484040b81841401840c0140003501c11590b07002c15035201001100180c2240c5080c4500784400e5070780c20443e558031500e54025000800c074044072400340c1141092909401080d080c0c000001404024080d040019584406801400810b403004030029a035001070003400c3c010808000001120855607a0381000050088400e01c2803000e14010321000e8140c02c0c40c2c24410494140756084a1441000103140040c000d0403040184441e24000a08012002d4440307142000581c6e0180f06854022048408441d0306080d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712089109 1250 712087859 712087867
    0xc03070c0312140f15060a12020702031606050d0c03180b070e03010c170a0b06040e09030702090406091b051008060a0f06092918010c0c06090503061614 67
    0x24241c000f4000031501280c03904070210a0144902c04110190700407034a40c000c1c80440600541400201c0c0241607110b000961201c07208101c01c02d507640106881ca0020701500c00300c4116024071075000780306c0e9120500150000841c14071484941c0301d0102001036600d8180801c040e14800b03100f640390b0062002e005410307417101285019003e400200900c078805002403020740ca9100c005440207140124080c1d5181002d400240460030b648141c0c680550014041c5040c181407030022007581030014200c0301144401c20440780560390300360b140e901c602e2045001141c0c3e2030703403031401099118203410311900d240795006062056903100c0c41034650181003494140010382c2d6980014581052990240d80701c01e034605004228a1762003000c10094812402c1c00003180d98a0086c4200b6070310b80e4200c0c1c40c042c82e40610108006541d82c0d01024600003051500c184480c440d0f449002d80c001090b8005408070309600341c20840c605050007001d0b4440c1e0350007507031000d40c18250340103411090000c2138a0311001d4006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712090359 1250 712089109 712089137
    0xc090306020d150b1c05010503060112110a0b07060b0d03080c09010306120515010b16030509010c140c150c060103020405060a0e1906091506140403061b080c03070c03 73
    0x150280040400d03c404a81c0403e5075100441a550303c10380c04c40b4503403a0208070040c00301c552070080504880b4050f004120707030703841c2c0031118891030012181160b0700e5102e254a02c810341d49241b00440907041800c0340d40c1e902c4490346005400c0f0394204071030a0041c02001005804a81c0066a0507801200600480e90316008040128000d00c0141c01100098114004440038444006000e00c2d4040100d03204050a90f00c9044000c65070083c002c041001c1442c01b0103040000c0e01c2100503010300380042c1030002c24528269503413104500000510016a8071065003d1050710b0600748558440c1c2c802112a440c00c403010b02241d846260500002e4011500d82d00412a02c0d200c0b04c01400041000c8a84402c090801c61a100c0e000090301d00344030005800d010020a0300d002d14401d6464030000c1e0101d03150f10903e8080c05136548144d102c4014480d00c000d00002010561601030054071044485c61030010800711080508000390140c031100045030f00703000b00300001e50489944c00d446501030034001c841c1804a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712091609 1250 712090359 712090361
    0xb18210a06051503030d0c0201151a1b030304050a030e0607020a12080708070605070e0f010c1203110c0c0306010b0412240912141305121002210105040c090306020d 72
    0x5001c03080d4251000050141504045034420b07803461f2925402032001b00d09042c400c02c1d002c02e0601908200f070074a50380e640300b00d082e058020720070445105030b46040c0800f141c402504580003102e0568035900031250070f0342059400b0780070b2043d8050171034001e41000019000b10721000e455002da41c06509143c00820140504d200680d80001da2007140703d0346c0c035206444c04401074202500d4280124052407800c10080c5005d080713007603c09506030b54071b596604441d00e4081d04244041a00f03418182d4964004494031803100c001c10884403c080284401d40342001858070f0400164011014100b091209211525002c200b42c4c1e11036402c18050008a81c90a00340d104451072501e08020716464190b2413130400695800c030080c560782c50b4035500b050a4000c4c00e031400034840d0f21401038501e51b0b81d0030180000d240154070081201d144104807101c14417006c0b1640c00304d078400302c0b00c40c80c40c1c152102000f07002d01e4010f0041340584030035201480401a904405020003000e03000081510b600483d4112180840e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712092859 1250 712091609 712091641
    0x12090f061d0301060f03050c030d0f0f14190801050904020303090d05150a0f0b18130c0e0709080d0c1109150409060b0102010c090e1602070b18210a0605 67
    0x700034001c200040c2d5030302c4803007029401488100d40d20300991021035054500440c0d042e00d0f0380641d4070340342ca00038070320501258404c11510301c81c020721100001c03050141000d000608004611404250f8032840202000381c040c1c60305034886445001d041c000c020050700e012065585110003900c1b580f448002514000d0308003034000400c000345111220030410070710040d4018103480d2581c000704210b410500402e01c900c4030340c5444481c455481c084c0c04641000c8035643e000c1007003400340d0320f01032a8544031001c44246500c240c480c4800550403040c1400020024402c00300c44040c0c904055101090307940e81d154a04900f0744096218480c014001031002180c1c42c3d8501d6100001401000a62450b240040082032401c41c01c030300641c600f400560425009055160a54404001e00c0c0d0040d61842d02d0500801c0608804000f14003035803000180704060720000e0000b14031000b40103003a9400207001c2c0700d40d9060008030b458180704140300103130300d169022802c031100580250001c101503540031246c012000c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712094109 1250 712092859 712092917
    0x3010b09040503122a07060b06090904080c0712050a0302070501020d08041104180f050d09080a11150d0e0d171302040e0709020d180206030a05150a06080412090f06 72
    0x108174401400803820000c000c00358107101e1041044a5403181041c407805008100800d0782240c4034001060100d12248003138000700e80540102d401e05030302c488900784900e01454040f207481e07001d144c1d131a08042e0140110005810288020320086015941c000e200d204064000b415998105071080416251500b0000704001d40c420f0340088032890707243c101e0403481c40040a80300d81c0038200c50303555442e00c41d150b02000c850000c0001d140440725915035841c81d00c429402d182d40305442400d03c00c0d0050568014003854001e001001840400704605107061030740300b20107981000b8184220228503040d4400d410740001d0044508200380113203202040007030800d41c404580512408500190442c3c1a0b00240542e21441d02c052140b031048450403141c4952002d0000c0d4040340c00d200003084441c440e48129803050080700e4481c0b01d00e01070000705450440039003204001504075010481440281e10f040041d8401900d4001c0c0e100380307000d1902c882c00c52580a401c04004590140d03070401980780142d960010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712095359 1250 712094109 712094161
    0x103090f03080a050c090a0e0604090c0b0703020106060503060d0b070e03061609050d020108041e0b01060e120606090c070221030a0f020607080606030c0c0a0b0603010b0904050312 79
    0x39215040c090a0b50008070382c58410181004000340c04002503200b0350ba40c0c83d8010700b9045240d8202034005500800040c58030350400d990700120004a6803864444000b040e515080660341c0b5000c5c10000d0a686003900a501488401c10900100d6194880e03154800358001d60040015180c40404551402000400c5e0380d01d8440d280a02c418a00c0710003d6130702441d980d07240c0c0d104071940c40c0c0038441e803100041c1019002c1044140001d01180725098401c0342c0e009580c0415110082e1682c4804240c6c0d0300b07070402c0c0006203410b50b0b5440c060402e10410880d0f0350062000300781d00c3c0f802c400064034110005000903040f40707000c2803100440d2162851100c0c0c007444010780c018940d0700030075420341e65003126044100050090200491712030001c1030301400342d440c41c1d844040c0d580c2c491042c407406130b0014006410085003000070950210b0b0600503900c20303a2203222248a2401c00100f0142540c101d8a1040d10400d110800e110004100004452040121040f201c081d035544103080100b00c50f6001c0a90516 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712096609 1250 712095359 712095383
    0x10b070b1506090f0d0210021b0a030b0c030c0408070f050a06030203060906060c0a0515040c0e191e0e150115050306300c031513020f0301020f04030f060b060901021902010309 77
    0x21034001c0341c40211070851907009c0b1198042581000302080e02484050328400c0c000c00442ea454140000844d4005150402ca81c41c069844d5402031900c01c0c56408245100740c101018080d9142044001c070040c01c1d0b40c0b4055085042800c0041c0c03451102070f050314800c0b0000a2074030b50901c000e02c000b001690b045000c0d034041003c40605114810800c403130071500c2000e44003010800511341200503005020070800744003c00d0201301c2020003404c030075100d242e0150114540c0c1c01c170fa01c1c4030301034845a000400041c0c01d04a00404100704a4001038208003800000b02070103c81c11948a010f0702e502001c1220900d000c2e0702032110211121031402c0c6404800000b20140981c440030003d0700d404065010380440f03000001c05500b000c07590368103071000080c1c400f0038615500035251181902003140c40041c001450054a4104050f696110303a204603405d624014101c81404400d1162004406092310b01c0c624003031290340001c0d103900100c29240c1142c65003041900569200707600124041e80c0c004409503031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712097859 1250 712096609 712096639
    0xc090d030e0a031109090d0503070c0215070501020a1806020a020118170304080f010903090b07020315240901060801030206030a1e0248010b0405010b070b1506090f0d02 74
    0x41c81420303100d44d41c0604036500c04200300040000d54802d003a8501e03074074030303007940c85903181251501001c000c183d901c20400000380ca5200e0102e4028280148503000041ea18190420043d15001d84d104000a00c5a6120002c01c80280c01065071000168241380c4600d1080140040c51078250003034000707542c0c034455000c100c0540c0c14008014000d90300c072001103644040c040c0080d40e00b41c0d460b40000038009400e81104100102c804006842003501c010107071404000ca803075140032010001c8401030390103156442c42c0390715280340004100c0c0c2c17a602500d00308420344c1411340c050142038061200a01400c1d00100041c28407601d5440044513507180450120640e8287c03200398041c0d040301041d510f00d6041c1840140035011052520098121102040d02131500c0524011500030050b44204600b5502d60611105c00ea07214070485000c0c0101e5007090748c0320703401e60400c0289400010095000301050316580182541ea4906484070f00c10110f680e541c1c4600b4403404503c2c1c41c3e0039910001c0d0400e81c08145400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712099109 1250 712097859 712097873
    0x6030f090c12151e0506120d0201060501090512070b09030a06060b03070e101e091703031806010f030f03031811030c04140c030402030703020d0302060106170c090d030e0a03 76
    0x14154080e072403400c0f203250710100705411110070007030f1458400080700000c0c4064840b42c00040d4094801811a22100c9002c07940320f0610104e84480ca0060f5034843d0305004540e0084a8080500020f895031a21104507210541d560500d601a0214852011401d100550340c108075640d2141c0d4002e9003405055928445070156800030746801011500d40c00300030490b07080804580c2150004d030381d2004152019280f0000d03001c5002280700003080709810011841c10887c0940350181c55541004559a1a240c00710341c00041061102d1042038110000402440ba040c0e4402001e0b641c120384800c0d144a05e80c6429802041848543e40400c54031442031400d11111744c910501180056003602c0303020014804000848042c0b008000c0110402008620445010000395620600c05811a0310041c0c503600001c0341414007210403001070380100010710040c1c0d44400c4100382114010080314450504c040d00e000c0c18012944004d0140540403500b40c02d05100b10b0003100803001c00382c1110394054803420082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712100359 1250 712099109 712099139
    0x1b0228080d02061506120402150c161401030605031509010f050f0601022b0503060f09040b16020a0c050103021c0524030312060d06021c06090b010207030c06030f090c 73
    0xa0138050301449602c41c00e0070200e0885840e08001c0040766659511a8208682070502d040c544c105140140465815130004000310702c600c000c0507881410051030b2500c1d074a0005a090f080300d04040c01c05104200710307140081d4405400c05480c21840d13055440103c1c650042144440c6001240c1c1000700f880082100b181d1600e020f00002e900341d490181007031b0702ca0840c00c561100a01ca0080040d00304100c03da220300d028540040c0010207034120294090000355060f902614142d8001c040711040c004d0646101600055122032030015040d0800d554a925045900a04c01c2c82d06140d000105031070019460003900175101d00d400000c1115007001e00b07503071945a41449032218500c0c01c911110a09190000070764400143d40c48d4030322090785e560410320844180d103180840380e083d000e0154054003000c000740b01c00c00ca50707000d200003001032804050000395100e00200c0c50541d080380e0300910101c0c100c024000203541c01c03800d0200d1551500e0b80088000c05030214060315010a002011641000800e506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 712101609 1250 712100359 712100371
    0xc0507060806090a060308042606090102040e100b03010e090a0f0b0a2003070318060204061713120e030c0910080601150c020103200304050106061b0228080d0206 71
    0x3d283c0c0d6a10400d8000c03100c090101400d4010203000030030558000c078000d0302c0e0f480e42c814600103240f400320032424038007402070700c0f108151f0350085030a0002c80c240b01030751a030081a8070000c6280d9403a01413044420300c03060007032010f0300fa140b03c00108100c008010030031030150b00407591004d00071075080c070000c40d0300c040d10800c0040e8149039016451744c2003e00e5200c4441d1401c02010b107983c450240c10b074000c0c2503100d09144640c0f0301081c140301040c0b16102810040040d500c40c4801710809491703a0045820040c50340c40c4c4000401c00c0d41c00801c41c41401d01c0d1548100341455081d070704100d00000d1400d806e012070240c1c001d00580c100200314000140703d8088a103182c040f9415640c841c3c0103000103040d81c0e24603000007a0003290403805584a50044008515521448014184a0360312481d4607031080b20700361082d0303450b84801c012035039100140002c0504240a20601c60b031041c3c0c001920030100e1a01c40381d103243c0196121400c01c1110f07401a0003400c044003107401601c0d4024000c0c0d1104022694 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 712102859 1250 712101609 712101619
    0x1506030703060602064503030106020c0f1020030c0a032607020a08130902070305070203070f05060d1a060a1101062106020c160801060302090a0b0d120c0507060806 72
    0x10660405030306d24000b0410104d07038252590705c1c83c400845041858552007405e40c003c0d0b102d9041504004c244011406054254060030705403400c03500b40b10f6420901c0652900a0740c103c4c0f0a185201d0b4049640c0040562814009000c00c01aa180130310318062100a200e05024411011042641088044410101003046076020300b88049002496a20407030300380c405038100c51910310003d0031000c000c02d0500591a40c1103001921282000100d82201400f00c000c200001000425403030100900d5005048000c4640d00d15405e01c0c01042d80d40c0194040400b4140d00d8000c01002403c2c415004d220b00440900380130340320150ba400c010000b0301e14890207c6154030304174004c2010515407105180b1651803a51070340c241851952400000c0d44030000100c80760107000044a00d00309040f1848004010490002c03810034298010801c0b02e40c009440d4085640c9000c11041041c1c8680344103140068101c44454103402041000b55800c40070b10b10000c0c0240540c46000c02c130a50441d81c902e014007403d9170 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 712104109 1250 712102859 712102861
    0x60d12020c1804080702010c0302160605030406150f140d060504061e0c0509060c19140d0306031a09240406050c0a1d0a09050903042409030b150603070306060206 71
    0x62000024281030710007901074502000340750051f500070304030004190310a104503030181700c00200304103802c4070300e81000000a400005010034007a8500070308100105031070041c0310061909081740c481e50100d109040d00e98120202e062540d40d0b46c0300c00c1118090b00500c0521181c0340500c0c0502c000e010004181560002d482e182c0c00d100105403082c200c0c0c164150f11510b10380002001003082c0b035041400008010f1007015140d0108035900b40c1c0e02c007440c6210701c18003505c020007942e200c1d0502c0718403054070080525209040011541c0002c070a04841748003041441c1507144c480b540c9050803007e107084c1c07641401048051011305c142d100180d100b64000d1208101c60346945c0008425031061004004c00145001010071b10761010091002c81100010000b50341c0e03039500c400e0401138440c201c54480d25900003080811010941c110301211402c2180380181205091050103000b11a0350300002d4008a0340b9000074002d03501092110714070b18801451280c036454140002406000c1a020b41001401140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 712105359 1250 712104109 712104139
    0x106080703090c0f1a19120219030906050703140408071b1d0a0b010507060b061903060f06110303070311160813050a080309040e15040f17070b0c03060d12020c 70
    0x4006e03118000542c0600494007080c0c1203040303030407851042c880031003161708005021601c08880c1502c3c201034910780b004a0ba0810a00700360046500c0203006c14141800c003004001040701103c4141d500950007090540c44128604203a021240d0002140030315400c01d02001c81c110020403070708104098824802ca4065807004000700a562507408024003290051050700001030540e04402441741d0007034400da0800d00e2010711014500c000345c0350300d000700303544031000e005810445090070054503540c02c028908140c2001001c0d620b01c4020049420580d8441400980e68000e03000c85185500c100d803110b040316201c0c209844503500400c941104603035109400150360401245200848018138091400c1c19061814003001d0702070440c40c801c603401039151080d9164120449103004a01a182d207614020045c603040200001c46528558001c0d0140702c0e80000600c0710b0320b03035680024654515500c80d1141c0004c102c6a807507511004003a50344018244103001d500040c1c1140f00c40d411074920106555407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 712106609 1250 712105359 712105409
    0x1020190c080c01053a1a04020309060c070f08040603061806080d031a0a090506010219050c010e0112060b0309120f040312120f320106080703090c0f 65
    0x8800b205000c07030f03024003140504000e80c5408003058200300400206203500e4031100d070b19481366030196100e401e9031800709550060f0b46d40039100c80d1010948003140345040001c49540d076144001d01c0020800f0000688008006003a180805032540c41100c450700d840d03e0396030207806080e00d4054102c4038084008000a15003041c010041120410005040840c0b040c1c3c6048002c1c10710103c0c5003202045520084a1903182c40742c17014000d0149520014017801c004000a0031301c0b03100180078505542440d003480100320b011440c4c0e43c82420900300304513141c41c8100107031002d885010710800d900749003000000b452000c0c2d00040d845040b032101603a101141001c401a1540030310046040d2080b0240000c0c40011003103610030b8443c032400c2c24010007407002010310105860341c460740000ba01d92108048000480968030710000801500b40000c40044071403c01c80110030140328030001c01a56401081d002c1d400782c2c1c003503030740741381c00c4088090915281e0340e01e03039000c0c100c0e8410416590451011a4009941d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 712107859 1250 712106609 712106623
    0x31501080412141210050a0b07032c1f0f02030703020a1101050415020f0c06030f07080c09040204030c0f0e010602062d0f0f0105040203061020190c08 66
    0xc0000c1d05510385004280440303c15075401c040003c3c3c400200312071012000e11440c0785118440c01502c141d02c09080c82c00740408048258000c0e0016402440038900181c1c120040e030000c0100e0302c102000011408114846120340f821300c9075085040d42015082111001d08420369200c3e280e16141c0314800c02d038800320394900c500341c80540140c004044030000502c41540300d00c80308405151131410302d43c841f201605030910700022a00940c0c000400c5802c0300c82c2c2481010410708044800c00d06515003030700008602c240003450482008194000070b038041900105850b4003903409042103490b292649050081c107801d0380104407441c1078005000440030b00b400400307816206030754040d0100303440c1c2d00010481c119041d0701035000348001c00c58542020403d542030f684642e807450a080c0941c2402030320095540c1040e00201d015a00400401005441e0f41113040e060184603e001c49810800c0d042c0d841488000540d066814055180550000c501504896903450301031a8900000d541e00c03c0c41c02c1e0b0710700c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 712109109 1250 712107859 712107863
    0x50f01050f0d0501110310031718010302090409080c0c010e150406080702030c06070504140a030224120103050705031b03121b010501080303190902030622060906020315010804 77
    0x844012003511904082469107150351103480042030b178540d4240c2d19685500b0031505041250385080b000c00c107001d030f8007840340b60710104004d000c1d00d040791038050b4014244501503454185600083c1000e00c0351900e42c0080b40c2950055000c61b01d401c030b00b0b0402500ca901303c044076400284085802c100c2d514180382d0301202884900710591625142403030503204180c000b840881940001d12601121820600569208944c40d40d00c030361b076440c1001c016544204204400701d01502c00c00c4c405100503151a411000030b469500c224400c0c02d6005000b1075154030400c1c010768400b0343c074200008104040061400b050300d20403015034020341c0190008840303005110b0075259055206103114079841300071100601710321098540c2c00302d8a440f05034642e401c0d50420781c000c13003e07903200200700182100752100c0b1244000701e02a052201c0070740754001903035031030002c1e00c3c401c4554144144400c0d644164010058002c0d4480d806010503010f6040c104000d410460300b02184001e4800e0085940d84101090b03840ba503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 712110359 1250 712109109 712109119
    0x41211100c14281e050423180c0409090609060b12030d020711030105131110090b0f120112020a211101020304090612050f010b011d0301020409180204050f0105 70
    0x506079240b0007512020f03052000d42403001510074070b940211440c1d00321080e81030640b12242c1c0c0318a0450721106002c00324140111400e00040c4400c69580c681d1040d101c0b0041070208240c2c65160070854510520484e80a6124940b408542604110150300000281800b604d820485880c41100344402d0940c0304140140300d4004100745c00740100f0640c0641241c3c1d0140489944000800b40030a007110030a8503944071744801d0f00805c20410019080e017810561094440e0504a50001d03c00340c51003a59020300800d22030007065140071003220301d06442201181c08100c1810796510034019030650342501c0168041c500600e004511a0040b50140c030308030941c1c42007040301c08095240d80003084040b1404c1ca045010810001510140760300a030800750280400d07483e908441d600d00946807084001d00380070a6410700d904201c40d0b0b0380100205440c862030156000310381305e500b0002802445541c00c90010703140303451807010071801201400129240b00b03440802c020f484458545100b44024480c0b00d03404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 712111609 1250 712110359 712110397
    0x4030303020c120c010f051b12040203030d05040b0108070b0403020108040206030a0b040e030c1c090e07090305010f0501140d0b01121a0c09011205040b041211100c14 73
    0x40d1007680102100e4603000180c03883c01403000b02c5001030798854030091240b030391108415481410f061040d65000801c1a507070400c50192035509002c02e00038010300144c00c0050307500140554a0a0040b103141d030052031410009450b10f0b140501400390280039900003803040e020007140e0b11200b5401c98058076016100c407265503480c0e508000c400d910082c0030030b64950301c40c024001d00d03881d2801280c1e680d40b01d43c8055070321000610006e170b1030b040c3d0240e5100c403a840c904074041c0c3c00c580c2103407100003580c80000305206e066403962030683d50716460741d000400b29881d00009006004003684500c0c184c40c04080b4a444c0c001d042010000020390303080d0f010780b10f80c610708010032054864240b81720701188140c0b1800311143c18190710882409080318041007071080003481c1c0031150ba00c000221310084000b1002c22050500d9203898540302c1008000902c020100c45503a84602c0c0141000d00481c145601281c100d4580d0b4032628020b08110100b8a0120b5000c924104030782c0c0c201800c1e9549003103084070308a0780c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 712112859 1250 712111609 712111613
    0x130e01030201140c100f0e251401021612030e0306040c06030c02010b030a0c050a2408060d0506090c0103150503030d0b0d02090c040e0a0207032001110d1a030c01050403 74
    0x101d84c40402941420300c6640e1001185905038015039019507001d0b10001100ca206640da203040001c00c10100c5008840380403102035001c032640301102134810801c0750a400004581c0140d00d403001e000301752508041e0003440095001d100d50051110705109030745e400118420082450350715001960010a4001d00c0c04040c400c0b14400c0d4031161681c1c1e61840045000101e406c0802e040c03a901d202c00780c0704812560024456410400301e460000c004000d040030003541c0c80b541340d80002c40f41c1850082001140000301d401030b5241e4424031500c5812406030b400c1d6042c0f60b0340d240d0395203042d01502c5e80030a01f40030440f0145d5814251080c22104085e0180d03140000100b4010004c066000c91154441030384c5182c2009038a8800da040d1251001101d1503036030302c2c1030a06505810344010580688640100500b2000942c070000d0f200e080d80788030082e4407c00501d00310403809484200c0d2a18401c00c0003280c030b9100e40340a60025103040428025040480390740308241030b1218000001903012600400c030400c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 712114109 1250 712112859 712112897
    0x100506010f0c1b03080d05150108150f270604020c070302090c0d050f18030f041e0302060d0207062a050d0e1b0405160806041a0301050408130e01030201 67
    0x4081ca00c583c00c00480c00040740b035080f04154031074205940b29040031980960030510740c4551781d0020406100c03040c0028a0710002030420070024031082042400850942240c1c448002148000c0002000810194040c600c0100030200312003d05d0000c00888000c41c035681414802c440c0303a0030301040901146420741d001c0c0001400047c14141201000304a00c80611440f0310489010710002c0b4090300d0b003404e00c0e00001c40f0484203c07038080303123580040019800c101c12100854085424401c2c400d65940d0384142c201d034282e0010791010390001d60000d2403488005080d4010702c20703144105410000b000749540200c58905007154006000491201250a19800380014001d510142e1902240d1492440c02d21810030440c84841e00505580b41104603041ca058021198041c0816001240244c41890010003006000d014540030380c0c0d4541440c0303a0445007802610210201030001e01150901d460640030591240000c98101070442402080c030410899a0303d0480c1c0d0140d40e0705075034011010000c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 712115359 1250 712114109 712114127
    0x71712040603091515210605070c0c0812090f01030207020a060305061809070905191506030606031a061303050304030b0f01080a0321091209090c05040303090b0c01090b040b0702100506010f 83
    0xc0980c186c1358040d88005505800340301d200f01036580e00c0603017054031454000880d019940141040d030b00007091144402e9500002d40d044a50100c5000c0a03c0040100603002442000000394001c40300b20004200c05406420082c054403081e2007040c0c0021140501000d0a00306882135034180e0003000e02080a004660800340d0031416001803100342d06c10f01a005000c9446003000b89004c614150400c0013002c0e01442070b90010061400c1c01d2000b550901003581c0c40030440c20b240c0b44240804940340c0d2800580b07a84013000b85031b103e030413a0b40d02d41d20707803d2480145c90300f220211001c003507400001c01d060700003044403145242d040d250944049030b44060840c1100d54590301c0d44c3c2041e510070903d000314201003155018140c840c1c4480c00c0040c1041e00181c240c484220380c10b4140402040100002030740417407290101c515007519903031103425202c0614003402c00c202c00a0100e80c140028402405a512441400750752290201c5d1421600c0c500c040050311001c80c0c819020a208c6d0130080b00d81802212070f9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 712116609 1250 712115359 712115399
    0xa05030a11040b011715040b01050327070f0602010204080106060e0d0803130c1e0503010b180901020d091406090a080910020c03010e03040503190203071712040603091515 75
    0x1c1c0c41d09020100402141100c1106c0b040e01256100201c1c400704e0402d8072030010520020301c6c01903d14940040328040911001e0205480003900480f04440300400340182d9000d000070030f02d03c000b85a80c5000003400307508140070b0303118a54030740307440003c1c15802440c50749881e42e805884821044010340707450019400003401510340044a551050015004d165070743d02030610708031078070100d90403c1c154400031441904514000d13131401000704c0d082d075219040504800404509a10700d40e0320b010380140603010349010686d20070b0601421504104103824240010080308040b41c6056480c60419640c0e0801c402d809011150108400417103400d219240c410881003500441d440242c68030b012070700b1030302c0d00c1c0c10b5200030b50804182400945003d2001c0d61540c440b60100c0280c080f85500080e441e00c0c4140308006000c00c00841e02d441c40d18003070000c154500024a202511580e0b1b0350409030103081c541104070ba61030403924043c0345141c41c41c4a400742c0038a00c84100901c0c079080101c2109581400701072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 712117859 1250 712116609 712116617
    0x3020706050a0314190e0c150f1e09130c0801090902010324081002040302130b0a150f08062d0102010f11130503060708130c050d030e0a05030a11040b01 67
    0x440940c211690718040c055081070501d1780028410300401001ca03000321421001c0e640000c0c41640035581c44030720b00a5034251955201d40c2d11081411700040ca40b160301101c000348905141070030303c060011300240c200d1b24000d4826004812034091144200c032640d007000404140c4040060000168a62026601c1481810005450501c404440b000204100340b083e407500744c20ba5081c040e403a4148034480091900350340c00e604107425540040e200490300c21480f80c0c1542d50b0ba10040d120741e91849a0002442c0c0252584001408003070000c2c099120142001d010501d58000700d085400c0c41d8018810801c2010304442003101c18902181030fa4902104240c1159210407422a50324140e01c180b0560682608025a07030314a1940400c507903036010790203103201380c118404002c42950086d454550060b1000e8610380c03004c52a151841c20140181c100a4200781e0050072002050741140941d00e040004999018099a0303400c1013598440520b0300051031090942d07040e61a500300764010205035801410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 712119109 1250 712117859 712117871
    0x303010e010e13081602010e010e0a03020f032a09100302030a06110408031606141308030604020d0e030a110d0f0815220b06070803010e060f06041e0f0303020706050a03 74
    0x1c52030340710380080780c03145d2910074481030034130845d82c214000d08002e280c00e00b0000140e10301240010f0140d2060321000c0e000e503045803050400c0356000c0c840b4601e0760002c069420003c0c800c466403140c00009843d80c0c0c41c05409020040340048000d076003400304981d4010300504c5200031582d105005803103090b071b20600544040c40042030b951014409003190486042e00a222400c03541049070580320040c10b4461106c0b071b00380510200506400c0392042640d0041d00a682d280c55100101c2d00a200d008013403850649000105080740f000400240443c1c0c100d030f6107481c0c1c0d004032103040caa1900500071014007c194031081e04443d180c01001c0701079102c62014a40c4002c02c07186d00c0800d4601e5030842c0316904400c801c64001c044c01400e03200f2000328203415148203003804bc107a5600c164600c0103000e8000e40041c0d00300002e03402d80e03c030084c034060004081d000a03165a5034a800d10105240e05034030144a110f41d40d401b1a02d4005202000c0493340c141c2d00610300780345064001d9805601c000084001c05458007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 712120359 1250 712119109 712119113
    0x30b03010204302112560909072414030c031e0420040906060e0a0e0a02100305090304030515010905090a170f071502030106030c020303010e010e13 65
    0x20081c0c41e601520340c80010340d070240110307006000380051249030170b070189041200c0a005012081d104514281a20159036110703042c0f40383c15420420070b070284203032219080e450404041000c42400d900d0f4041d28415001d40f034502d801070300d402e1540551001c1c80c00d00042e05c6103c3d0810f01d0b20030400345450500c8079814a9010010613079900444103d41c02410001c14405c862040f0220614080344005c044030250825a039001180d5031903c400c480600008244081c003035855a0110109980c8001d007008034a41c0c500751801001000c032041c2c1d03041c624107036013881055004512511140d1740180141c404141181c0305400a001c06020b8424500c401e01c004400207604021481c03981800c0c1120b2489989040d03c1c140c11348400402c00c0820750040c480c1d100000303031600207424041580c00001d82d1242080414091240212903000d00030301000c0c500e000c2c1e8002654000c5040e28a25601030100050031502a41e49220030300c134226036442c00f00c00400035103a005410980150988012034071840307481e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 712121609 1250 712120359 712120373
    0xa2c032a03100b0a0602070f09050403050d0e0f06010f1a0d061205030306100903080d0c021c03061404143106140a0e0d1b02061603030b0301020430 65
    0x1042d55401203503544405100303840d02c5010341d8010708491004000017402c085000046811501c07030912826100c2c0082003c060140b8144e49840e105c0e20f0702000011680122169901c82d070120f1026140240400819401e075000c40d02c40135182e0a2801c0c4070f68071000c1d1030b1480158440c0c42c0000206a5915012591400d40a80064842c0c0290000c6889041030410484039408407111582444010007080002891b210142d810200030320600003501c101044042c3d0610507a800e400500200d1500c1001000340c0583c0041c1c1600d8100c000950408050003d02085501b010255071a001d40074002501541464107a9034901100c0b48516181b01d4000032a0300c45840136203400ca500d00d45800d11151102102c0c403000d507000f000d600050080705010403070f00b80c40f00040b954850800503410041e4540c01248403641080c694060f082642c0e41207100200c0902000c01c4600301e00107420941c00140e50726050082d241940d19804980d040800700071508001003143c140d0300208041200d41d40000b050b04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 712122859 1250 712121609 712121623
    0x809030f0a0305180103050f0f25020a030e0301150524040311010e01030b09060d030e030a0605010503060a0b01022d01052a0c070302010507170a2c032a03 68
    0x4070f6150141c40707060300800c61040105011000e030405180008201d6519003040015810440d0600c00e01c0098661162900324040c25400c03044000b000d03013041504c031503400207003000c8590185d540c2e081e001e0b040740105401d95041c035100c520700d41c0340c2c202c0a1005c0c0c50902e80b10079501d46a24211030401d49034082d11007282c1c0280c1c1c41981c400b030782d004100c00e0710758104000020a950918040080300c01c5800000c04102c0d000d440c060080741d44404c520100f40c091441052040e0005041f41c082c418175103001707000380c5000d000e014040d009403004910203034000c5c01081035076541600a003284c0c1c0c0d02c1000c0c0b800e4800094841071010200465011015078080c401c0030301031741d501403c07545d001180350b020003802d448150803050b40010030424203800b8500071034140152542403a0866030340480e400c02c4a0055002d55403641a03040010b00c005034560403090000c2d1061a10018900c0c2c261008818410400a80501c5805400c024028007518110041d5004040200c07441403500000c540046858020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 712124109 1250 712122859 712122863
    0x512010603090c09140c130b0310030309051807050d0207080a09030b150a0b0c0c090a14310204110a050d18021503101a0d11040609030809030f0a 64
    0x10b5164445010700035090000c82c0645001ca10900044843e14540d079468500103100200c1e01c81c000c2040140585020342140080c00030340c10058507800d090158000c4a001444200c0100e00f02440c001401d040610f0441c00c02041905003050681e506141916113501003d0303502c0c031140e4204482400182601d000d03256421040c0da80c500303002e045203002042d4141c0501841d20b25a0101171a018035580c00340c00b901a078510180719070320746070300324005454502c1c1d02d03d0866000c5000020000071410550010710315450b40000510143c17a00301460340000d41100d202c1066410303034410b03070030941c2c0c10044c4030b054188003500c00241402c091204681e142c2007144000c000860001b83c0052030314890050b0700201003240c00343e44201c0c80e81d50000718181000c41c114a41401d0120008840e00c0c5003010060080601680039050403e088444024035840002640c9025160130f400c030024840380710545065510f01e8543c40b21080c00d64641844541221100603071600c02c21003055002d907028802c0702d42d964 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 712125359 1250 712124109 712124111
    0x3070f0f0b04061b03020408100915060e070e06071101180e010b0a12271b030c091a0f0f1504060504150c0f060f0e060c0a09060c080307030c0512010603 67
    0xd50003c580c0003090b44413402c6010980140001d028404021854140800c48950f0024032410285040242210a003904d00b02c0c6900d850380c00100b118644114901c951003030f0b643c03206101d0750710302045110300401101424102c0c0406401d8043d5010340384041e0b240710440b020002d8156a500f04900400f0f00f6000030f0f408081c0031510500c02e80d08122550341c040c04020080c80114880b44154071942880c28801204041da441804180040c0756000c2d089095000c410340c000b5500da00f80200008442d101d01c940540c0391800729442c4420f400c40b50130f0402002803000c689801440f080084c0d280540d544241c0c418807450700b038801c5031002d00c010001014a522880e40355072074a400b090041038000049400c1c080a5103036000001d440c0341800046a900550000340d42c98192001c0c001001206884d001a2040700d0902144000b02c0010348504800c0303550b60f1001341d841d54030460342d036030040c40b00074028841440450f013041e000ea0080564203500b4079117641010800030202011031402c0e80040003003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 712126609 1250 712125359 712125371
    0x22050c04060e0903180d0c080c090a090c03150b0d0c1401020d080a05070507050105090c090105101d03031317070e0c1e09040908120906010803070f0f0b0406 69
    0x14181030160100409031021110700383c0c40c285100503240e1061801c400315082d03070340031052083c0e0340b104002c08400c0e410010403054241c41c2d5801665a42d508021544200b1034080007401d00902400307410040c0360300c12140744060b03185542304051441025082d0b26186d44030311007402d0640710140c42d094001d0080e00d512880d28038107101d909403085544c003c54119001000680350035131700310100641000300440c00049607910484211050700440034010155400c15041c000075000010f140706005e4800c481815080c1d03a61030070000d031210040b1007500868981603030282c9403507103544052000840a41941e1910710700d0311041070f01a41c16041b005507400301030210b030803d000401c40314020741200d0a001d411030502c080b20103e1401119240480401c201414101c00408041540c110000140062140202ca0300e80b04c00650072400448003e80c482e03600040c2e4658000a1b41c904a848802c0035529101054075a84c205042889055581c2c4a241181900081c1d48400003485240917810020321 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 712127859 1250 712126609 712126633
    0x7060605040e0318010c08030a0e100612110604030b10060809030a080411010c0606062703020a06050d020408330106120c0e10030b090112080405092205 67
    0x8681460300414041d626241d40841404000811541c0d4203c1c4c110040b280081400012a406100304900404004001c01440b1801c00f46401011280d40c03880190382d05210100c08450444445200b0314500941064811011582c0e201001c1c01140021307000310310b072a803030707403200d0420100c01c0d2554840340850800810059a00241f025007001101e4061031801840c1e0f10010640100a88040c088182800b510760050307010b1611450016403283c01072107000d5444034003415410910788001c000c404441607414601402a44505c1502da00803c0000e51031308004007114503070000801076007900c0e803c110104000800700b0004405039084180001603040341041128030188009070f0f80702e41c0008100500c501a0080044240390900800000d43c2c41c0800c1c00c201c0d41000101003054201520b40f4200c403445505820000c50500103176001c04880e40e9031a081c1a10300d410007405455400203000c240030911f0080c00480d0003101c00300c5180b00000103c59402c8091164030811907150703002c5c1e0b00c5000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 712129109 1250 712127859 712127861
    0x140c0a03171b04030308090109020409200102060c0429040311130203070e12100501120204060f12060207060905061e0106020f0303180a05030a02030a08060d03021504030201021c020706 81
    0x1d80b2079101544621040a01030304070100b8000d900005060148410010b0100c00003503201c205510b400034000e009001542c04d00c00c0440c01010014900203801010b5501301d03500000d00203008840880b90585082e2a111802c2c803140e050311080089440e849000c2600c2e264040c0240000e540070302200761007a82c0210411007508200451460340714010300c104036199070403181140304100d05694070b4070500e06c40300401d410501d0003541e0300c014a1501d40003241403a80988903050769442980c0412100345c03214985d2040e4103c0d40320b50102c804a8525000015486401070f0171481d2182401059854069880c81c2c200403007180c5071ba000c0701d80d2104031301d941340c0c10030f030390a00400c418009000342d40710500340319480740300c0100000810f07440c0002d0409600c500300525040550001d0070399840b0310b08440000e441c4c2c0e1002004000003000390001c03070300324501044901843c561540042c003100300700070f00c003c00d0400c000b4400d40640d5402d00c01d0629400f1600a00700c80c101d40013100507074441c12450000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 712130359 1250 712129109 712129111
    0xc06130603050105100804030320040e1603020c0d0507050a0b09030904110a0e0103021c091b08011104151e0f02072c0a060305120c0c0f10140c0a0317 66
    0x584170301e4100d03c1c1c0541041d00301400303a41150705031a004c106d41d002c10315004c0303002d07007243c41103581d04800003400525080d800006500801d441ca0f8040748015581c0411030503030040140c55400d90300304030860030409004000800c1c1e0713240703e901030710308000c0c060302c49001c00a030444110000b60800540c4200718a40342c0b207040041080d0b20752641c200700042c40000c10203100150321a0500d580068060140e0308031500168100c0b402000600c04003000385446600b00072840e02101054080e8500859070b29018010181c900368039032525414545007001491f0328000226040b024041c00321402c030406c10402c9840101d0001a17103469007000b004d6400203207041c91b940c2c4409800251001080100d0840c190804a00242e1280d07509aa0311201d8000e070040c415540014083d12071046a00010400d04010702010ba50800c103a1f01900302210900030803500d030380422a4844140001e04020500034014245101d0503004140e0400746502400751910380a075800390b01081c22050310300d0403204070107061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 712131609 1250 712130359 712130369
    0x110d1a030601180f060519060809030405100e0112051f1a0d0c14040e040c1401081f0b030a02070c05100c02010507080d15062703060b030c061306030501 67
    0x90806602d015100c8111440d500004414903480d03502013041030107103030800005403a005014601c641450041c06056081c0d511491011602503030019807440400f20544048901c081e01841d58035940c140200d4500d000840d440b4180001038100c3c814806561080c02c0c0300c0e11543c14045045014034020250441e280e42c480c00c5010008004417001c00003000c207a40c400c0c4150301e0081070011501009940e403207080140c5a8150001090000c3e41c0c0000803992070185005801070308c0c0080c1c48030250412031000c0b42e296800f003459200804d0744ca01080720200720b441d03400f902d00c940458075039111b911680e00586403600b0182e004200c00c1c00f807006a070350100c01088100c6020410b0300c030381c05028005a41c0c806010b070510001007000c50a1102040c1101c140c1c000c0c0440402030001d9031003030781c0c038a5101c42c000d4034002035888045950383d00b4068000394a8811800501140915580e00d0101031700d014000a0b82600884980160755219007000d0688440c100c85402104c504010000703044980503400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 712132859 1250 712131609 712131613
    0xa0908031018061d0405030c060a02040f1d07080405011d060f01082b090f180c05250c0510170f04080d0e1f020406090b0f0405010f03110d1a03 63
    0x40110b825502c4104030a619426130103c810b684500304682107024080b12407450740507040800031320080e258010000e840140c100103000507201d801c10906003042014a140c0600c0e20350200b40c0703172030003507004951051058001240d2540c40007a030140134008840c1510560b0b018205200d0001c100310b003080c2c007404940006000b42208403005154030003801d4901801c17800100342c132000307040c03040001c00e014002c000b40042003a659000940104010458403103021842d00740b26403000d5126004071155141d0180d041c1c2812111140e500810400d0280300702ca40220007000020030340c40f42c00031ba4520802d162900410310000b00c44443d40c50f00014900d10b402c00b503900800000844d15030945080380500da60001341d030709911803c285002d0040d201e525408040c1141003401a03804d400403c02d4811a644100301d0f140d42e204041401d01850140040c40c09040c001031000e944074070255048413840f454042015448245804420703071084810200940d103070780c041624a040c1c80800311a00c1000c3d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 712134109 1250 712132859 712132871
    0x50706110c151806010303200d0816050c071202030f010509030711010c0507031202150108030a03110d140a0b03030702010207170a2a0503120a080a0908031018 70
    0x19940d40c0320b8005042c40c1c01840c004501007403181403086203403080e84032502c040340d00f996160708004c1e190384901480ba1000000d040000352011718080754081f414040303901c2d501b100781c0f07810108801c1034138401981009c10000b80f180040d0b00b03600b08292030040514800400702403038540141402c00800700f040c184143c9c1810b052203032003e40001103480c41a0850009000c0c0701c5e0140048440b00c078030304005005445038017808010300c0498418040500c156400b110040c600c0154421b201c01c100f4070a14a03650018040410900d00a4201c40b0b10050700f03550052601c2081c0500d50100c4010b641c0d901d402ea84120100011b02200f07100c4c00c00040412001541000e1041e80000d5940106015045083d40d1101a03500c00711400c102c0840c10560205500d1000321444418110200c84800c400340c2800000b44001f40c24200450361009180c082d6400903e420314400060f5803114014107900001d540e03c0b00c6901c00f203083d00b00910b00825020b543e152085141c5122030b40307100701580c5520581c0c3c1c41c0203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 712135359 1250 712134109 712134127
    0x1b01060920120103240c0f021903050405040c03020c030c07050a0518060f0a051c02030d080f043e01081506040512030c01060f08070602030a21061505070611 69
    0x21410303046903400b01440380d1424400c5588194105c01c261018040b604200321030141542112240d10f080782c0c41d80c00c13100d980c0e001c50110544a0301c02240030b0f000c00c000b004140140d080075000f82010215034140949014032088889283d540700c0c0c1c41c02045a00003150900403454450b07031010050a0132500d40013841d60b092065060485c0207000d881c1b086903504c003102d4440d164844c4500081c01d00400e502c400d10310f0300e407030040c20b2031004000700d100e03015903a88990a140a1a0b0150041d020840980e040c1d9a44d81e440e14218250480c500041840c1c54140000d80c002e540703541c2c5101801100c00040940359500003400811024101d0020070703401000816490310360100780c0381141c03001c56480400001d081403080c00c40c41360b0601841207500704100401c81500340c200d40c0040b079803244111206140c0d202022030310386c05000f41d204001607d0301c5612100c005100200c2c40300c1c84801c6800504140d5494400c0c00d080300d442c17044000301c5d08c0132030040d05200551096594038210001844d240c00d03104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 712136609 1250 712135359 712135387
    0x50307051005070e120c0a06050403020415030302030304080703020c0603040c09050a0603050c0609010e090f04050609120304200415050f060717070c08010905030910020c0d081b01060920 82
    0x9001d04e28091980b582407504900c2d400c204699807060007404c0380c170b00152142402483c2c0c0e8490f0100307901603410100060f41c0c5c02c407032600300b0003203903010f034055419511036603143c80c0b43d42c5c82100145c08502c00c202e5100381c1a036501c2c000b140243d101e90118081180b07803140a0307059500003400d030402d0504c1c0c9107040020aa0100d00d0a002c01000c4031059520022130005071116200011201e03002250102000001d0415480e402e00850003a0b0847d08540d80d409803107a070b14400b81c5400706d00b45a043c80031a002400001012012289880c0222107038155607002c00c0c01c4070064019206601c641c07041c03c111504141d04600c415280c00d880d1207150074840e4607a160303002000071540d48000c00c00906201400754045900d405800f0f13490080c41007100b80e040a5607030380c1114003114030409141c0c140302a020300000320400c0600b0058286020198592105100740c3c000c0b02d40004401d800188200d0491401c0c400d0b900075000b41a0b0020340020010702c08041103d48030034060344644100068808080c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 712137859 1250 712136609 712136627
    0x7061107080a05030a03050f070c0f14010e0607090f0302210102040b0d02041802071a065413170301030302010203180102090d0b1f0305030705100507 66
    0x11428116201104080880d26109141d0300c11901030088401e01c2081010120013446a4015560280025107501040c004100da00307494400c04a410325484a0000d22544141c2142c03900403181450440b02c5c0d040701c9400d482c4003015004083d04110200007509412a95990140c200c00c1c03416101e0900310b6022840d68481000c0c00341807130041c0741040942040c2501110083c0c500041455190340150820401a4001e801010540140c82e15810007083c00740c400c0e030380c186808c0191400d00f00703455081341403290006440c4c40d80043c5000074803c1da003488010041d0205502d034010550740c4401071910410124005c900145035502c1410460041030301980480e0000f0740c1400e108400944d51070007103031030103010190180050021000106040d01940514440c0d494003080c1c02c038000400b44954201e214207901954007140340d81c0030401241c050183b5540c0b1520300f00c0c107042c44002c0c0c856220640300c4c0540c008c841551001a20004209044c4880e4101940c00142401710341000d001c00b82078004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 712139109 1250 712137859 712137869
    0x3060207031101050121110a031a01150305100603020903101b08060f092205120d0c140f09040b0a090c020f0606030d0804060227040c08060a0b0c120307050a0801090e07 74
    0x1460031860150340d035a00142900540e0702c8ae0000749003001c41400850011004d104242038250740a21120140707004c0e000e1284581c0000441311590340c1043c0c03059000350403d210541e0148290010360345c03502031a20481e00c1144205000604942c1e0304000100058802400d55002e0080e4107949a80c035100c10100c640c0098031130f1514201c03100e140d4006251040c241001070b100384142e8071848103040d044001041d406190032401d100140c5403d0054a43c165809a0a102c2c040708200010526202c0c00103020b80b688014000300703d80f800c0740c001500c0d107803082d00441c91880c1d64214420410340c04202c1d901e5507030b0100707010f4561481e05c140000d40b01c4044140e0402800340c0d40c0000b8040001c103074121010f0b031403d4056141c81c480400c1d20b00924180c001e40e19802070303143c03a51100b03846000d40b4810703200c1d160080c504030549080c20580949900300b07285000d501e2040b0140300000e07016200196100d0810b907a03e0649480741c101009081c2241030384480c1542f0301e40b1108602841001c05c1e2036007990 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 712140359 1250 712139109 712139123
    0x9110405130c0c051b0901120210110a171213050a0b040f0803041a0c0f032706010801020d0b09011d0c09030a141204060f03110403060207031101050121 67
    0x740012003540c0603c01148018540d0190010382c011007110b4207a0455155819a200d403031aa0300c0c0c1c540307007080d9218100040e42c0b15989200c0c8401d060320139840152031014210540b021014103540c2d0545d891203074401d00c0c06075400800c0e00342c036840c8508911607001211309500f9a00b1700701070302e45036103820002c00301408c02150305000606000030351a47e0214254080c4d00541d5038600350900103d20349906c1e51102c0c901c42102d010820b0000030005561480360f5800f000c1c1d141d51207003405c1540c800300c0c0d41015103070845805101c00d81610700340905802454000700142c2e07100ca00d0380e011000c80703107189026445400441c00600a8600314020700c60007002d481c491009a44610342d5545460007206549541403117042c031031004010380b101e100ca0030785962204450b060103054400454500031030046030006002d907001810824803039002403280e140c82c0241d9a14044c1c4075158001030303910481094000c0384881d4040310000d4424841c49004040c940112001840a0311804505900211015050f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 712141609 1250 712140359 712140371
    0xa05041404020f0d020304051c09060c1b03050304060813110d0f051b0117070e0d1b0f0302030c090702121c060303260f0103020d0809090108070911040513 68
    0x303464590441c0d5440f00140348540c0c541001d040ca0002950003118125500d008840c20754401d100c6440344d094003044640c9a0305403403410301c1c2d0201c448218007141603d055511801ea54034402d92030241c10040c0d0f00500240d650783e400d144000d403501c0e201500201c1ca10407040707600004a00801c6c500381c0f50740c500b16944e017490003903410643d00e0703081100800b400500a1100d1804041030203612440c2c880d0081c1c81d152005010804140854130382100d40700d01203001e241000f140380c5090719401d201140301c3c80c0b0148500002e00b40c00c002140940d00b003e000154004c07070a1080d890b00300503d1005030812503545513180f0b05410000e4a845141040140c21203020070b2545102400d0b00d0900c040c022403220810219540c1c0c00d0050003c0500b01c92402c04400320b1403410218409840c002d4424014210107003290f921f10340c2800103070300017a44140c480c220180700b00301d000d9071001a80e50080c0070210080103003606204800048075040d030070007003c06000300720030852038072201c0b4000808101301c9000101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 712142859 1250 712141609 712141649
    0x105091603090203120903010b0111030304030e01110a0c0509010510230417010f05010b0a0f1d0306070c05060a0204051302070f050d030f05011403100e010b0307060207030b09030a0504 81
    0x30300b6003120700942c540901c6191040580c4502d0180c07512840850080c0b280030801c800544041000d02804000ca400410008020900422841780c0720b400615200d070200c211002100c0c10071411900032145e90f0300c0a54100100e19150843e580500310484169441d02c1c0c2c3e160018102c3d2000419201c028880d0081c4048520010f07010307103008222000307544020444422038207001740090080065580e00e0f110000c90108003150035655581c82c1510b80c1c1c3c200380d29014042c2c070b1a43d1094180340000c00101070159036174030305200203070041c1829150703000c2c4000e15152041c00c0607002040320b1540b034414030080003942d5550447c0c0540b0380541000580d510300360f0034001c6407842488800b800c2d41c81349118541c0305c90380c1580040c054031007203c1300b006183d8a03134600802000700d01414640c143d02c420a10380e843c038001d03444010204d016000011f400004100403d0a0091a0b44403002507000848200140804c40c4016036004006002861400e01c801d8000303409400fa5006a2014404d040d061240d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 712144109 1250 712142859 712142861
    0x3030815131104051203030f09070e0f06040207080406021b030129150c0a0c0915030312060906090c17060d0803090718020c15010608130c051503010515030105091603 73
    0xc09040c01501005c0182500e507041641d030790054820041003440b03070700080e00c01d01001c01c90340250341d441c441c6525180c07100c1900d0048150007802c05a40705508000380c030001080c3c20001c00c01480c0ca50003910320106d155500d641c2c00322011102c0c40c0264100700c9400c041c040001c5c03c100318917003100d055001130f00c0c504021410441c0d03c8000401464400106100008000500c8a803991301c51010032909944901400c0252205502c1040300c00c506510140000b034003503410b20f519400d00d51170014282d03a603004644181c4405600120644d560b51281c06000c0d5030228003030342c244850101901250038860049940d913030040b000602250b4002c000708020902c01d0120030300501c85aa03845940d2800e9015000081d23000c01c2140d40c8030310801e5207001081000014150481d1025112481c032a40e4441c4092204440e0074011503440d208410041469070300e00015403944403404019544a40c1824140034212082c07440400107050b042c4010043d80e030381c0004072580104d141100150302140c2e940150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 712145359 1250 712144109 712144117
    0x1502010e06010e2a0f0708120a24051e18040308010e15100e1201061d011a03040f031e0c061506020a0f050c0a0b04030308151311 57
    0xa011400341c00000035800590404241c010400c44885480f8000510340c0408030040c080c4540314091001d0005c040003a0f40c0c0701c040c3c4040ea004002092038034508140d42d8032840011564447c0890341c0c0c00d0740000c03e8840107904d5180b4600400c2e0280541d060800060a2000304520000d801491440140d000e890703044040c2046822110071481d941410302c0c01401642e130902400c25402c04070340002e00038110607404c041034504050a4110b04605514049420806581000e5041407501580c0c841000091059130020f02c103282c0ca10503000010894074a201038103a001c4101008c056440000c1411030008994000b54407801009405011786030585880c4070055900c803070040c460b11804001c42c1c00020240180340b29032810010750bd89103038044011f1050380541c0005178050041e840c0040c450003440c00c0c00030b014504a03400f16814400080c65030900b1b81044480301d802140130001c05030401400d030341140d21502c041d812000308401203a6200d80300201d0b42c0c0e10984034a4000c00b00c0c02124211 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 712146609 1250 712145359 712145381
    0x914040b0a061d010816050117090313260a0b0f1302060715050108014107090806060d02130b0135010518010b03071b060e010507080907150201 63
    0x4001c3d020f03125048642000f4804d01d1000d00a400c00240d002070340d4200341080d00c0058441440d400320b0481e61200c60b038001010201e00f84410000141d008ea8246400c0000b00541c00202a0003141048032180300328205410f408154003a80000c000145034201460b4007402c021440601d559841c0c4200000d04a0920040d410a034002011300130b012040c0c4500d03409403160002440341d070344c0e0f806046007210b078102000048a200518042c103014a03a291800c0541d20b4401e14051510640f00d404108250554401c00490811034080003202c405104c0703207a101c3c0c0105c45403006202c41d600031070300202145c94035820540d03480c2c080c885140c1c0110024100310f415160301c00801c8403c0d03200002c190508100d605446c4c0d15400c00081c59113007041444400600c0c0c10012500da920f081d8441241d030f0809846802800402c01840d9a03940c201207121410354068980492880d4a01da100350071900c014011500b04583d241c2000030300940054000115810f1554001d41408851300481c0108140d12107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 712147859 1250 712146609 712146629
    0x1a10030f030c030e1f0e0607020a06050702030724050a020102070506070815030109120807140f03011a0a09050f030a2a06020f1903090902070302010c0206010914040b0a06 75
    0x5000103056000c0d0302664964800c4e00c1c0d0592011288042202608450104100319008841c00d0307241180b042c0359202851341d000d05010b040400a0380003c0c54207180c0c0c0c0020001034400f02d02402589010840e4034028410707400d404081d44081b180d000d04004d860007101052260025505a0b082d00c05d504981603e600701e01610308500b00301700002d201e4503003518120030103182c80007044100c0c50184507803211603500004403008100a51410390305104000c2404d014400c4090040d002d428224004000410038529907641e20360501003681002c080c540790541040d102801300d0a00c141e005842142a504100d6401252841140003c2c0c504580200020064a0140940100002c50650142d0b01c44070513408900c403203032581004c03070f07a84c58041880480d540c44200398405400d104c9008210060080c541035020903113403047e6000380d9010380c004a0050390358100c0045544d42c14050b55016008520b000e100c000c0382c020141c1c690721005400a40107180b8400071541000f0030740e1124000b40640c0c1c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 712149109 1250 712147859 712147883
    0x908071a04170c1203120109050a090807110901060c11091906030620071e05030d050403020c0a060503100b0c010b0a0b030103050c0604210212010e07051c1a1003 71
    0xc0b00546030100a80c09902500c075140e0b10f480012808010754051841130361110007503a18061600c0080d2901030f0103416000ea882030207902180c0744a0051201500494861621a404c07900b80000100141e20107030410880c09880c3c0005540f07481c10310000c00e4112411034031078035240000c0302c200240d0f00c2c5400da40c91400c0e20000421000b80c1040003440b000344810901407035003e0442c240340c1320f061001032610954a01040c40c080003181c0c40410140a00f00300d03810810603540f0300c41122426102900568090080c50005241040519010340410b02c2d0941c214101803008000000b494022201d007020003040090030741c0b4007548440000c0c0d10041c6240001565200094002c2c1e1080c00151154090809209454240402250704950b103e1800d6810301d03021a400002c8480101c00403640034522001e000d9466409010344203802c3d10060260584a250100f0003000381c5110041a160450191a04000c13484110180d40c4400b44885080801c0d03450403150302245007a60401441a080c080c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 712150359 1250 712149109 712149149
    0xe0307080c15040e160504030602030a0204080c100f050a1b12090e040201021b010e04090501061401030506090109150801020f030106110a151d0102120a0c0908071a04 73
    0x300c9001030341098940b10004546a080c0d041c061085004502d121901d5501107006603909040700b4000324030310b1401506084d100d55600c400d0741e0007071301c0e0b42c1035041e0045001d008503601444582c0c1003150440704d5072890b82c5514000b41072101c1103c0c020061242c0415100a094001c18211031882580400b50140e40000e1402c2c1120004800c007040000b82d1120000c2824400e81d0281e84c090b031340503001030881ca0340c1504c680303050030000344441d030410212007600101519640200c03403605210718008240d450410740442a0b040005600c41d0405050105201080c0c80e006091815a80070703a82c041440310500c408240b06218540c0281d0707496100003450007640e01540d01440c1a294503980e059007034010780031b200340c2e10040301d0b502520400620380c085801d1501580040c0c56080e444000340b000300540f0044901326085004491204a20081081041c00080c03007545070005035400e04502050820310709554584590154400010241b108070700701201d000240c1c1c0c024a80420220f034504598 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 712151609 1250 712150359 712150363
    0x610061d06040320091b0f0d0e0d030e0106060504090902040603080a1205150102100e0f0d05031603061d130b0a091a0c09010c0212010606020d110a0209060603070e030708 75
    0x200d0a00c1c1e5920440081c0c0304c00344c80c0401c22140241c01c04601103000d04410aa010034680c0b1502c240901d00404010b146104146030040c1c404000312500079001c3c134122500003074140c800b08104c0714101e915190082c03014541050036a01504c441d010005080051440820000e219541004e0320110b008140380b00c82c603910134460b040000310108188500d44541001203000c0300409003040c0940c110921065912080368022a4000000e400329540312580700c1d026414080440e041c0c000050b800400c10110400401c0c034001044c1217440d040010030b1400b0310694003031030608103085050045401003a820000d40110021881d0024440030113400c0500001c401004981022510a107030140401d09009400c0c40040c410141c04003010f10340700707100d0011a0904004003080740d2140c104508419a83d0702449020040c00703064000701340d00e600c4400040c02e146003911540d0303d1030b4400800e84005803180740d211500100291a8640c0340e031074034001034940c0c41e584600701d901031140c01d800180345440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 712152859 1250 712151609 712151633
    0x528120b090c01050412020108090705130c0e060a0504181116110118060f0c080a0918020c0c090c09030d0806120601030203060610120e061005030610061d060403 71
    0xc484102c4412142040040d036107070046203d0488514203a002c45000355005500c8181d0000010050300d998a8680b4000703201404018002117800d0364940b52428003a07007060b110301c884403044070941c1c107000f903003200141140300f01d0140241900d0380f2440d2011800d4030350844400000000c1102d44c40e8580945189a902c010b203c060b01e44440d990503604055000e44100c0c4158080103810400352401e21784240e880d40d66984503841048204c031300b468041008030001c0e0681826513074440c0c0426261410508054101810174200a44108250b521381c14000410140050080c2c2c0c0c200609d65560030740c8030150144050464050049040a0114551002c2c04501c1208100d903900f0b9070301070201d00151345040c02d0100940542c01807011a400d0f18090020300100007451800006400f404a080f206540c0101c44107101d5511000074031882d0702c00340e480c0d540030f00000d500401075032a00303803103903125400c2c10f1081500340401c00050060360f5110000c81000603102902041e0350319940e1070400c0c02684 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 712154109 1250 712152859 712152871
    0xc030a0e010801120c03120c15090b1609290d0c03060b0f04092a0915080c0d050a110c0a140309060409020c0a020a0e16090528120b 58
    0xb94100046820f40410090541d16a004485140050706542d1019507407002080c2c183c5c20b000a00e90011300241214402e212070540d825000b08040403036192441000704050440007070300304851502000c0d1640a025001251041c4808981300c040144c0724003d110a400e040c0708072a41d00140580ea05030254114181d20302403590100407140e90b460058440340a0003254618071501044100704c860020380184041c1103c2d0701c59aa070a4030b14a15145a02c2d1802d8100e802045d50018104412003651103e0752010301c15090441140c80c0483d00d44581d88101744111080580d01e40c04a01518485c1c1d024010180c03246040d07542e84c03c400328500d0383d200041401291070400002c1c00d15441200841a24901b04003e00308a003800c1c10007840401940089089c00c185120314205c0d00091f0307960310700260041402501103042c2c0d0a0080864001c01c00e421031010030300445060802054440c003c910301c1a4900c01001c494203d81c15120100c41c90300d5906c0f0420040f6100042800c0c0b10711080c259008074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 712155359 1250 712154109 712154117
    0x190303200d0905061515030408042706120f0204050702211b030c0606010c060f020f030a15050306160201140705041d040302070b0d0b0a35060406110c030a0e01 70
    0x1d13070f40d041c55090080721701d0205908181070001181d1102e00d50000ba58026108441050030640c59483e101c039101d0312a0180401c45050780c400208045441c800c007070250080c0e20b405140403416441c2c0510f800c8291070700900840e039400008180c18403c1c0310341c0507002e500542e0014204101e0f04d0f00d204680050315180c0503d04180141e0108950010072078085803031510140c00c2c50342c0d0744001910f000d04d010005460080c1c940c11280640b80407403000389004022172100d29140d0510030340d500121401a0081c00c070795110b112090000ea40d000803450340c0407000c603400e0078810b24110b5040f07000d0160301c03040348029501c44052280807600f2070090810b613581c400502604400c200f4010100740003d880140160f0081c6a0a000301c20b40c0f07000804490b0440100070850070700c1400410f9804569030f0144010791450241c61251400179210040c40c58403080724001128100c0303c0941e1034141c050320040c0030554807840e102112144000782c40c049081903007620740312080c1e4100030349890100a00ca500003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 712156609 1250 712155359 712155361
    0x3040f06090215191106010603200a0206040c0b0309070b03070314010801060305210301090c031b08060f120c0d02010201090f030804120f0219030e1c02030c0102190303200d090506 79
    0x3d6100c1ca200d4482172445000800d4140d02c0c04509600a180081811940030b441481e10808405081c0080c000c079651030307006025928040c10305600709440d5800010010000f042030161000000808030241c0f169001c1095980d00d030428140e00401605540d1400e0b9050440002100401940030342e08590181083d1040e40c035950340d92444000c41401c0300e0322560b2046c0010301808185500002c00c149081c14001246a0300000c4046440c1d15030054a0020340035004100ac1403c00000300050042c3c00d894004031910a04d02c4903440e21900507047e03004882070350003034065a200350030054401c0c0c3c1040707812a0003da6824002c01c0c0100465094501d50488424022410b105108500e04410b2513806001807020943d0301c0c06072350201060035010415030b8404203400d0307580c1d40941c24205a9956040e4540031043c410705041420421803941950003078241d502650b03108403200c031187e55051400107a2030040354204101c940706065425013010020481e20100c903101d41c40213241130f010700101c441d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 712157859 1250 712156609 712156657
    0x6160c0503010f0b0901120201020c0d12031b02070302010810030b070206040b070e090103112209110303070206030619030b0c0705100605010e1002010e0303090d0f0804020603040f06090215 83
    0x60304c14004615800190101c01041a0004180501c288030310520580360021303084c0c40041d520303242440381070715140401003410700080d40520414032450b006c281d2030303d81f20761880340280d122082444041c1c107005407000020020000809400040c590000c042c4495084c01a0000d50f41d50741102e00304c0c0c01107009404104218020365040128900080c0803950680c2140d8926412030049074a45030404034002c442d02804c146070140559155429000040c1d4142d10305107902d20300d4140610394001e40080240701c0140c4c0303910085950007001036812111290b480300d103070300101060b40d0015140e4068002840108544c031401450414000d03000c94003078142980c1440c007100d0261281d240450001c203400c410b5804e00c1c5490b111181c0c540e000000384030b403507145213038215402200c82034000d4000d40e000d00155600318071545003140061809070000c1c5401d6020902d188409070024010061404041c410014a07801c5401819409030600b0180c00c680321000c0b103070340c20441d5600d03c082c10000c08122 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 712159109 1250 712157859 712157861
    0xb0c0f160807060c0b0601050c1614010e04022a12070c050109150e19120f031e0e220f14090109110f01021212040308060f06070b0606160c0503010f 65
    0x29904d038011410001c80d80b0b8100041d1103540c440c0d280074549001d41c44c01c0b500c000c407000356488010300700110034003601c001e000f00050180b041031651912941c41803003040440115201c5400d81210b4031040c060001001d4148549130000a102100c40480009175000800020b02124000c0700c1c4280c0791005000c1c2c442100403601002c071144040000c029055030074981c68284e8403005921031401d03040d00d0494645601a001c01141e420560307821120700400010981d212802d10329040c500c0f004a1480b00e81d00d00d0081042106c85601c6204480c4500000c40d40220440c42145200900c071040081038005100f0340c1c0605041c0f040c0a00c0d0000c110005000c000040c0102c0880e50b40c0000740c140560465003c0000140c500718215046200c1c040764052940003060042c080011010640c040f00c1ca45850002d04208000b820740340142c421580c00241512442d0540c1e5406078031980f0b500e40ca076a0b07440400c80e1801a0050008075464008108040c071030302d10843d10907100c00790000c3c45040c610182130343c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 712160359 1250 712159109 712159127
    0x7090506060403030827030412150e061305011e0f0b04060b0f070606050a080f2b05030403022d10021317030403050a03030c021c02070b0c0f16080706 66
    0x940032400a800041012640c07540c6e80c28035103e6403032440140c00c500f40e201441c40d0004d8104140c207401091042e000d0105091104948c121800402d01403d044401d0b00303600c415024042c40700400d0902404000c2210030740184040d01691003009400c0400748001c1e40140c0aa0f100c001c903c145440c80602c1141464010127095414030b804842c90443e14842c024006d82c402803043d124140d4034400807078680e0742c0740f4a0f00300800552000b003010814501005040a0071441401041e00b0b01a8180c0c581d0103103100500303440421803c1060b20707682c9909007070742060030000c294488114200440880300c01074440b04c06d11a40102c1c115107640d81c0c0c900c042c00813803045c18664810186891000c01403e82406c0d094071600c6040790580c0e05040c1c0e02e6948503e405080c040071000b00e6100c1d05400c50311581085214651444464100040c2010120181d203480702070040e1002c124000801d43c034070a00030004010880c0280088a01c901015085010108505d0140c0065800790000028106124111403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 712161609 1250 712160359 712160363
    0x80319120c260f071206051903020a0e04030804080706020909010b03070201060803090303190912110f0409150c110304150f020703030e041a061b120c10050403170907090506060403 79
    0x800010b1300e9450003512a0300c043d2048141240d10b6800221300c44c0c0b14441c00840c10341d00701e401d03511003606510400050280642121104980321003c2102003548002c449411070340010085540300c03c81d0801c04c010344105c6c64010303005000500001080b0701d034080110311a03502c0354000c0010315110f0031486c1c2c0b80d2268900c804d600d030b80280b10265010701d5555040d0f070122500d040c40c207284e42d07980c1884e2024900c80d41c0295400d43c42e00e00c8045060612083e14124490111000c12000840d5902d0350702d42c01505006003071a41d99281c08060150050500f4680d444280084a03191a616021583c88080740e062480028000300341c0d00c07404500014010b0700b9282c0c5600c60b0f40d21806842d00703220044c0482440b019601007084e1000d4256116480140007251900d60820782c0b860302d03c50300178600341091a40244011081002c01d09410010a001d0880348445501080702c1c0c40b035080880c1e1882036020180190000c04003400314100d0700140040031209110402e1000d81d60303040400c480c50003503102c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 712162859 1250 712161609 712161631
    0x3090603110a14130e150f010503010320040e0102070b0a0b0d020a0312020316060e0d0813080318010c09030302010e19080903071806030501060906080319120c26 71
    0x1060340303050b0200c002e822900440480c034108144d4550b00b80e00740217402d84805003d600581d241041c0d504081c4284540140c082c24110f1a55155070b40f0708118201c8803440d145240e034480d49400041d40c50b9000030f040031200000075500d035411403c014403a01c03003d5a096401d545889039110f40c5d070805000d4603042070b03002000441400e1550710b8015910118001c1042140010009000c2100f00451007a80c2240240c02c00100034520190715481c04a5807287c40c42030250362001c0200d440d45c908880094664040107042d125140c1041207018070900c103003946259400c1410b80c0302c5203a400107407901268003907402070103000340402e00c590315503502c803000480c0007084003d030601003038803480108200314001d4121141166540d08400900b042d10343d0002da5903846035810807e0200901408000c4c00211170704000c61481c01c100d0503075a20856562100d00c0400d0845020400e00a45c000c00b14814455018003960200c40070042c50307000c41e030780c040500010b100001089041c8050b84580300b1141812 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 712164109 1250 712162859 712162877
    0xa210206030c0409050f040210030b030d11010906060b0705100504031b02120a150b0901080a11011b2907020a030305060d020a0f0905180c012a03090603110a 69
    0xa00c541644020840d0081401c10080000c01980d84c0c031800744100701941c03007a0301500340f0b441044125909900d2504c00c050805240c054a60b038085058404101c1f1410201c62a07840390151501506ca48100505070610704100084c414840744020000c0b0303440341094031107021150611030212042510050000344507125080b038518079002007801550b0000704004c0c0c2c00301d40302c1c03201c51420406450840385c00e40d4009810084090a00511000090480e403200d040d604106c021503454202040180c95082e4603655103984c0c1c1d010f051083d00121162007040030a1143d4100744040d20340754041c01401c2c07525495a9000f48925551076400b83d4210b034040e01d046101c6440403005840d010f050680e0000d180c00c2942c00680c0d954845da401030101d2580d400361186010a0b003001ca50000f48000c28041c07108204844041c0b021880315861242401c01c2d5405801a0300c05450100c01c0c1c0d12200000758070000000d013851b4000d04440e0448080d07940034446102d80c00303800900b90090f00c011a0104514031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 712165359 1250 712164109 712164113
    0x81606021005280905071418040c050a080f060703060b0904091103150f0c0412140c150c010b1e040906020c0a031d06070c1e03120e0a21 60
    0x600b0030b54100c0035a205001d249000c200d032035880c0b490054190f0031040d50341d2201c14204403060250390010004441e02c02e4a500003100441c0c660710041b0140c8804646540c0002d04000c2800c2c140710291002030700b0b28824030f40b83c0321000c0d582c03108010300c0b085500c14240051941c9103e03004080503a541005403e0a0400c08410b10000d0140c10004854100e030342011603580d0f0300e0820030030504191f030703850320103540c24600c4007102c107654042d240540d01da504100602018031088210314200d0384c01103424010804010580c0d040c4440c13000a158420008004180354418010251070328203050790080240301e01c00f004102c205040c1e002882c9142183c00040f14a52500350b200490203400303101e01516243c04074581c542049031606d81100840c03400385c07403030f0106042c0c2c07040541c0d0b41030152005c52800c001031301c840e500c0f04590f21039400700e11060030001030351902c00c609100042d5031010003064900941d01c80a003000d140307604003030b0003a580d01360005003818080b100210102c28913203031004100c0e015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 712166609 1250 712165359 712165361
    0x1805180a15111c09020a0305010507050d0605060307210b21010e0c0a05061615052a0403060c0c0c060509030f03040e131a04060209040b0f01080c310816060210 70
    0x22841c1a64441b5420000101003102030084510031006541e80d035176603a0769080800e04a0301260080e50280d0303014401c001440380c021054114004103c502000704441500c5660017400b0307900c4800f600503800e140c090080c2140f44401350241c0900d13030020b01c02c0300300002459540740054894154054074000081100d420454004e00040301e40f110503402003699900c484000d035070090000d665182c2d8510801c10100c48802451540000c80010000d9a00d80c10b001d604039401540400f524256690050f0b5801c0e0303015003540700030740e5400044000d0361561040040d1054100c8002c0ca80680a03200100c40d0808003c02101c05540d1440c0703075080c0035200e503039651825024040d000c50702078880841c10014480004000d81c41140318103070140c0c2da0340740705050009823200406118010102540c1000040e0380000100f980034950100260b100c1030040ca0807032400c103400405003101341c10001046002d2301c83c2e01128050b580414205e03045410ba45500d0004000d6510a80e00160407c0701c801942c01e0301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 712167859 1250 712166609 712166621
    0x70201120e21040e0114010e010203030403080c030c070f151104030c1a0f0c1c0804020f040c050d0903020a0c05011e03020715060909021206011805180a15111c 70
    0x2107240e00703e0a20780c892615446915007a0060340401c1404094000d003903901601180d1140b90a00c091810360516940240c0700400140200c15102c1c004030004141c00400c00c16204910f41080e030107030b06002c15080000c11200c40c66500c1a00e5420804100486445001104e00301d90f4440d602d100d94a00e440002d8100c0d000c8000303210025413041200c110740c3c1c5402000307084400e0007103010304400040c900e01d08000d885c80c20444418441d0f00020000903a44000b039074141040181d40105001030111000c032040d03c5105003001c034032480c041401060542c001400302415208000000b0303c148c03507400548030541202070751712800d90b0300041292218400d0b0060030a242c0b044080b60480e80c02d042c84142034441c1c54014120b540c0e5580c5000055160425109c803080900401510310381d414103c00b45031f00c1001c2d580083c4a5501c0d030020510800b9030640d22119081c461098407000c0041c1d141c0014014015650900b2907800c246400d01049058011610003515629542c4481c00b200c0a08101406d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 712169109 1250 712167859 712167913
    0x2030a080406150b0a11010b0a060e0a090203090a02010e03150103140c150c060a0c0909090f08030108031e09010822051e0d0305040f0b0c0d06080102070201120e 71
    0x2482d0681c3d1120022407003003840181c5100806a0741320200c0e180020041c0c004400c58460aa04014014030b0a80b142c0003040150785582c5000c6002c1c22103840850050001a0b106541d21032000003081004d007030201c5c900c440035100344e842e44d442911400825580c0e181003201103030a414141c00410015904c50791440c581d001003020f441614981c040002c0c80701c0c0c0e90101c1c541c12a4000942032001103c28464554040010002085841507011004002d0101802070100c100c1d0b40e002d1117024800e00d10000b280e80f50f4800e540c5580c070742c0c480003035580769081003800f103d40c0d4003401c41100081c1100c07825103034041c02c10b944d950b1481c0e03540d407890f0418810381a000f0011910352030b05d090205030b00b40304404010020b0202d0400c80c00440080d01c0c5840d05201c4810100351034001804000b40390210107a1800390003610444041d01c542201c0500c130711a080c002106149888400191a00d040d005452654001d88511a1510811b8001d07416245100c05d141d00503003200d01005080d11600305400c620390 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 712170359 1250 712169109 712169111
    0x120d05100b1c140f0408160816061401080d082205010501320402181201230c03040303110903190b0a02040602060711100f020304050d020c0102030a080406 68
    0x660700c4100c0c000702e501001e550486881e65014410052030310740074071841480031011070141480c09011000d038885001d4001003002c000000d090310210907400103004100d410a00c9107030354000860243e5420202c4490880e000743c140219030301c4000340c0d0071055049420700c01c0582801300289104850642c2e00600780c440c14449000e042401c02130051380c2c00c560602c51000019554100300741340030000c40301161103002c03031003698103101c1c000700828801c01e0988040e1070160704c5840c00d10308660345100d0001001e420501c1d0f031003080c601450541288603004c0c182d011041e046403c02c2d422541004048030800c01ca00340c20030214001900c01d82c80b4002e4041c103d020941406911000030781806d40e1040c00326080707126000c04005002070600d0a0390048481c039401c5241504c0c064019445000040014041c040c1d59460b0725030145003805458000302d01407004214006400440c240203410a07a0b090315248201c4da803d0030000e000145400309228140c0045003008061142290309100c0104211205 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 712171609 1250 712170359 712170391
    0x5041e0909060e0c03030a270306020c100b150f07020d060510030b22030c05010615050417070b0d09140105130b1e0403030f2004090e120d05 62
    0x19080c42107840651048001042c142c1520380c82c90f1a00c03418a81c600d10a41080014118842d0030121038840341d00c00b01e54003107102c4840040d1350345015041d0300241c905800002c0903401004042003807c80d09840d80d03004c00c544d98420080c012080e000072100041e00004000c007102145805003d8241144004c010040790342041d80d40c882a030308141e861300da548100324002c0c4200140c0003100faa20010f1000030002c50380104d424940d050003001c20150a00c05007400b80c0701030160a400c1540605080c0341a001051032842005007150b100d48100381c18802001c005405414001c56a60103d070300704010a0704054600003507000402c0000c07811101c0b0050780d034680c00015001c3c0240c038452412003a00c40b401207030318142130100703440041020104502100024001035602040c0342d40294052500007411003000c800c0100624880c115076020302c2082e000c61008116200041050f80d01c6143d0070300c0210b80c0c0b1800c0651740d000800d034444100b241403201c0d407015040c55204a610040f03040700c407040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 712172859 1250 712171609 712171619
    0x6040c23040603050606030c1e09061302040f0302090901140708060315100f050a030c090c0c02030604051c030e07091a0612061903051b04060f08060a05061005041e 72
    0x2c84481c1d80c42100c094012104000075840d0600c041d01820303c041d10a0f00410788a42034104114200074082441060b0381c01c0880c070540c455586414800e502c0220465403103884900c1c3c20b0401065200803841340d070302d01000031003042c0107024075561107440a011344c0d40744c0c030f941e0b8040d2203485005003c00c0d018803415000c0390003c130603041054090300c12040e02e0742c1080d090070301c060200642c90300118014a2030100420000780c0e0402040120b82c1c80d080001101ea03520041240d01503005030020f9458401e0000b80402d2004c0441c08a4041307030f4503413481036100c001c1c00c0d0a80c10350300144101c1029410101c010072010400e50005071200901502203e02c1a071158006041500080c958254240001003080500d092103034a44003003001803204c44210502d0750f9101a034a8005400f21a000c0100180100054a41d0703000305000c0c122102c00d964085440d002c101d030340d070841240e00502e03280c141000b04d04c190512003520b184800c4280d450700e1a050910b41294900740341140d141048409030100010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 712174109 1250 712172859 712172861
    0x601050d020711040c17130c030804030506090c091522060f0303020f12090d140105160207120209011502030f0d0e0105150109090c02012009011106040c2304 69
    0x220107200d8181041c0c1003000d0414002203c07035511205c1c00780f2086c203030641607581501d0700003580076201c2c201318401d40440d03207485106556182c7c001002c0707400115001c0708102c408120b1600c50a1100f003101c0f6201203a01c1044203140051b41d0179651055603d00071001420640740c0e0902c40501521800e03400065000c102c0c04448180c2c0c007811406840a83c14410198188803c100c00c905a0300100000c0a000e020b1001510800b03038101d2051032440a41010464102d82114000070b2980c000c100c0c0d881c00f90180490804c41e803400c0c00045c000d8441c0401d004500501a2404070b80152080304942e00b400d10301c0003c160b003101504154071060001082e90316122004140c4003901440100359203403007040301c9003903401c0a000800e0b107004100c039010299a00c0300c14682207a5030008041190140c0a509a006054585016082c00460074590312285014002030240301405e981d0f694181941210301901c81c0f03000e95000307014441c8070808100c3e00007491242091401490b20540080c0c8038140014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 712175359 1250 712174109 712174117
    0x305040210050c01110c0c150414040b0f030d030507090b0f0a030e0f0610061d1e0a0308070b0105091015030f0e0303091b01021209040509030f0d0e070501030209090604050601050d02 80
    0x6a1030f4072a02c9000303412304203c6003401c3d8030002c40742240d050608080c2c50044000d80c014485026640d47c5001c9483d542d58885045030b410009000d441070188201d100402400e010ce422a0115200d40d00004118041008030740382140300b0341d655804d020700c9440c11000b91190300c041281d0782c4501008441440020f0060f10700131036000041ca0659881e05c14081d02c0303082034205e280c0d011a0400d600603950f44413041c03c4410803c04585015014808000240c40040c8541000e008000c011a401e401c00030762078001e5060300c104444082c026030382e20590800a0965024910200e0740d08543c010116001c1d070090001421030740c0303000c40d400741d050034900d16580040350145c040d544580001c1c0c200100042c0e4101080070300313201520094207a10041e076000c0c0300d00c6900e00e0045a8410002d014102c0070310035240000c0800500d030382e07281003a45007100600402000c804c0180600d0400143c95806442291220390b4040c105122564400341040000d003401890030f4180001003102c1c0c0004401d0340300034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 712176609 1250 712175359 712175377
    0x2150c100902030c010c030e010e0102030d11090f04111b010603140a020f03070b0f03100801110a08060913081c050705130509040503040e0702010618050a0c0305040210050c0111 78
    0x4808009004242c60003130924111814040c0d00316540000c21707404001910885028200300c0c05011800004178510310404026802c40340c6846102001c0b0700f94030006243d040001c50781400c010311801d0030882203552140e804080703203d0400c440d40191a00040060036212070000004001e50b59454000000440c1c200108017500107018242c01c44c038001d8000b210b00038054000308050307410110484cc04c3e00c240c88031454601000301c0040c105201115041e07029001000090001d52008042c1c001603030009400391000c0780070400003c1450412030056403243c041c0c6a842c41900000d600d40340b1240d400101d0f030071280c16202062841c80c9026000c0c00d8052469551025a07a00f01414010b52005054002600c640e42603018040401c6d00002a9404d480b40b5080650044e10b030220309a00400745035000c2401502e0f15090064003210740e500c00351140642c188107000300500300c1411000c69400b01c3d00250b010403c100c00c00c10b590b200c0c00c0a01288210100000f81100844001d400304d03400581d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 712177859 1250 712176609 712176611
    0x506030709091505060d02090303040909080a110f0a0602071a151003090537060f0f0e0709050c1c020c010e03160f0317040501050f09070b0702150c10 66
    0x1004030300c0e040e00c07030400100c00001d20f50b07040b41c0c00c200000b129032150f032000d0000c1640124101d06144e5082c02290003c0c1039480081081000c603140c141041d4009102c0d00003c9a010f601e05290f054000c101074090403019009440050003d40d10315000750000070fc10384a101500e02c01847d846060f40600340103400e0b00048244a41c5071000704050030080010443c2058148041200055800a009172801c008000445000d42040e01803495600201c15207185500b4070302e10040911065900402c4441040c803028018810708509203c180e411000d81d1100551104d24208804241580159048010f03a12a1440d02d200902180100c04200001004440e0b00040e88001034009100d40d4040c002100040c60034000034102503044841c10320f01c0078000e4140b0201c16820188104440c0722000d171070407580181c6061605115000b0001100ea140300540d019000c17818002c4001101c0086510000d0b030141ba2403100ea090003080032102901c0c1200d8081072002c001c02c0e140070f04ca040d8245024800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 712179109 1250 712177859 712177877
    0xe060d1a0a2c0115050d0803040609020306152b0b041401020f13050f060d020307140f0c061503101503020d1b06030213210b0112050f0102131203020705060307 70
    0xc802c0f0708440200c002c000c1251140c600400c002c0c1c0700d100c1d13500c50303058011006a45a64503402d03c10084c1202180003036050241c5420061803c8610444100405068801d4600c1841c402902d0120040c6030511120b0b81e0b03007080c00d080000700840c40150340b0070b1003547d05400349000040070700c4c26a0000c203e50103100b800030401c8001129240d000d50000d0008444509803860304d10040741091007070741c10b4100f14540000001d900d06005541000c41201181d4502d50380b041e41c25003081d2250420b207071a4001d800307694040780d0344400c044d00d014503464009000d407501c050145500f200170729540088203140e030140c2400001682c6c4841c00d14034440e000d800307201c0c907100d81200c643c180c14080f504201e0a01d881402a0700c843c0541c001d40340e00384d0b05c10303071440020299881d0764a0b62038484c8a070010041c00384000049085201100c200614a2090341290080001c40c06010b090340035038814000b1000c20070100b003007140350340c41d00f0550301c0c0e00900580c0d074084e0700c3e000880c0ca035134000c0711075501068101c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712180359 1250 712179109 712179191
    0xa060e330a030e0c06160f080703050304060b0a300b010605070510060303050f091903110307080111032a0a180510170a0b12070e060d1a0a 61
    0xf005500103100303080003804400c81a000081c0007070090b110760382d01a201e405000000c1059424461410076002010f4139100e0b09549001000f90b8800c8408460310340c1002d0707042c000c40c101030411100342d03a00c09100507280711561150104501d8002c0001506440381d4408502003045403100c140a04800c7e41c03000e07552030040c140545820002c4a40002e12864000d040001c0b0398410282c4001480c241180c0f0765804032040090800081841ea41070b1990800300004100301c2803050381e9050180641c10380b1034036507580200300d08030382740b02c40c0b00c1210003030400009000060740741020303c83d4500843c0000c5040000030301c10301c43c0d8100400d44800318000c04222004224501b404400a2104840c00390f1503c0500400910000aa80d003040d9842c620034003040e800902908804e0f88150040c0c000802c285050400c5a85d4400781c0c854440501070305008038120341000d62544800070f4208841ca0016240c1000700c45c5014001041c4d5034405d65a526080700541c444001d900d03400359000f20f2005114040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712181609 1250 712180359 712180361
    0x506030f040b06030f03030403030f06080d090920030c030403090305120a021209062a0f1c0507021804030201020702040204290a021209040608010c09090b0a060e330a03 74
    0x5444644a984841d0285c00c200d82c00000320b80d402507040c603000c6601c0c0c1132002c41c20f01810480c1c000041c180a54004500300035407007013440c0704480400005103c00341d801e2038603100c0f2060344100440c0a400410004450b06140802550414424501001e00d02e42d6900d5031414a0041c40210f120b007440002c13611000303a41000504040b18400b1010b500d41285030f00041c0c003e12034a030030319180f80101d81e000024060241c405c2069101c021054600c500e24111800c1d4844102c040300ca842c0300c0240e980215918410000d03124200e5000c0e1038014201c0858442c01e0b40014000c0c0120115034080003c2d10045e1118001380c8020554a1000e00038529103444051240078821400f0060100600900d1070483d40011420009102c08000b00d54469681001c640600025080783e100c560030300d40c580ca00140c1c000c1c0c20f2003c4403035000301041020138403020040252201e01c548400140d2903102203c0c286002c4185404c402c0f5408000a00412a030f000480d100001c2030b21407142110100f9a03080c42501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712182859 1250 712181609 712181611
    0x40510120c17040204090204091211120406050f070f06060b03042603221202030a09140f13090501150612090f08130e0906100e0403270506030f040b 65
    0x501d041582181050b400c0c409500c01c0c00900c081c2c0710356107030201041075445a502104406801080445003100f82c990040c081a0700c4c0300b03800519126000140e0114012030050720183da80640c0c403e403801854001d04c006680203000c055540341c401c2108000010700b240700310700007003c4c0100a180c580c9400e007000880d05c8003250b000c3c011115040360284c0e0030025081141c1c0d008219840e07520100500d8240300d202c91000c0d81d4000c2c00701024820443d51190000302070642c3c69403039552460403c1c2c94040d484074910310510b4050704000103005180f52032404645403d801d208618001690ba402a201d15007556945044c030306240000340703024012560310085980d500303105282c090180c0744890346c0b64031881c0c0c0c07005c1010386443e4011032a45d01c1540d0750720f103182c000e0401092140712410031070502919080146c5402038544440c903000106403205210700c40c444d542503200c1d0f01c24201a1000000f140d010302d452020340914001c0c001c540c40d55420003031400388240440648143c946440e10f0904010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712184109 1250 712182859 712182881
    0x1d03030a060f0803130902030a0b15180d0b240409031e11060408070f0209010806061003050915060a0510030f0e010603020901090c0903170c210405011404051012 71
    0x810400c01010218805c0000102e0b110141c0040e9a9034509c0c0c08074008054008051394854102d00c0c0d405481e5522101514110703000440690811078820b04200804003400c1e00140002003060001d80303501c00008050f880028002e881041c00d03030b0f800000504692544c2c4c81100821210741200c0d000c8441c11008101511007030900021000d40058515920000200024410007000a442c000c010800d000c80071400d5010304240705550315001402d86640003100d49a002e4150b4600410602d80302c5d010310341c002d0b007003007000d480f08141e03010000300c42c44002049c0a401c42c41d074100010381520303142003021440c0360a50b4006850040c0c0d900c880180d901840441551380c1c14400c083c005a0346082c20241100d01e40d00e0002810021141d013580d421060348d1010b8041c0421820004221001000401b64000210151810900340e4540300759020b00143c038401e502030381440107010075400303605040c40f052071407000342c0d0038140d44200203004030035000004000a0409000c2c0303215800e6034000c02d45188 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712185359 1250 712184109 712184113
    0xa0e10060504060507021306090513050c100f0f2c0307080a0b06061308031603112802040e1c0909050702060f040204020c0a03081503010b0d02041d03030a060f08 71
    0x549410701c018131602503004040e10800c52418011020b130916401301d801091090002d008501e88002c00700e9000000100035642400354104000c0c180c60003078000b000041854551489a54030f45004032078200f1074031050340511031081d559500782c510801e40800748406000c0081101c11601081c9030900c2c00b25031219201780e00440701d00000580c4140703410b41c000c030107403107150302c0e2011080442c0c10340c00b45d0741c848207103400002940881e550315040f0f1900002e00989884404c0c144841e14903640c0c03c81804526854500c45040841c00300d12521010142400200007003117204d80c40704a036003440c204c444020580c15104d0301000e080360b00140250020445201c003001a450a008080e44400300142500c0220001d807001031300b15502c50303055030400a0108100e1b103c031080f510b8094551103080d100e101e04a6110b031060001840c05000d10070705100081d200d492034182c15400d100240a84284900e0740c224030030b0f06515800003c1000c1c502c02c0742c0c030441c045002e07440c2440b410040111508004425 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712186609 1250 712185359 712185367
    0x306180f1b290901050f040f1508060d02040c02010b06120106020d0203031e0601120207061a041119170f040c09020405012115030f1106030f04060207110a0e100605 72
    0x1842c03100340c000306440d01c0407607540354428001202c0d144145440b03501d490602003008500712050281c4c4a040c7d40810110100d55001e400082d0b81d8050221005030340440310384070020050030319800c104000145400041601036083e00010300d65006818111100c1350400010012241c1c1003095400c198280c1c0040d500e1410842002c90500303240c803200700c084100c0c100c00320710141d1262080c10300369160780c40c1c115103505481c504034001d0f01a442484e42d00c001929804d11607407815104106280b14180740b0030749000448015814a01d031008612001d00c111400d03085c84980b4880146440740d001400045558a01480c1080c68100f02e034100b01c0b0904c0c4140428000e69801280c60589104148a1a80144048105174011b001452805000714841175400810421040089101030340300c0d80318145150300c2c11080c00741600040311840303c50460302000c2004a0500e5000303002c2103014640141c000311008011820010325540803019101c0c6c0001044980d2202480038800780505180003464 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712187859 1250 712186609 712186649
    0x414040305120709150806010315080a0b130605090304091118091305030a0e031504030207050118090c0507050c090103020a0504021c050108030702010f05040b03010306180f1b 77
    0x41e4010051110384a01600c0301040c1d400e03001d051940c004100c1e00202c030700b440e461940300410088068440901090401411201119200c00d40e601514140320082c182c64103103443d9000300c11006072215201c0c0c02d000c14500041581802580d02c503486901c01150780e2440e1400d11000c5580259403c01c8000003030001e1400c0b100b8048000e0181d4404558034813954032100110f0f60030308000c0100810034480020f070141003580280c8003047c010700440542d02c0d400340b950242101108101e0703004005800c1444103100940c05040300102030b01003150028080c94407001080112281c01e00201d01040c0d021450310108401000310aa020105503482070480d451940480c4014220740509841a90003007440c0008000d2a407244001108401040c00300307503520b6031150b0300d80d44000d80c141d0006040130000300200307001c0c41c201c0307044480000c08945143c0c03950700c89a00030720240038900300001c80c4912030743c081400c26500c840107601524100e07400044c0c9406034450101c1581c08400d03d0b402401302045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712189109 1250 712187859 712187867
    0xb09100614010e060c0105040506070908070f05040e10020406020303010e0c0a0e040b03101104050406080313034706040c02101505030715030b01031a010c060f11030604140403 77
    0x8207082080c00c3c1080f514100c800050994001d40c1ca81d45210341c604010401030280016615004203070035201c60300c1a5072503e07030342920384029014210745e1041d02c000170802030806501108481c00b07070703b017a40c0d9007400b401c2168090f81c0c03056001c14010b03440400107001c241c0c0180d05494108031031200a0b4602801c00740d001c0c005a001020382c0d40300c1c0355507841040e40d42d18140410200e0305400e036020821100b1a0302c0d91100c0d90804e003d12400340d880d0550100d0220700c00011110300702c204102d083d48961070350b0340f6105203064409040c0480640c115045c03100b05940c5182c0d11219948403074800611116800c40714605070000c210134810f60802c550151200c2c0c02060360384d128800b0341400315200b61a40001d90300c0c0280e40e8401c2e6014451800005484204156503aa4101c05a40c0500c20728034000011020b8400414880c0d0141c2501d42c0030240a6004100c0210390038481d07000403440e4a401d10b0b0f890100d4050900003200a4030001c10041603182c03520a44180390b5803034038400014281a18000c4c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712190359 1250 712189109 712189139
    0x1050a0602150703021603050c1c0c1410060b0306040b01050f070b06210d1803080301051011030309010e01051f051e0607060f0e06062803050a0b091006 67
    0x20b5031000c00b07901080d00c1034400c0c0c04842e40540e00c0c07240034071a0011454002c040750b002c000401c0c1d65000e020044440f0740600f0401c0c2d404119a940d0f012004101a1140b030700744000b4015134140b40c400c904c0e90003002001c500845009000d02c1c074049450745004002d22090b5051000c40303a04200c4100080c0e846d50307982000b5140c00d190441c245500541d03600700440c2e0320805410000d60040c44080c0620702e104070002d10005150455610030300c03440b800c41080c140d00307011804010420342040c00140110700300050950044842031800c03000d07100c814030030503080d6401a078010348a40d46a10303044a0042c400d000748c0390001102c910030780c3c100c041003d60701c088841d1030003064484c40740b000e90000f414400c124a00c0c0786d00002000c25a481d103140c40c0000c0200039443c414000c036410300c801165a42c0000ca0707000e100d1070700903180d00c40841812807221000041030710180035116403030b036022001c90400c010f110001ca03c13800c440552800e001c02d919240c920307542c20411070036040c04c20600907001504090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712191609 1250 712190359 712190383
    0x30807032726031f0b040e0117030406021f0f0504050f0d050c0a060e12030106030f051e0708060109180507030e06010b04060c030c200f101709070f0608070801050a0602 74
    0x4525510001d192040c1520051784a01c0c00c0740d0340818003140380304980f140a030413180031690300b810320720540050a480380628883d070000750300603a1407182c91082050301c041a81c0d0403507000103000b044010740d00c422201c00f03031401e64541e8000d61102103d05401c00001c0c2c0c4440207404c023542031036120710704981d4420b009500208941d4491842103400ca10820000c1600d1803148002500c130746c0c440790000e0003410164040c0303103800d04190200b504610042c20180100d01c1000f5201c0c0917075030342d038020b8500310b0002c5c00441c1085284040010f014225190100c0820042c01002c212410004030080641381000c002e403030190045001000380182d01c0045400303c031614185010004580d00742a2415000201e025000c4200c0d0341c007040b8810082c4040c0d00c4220400c44d0340380e0380c0105903401d011524400401c60030218019a40d101c00450b085040c0780c0d4004410803c4403000c1c1d40f1249660171003055036000341c0204440405001d00c0c1900718a03c3e501500c0c0582e0281c141d240781000c000e581c0c40d10440c031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712192859 1250 712191609 712191631
    0xd1a04151515090308030c07050d080601080a0515030102070809100801081f140a0c0908010c09030b0a18080c0d0507020607120207050a080c0310051303080703272603 73
    0x4480103d020728000c3e401580c1041d43c550f1286844070001d692a032148000721090b004040065000310b00174600d507070081c007069441503220340d180a1690000c12000c0e10a0011014a40703089000782c0e02400103041e054861003209071904100c409009012140c0e1861307906011207100144007001c4d000030451058804131440602000d86166140020000c40d240c030752100d0031100400c110b41c1d005030040c03541c0d5605981c40740603082d65046a0342c00c03601da140e8103000080710100f041001c02c1c10941025080300121000082440008801c800e403220208405c0b520040041075602c5400828414030480228506040380751489582c0040d40600c6403c20040442c210100d00a41080c400c103c018054038015000b80c5103182c175850015a1180200280d0b8420b104222002c0c400804074010a030181c4c112000030324614030a80ea058a00c800010302d40740030140e8900c2c10258100d0f040e140704081c0741035070f1400049170700d0600b009e0b55181408603115030001d2501c010241c0100c0782d80c0480754045602c1718 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712194109 1250 712192859 712192889
    0x60402030d1209060504030f02060a0b030709020f0c030a03090b1608070c14061f170c0114120408030105010f050304050c01113a020a0c05040b0d1a041515 68
    0x91450020b0481c054040c1c8005c0c5060100820181c002c88155002100764085444660328800340500759040008400d4040d0040c040400c03406000750003500e110031018500c20304008050340e01d01e03e1a0000e00714840001d40f00c8070007106000601d441980c00c000244a0b2081128039858064101e50001c0c04880400150070703508418413812280400f50001c004050342c0c6141007003025480040440380c0001308d207010232080007039509034031100e40755000e4512000d07101118040b80155020900000c002e812001c0800c01a0100528100028859440f8850040d280d5041c2000103110611030745a0b00306000d410800d0101250340003690032004102460020104110280014140074034108480300c883e501d0000c031a40d21002d2000d2276108641c5402010707010b551030b281260780703242000f40906940d0136403400703100318281a04142581305000d4401d10007047e8981d2074810850b907180e00351502603034071000e1004020001922840d25200003a083c07001c0081e00030100340c00c45451041301d0300812504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712195359 1250 712194109 712194137
    0x6080f0a080f1b010b1e03060f091c0302070302010b0a030f06090203010209030a060605040b091b250305071a01181d01061d0609070503010e070e2709060402030d 71
    0x45445030311802030510301003956182c0d858041c05c0b120105521031001c44002924003100c1288002d41440005c004000684490842450704080600071800900501c5260108210b6210385c24032034802d503940060340e6040505009007121424440c03d4030501205a0030001b0981c2d0103000c0b9001d03900100009015051440020b00900c40d041c106c54250094580d49024400c15900c4171080b144280c0e03050000e00c00310b03c20002800b00407030320b51013181d400c2007450448520300000361078443d462580b00c4080c5075003284440f001ca1141c1c0b0301107000030070026081c0100318a019880340c0c00c2c07000d030b00045950f504201a82d04582c1c01007042c01c20f8940d841300c1002c0c0711050050710140d4020010001c01c0100e4036411101c04541800c0350840e0f03109041404196107080051441d4490485a0340d000c5c1103034200780340012507220103440c9000b0401082654501540c0d000184584035014990005200314800b0f411464400010310182c03198101e0002c010150b10045200506404d1903d05040c4143c00780c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712196609 1250 712195359 712195387
    0xa1202040b030a0209041509061d071e0c0819030f1b03020a0203040509010311120f070611100c030f0c11030316121518020c0a0305030c1b01090606080f0a08 69
    0x444600c04481e20b00800048c0d00191640820300380c038445012101b0b903401c05284540e481805a17407050008960348400d07042424043c003441c4c50003060b480c5c5030403a0f40c59511036034904c0c3c001c0d010030010880085c0317410b0101c0341c26200b444985001541d0502c410003000100c1c100200c02070660034145900080d0a01105100340300320f5000e0003005007001504e50b120704207413400d42c0841c0c400074000d601030110030203e09000207100c810722034064000c0c05180e042c24030840d400350032001d00205034814540220722254031406420100031180d40c1c0000c40d0303d0411018000c2e99240f03403440041c40340c100e252108241d400b0040326400b450700d07411050320840d03145046034618495042120030518118039003072003001980c4100104c3d9501486025074203003002d6a50102c0c41403070248181039011500c02c10020380100e01951384204c42c01003050619249014000080003c2181e80340309940d940401010131007148212000b03080001c000340401010210507030350b80c01085402800701c404c08644503404001d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712197859 1250 712196609 712196621
    0x504051c09050306040503040326160213020a0305060103060510021b0d0c0308030f1b0304021e130605190b030c03060303130801021b1c05070f0f080a1202040b030a020904 75
    0x2025048408500d41401e206c2d031203410a000440300720407242450f84400c00362060b03c03001401400091450b125040d18056101001141c040741c100011040d005010750140c4003820102001d5140821289440c6000404070f48050304a079105042c40765800c1c0c007a950009604001c4c02030001d4490f005101c107000100c008202c020010040798045101100f0420b1440c040d41c0270b0b0135a400003414a8884500203043c3d90b062405100004005000040142c0b402c1e88956800d40b07008105501200b0148010814400740110500c40d00c5440c2d0a082042d801c11455010964241100c4000c400d414505180301612001d88070001c2c1c09004800300303071556810b0046a4181400e10000b00140b41d403480300d82d01035004114040c101824102c107000c0e40d0400401c0d130b400b944140101c8080440e400440a40e8140c000c24000c2d0f520310758000070740001994000084e03115500400c0880d8641c0a40200100840b10303004a41c8162030040c8010041003003440c00350380c3c1040d0009005604c07041d800c0301140042c80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712199109 1250 712197859 712197869
    0x503090a0b15100f08060a1d1314010e120f030105102f011a030c22111209300706290603060d0206070f05071d0108010504051c09 57
    0x4000800100c2240c1c02c0107a254034131010361100c21440c4d983d4001c2080013005889400c030754159400d1800317403040721041040c1c2e10a5015031581d8000e42c05440301038405607a4000e07002e0f0742c6c0d540d101c8954080020442d0050309407101a4003460b20310f1181c0080c40500040c0b08244c0101d03448000c00ca00b240c01540e0a1240d03030410f00c0040c01d40c0d405c2441d140c880300c50942ca840029461f0000207550305004110b0b604d102c0c3c1015009040901c166018840e03411003c0344041c100700c180503001505883c0034000c0d030f03041e01a809400c6440d2544990740c08c1c101d004c081c0110009910910b1030b1740c1410602a403a082e00c02015001d844411a0545034905038410304000800340c03840e089007285c44d942d080703031001404407400b003690034000c0c8860b06101d940e12064610b80e5000800c14012401464006d00408000384644116600001c2540d0b0302468404190000d80d180a038603035515078031508e01105c0c24014600c85000344914145521441e4403042031040048040035540c2001d410310b401881720100800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712200359 1250 712199109 712199119
    0x10e01021812100e0604061b021c090b0705070503011d061603110309060103030906020d12111c05060103050c071115210108070902030c0406030c0c0609030305060306070503090a0b15 80
    0x2034044901c5031105d004032130440e50f152414032518400481d0004442c05102681c0040451504081507500c044848111040800240d100041100c4007441c0250040710310900041a0b0319091008160030743c2e181c2441c5008040c1d07205001c03050514001035a5070000c2144003900740c2c48010380422405032405040081e4004400401d1180d540000581c8034100d82c02035640c2c0079000c0d1200000c0380c490001e00d4609002403400400c4070450800ca91141c0034083c0e515521a00c0c00b01030505001d00029000c20745a081580c0707104105c01075825000d1142c0c031541c00355280340b9205a43d0780d6800c1404075200382034002c1800341400090802c02e1405c40b028000300c429814050b0498106a0542070b03424010510b50340501440000d94108a00031b41e8016144003410605160414804400825182c51050100022100c00501050f041d105030050700340a5907010500d80303442c50500d490003002511354020490300300308101202c040480c41d041c6c05580801c0e007102d607032038171109540b100c26036850b11076000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712201609 1250 712200359 712200371
    0x91207080c120c0a020307051905210a0c06140a0906050d0b0418110a0305070b1c06090e160e0c280c052406090a0e070603020c010e0102181210 63
    0x125400060003d13000303100b201101d0b0a117440e4024841c02e04548070360009080c00ca880c09022501e0800e44d017100815400c48903a070310f4008442205e00c0c0621644046d03e01d004243c00c24040542e00503c800c0d1107800104c000391030305081b200020107000040c07080710104000421480204c950941020704c1012008205004002c44030348540c11904407940d049030003640060000d10903003011158102200e8100d006040180d14206540003198014103142d1070441c1e1706040d0040c0e51302144104005080140713400165051006080c51501e4903910040c1e81c0307521110300401040c0d90201c4200d80c04917029000540714108940802d0300d0022000809401c49850303d54808196407083c420b0a42a004d5811603281e02101302218030140c1c2465a02c1c01074030b81c2600040e4543c140011074540104d0314840c0060f50b034200e980e500d0300b4402c00e0b801030800260001b840c03412440c402d02403900c4500c00c6000071454584108904000c03040f1003d107550291240e03880503030340d060090144202c3c2e101804014041c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712202859 1250 712201609 712201627
    0xc0c050f07081005010e0a020304031b0606060e0108101a04080316020a0e0912090a03050d12050108010b1c06060e0c04030203121614120d0e06091207080c12 69
    0x568241d402854598800d00c0c0f91488003490901a0074121800304004c2203070b035180d03030030320300081e42c0028025820312002122a40d50100024140d140031401114005101406c000000704841c5502488a041001090502c80e401001c0050001200c20201415105030010b121451072030040d980b144079103000108001c0e0300d249a4070a06c07048144215040400d0719140d101000c1d0300c4605560a048590201c100c0080103812800241294074008140c00e030707543c0d81c0e035440b02d14082c1100b009400080241450386000c0c005401400e0152044000a1103c0580e0800ac90b000102407923800c0300c80132508620100744021a4825400740c01d00c1850706115113030150703412140b607001d0702c0220b00a120f1200102140a00502a81c8021184040e14082820281c4800d254079000350001c10342c9000744404080c18101010040c070802c440414007003541e810760304900d03042007001401c2c0199500034039124542d24442c003080702e0105034440321182d1140e28002c5120303c0c002c2d6480440132860400a20410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712204109 1250 712202859 712202863
    0x50424020c0d02120a050a0e04020307020a110a050d02090a060b0406230a0503070507050c1e0306060904020d02130e031602120a170703020f030d1d0c0604090c0c050f 73
    0x190001c50408488074412030300c000300d0f614905032040b03c683c0b10061020030640c0b4130680090046101e680b51400e000c0350a02d000604030f0748241e92103030150780009010400c001c074040080401060844140d0f0b509850a000b0481e441e40e40d0b40024420030360400052140007580e48090041c0a94203041030f250b0382c59080141501e0b2134156003843c5695a0340307050854800c1d010855032002000d035100b500b10384070300f03a00399501e4222050454460041c01c2141c00a615844801404140780c00700345000c1e48000e0b01418204500a03220602a018150410006d6103900900c40202030381650802c405200589403d00245250004040b55000015141552002107528040c0d410300031140a00f140c0700c00c503007150ba20525440002c00403030381020b096000307681c03420107020384500900690700c4503401400c0c001d05540c07010003405180d6a0303401500c001501500040d812048441c0020b1038410700e0400040e0841c000e81c4100b80300d65031211000301c00c0c1403041c103000c0e5040e0b602104540d040703401003244035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712205359 1250 712204109 712204117
    0x503180117070e06030a0e1204090f0603050303010608060102030c01050108150702011404080c03040306020d0203010f05180627040501091b061b06020708030901050f01060c1505042402 81
    0x3030014514142009001c1d81c410030003801101c1e251108043c200d0103806006060b00001c0000c40080c3e1340b8585001210020710007006440640103401c0d43d113504025030542118040810700000c03902d441c0c000e2000410000840c3d040d80d0709030805000301d99403c40102c0c0345211b480580c0682e542000b0000501c0c02d400914494a282c008054a10940d01d0302d500324200c854111250356503030810404500401c102e0401030903460174560a592405491381c407038a09a920881001c1c1405600200401500084001070409407404980c1c030350b170a6548062003002d8910140c00184208034951403145030807800c0340e25a244094049079003000c3d26150030003600030300c890381064401c4048501c050700010400200e040c10b598441d03c3d441052401e004029101c2c180d00c01046030016804c10210b00030030414400741d0f20032813412001242615000010818404069100006120150820310001141d00d12202000281a0f400203201d80d0381d8101400803624a80aa0640302c1c01e5400072072102540760020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712206609 1250 712205359 712205407
    0x909170a020714180402090604110a02030d14010308040915030c08030901090f050d080c2506030b040b0904080c0c1005040306060806101503020408010f0209010e0d110f0d0503 77
    0x503c0311480b480a10160003c200c84940041000e0310014005251004460f604140050310002d125070400f4882403280c1d000424041c00340c0e1000c18244104040c601400d0345c071002151000b0102d5265542c0e06905000741d014400d030190303d40c1c200491030f41d9030030b525074005d60300682d2418281e5a01c0c00c015481e175012080c65030006403441d0001c00c602d01d401102c0703c201c600c00341c0a071882e108580c9130f403051908240501443c40c0501c803420703c80b180540d2000c6441c18080408941585e01d028001b8040341e20409034030b4065800c25142550a40d142074100381d01030b810684180d56020040310b01d5050142c500d046030790000403c20443c95090f8043c01500030b6038441c103000c000b101e0300c800c403141d40d41c0d070202c8480103500740991050181c8201e84016120317071050790134098105905c0b03082c0f6030b00b501c0d000d8410656240c1d0201c1e030980b0541e40b02d03031005a88201aa400c090000d49a00c900300a140100d44a84c000c00d0103070300302d001603200c40000390700719500002582d0320303656004018030620307010040d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712207859 1250 712206609 712206629
    0x3120103110a08060c070213050f09071e0b0c01090204060b0309011d0a0228062309030d180519150f0215042f0a0603060b040909170a0207 61
    0x101c0d0607414100c800006661520000300380300d6486190200240d44020700481c1c1113002e0b0514841c00d406c290041ca8020610305200400519014406c5450328850741d20043c118007010948043d07094445002c14151451100055505c1d40000d1009016001031b940094000345030000018848821802030750080d156840240700313052940b51045001038410010801d9034120b4000c0c0c000615054071001039100c4101c1c003000c1020801d03902918019045d03840318020510b0141c0e0f00c5150741e0704601011400d04180d0000d81040303c0180829580c51050004800388401d03500307454411403131003448200806004000c060110300b42070903800c003034481d071080324108070704826040019401807110130300c1800582d00503c1080351000305900d030404003034010741d9810140d80140d85455440350f4940427150300d40d5440110220508280485149154802c134200340c40c1681c140070741000d501c00c4034110b035201c49000c110070081c0d0500001c0d5600803441d8044504002079035086094010680004882103407035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712209109 1250 712207859 712207883
    0x60408060f040618110915030f03070201030b04230901060f0b19030c1d0d0204050411090603030a0917100207030206070824040c021f06140a0b0a120e03120103 70
    0x46910400c011000020441c400d0071048042c1c50521b201e4107540311588a400d01c40030125078000c20b0420480160070b07242500001520340039035806000b582c0f1618401c4e181008250026a17803a1252a000c10266845e0440940401c0c60004250007040141800380503009580f691402002076030b030300003907401106071009030340303070700010b019108900543c4a0303601c03402d4400d10364082f5016450400e48401d90b004140c1450000036071a0380c07040d1441140304e030000c0d400c84003140e01040070b0b4582c0140310300e200c1d5004000340c4140542c03158100046541080e070b500ba030200c800c00700300d00700143d03414000d10703051021410034141a80025080e010b450580c5030001d580c4c03104420300e0302c02080236000c507010824140000c1941e04256010591940b02481501c01040080148100725036129540400e0541c4403202845500c11088501040b43c8044038040d23034941c81c02d01440c01c1809040b020200f070050b51030301f013090f1411542140f0500c00c054000e40b81e036001c0b2441494007000c030a000a03244091406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712210359 1250 712209109 712209131
    0xc12140705060702130204030c090204080f0a030f120b1302030f07020f1b0310060b0a020721030e0a171005070509130b010306031703043806060408060f0406 69
    0x108140c815030310080c2c0810300d010816001e0010302468041c00300c0c03640ea03003008000701060070324980310041d00c0104000350380c0e00d00d04021a440c040000d680c0711070980004c0b2200d4000380d04001800d43c1c41140382040240310900000340c90081540041341ca401c001c18071801c0074114100c0c2d00541c0700b1412020142015201e40030220303625009501d2910302a0b0118030084040101c0e40001030398010000d0031525001d68002000043d00c0803644403028144c80810480e580c26018000940500781445820880a0903000b0403041d1000501018017442030384030048456455803aa62400f8003001410f103215100c12481441c0d0b240d408074184040302d450480482c151178407440071240b2001c0d00810030b050aa452000400c02844040243e606041e9134001c000009030b51504c00c5415102070950040c0c0301d1402d81410358582c0c44038400c0d810224400030400034100c17040c0121141c00040c1c0c00f40c041d01560350b8400300301036124a40000d0300301d200b000100014612811a900c1c40340c0d01c64981440794000308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712211609 1250 712210359 712210363
    0xa0b0307030c03050105061c0809151b010e01050a1802130207051b0301051302010522080d0c1208040506010e0c090a0e150303041406032d01060306050a06080613090c1214 75
    0x640c1c0024007403c0c00b0044022b4500e4148044440e10030310b034182616119550304980b01c003454820010301c0c2651502d1911210040a03c10907520003d141001e02441c6816010603840710340c01c90f002480350540520b5603401000b82e5040c0c1c0c48050b8080100ca200c40c80058030400001611035180d403096081500040c00031410481c183c140300d038180c56040c2040360703808485003900300d04000c503100850024400584e924042101503440241500d80e1006481e241c149112440204070b0789409010421062200084001a42e6411101d400d08142a1502c4092002c8854071502242c140d10902e0b40501107004012801c40d1401003d601441f1b00b070211892043c15241d000b0361080940c4034001c0344101c1d100d0b00300702000f1644042013600b503600d141d08a200703101810800c0e40c640489400003000512203250944603c0c0050842200c00600983c94194014020b440041610b030040b001050761b500145030580201c2c2007690700415010729252183c440f11096024403505803080039a44504d14100d002c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712212859 1250 712211609 712211659
    0x5030a06080c06120405121908090f0a03050c01090609060b01080a0b06090f060c0102040e011502070b0405150c100516080105100503040812070306050109060f080a0b0307030c0305010506 82
    0x2001e0300d80c0c1c0c1044d01c0d80161008031040240166502d02809014100700c809445c0100b01c00d0504608018807845d071181c0042500320010304614069105100b495058540050300c070140725403510300035660b01c0e0f100c0151400740079482d60041c0b819040403a40700401c016a080341c95100e0b0280d85800080d036401f0490420f40d0115600c1caa00602d08100a81107802e050020039160a00030b442a45000f2004c0441804c80c0d0040c1e000c800f8036550716005000405d844209003030451707224070040810905201041c3d08501c220b2242511840c200076015030704d00d030010240c400c280445006c1d6444000c1207828003001e40010bd444400c0d202c0740303100003c2d0fa1401341505a040c2c0c1c078090a40c803039200503070005492550000c0c00941d000c540520954165040841c80c040c854205036034040b440b9454200050031114250700403606106806094082c0658410812548903100700c1c000f10300c0600c8500468240b40c03194001030304035200300380048180441500024090300081d02e41d0f182c0540d00211300f10700580c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712214109 1250 712212859 712212883
    0x803071112190b0615030a0b090c030103120e01200a03021213090f021903090209010611060601030903030e010e03120c0c060a0f0237051e160209040305030a0608 71
    0xc91202c2c650003040006420940c40407000e00001d4400300d5880443c0c80e590811240c2c816070681b03401c00c200090510400d92a005411880218110f5045940786011340e803050495400700420501c1d4590580c1c0318403140e0b00f00002013041d4441c1003030540001a211105003405402611030300e8800720f0b184200c84126280e8540002c42105ca4a0419244c078015240c00c140c40000b498081c0051401c10f507a241d1061040c01d801d4a0000d20400c0602c1070002d40d40c0d050380001c081c400b56541310f406082c404035016500490034600080c00306080d02e0160014851902801125881c280328a840e40c04004014055200600c000140d0796036000584444c500c6820f20401d0707190007103c041040320b850398000c0c210507d0075020141c00d1018503e000b41010f011a851550400d4a4911030241050f00b507000120001d82460050f103411240e581c01c112004015120840340c84000071491080016107000c01c00c0b40342e000b00101c40e2340c203040c140100700d07410658240c4072040c40e001c400121700f200082c0e5040411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712215359 1250 712214109 712214143
    0x3030c090319081e0f0901030b0312121608060904060e1222050f030c0d0c03061109010f020105060a060513090c11120301270f09030f1704081902070803071112 70
    0x211086c0300440140001595203034041c40790b085d80c1c507c1266940c0c041c1171200190034400a0b18548038a02c540f1000c0c4220301d200a004c070b200e081c4212520341c0d804c0d250f40180c02400101310704550444c00b0b031404200300101e10f030341000071840c0410311303916048012088289004500c50f05458504100d142412042450741c180d019000d03092072810106c000341c401c0307801400520a815569181c503415903920b80920410480006a0160150b1300300b0155910103030ba500c002c10682c030b04080400c042403c00d026000070b1101c0402c514010b01121f650480c050150a0824050029203000280c082e448048042d0401d0091034203e00c0714410b01c60070b590403203902544a035040101690300460f0518404950680c3c140c0baa10380120169080c0a5041228829620a807814003c02c20007032a844c1074407c244414555001031001140d02c44040d41d29012090b1808403a40c1c55650f8107a180c582103038051035280c00045180c409000d002c5010788001d410542d91899031035080b10440ea01d61091206c0d1040b45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712216609 1250 712215359 712215367
    0x80606030f0606130b1207030207110f0f0402070506180307030e01050a052203020a05030102070b01091515080105030d2a0203070f0e061f0203030c090319081e0f 71
    0x3020001e100da80c100384007a203400d00d40715005220701100e42054120304454900001e0b20004030101040f0164014030b54a0114101101950380c403101000d100001072250507400c010421994a00000000100d0020000c550711141d0340b4206071164402c0318120f03040c0055540c1d9560003080841100c808031303419982e8801c8059181e0040d10b02d60404500c0d9401c2110070301c5445c01d1001e52800c240e280c007070b640003007046417440e6104000d01d2103602d030040f90180c1d0041c015040055502c00045042d81c820041c0810004124002001d10f244a40e02c084800507009a43d401601d4004d06098103072001074003650720210005805640d00d0706480802034943e005a0915510f03e40ea80001c840701f948024103444203d56101520402c00c40e464016180b840c1504007071003000e10b0404500c0c18403034403100300380034259490b04000e5100d0000915902c00790310005000d0200d50750a1000fa500000c100c410649504201c0c00c1103042c0350440805079014820f01001d455151890720191003960700e101151310301d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712217859 1250 712216609 712216621
    0x6030f0c010f030e0a080414090c090114183a020a03150617030c070f0b0a110106030501020d05040b060a030203071703040503010501080a0b070833090a1b08060603 72
    0x100000c200071104e03401108403000c0001c041000400c000e01d4a501da01c1050402c1108000e12108003804031181c50301c080003c1d43c4240d800c80a15012103500565280d110103900403503403031802c9204aa036034882c50b1007814501c03410350868005500b1850000d00f40704000c1000c071061014030094006075001500c5603042000540003000c3c040000034400300810499039908920090a903042d41014494101081d0303408080c0c020000c103030041a0000409829600d04800c079480c42c465030341004100504070065203000d00007500000c0c000c6500200856440421041000007814281c50465030003c4810124030b0615111080b20184ca4000300070f4501c051600c021036080e80c5500c5640394040c001404001981e84d420b224040c0200000c4000e40740d000401d01d0800361410005103c282406003901c14080c040f24201849891000c81004240d886c403aa000f5410520810038000f0b07611003104002c201d0344d03c10343e41211801e007402c280401c8031100d5852060b560801e0440f0300b40d410401c10320000318 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712219109 1250 712217859 712217861
    0x50711120307060c1d060f09150408071203260a02030a0b041104030b100b0d020a03020c0d09050307080c030c13060302032b03051504090804050d0b06030f0c010f03 72
    0x280c00044040707a00d010400e603183d40c203842242d10103d021455069a181210043c1c50410310242c004884461800325003040e00c00d41c034041d0742c070101c0c00750240008011030b1032807a00490b0041c0029100b21a4050b58070b03941a00303008840003007140018401c80215000400c0c11403080381c499000342843c0740661310964200d00a400007881d20b091507485090030701e050f8540344920244034150340c003141e64603800d509100c40512400f80c40501e100d01c141204003d402e90090030b466203100b0007040580e03102c04d030280c00c5010340200140c0c003006001d84031841d000d1641107200c92080300d406500342ca200076a20142c5a485283d02c4c5407041e01a00281c00010682c0340640700c07030388034485049000881c2c40c0c0b03d80100b4506003080140e950900c00301c1101d02e42c412598441510b0700503441c502072289117492144026100c43c1e08207290300482e01d80c09518100716260080e02d02800d806421034140036000d04150099180c1174810381d01074011400381c0700e203020300850540051181030b102d04902c1001204120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712220359 1250 712219109 712219129
    0x1081501050f07030c1202030c07120f080307030b030c030105130f061515031406100f02100e0102090406080a03320a1d01021606030b0a05040e0a050d050711 69
    0xa04210301040610b14420340080684010382c082d44e0343c5036030440d80d40b4005450b1a100c031500320542d401480080f1300b42e4000030308141074410b507080c120081130752440c000300040182503009001c5d0001200f00103826900d6400141040c00031401c82c0ca0125058090508a44042e200c4151884038000e0600c04503050408003c802c0344544d40001d0124460084141d005842d40c22490030001703086903003501158107000f800c0d940170040e0a8102c10703082080020300700c180301010310010b000030346450340341d554000d0001080f07205401c0c0d400d011050507400d1460003540254100d0344664a00800032030740290004905401662585942c200030f0503491b80000105c9d0748403005184c18912040384211020035002418240f0032079159284481a48440d44480c00c4c0806d240e0750442d842076612103848090301d070440003101d40c14100050850307100808107640f45115005070742c001d0300f00f080c2c0001d5a480000c1c190190340c095415138042c2c4616070700031101072180500c040e00740228048802c1035407521020032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712221609 1250 712220359 712220401
    0x9340e1522092901031a070f0f0c020414061008011a16060204031104060503010c140d0b1c035c0a0b0a020f030417070203101a040b0108 60
    0x3d084000c0f092980500d04400030211422409018001042041010601c22220717000790a40a000e6180071074004003000c8071001050200520650100200c82c01070424401c0c45e9000b030000e0020f500c01140c010300c4002c040d00c0c01c6001c1c0b101c00c1c0c3c541c40328502c15030f0380a05951804015030350941140c5000e841940200d15541c00c2c0c1c9014480270000101d8901c0240000e51050303031900d110710000c0f8104811202e20b90b00c624007a904000c43e984a0a51080510341880d0350720101c19210540111994003d000d884c2c520f98104194001c1d5440700c40c0c40c0b40d1031501c5648139603100d00b070b8400507811102c1d03180d05440413400c03151000c2c10b0707071142240001141c50442c5c08101c442c40034040050704941c43d001049941d083e403500301c0001c5100f4080000181e940c00100c103070080d031500c8076009106005100c01040a03285441c07049880c0c48512610080b100c0c034680040c2113031003841364010340500030421040540750711000b0710103000141c2000e005a510007403058480003540e948046049140481c40f01c0700c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712222859 1250 712221609 712221623
    0x303020f1b06030c130806040317070c0236060306010501030915050705130b0909090d05180f040c080f130c2306040b04090609020309340e152209 64
    0x5088440e22240082070b000b00800001007416007000c9c100a440e106ca080f00b21000c0760307440340c01c00c070045821050440509605035803074407151090b000004082c0541c640e085001501c50100808903440004109006001c220161010341c0d99400c019812990b84440080100d00c0c0100702c80c848140303a0340020340c010120305101e89001c0d0714000c82d980e800200c2d0440c03400c0400202e01c6407a281404c076909640411002d0081c014170b52030210150480c01400e242c0c0f01840380f200c200140e26200d6a002d48503569002d0800c0c0101802c040000e440001e04946903032408101c20001840c03014203080c010a00d40c1c102204040343da00f807100301c0c000324000c05c4103400011481540a8180d40701e00b00204010f0419060307240d200c0d07003840b00e0308081e0b030762550001076002d0040c01071068000d03010840c0650a007101111f0243d4540f181340c0030821070342c0040c181400050300e4100150701c4907200c65552103424426440d80c00300078a80b0401c8600300301c090501c03081c10545401c822990304994404400540210b030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712224109 1250 712222859 712222867
    0x19050d0b15150a08100f090c020304030812160309031b1113020301140409050c0f0a1d0109050601081608060105070203011509050903040e070f09090e06010303020f1b06030c 76
    0x40812449141540c1c0782d03034814000981c1003025540f03c002a40c00c440741410b1070b28440e107404811201e009450050449440e80c484000744d0301802041140d000307607804043c0c140c88052020300034581d28400ca45a0410b107045801c014540c521034810203156580c192581030254071091005103014041010490b00d40e00301d02c3c0001a540d03141c280a5541034031802015a603581000d00c0c6851103114070340740e039000f1400c00c421080004e002061080d9a000269000310030383d0701c07080c0042c8105070503030712072180c21800c25000c00a034040c2a00b100d0513074036504001c1c840703502c49800460741c0b160201c1c1e80c00392100c01c1d00703860034090b0320519585400100503d8200d05086a81d00003c1c21a040f00780380c074190301c00d58001040840c00034001c0799845101c860155090900c0c00f1a03001b92450020302c20b0040102038010850807900600354a8040c1c00070040412101001500459a412007030005030050700c27032a0800c10110900181c040309540c0c1305070b0b072804915640c4040c4800d580000d0812910300e04180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712225359 1250 712224109 712224151
    0x30c0809120609011d0a0506010b07030e060708040303032909040302032109010e1507030f020f07050c090c0f0a0c02040902060a170a0908030f1512030919050d0b 71
    0x20442d4000c10300b48000060741c103014404021801c0c849220660070360452841100401c170081490fa04540d0180900e99880340780e49030840d41c2031f040c0d8a04960000700403e884060003041805841074074031070740b000c10000c1c2c01481c2c1000b96481007480d0460181c14040140d825041407510746400074868012603003803607a03aa4000c1e05015013003000142d046120020041f01c40024081d64428004a00140c8aa00b4250a0011b10310304001c2c40c1b00b0505498a081a00040d02035040302c036641e040d22105074940f01d182c03525684485056120f82d00c25009140807a1380c1c460303100d0403a60341042402d2202c1c60229080d0003580c602d00e46040c2640c1c0a5903500c0c000000d611058000c19400c0f4099a80c42c03000c46804600d0350900801510090210340380c0b01c2034000161454044a81150801c02e41c41920b070341d4080d0300e003504180c00306085e400880751b0018152080000003e88940751045641105c05460180d0003001440300e80724403584075028000c43c0020079000b0148503004031440c180c041a1071816 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712226609 1250 712225359 712225363
    0x10b0d06020d0b10170c030403020a08130e0c04090f0510051903142b020c0906060d060e0601020d1806080408042c0c07170f1309020306120a030c080912 67
    0x141c0c50305030105a400710581e0b000e40301005d00c0341d0f001514904135429030030203880c000e42d1500746140007400041d001031685180810b68801000600c005e84c81c3d02064640b141120344603400c2441041d400f0b07070421010b1038003e1000c2c0642441602d403c0030415030342d4900010040b820344081d50401e81d000001e54003002050710b50f094800d48100890090201d84030341d804204a45001d00d046050286183d83d0030340d60b4550200e510000b03140119007000c040d80b01d00d0005613852049007180741d901840e100300011b5803c92100c1030b5120b807009070240c4078800c1c40700e40150b0b07040540c110512440740c0c2c042420702106000780407460300280a03440580c18242c4070752002582c82c041918ac0c100e07a40c147c9403061107450b0000c2c206540300640880140c184145030ba119003a800440c1c4403040258030116801203200800d00c162000c04040e0b240c0010b1340d0341e48014040081d88140c07006405507000c0d102ca0071f0300c0c45001841044c1d0300c0e0300d5541c582d00005d45484d8040240c0161003615440240e5402c016003003401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712227859 1250 712226609 712226629
    0x905060403180e1f0806041e2a090e030408031909080d0801080705040e0a0303240f080d050c0304090b1908010f1515050f0c0109050a14010b0d06020d0b 67
    0x12200c0c1c030075803268400c5942c007444001684029003a5000c0001c00c8000323044a031202c0c0043c140e401c6541c030f01e180940380c03d816207520a4520b0030b54000d0151040c0d00f101420814004540034100304128030442404900d8032480369002e50142503108001394030201030003d155240c00310f6586401140f880d141c5107418245a17004546400280072800180f01305d00e003c0c000e08004210861301005207000c01c80c401500c2e4001e60030007405240d650101d19082d012101c00c0110f0300780c0b60880c000a83c580350307003031310b4112007450250711042d1107440071780790a45000d10304840300c2d0074260004505082c90301c07845201500034022001d400402d102110405480c0c00c024400c0a810840008508059550101401c0310009601d9802224244070200b00b042944400c00e03445810344d1400541ea04c064040d50441845601c000054945c0307130021070414081c000c107884a85901c40d00e4030050311802d1f40225400d840c030085015a0083c1d02c44600300005000b0390040c20a55110b03840802c555040c5000202a154 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712229109 1250 712227859 712227871
    0x908031807060309021e0102070911180402030f060d03050405040507030c120b01120f02090307150f0201050105101101150f050f1212160c0603090303050108010905060403180e 77
    0x208040324100c51040910855014041500d030803c072030b003a076400050301281e400c025042850003400030459507034400e01070344d405032070b1030701080c0082622040e928449921038600881c0d03106070f40d08111850303d401e008032030082828042d004103e440d640100f02003140c21500843c02e201d0104800141512180079081c41007103c0c0d180081c002d0162440030381280c405084180702c0d68a40b6013400e5039603800c0b0b21201c00480800c81d00041c452a4605400028407456840e1503040c0b00d6803030b002410843c4030030002111040c560303603049050302c2d1180c141d00362082801210f41c4028405c180080b200e10070795480b01c5881701600007007101c10004609080305040c9400550508600840034020741c00c0034541510800703002d1f2204881e40e03000084103500c0d1094000f40a428403070009200241071000d90000d00b01681090318480e4060390340d400a0000c01c6011411008203060400000380e04c001071049441c0d0b02d4210014000d0740d55555002c6880c0c000c0140217981c10a689080421101c202c510b00758071600c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712230215 1106 712229109 712229131
    0x809040b300a050703060b01020d0816030506010e0405100305061308030109020705071d01090b0604060c030e04060f030b010503070e0c041e0b120406060605090102030a050d090803 79
    0x1c0c0c00d02c44050110b100c0d50714040280032940e4010121103a090702190101d1b01b400f8019500841c0c11181e0700f95034042c031481044407074042d400c86035000d141403410901c24280b4000140c111071040d00d941001e80680c003801c0c410001c082000307540012b014a0340032103411050341c030400e140c072050107030410481d0089250802c110040004401805c848a8400c40c40b014010414142807003d10031070860740c1c180040b010007410b1020848007503d2050761000030078140c80e14140e074403070200e19a032a00196510030010300d100361504000c01540c80703021201a07551511041504c0c0c511140c00c6941191280b0080c050703255800780031102190310801c07400c08401401d01000c0e10445040d4469000c10f1400250114120454650340f4032880c4070360000c12541c0e840e100102d900f401504071650150f4000c200c00c3d46441d01035400b4081080104a0100d10760096560b030b8003881c0c100707841c044c2d04a = true := by decide +kernel

theorem cover : BRFrame.Cov 712050359 712230215 := by
  have h0 := BRFrame.cov_init 712050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712050359 ≤ n) (h2 : n < 712230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
