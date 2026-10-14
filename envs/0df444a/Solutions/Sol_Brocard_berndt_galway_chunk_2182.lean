-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:54:37.949292+00:00
-- url     : https://prove2.me/submissions/a8b39bee-5839-4ef7-81f0-b4756d92131d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392266187 ≤ n < 392446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392267437 1250 392266187 392266223
    0x100b4504020d021e04080c19060f09080d08010501020f030a0221070b13020108060414070c051f0218150a030510260d0e0d0605090c03011506032d0b0409 67
    0x8085c10032204248203a84102200c8000d000500164490002e081c5106810510215005120580c4540024900075609985500b0107034034101380c0441580205000e0300c0100415a170400c020415014488080c50500e031010001039942d003e01d0007901640c88101d20070350103450f000425101c01a80241c218011400d00c0c9103044005c0001000582c0002c103584c0008000b82007034014119000d0501c100e0003801d0f668110308844100390398200700c84074002d032032600f881c1d0114107002401e49425800016606c0c2d18240310540d4075080c110031b05009110701031200e441e50540009581108500c1d09011596581e61021900d0440407a0001d041c5004a6603021015208940d118052510500300b220000400d0b09803c0d80c00c0040780f14510b070303c00c0c8101d00c120b000582980002e50042510012180c44082c00c00c0002c0c05e441041d261001c00c02e0500700f0400a50b13a05015540000306010107100070030308018a40c1d0300314150340844000e415100d80b552440358a41707501003400c10f9000140c603515032007114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392268687 1250 392267437 392267497
    0x80a050105150414131811010306050f0d1a07111614060d090804030b040b090f0c0415050a061821030c110a030305130e010e040b100b4504020d02 64
    0x100b1b003610206007685862445502a128150a07150000d000c40000d2800341d0800084101c401000c4914852606042c1da03030345c2944200328042d4070309480f2140e4907207610301031614095102110310044580440200300150700304c06981140482502c116503109550000c2202030664501c1c014401500000c0c00810301003030003100c2e030050340f04901101980c0c59072400942d42c0c55010750450ba89400c42e0701040814600b42d88111051104148595805542c4a0015255402c150b0000340440e484030b080361602e0b490702004101604e503c4083c40100940100b000c00000340d41940181484110083c1c44180800c00c00c81088001005100d10031407078991400404030f801556100c400640324004c0401c4078403a02860364103030707284d207040140309a8075a141e00f5000940034027140390106043d0804960901400c009201c444107000305c80d158a07115410680c10300d0200e101c2842c40e02c07c0744000308050480003040c030700b90b554116000360300d4400d4000d800e0020722402c03c42c03138403a12030800b040054080e03079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392269937 1250 392268687 392268731
    0x903050403051f230a1508100c020c1008040b0402042415030908090607140a061b0c05100c02280b060301090c09020c030d0903080a05010515041413 65
    0x15403401d201c0c80c2d980508244080030ba60f0804034500481c00700080c10318085e54481d40c161840c03091407050740e030b0b61f5150407400c005031606a440043d0310360f41c0b61a001c540400400040d0034003a02c8201000076080d00040411802400c014821401c000204040d980d642d003008860003401d2100104002c64651010a060418410012860070700c102510035a4080c0c030400c40c6141d00030130154500a4413404006081c1c0c02440c007207580c10505c210044807075008000f1610614400c0034001a91000e1081e03c01c602c5141001000030030082c004220000380c00400c0d40d407200d00189802140e10092810240d05011624511043d101c1806220b06903502810072106150750250f180254103803281420f0502340c0f4049640a440d0741c07030350b06041141610b954018428a07800c0d405032400c1441c03c0d1001415180c90100a500180d490700a00400d041c070751007110f0051204031801013080070303030449915840c01944600345540b000c0d48040c43c0d2503111105408580c048a00b070401c10340c40090394040444c900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392271187 1250 392269937 392269993
    0x7210806090702030a090506130906080d030f020708090402160203120703090b12131a28141504060e09070806010b070305040e0705070f08030711010b090a090305040305 74
    0x75003408140710a0000c412511569001d42d2480301a40c14007050004550218480540e5600c09000020b4072183c0703407040401a042c0300c03001c0e010036030401900606071010480c3c6c5400c1d0f5031040003120001030010b822075000d441c05880c0943c80c0d052440501944c0c42c81180c004e03406016803481391400414104c0140419442500c983c1c0d84640c8402e05080503004001015001006401c04201c0e1411410710341c440309485030307ca003444e480203600c014500b03407001e4030000b40680c8920401c0780483c1140c2c7d0004140002440d080100c0c07410050941d5135035501130318445200203a541e03980714a0b00d890b0400070141c041c0041102c07480c10605001649d0361000d1151040034003c80f000450003215200440314100d0701a17417680d042504145881400080140c01c00c41801420480d060000b189680c00782d12040c01380e9101c40e00c80c82c1c4014060580304603010800b800740d1410100448643da0540c0c100c0d0020301804002030500342d01d1605407207a116580020741a4800c23900456030130400509004a4582 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392272437 1250 392271187 392271199
    0x3050405010f05031e0414010c05090f1c0206030901090609050d030606020a050a02090a0e01090c03020109060e011704080c0a0503090a122a051008060a0b030603060c07210806 77
    0x11500812240340c0020317182002524420342e41c5100c45020400b8440d001806000c2c02c00c011a8a0314801e8215240c14044902040c07010480214601c0c245000940300e21003598801040c000042e00039070701101c0007400903c6454080045140d5400035130101442d00c0e881401007100307050741d0600726a10b08044160fa40041d00f80500881e41034801300d81190710a501100030100e6036150340c01c10070f005000030104101d0319601c45032100002000d004d0040d80d14059a5019841810341c000140030580903002a42404219031103c541e60b68000c40d115081110444469490b803a1803800001522402c1c110510b2841640001c0052041c0400108000e1a0855803a501c40399203003011780010b0030b0001c000c0c2025046109480900c1074135450441d0f01455003001c186403d0700d500000d40da0040504080300050051002c205003402d1048d01240a007540c801c070305086182c400f001a80c1c3d00b900800002c0d4800000c9403d0f810441002c01c1c80da4400002950300c40030007681d0000400d4000101d5101d40300708 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392273687 1250 392272437 392272457
    0xa02060a0e0f0d030b04020702041b0305010b16110a08030301170d020a02010f08070201060f1d0a11040b070507090603080a08070c030807030b120303010b22051807030b0d0305040501 80
    0x300241d60380b101d0025102800c400121414203900500c210704e15907412540030003030100180d54500c60303552000c017441a180988070b4006002411244140c100c820191700810120100350300403e900300e801640056140607410b614004a041d400150b482a1400c0c4800b000108140501c01005001d2003002800c494a000c401c00e801c99031080c400300007030301007980c403d441c2d00614864010f45030701204078000402c141d5038030910003c00c0580d540c8241e070600c0030086059040c0050a05e4140c00050b020360501800b5840e4601c40ca0501c502e1254001c2c1c1c16001640000700042485428000e00440d8030400006549040030a4035511840c1d00780000343c0b4031000581568080e0328007404194160352448000c2c0c0d5542420f900030700040d104540d016040c040200018802000110302800185181c10b8840545070058482d409a561201001141c2d03400144240c0e125000c09003802c40074480844407a440d580d038290010300f01c1400c400e4000c1a00e2180f00103058002c80200708807602a0f272200b101e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392274937 1250 392273687 392273711
    0x105040308030a0605030f0c06030c250b1f0f0b03250203041410141323030606030303010602030a120b18040c170715030b030d020d08060d1e05010b04020a02060a 71
    0x8c94004409691180003400840c0405031508041c0070072114440702c0030441c0519985c1044801b08030b25040302c0c562820000c00c2014440281000c4051034240ea00402075420702024007001d001902650400c03100c04800a0708140e8001d10300322038840b0502d031090580300601802510317035015010301d0070228a00c014807011400c10445404204000c5d40e01c440c4040e0740c500b4817051540c0418184222400702605c007080080c20b803281d400303c03118145002010f0440c25001e050a012009103034a110380c03c18401004219008011285811700078500308524500c0e00310744000406250f603402d900700038061543e05410f0851510f0700d0107a409504400d40255a9442c1040c0f1400321081d50f02980c1c1108000304091800072003241442030080c1404544681220702103490300200182e03403801640301140740811a41c01441e05034003c0000c0e02d03a80e490004d50b40314590701d250140305202e0400c0ca8450602d0501c50207510100b41d1402c020420741d50307070001d494020768511050f00c2141c083c40c0307000498414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392276187 1250 392274937 392274943
    0x90c03111e0f1306080114011409010e07080907030b01092a05160f02041506110c060304260c0f07080a0b061c08030106111c0207140105040308030a0605030f 69
    0x34a2000500c640c1d61082c450b01400402e8000100e000e0f03a9540311039010510b03600070f000358007410b02c240c0c820004640c54040301e0038405000c5540c10f8001c0720040f00601451070300c25000d960004d0181400b00803901c45209249c40c4c0b07516548090246824030001081591907500b04066548000d4100c10005d1448038480200c10406402c91011032070070004080c1e0012080140c26105005412180709408203802140c02d407006c90781c200c002d415048034240881600507020801400201c4014400600c079400499201c0c84050f001a00441031115900104490300c0402d954059003031401c1750b110852625170b242d480c00c01e0b200502e410f01950b040841d03e50700000344907000642048100c4581c1d12a00240301401c54a07132140300020311141022004984074800541c02440565254203000b0050404c40b401c00002c0049490511107121418140e160b0014180d030680728400c030911928800c4100589030381c80340340c0c0001c0c030b68800802040900d4403241c0c404012950181c080d0f0b09010040078055131 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392277437 1250 392276187 392276239
    0x50609010e01121505152d04020c0a14010b010e180c0a2d08070c11060c010e1e0f1c051309020c100b1206010e0604090c0311 55
    0x1c0305450070001000007410b035600c80c40d009401041c818411050781142c480580e40d089560801506210750100d090b400d0554885890740109807a80d010120081c149429924108104521458010903020300c0070704140030b2504810740c4004441401065806028080d0a10381c9089010415000e0a06200d04011b038040c1c1d940c251082c4404695030302c06140354080c6e004501003801304108900c4c0300902c503aa1901900380c0850044c241c08071007052070801011004010841401c00c06000111000038070045282501c0640460340d0310345030316046c189503004160489100d0f1461060b800e080215514180e000d204041e00e080541e8006484a07420542c1d40d14001e444044101c0c0c0301a041012610400240c8625502031202e04202130743c83c49070350260307000392803200025046150552028904c0d4450760380140c50568009800c010740d8038500380c030b50a051181c1043c1c8846040051155526075000c0000c0e140d00036400d00629032242030612004100d024880e004a40080d0082421449414452 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392278687 1250 392277437 392277449
    0x103090312020c12041d070516020f13110702030f010203071205070c0206070602032703040e0a0b0d0309031202010522150e101401030f03110c0402030703020d05060901 74
    0x3056801ca820120007580000f00c07280041c041c1408080b000788216005000078000350718060b0008103007074035200a0f000050504814004100300d8044030769003e80b8084506501280c038021007080410100f21008a074001c0580c495250940b00004007850740060800c0f140260112031140318401c641600301e200a94111001c540001c409882c1116240c01080c1e01c4041403514035111140ca60104940d5008480103c2e00180c01108000320410314490301100788940e0282c1301031890740d00440310344038841c46c062a1826038000d0000350313900034681c000000c80e05d005071a402400ba42c5040090110109000890b002d031107800485030564414014180510b10b41c0c001009000401350454908a080500271a020341c034890b5600d904407283c0c459440001c590001038400c880c0300700041421500700843c16181e0300000c00052010990b42d00480080f140d0500703112a0700b0902e41c0c07807145044803da4656a01500000800c5a41c076415006000c440c0248075091140d82c40d19801c200c00d0b1a4240200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392279937 1250 392278687 392278697
    0xf01030f06020c030304060606080f070f030b0118030302010606140f0a0c021f08011502010e0c06030606070c060507021f0c0209100e090703050607171b211501030903 73
    0x18004288030502034068544121401460480f803d50200e096410854040d82c040c0c0c1d903444100411030300101d2859001c3c80c0c2c0d403241e43e918a040000900712885031030580c000c043d0303114030000e0b50b03034011464440d00091061200c2041d550340d25000b4080d00382401298005182180c801c41d07c4070721107090750140b0070a040901c0c28041e0004040320612954082a0382c425032103507013030b002c01d108413201011048080c0c2e0351441960412402203600101060b0103c1168075194002e80e05801c00f140c1440c0c081000c60798180d40340c44801c0064242d01442a0103044e0303280d0110300084058010005000040c4240c0c0c503101c06e030b0f80445d581003c60b20702d61030020124042c16600300040c5002101e003540540c4c106c85001c400c544408000d4241102116161101d40c800c0c070040c02800003c111580e031001c20b601e403c0742c40154415404e041e01902030020301120326011021425081c0f101c0940d0702a09000c1c0078907188011400c0302c005031407410b0710401c1c105002ca100400003944a0f0082e50509038041d118 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 392281187 1250 392279937 392279939
    0x50f04030318090e0703060e030a0c0b06030703120503330f01110a03020a06110301050120071701051b03090c060d02040b040e0405060f1b030907050a0605130e0f01 72
    0x41a1548100b00310903920712405650041840c500e144540c1400c54010002480201e0031b44c6884802c0b50101682c0340f00c40c1d8070511030390b83e0140d8090044107059900500c0c05107181c0304d09000c285800c1c074270341000700244801c0040008450340500954440c01c403401801c0c61540400056a181c001012034076a40744102403070943c22414156010401260113140c040c8121941c90901d03070414040c01c40c202c0c0140c000c10002003d015032401019010700c00100c0700c42c695494500043c14642d5080f10900000208014a101011060001500034a07200711901502c202c80390095000700403c071411502101c40b5207014001441402c1a02c0c451440382004003600b120400811203d900f041c9000c11401b502048041114924803014100802c1c0c8040c101826051610385241450340080c500058100f40c4000c01c9a2810880011301111b40a2001d181c2c0c0c903180d50405c1030616000c1e422050300415481000149198400001c100321059000c4210619481f0040144c2802c001e440384082e00e040e01c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 392282437 1250 392281187 392281193
    0x3091a030a0b0310020c0c13020301050d0f06020702060a08070f0c0308010b2203030305041a22080706060e01050103060807050907112104180203040f0305091503041b06050f0403 78
    0xc01845034120007012a40001107240c18441607a00c065685406c2d500b19881c4866a814102c00748500488000300942c1190b0524006c5070f450303107641c48040c00d245000d81994041c030003140e044548503a0080c00c2295075111140001c0d00c90300040d296200001c2d105003107400420700c540d0594048070fa1503039400342240d181000074142d5070000d200c501544080340911101140362404001c004511070389000c0340c580b80c18106661400500c502000c100f500381820081c0c0070044010040070f81244591405000501d42481c4005000d01040200002e01d000c401003244a0b609031528101c031801d90b8240039180d05c81003213303160001e038070410f0b03041f0701c240000c10001030103440e10340201d040490803101c0700d0210701e030b240440980184a1888d50741c40050705200924220380d14540304c0b00c0d00e02040d4650b06003a552440001400240541009804500c0c1c0c0c00744c9e50741d074001c0d0039281c01008020ba203c1c14141801400344500c02c440c0e2400c0480301400281d04da00400580d0075424040141034100741c6592 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 392283687 1250 392282437 392282441
    0x20d0906110c030a0b0114030a030210110c10050405010b04090b0613020c1219050403080a034107030905120f120c0a020105090331120f03091a030a 65
    0x2003803001e9680111480360350151400c018005a10b070013130022046951401c084400760312001418a4020b0700511001c03404284c00080000805500903400105040580d4019819008440e501035a5024a01060000e505260842c6000380c0c0a0002005414003c40400044501035400182158071410010b2950b01e45842c80010402413500058504203810b02070341c0c140301e17103200d40b44c0b400e800c045840c00da0ba031002501c202c080b9a0030b0030100e240500b540c607000450701542925108150f01d54030002405816070000f26204421107010101c1c034101034910452000c0328103003103002c4810642c00115040d01c80d02643c242181c20902a200b285002e1820001d154081c000702001e911080205406807c004804184644104c2d28119143ca804240007401d4900151002d200c5600600030350200f007580c8003540d042c09501300000d0824906980005600c044183d000c211441055101c15040c0b201361040f03241064842d60300c03111407548811010080a15080b0f04d255048414000a0680d406e9a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 392284937 1250 392283687 392283707
    0x20c0627010908120313060213060f17130c030b0a06170106150c0f02030a03260c0405010f0c08161502030712020c011d0d0906020f0c04150911120601020d0906 70
    0x841e46c001d481c42d0b545c035040140d03031001d5004400111104410480340e58405404000003115151503d00b034080e400e8180d0081c00068004080050004049000c00804070610001142d0041a054440c034020421070000c0c4201e11649440740c0703400c22800312030281032042e503064030a034440d002400d0368860000c0320301440500d0b01b141c410526100c5940540d800f044a400514425a20280d4002c401300501001c8804201d041400341246414001d03500100030655060b01e01c203180c04420074203500b60490f118401c00e10064141d60001801103034000681162014aa00424444039585290740c0380c18101d1008603040c00000b41010b01402005100390002e000080d810070000c2000a44440401ccd40c6050007c1000c459601c2008446008c80c2c0000845c0024006400030b449540c4881442c680c41b07540b5810781a100d5581c1d60410684c0c440c04007013982c007406c4c000e00104214660b501032080503500001170741010003c40740014402d9880014a00c031054a155034100c800d5240801c140d8682c0e8513 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 392286187 1250 392284937 392284951
    0x30f0902091512070b0a0e010804020a0e0a060315020903150103050705040906090b31020303090d0c0b0f0d06210b10050d030e1507020102030f0a020c06270109081203 73
    0x1100d414030541040c00c01c860b40c0035250116250742c0d10280091b01410740300600c400d841c18804002c0400015079102c4140c002140c1050010315142d5503109203440050100c0d03080101080c1c85100d524041024550140908440940c03ca400c50919425480c094250901c40207003607501c02d100511003418140c1040c03038007610038140400c0481c82130352001005c1c10b084410000c000c07070710400c082032044200481230355401c040c0c01894007030885401007500c0388900c6881c1401000d00a0110081000d0414254018100c0c0c00c42070345c035240064280c3e0004e43c0408900c80d1614280000231550298501010ba04103908003a50500b11503980d41d100300c0301100074016174001071290800100b58aa1410000f00c45c0c0c821381e95800c0144c009001c00201c0760200201082001041c0001c50044c0d030004126424810740000060f100c04000000b05c2c41d001071481c066800c03403804070700480000003000340046103c2c0c440a034441814915001103a41c50300c2c1c0e20400e0b8240d40442642d50f6086962001503030002c41c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 392287437 1250 392286187 392286199
    0x3906012c01120203030f0d02271507021801030f0512030f04120c0204020d0b0411040605162603070e03010c0e1203071b0518070f08060d020409060c030f09020915 71
    0x1042d00310607086c0750040320f00364200035000200b9244001c000c4280e62040e00b64501e01c42028101400425440c14000b40704903540d00d030003c0d0303100941d03a80c1d511382a4152408942181c49684900c2c1901c0001035200040311140300d100020416041d981c0260380c881c580c100e000040c0c650303480d01c80103c000c01c1034181c00300303010701d0410800250302e541c00145081c01300b0820104d403c03e1041e0511007190f0700d280d09034040708014070080c00941d9010080703440c00303005020307500600101400c00303aa003203050032a82c00110060080e017403450111b102c0035600c10909900e40b82c100c055050185402d0700c007603109800c00100d50f070003816001e15019a481c41d144109408590030035501c0c0e5507241102d1202030303100c00543c280e040104424074108041000e540062080c1c1011414a2100a08060a180d00450500207e800090116284e14010940c3d294000f8420b210940b07103030070031800404420b4003d00019041600c012039401d1030740905610140c0c0a040b4506507554040000e41e2440e9001c00c50758086 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 392288687 1250 392287437 392287447
    0x604030e0907170c040503070506040510030b03240f06010f0c0204020c070801050907030c08120d0c030207060c1d011106040b0604020f04030c0503060f0105063906012c0112020303 79
    0x200301c1c040c640344510251300020b5a034500307280415117002180e078030141c41464108400d100035154544003505c40005070a01290000a8a000a081861450141e80020b4122050061003054140e000f405a488000b58030015126036004680f24800c0700c1c5280d000c5000022030308011b00341507000303007100c042e05400e840c40380e612400010b003514001d03203078403603254070000081c4240001050400b0003402d200c00140140a4007101094040c081c90303080310740350741d500c0c030314100c03554065011500f103a6480f8034104110410140c0140c001c460081c3d061154400c1c2c520010100c2d40154040925985c03200000d0030380b07590b1079440e01a401d200500807908150207205408100d2034a5016001840c4100d0020350b0342e40c2441c00b0f05191100040158440140c0d0300010001c0382c5405080740c0140c641c8a4000710781454200442510349000c41e81d6050402040705c841c01034140c00300e50706050301e0305540c40d0000306011410501070300c030103034211503c14000e9000411400303c091051030344061000e4292400c013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 392289937 1250 392288687 392288717
    0xf1403090d030203030105042a03020a1403180c01110312040c030209010602060a050c031003080d0b0a0b130e0c0a1b061e0b030708060c0d020408010c020a050f0604030e0907 76
    0x50180c0780800c80140c0d0000c40180b009192a02990311890090400c420080701c011140544011801222105040d80001c140c48058032824a08121807034400f80076a036030400403600010990b50260310049170042035445841907205400054110007100d0042d4240110004103d410b640d01400c01c4035940c00421f80000161030300340e400d40c008c140d03a4014140a02d00f0610782426920010040c0081000c10410071000910141d006015079402c5112140c5400d400c10445000f484c10540560f841a40702000140d952407040c01010500b030444e03801620b0380c0c0d0f6030302181c04880040da00c0900c60501813000c00c3c00c0c0c500c9a02040d40b1030011052540400005464032400c03124005e6400c00d00841f40b507980101042c0502405152000990052540d5458410510348600c0043d10300803400b071001840300c252030810340649000d060140000c004400880c0d0002e0342d00c814190303044603980501d0001038050b584c00b040e602d1003541c26131543c440600d80b59041201c485c100405032814005562004195 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 392291187 1250 392289937 392289949
    0x303090901051014361513080f061806060102071710090c0602010f0b060d020903100f090303270b060316090c02070506130b033606090307110f011e050711060301030f140309 76
    0x1d6001d1807000c1e003458148807912038414040040bc0300038030303403042050000c10707680021104100c41b455984050b40703400c144034150504001c4100d40b02c08a0420369041e060021030b05446044441c81e400800071060081240340950b070041450030351001c1c060103003841c3c000080e0028000001b00802399154941101907540c2210905442002c529507154085010980c16128500440f41480503040d11101180c6254030002101d80c0024a5801c40031701044041d1003c0006d8800485d40c9000c0c84910b54607043e4000c0142012481c03c001481045400201030401ca011228020301303214035004400c0c200158001c165002410301052004540c4402c41c0c41880e0304000ca119446052560b940184e034034980398600780c0b024202840541040207064009080c1c025001e00c6401c2c00e44940d0105031000300160f80b54408441482c506041408004c1e56155001d001008064480e00c1600424840ca00034032203580001d010007409114180c0d02e0101090841c1200c0301e440c0c2250040301e107045400c2c004a40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 392292437 1250 392291187 392291203
    0x6090a030b0c03010915030206090d03140a0503040c0b03011802090f1206070f21090503120f0108071e090b0f1009050906030309090105101436151308 66
    0x181c1a0b50100051140d007419000c1c1c440001c00c00c800e003040d558156000181144160702c000ba00c240c0e0784030f98580426010384040b004444000e01c020b6219030403104064032990007214111803c1800f41c80c080ac0828101c01524187c03050b80514031084c481d1044448000e44c0240f4401e079000420782800c1f10a030744c030301403101c03142032400c00500340e00c2c100544040d2401e40d580019205220240c84504445000350748908424103000301c002c5540d072911b09090f42144520802d4500c480f400d50200240700e5000103003117048440d110101d4000c6540c4000c141800a600041d4010b0502d500000300300c003070300942000d0704204004152800c1c41f55444006410f040300c0c1d220007004a282c01d00b0403c0146054180c099012800ba0302451400c0000c0300000d140d8001405224440d042d560080b42c14544a6184c001405640f144525500c000040744440c480300c00c03080465000141315600d858980303d0002c0c201d107924014252038201c0144074020003158000d18008845c82c100c00d100060342900410041d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 392293687 1250 392292437 392292451
    0x8031807180c030b01090e060d020f0d05030a1407030c121b060b0f0a1203050f070605040b010510180b030a0905010207060510080708030304080a110f0d0f0f020c06090a030b 76
    0x2500d840460000703029114100013076414811005020010304807481002640503008440042080300c007480064840c0c0445072401e81c01010182e44101000000001409070030025102d540049003010003001c2d8070b01c00d512004000483c08025000003400c0c0159100319039003e424031081650014000b038120702c1c10030300143e418544441800f41e240c149895054a20031054508203001428803139803040020f48004001c041000c001000b4254000080a40c0c142070f0b882181440203003418149000448801c0c02a54030540c004c4003202c02e81c1d4001c800054244a06440302c8410300d1034038a501d00f49401c000c1020b030b01035444a01c5140081d90a200411b5614400c2000150500301141c051410038880d40180c14a07078130000302030003076031000000d4a612a5010743c0c440c2d6221540d2a0494a07091004044c0507140f043e084002e140d60000724000c1000d014581c0c546954024000c400c03680041c483c400030700540c0205210f40200e0038408014131401c0400303840c1c0c000030b035607036503d21102141c115444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 392294937 1250 392293687 392293691
    0xa08041a041203060b360d200906090a15050a06080907050d0f08030a111803012702151201081b03010b1008040501110a020c1201090803180718 63
    0xa5542c15206000103884170111103030031300010741d107502800c001d400e507200282c80003650881491030503540c010442a4001d400b1505044191401c84441381f600402c80c0e01007400044c000446040000c0030510441008103038007102d450720f000a10090003442d50388640c000e2001e0300030072180c641d4038025000f4170040d55111894a00075150703904001c0c0d41d0308903a2155a000c0780001c0401c2c031450007442c1ca075400817201c42e80c3c0c0d00c4030ba001d04018880001f0a5046c030101080c0c4000658070341d030030800030600503030080c48200c8010026402c21100c0f03098504003086a8009840503040040050b0500c07200501e10302e1922103418869418110709074003409190b03100d154544013251460030090690102a8000c1c04980b00000000741400c240c498400704105031140080e091044c01d40102c1034410224141d0b580c2c5088001000f0344a14405d2080c1c0e0080b4a0f46000d106402014030554403002d0b0000d20031429130b281d8000500b401030491440d20324900c1800001b0802086c00801c003003c2c070b0308410340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 392296187 1250 392294937 392294963
    0x60406080607021e0c0121090f0c080c0a0e01210204050f04050d0807081b0702090a061a040b03010b0702060d0e0313080d09030210051e09091305030a08041a04 70
    0x3219640e41303c040100301d11500209100710850341c000030710340b1003c4031b009203031084405500e4078040100480355019040c0303130201c3d0740d0b1010f01c240b45c110318003542c1c001e070144c0354034070040750900200c80228440c001540c510400104020441e01d40c04992815881010207401c1c0e4040e00024103546040d195071a01003a00e4080c0004c0120170442c8804480c040e0a200d8901e14107110003809001d0010701c41d01258603100780100e84150402d04850100d0342c000d0001071141130541d1404002c02d00780c05511600c6109482d03000c21048404251411a501c0c5e0300102c0c13860382040d00040003900b284504a0300a5001d010500c2c40300c207a40910900341003401c00654079040420b05000003071880d9801203002e50401985000f105901c1001c010699070156441d0f0018540b28508403000d1040300242c03242030544d611071840d00b041300c000905030003400321a01c03841a11785020002d900048408010030b0b03540104111308c00c8600880100d540140229041c044004400111125a0b881201c04445a28072014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 392297437 1250 392296187 392296213
    0xe0109141020041a0d0c0206011404060b04090b0a050901030302100f09032f030c030705071502100f02040f060507150b0a0909050f0307080c010f090803060906040608060702 76
    0x1180440c240b4018202110300d00350030380c405440d4410b03402013000340d6001042000d6084040d0701160441c415410b400c1000440c9010025180c807828003440c2100c2d110010310f0034441c9458041c010036644213001c058900383c907003161040185480b0460980003d00010300065030b0342c8002029000b14000c1e0085c00356814007000039401c80d0151000358440514155403000800d5105802d00d102040303a01c2c49140c034942410300d0040140005190070304511001540c0c81c070380c050110141c8209442070303045035030381c6886030048a81a469000003000603882840000c1400020343c00205400c044004c0052800d6150012003544035126003000c0c0101d40b000404070100602d601d1000c4682c840e141040000d60303c1100042c00c6000644599250700d0b440341c00395000d000b400d00294813a01c22100c1241c1d513850740351410099581100070032551951034121b80c404c402c406030040070481e962201030189560340748020482c040b02c015042641082d503075003010510400400c5414002c0e0301e0b5030018810000004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392298687 1250 392297437 392297441
    0xa0e0a1b081609030c0b0d150f05010801091b140705030a030b1e010221300903090a090e030909010b0405150c1c02150106030606030e01090201120e01091410 69
    0x540b250742000002103080020a0000d0207403425034049182e89030b5121160160034000d02803415800607440d080020018020400010a8003140d400b0380380d8110030780e0ba0382c0d610000c80360b0b4100008403501420f85c0d0050042e10075079550300c51100040031036040000d1515107901d1600615401000f00b603695203621020310300210700721050303000040206409900c22000030f48807000c25400c01221103100c00d00002c1c0c000e4003016100c0601c003144219281104c210034140a04a04080200800e0b0a00b00404d50054001c002c0380e240b00f0029004050441c6030245c020010041035015a555000501605242d41d9230240c455000345000508680c545041c4004c00001020820500103494000c00c041000c0e020040303028002d0142d9115100c018042d031740d0003603003030092024004950642c4840041400d0341c05512800c00e076801c0e5034003041182d8641280d28200c41038118040c2c00704004200340c1d5040e03143d0760082a804c0d20003000128240140359034448150b44107102d4038030190000681c0c000c00d85403034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 392299937 1250 392298687 392298721
    0x4141c02100608030c0d20100b01140301030b011a07080c0d03060b1e0705010b0a03030807020d08060906090c090406090603060c030504030c060b040908030f040507060e0a0e0a1b08 79
    0x503020b54603010f1030004070b69540800341b10401c00d0184100c9007000600b513004190700701d02e030300030306582c4c541040b0388000c00100180048203020404100740c0c2c403521480f000a80781030746d038070080c420380a0b4203052440840a8140603800c07a159000c005c1c0d000040c4140c00030342032120241c401031011000b0400c018041e2080781e00f004044101c1800690100c00e080d10101c6030401d821100f440c0d589807a0b0030041d000d01820f9020300d0701712041e100c0c0001019448408540304440c0c2d0f900340d0340c001071480c1c001c407040c550079144d5940c803c503d103010856628058100903040150380703940f24906a0701c0c8000ca4107a034403592000b01c031142d982200b0801c0c880903001d000c6411005e840c0c100120b02c8c103581c000c0d0030071801c001d0250645550746d040600302d480b150b00c43d5450541083c40d464803482d01c0102466800f408540880e541e0042d000c002403028001d0841180c0c400c0000c20044040d0f042003c1c001c104c1c40300a0626248907214044c840300c401140c40c15264002a80c1d958110a252004040b009902c030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 392301187 1250 392299937 392299949
    0x80c010e0709050c040b0c01020c2a060a12021605070611010516050a0c0f060501031112010b03030d0b0411030c07050d090b07020603060d060501080f010b01080f04141c021006 77
    0x30403082000d1080240100c031709441400c0030507502c030010405d9040c0203000b82040c655040c8240c907600c956541502d26011040712103488001e0b01190140c00b48045400303a48240b00100350302c0646410041081d4010701511f0103415200768a0700d69a4480f40e107803400319070264000c61b80700c01d403d013880d40c0280900755204001c0300c5960303d00b900466000780140700307101420041204104013001007118044076004010f4028178180620350712400d00c04068501e0481552113030026428a208501040c042c801301042c00501450401d004180d00e20050403107925416030150f5903178404c160000c50b00002e54021424984003d4032180145085450944101c901070280100400c0822080b201d0408440b100b6a055481a89944465002c40c09003101104028038081c280030001c40c00f00360005a03c0405500301000344084070389403005481c140c1e4162680f40060145a00140c081441c07880d0602c1c12031110800ca03480c114030040f14083c0034104141010068000f914180203054140c02a1806004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 392302437 1250 392301187 392301191
    0xf090c042309010621050a0204062706030e03091203090103060e0906070f09150e09011e12030207081005101a1c1b090f120b01170a080c010e0709 64
    0x1d840d01c00907912040500c5003004104041010000d81d401800710703101e540303410304428025400c0c4903251034069081401050002000c0c540084c0150901c0d000035944c00440740820009541090011006055003050300381c03403031104100c07600c0f06440c1c00482421800940c4059525000e91350001020b07560075a02140801c000f02091042c0d800c03022456039003200e02d5050040122060080a83d0007900c1e550100c40e84001c600006011107401041f07400007098100c4084265a032542603001511091041200c0c041100c09410f00981703009001d46903900b400390040322003440e030b64591545000c808410400c105178540c2c00b8800c210281000300400f501c904014140e04150590480c0c3d0709005038940700401c40e00c40c5419400800d1184c0c003040358800d2010003010304d8664210301800c568550b206000f81441003040c00603030020b02c594860a46540800c94203902d92078880d24014032000c0c00f0320f081c1c2d140980101c0394000342c041c100501c0d84141c0700b400450a401c442d0500e50606810b41d0002e140a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 392303687 1250 392302437 392302499
    0x5011406030915100905010b030a06241d0901120b060f09040618020a0b1b01020702011b0303020d02030f06040b15030604090503040503010609150f03021e0f090c04 72
    0x2080852200d0300f11421858600403a0b031040c28030305412880b944550121441e2200100300c4602c410002c521842c1424401e00c5402c0d503881903000c107a4841850038400d00b0104050101c064800d00341000040d2208580f08801001e03c2c1c00525112000c0c0d1051111110310032881c800c10441116462f40503004840078101081d21002180c5e51580082c0300420b0650b490928082220503500c043e9a415006004015160b80300c2d0344101169000d0300616001601c0c080880c41e0500050003100d00196040c0d441e4ac0040c4003030401030000601300c84040302815000c2c800354410302c4040c405144107803100c28202502d410014240002c4a8034000900e01480384042c2d000b041e1040c0c4004c5a8002c103090358005841042030070300034158095900815810f500748100014a41d0841d00450a1050609140c40340e0503a01c1428107541040ca00c0002d401c221159a44080720180000c001c4082401402030140f0503007a170006005144200d415203480c680100d001d00000003601c803021104807071801007001e05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 392304937 1250 392303687 392303701
    0x6060109030b0a0e0a050607230f0318030d1a04151421010f050c04080709150308070f0b06010e090115031d010c020d0819090615090501140603 63
    0x4500315020103840c601c2c1c0900403900080180d07100078803140c3c004003694030540d541d29180f40c56440c260381c00380005802450221000280030318100c6442400405103107002c2400d2803280850700300034840b800f8445200f03aa8601040103000610740c40380a82c1c8001400b0180446d0032503030804400526000d1031902c0c4408800102c8403503000c081d104000031000c0c183c0946000101d2800090000341c000400034085408580c00541200c504011280700034440c9980747c6400c0e40c1240124440c00e802588007a604000300000d983c480c00c4021450001240d640d0f88036100d0000703940c0607003030883d99075200a80213018003000318110342d0441001d2801100312a40e032000a00c54407810701521607184405a20460243e0280d0301100c14441601c20700043c0200c01d98055009107102e40450026024906e0081c448502c2841c8080c8a01c003030b8450b240003101145040001000075003012600c15548403a006030030442044202c00809005a01140c04e40c101100144e00301c0c03411864030300407802802031040b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 392306187 1250 392304937 392304947
    0x106030516110325060b1503041e080703020a050d0503011a0924070b010614121005120706140a02060c031003060f0218010f022508030406090314060601 67
    0x3a10180c2d281003019481880840380c02c51094040f1200644a6010101d0742c0c40c1c2c00d05545001d05011390b400304075a464242c2480b81d4203508500340400e6100800c00600000c0b840b0000e42c1030810760a042802145d22544c0742c228950018130194003503800788007000100141044501c10611081c5000c504651504503080402c50762544010b41000000c507100443d40c48203030000012200311026500b0303120440a00e14041d61000c241590000c5607076001043d160b0048031244400b01c01d58180b01c0c40d0000c5984000c1c80c00802801034141c010403520001032658820b807511202c0708550015100440c81d21101900004480007a190040310070310013802201d8001c102680d0142c4501e0155a0701c4e035441d1680c038900d1035240c10042c1950314000460b500c0640c282c0c00790031510584200b0a0a8074800741c01503620302c00a5080c18016405640380441040140c199084d0103082c10000a03480d030785803030400341150410b4001c403000820016041040c4010030062504401441c0d001c0c0c03130942030100000305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 392307437 1250 392306187 392306221
    0x150409030f0f0302090402040303031401090c09090221040302010609150e01150c06021215040209130c030f1407090f03030801090c05070b130213020c030d0b0301020c0a05100501060305 81
    0x60110b8106050101e80c00b030b404136420140020011540d4a480340f9000d8000e0503000030044000304114000308441e800e03171183c60f4080302d00d601c8100c000ca282c05001c101941c00010401130030075001c0d01d00d124201143d80a54042d51094002184850810413100100c692100641044810340c03802084080800700c0390a05442c031017401c041c682e000b0b8a506a0700b000700707043d00810440c03002454580001007a14000d0080c0603d481c4d008100c4441400c003c164011881c1c001e611100700410004c1e040301d60750081001010504011864124030443c0038100e615203041c85d400e0352014410840303070940c848440006030820b150980f01060454a00808080050090f900320031f503154002440d8501a005440c03515900180c884121305d44080f60144088958400300d00a0280c4110b000401c07400e4001d4482c000050401181004020007403900600000102503806550802600040c0031050088d00c82c03640c0940001c142001c9160b079410202d507816030080c42050b01d000140020704c0303840f0b20416 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 392308687 1250 392307437 392307467
    0x60c0a120504060b030a050709060b090f040509123c0406030507021006170c0a060203072010020f06100302010e0d0203070f09090507050d0c0608190203010e15040903 73
    0x7225521840d100d40106050f50711035030300d4851030b51030a040210000c0c2075815244880c2061144685c2d0f103d90070308038024400345c0c2c0d9001a00313402d6903c0900f020b5000e00d0f80061540b04036224200c0410005080742e02400d0030003080504280c88090098002d003843c880040c0001341c4142d00b200600c2e040e074040c0958029a000c00d500d03480400d40c802c1c404c04c000b121030351200c001005840d60303a030010040c0f020000c2803030195000700380c6081d0052801c40413101c221019600654581a143e40d1141020720188250002d2483c00902d00e8000d038584101d4507238418004d03001082e0503805104941c1c03804000900b042a010042481800140d90100c5083d003894030547c1c0146602110b40f001a0405000d9048030000d001c00203030014200d4001c0c0c0015001c5402039064462003900c510501803642c666030f00242c501803000c0c008109241c400c07009079a2001c01003400e07841980b600104801640e0080c0d01107580320742c0e00001d211001c00c0c4051010040340c1c044034200900c3c503480e034001e4110406007002d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 392309937 1250 392308687 392308691
    0x80919170403021c02040e0604050718020f0c1612120305040302100504030305010f09061d060d0507030f0209010806072304050919050702030c03030406092909060c0a12 74
    0x51684210a8401d035009580d00400440b01011038004140c0e00d2102c404060307102d68107084c1200c95002020503054061034101d0094000941046e0380c1e0170380070140c00104203845a0800a140c0c60411203400f60500350410381c0500f8048258010035a807200b00c54004d0306494141403107030b0002800c0d01046032211105401e0200d00c0780d45e542010307420100b140d070102810311304140030041016455801103042c1c1e10300500340703081c0c44d46502d500022100c45008181805402c503d0040d000202c5114032a4040b20003084440398ad2443d03a034150410f08940e10840d081c0306001d030110118948908200e003d4154400100344a00c1d0088004181810441c110100404c00da03a15a00c001c01210469024040182048610b4100b12031440d220551000603000c9440c07400e000700714010320210843d400030070004000c40c1140ca40e5200c1e0001000c00c18400c4070984403025103008010180200540408540d400743c00e030b1454005546400c0140040c115440f0100410107a240c8940003504010010220000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 392311187 1250 392309937 392309963
    0x120708060121050a020f0705070302010f030b0f1c0206070b19020f0d052d061206060109060e031f0b0a06032d060801110d0b0a0f06230a0906080919 65
    0x1908024418020324142c0c0d03006c0005c0305000d100001808000701e91007a6601d80c202c0e100c841c0708404407138031011010362040d030f803200e08449468420070036800c02c466450380b802c0b42d020641c0090300c5ca50104204840030880d180c2006100310686210244604000b00b0952500c09140d03200020b500c540840c0310050340d03032030010949400c20007548801888601070304190f500100d8010020801d4101e40c0184544040c1050024510005c1100e90003004180c480ba2826410014251134041210700100c2d0144900d558200c412110b0703401c03d100005000900094026912003400907058460b0050002c0c18140b40b09512120742031207000c03600c0c0003800c101780d02d070850005075440a4800f51380078081c15804d0031389a55544015500405890b10402010040301c40e556081c000520902c0c4152100780d1400b00b010020507001e003020210100c00c000080f1a403035081c05000d101d41d0440e807062000a1580601800100d401000b895040088080100409100e84a00c1c403050314030b441009000d400d442c41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 392312437 1250 392311187 392311201
    0x3080a030b061b070f26030f1b0f1b040c0c05070803030105011e0f03020a030e1e01230109020708040906060c06051303120b1512070806012105 63
    0x100000048074010056551124410000800e01c445418100391902440700000340c0f5004c00040401141c0590900c1030400103100410321442d0320112030b60202e40001c10040c1d503d01041002071540f07100981c2100064281d01802500d4842d0300c4050103215030000e03001e00041e14206c1d42d2041e0902c0220f6000c1a814000710003101c403990810700040a9100303488000c0340c00c1502001860699400380d03103030b0204003103030301002545078098074584020600c0e03000712915561007500103000c010340a0130007152000f48081035614103045a0b8400b44101107a00050b2036914080c0a0340010105400410950f000382e00c80d0115801818072803461640c5c0d0020301c0c0c004000c0c290040d24018425000d04000700c550b07402018084a8800d0411150b036031a11000581c4180c00403508004c46070940d591003060707607210210320001c00f58a1301a40e8841d01c030030661480c1200780d1005100030100428a60300d0303420a80c0c005419400080c1c00d03035052124280b900d8800003042c2c0030742054402650707404034407511180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 392313687 1250 392312437 392312441
    0x120a0e0c0306090d11071d0403030b0607050c010f0903030e1314010902030405070f15030f02190c020306150d0611040902040b1306050f0d0f111c06140105030103080a03 74
    0x10300e81a405014560030060101d40100d41d44042c0000c646036201c0210041c240d81d034a417082d41c00b80d81060041c0034200c44940d01d1480200b50b2141c480e00380020070f82d0840c1c0000380160040c000840b050381c445640944a541e00035241d0403008103604201c9a040d040d590081c2030001106032142c040d0107000166000d80c0c1c001d40011686102c0114940c54950311406000065401104e042d0365a101e141c40020701824440081400c80b0358007800818071240c621004c0b800350142c0c00c1c00100d05a0240b00d00410a9108490500c0c21103598450200821a51041c103080840080c400c0003c0301e681d951414181c0c80b028011095580d01000000d1441c06a0950050900541e042011700c0340c40460042001035483d40280317000651035151030310f95550344034200c0f0343e882078880b003e0368508103001d580d8000c00c281c1c01c410302c46d07440c0380c5010681a500040c000042d402102c1e2101e44580c2800a409103607100f4440c1e10040c040d00382a0f600022400303800038001388418800208524000905000110301c03a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 392314937 1250 392313687 392313703
    0xf0b04020c0d02060106090f05012106120b0a06030812190c0908100501050105090d150207030905120a020904110d050a03020d0e010918050705070f05010204090b010203120a0e 77
    0x10000c54aa680c114102641c9604010a400240c03050380000704030b150140f444882100d42c00300d5500308072414440111400c0054000220301e6810003581c0030700304c5909004d00409040000300c0c44c240d4800904108203801700c0500140c41e11031600342c080c130224403100112002d001c0c3c64443c0351101d854513080c04420300751000c0c1810380e980c40c00b008180c03100d500503865801c9a00300c2c0c0803210101b15060030841110780038070030b49020070010000e40c1010b0400c2100281941d0060780c1c03035400e000000c041c510999200560480c0003c114400038460340c5080c9500881e02030143c001000c1c408840e9010076803101001d403010b0309003814100500101c0d51a0009815116408801e9030384041c5e40c2c1c0b170046d5450b0091807114000c18042c4400758055442210030500f11002c16600101d00d862500340040201005040802005802c04c2a40d02140c00b4404903d4810320800006950328a0280300c00101c400c4403040d581150801c100103030000074845101c80d000b50600500044284511480c0b0b4580205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 392316187 1250 392314937 392314939
    0x15050a170906010e090f0a1401090501020d0605030f0a03020d030906110a120b191a09060a0c050601050a0509152403012402030a05031009090f150b030304090f0b 71
    0x61410401d01c8030010030501c0c126403a40780e0300e00ca00d8654044031625035a190004002036072010080340f000c2201c0e0b01d001014003651400028103034131252a000d0070790303001204c000b02c0545c850b03500300580d0a040041c0030030307028960060076001d491954025200c11340d1301c00040401d41c03908100018080b0030b83c01841d0b0190500c150503034405218901903c4107010401c5500b5280c42c1c0014240e02c0c1c1800400754400d520050b580303d12071802d0500040301d14104040d0a08041d2051111040301c4d22032500802c4508030300d44800707800c240c0b940f600903d44141600480e010b1007180c1c0c0100302a858484c185074120580b2001d43ca036890050010520701d0300700f4140c04140c4004001110034900c080e80c015030590b50300721703021982d6003044407000740c4080f4801c09400040e40304000b6a59103078800d00c0a19001614040100c503100d9541e84c0ca0000d1b5803d004043d2002e1245000d02c0e0200680c40041c0c0d9014010940e080c058810803c1c0081e440303005034403c4c00751050b181c0c074403002d0040050340321030207040c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 392317437 1250 392316187 392316227
    0x60c1209060203180612070e0a0b2505010612080304061b0e040c03090b0a06031502040501020c01050c0705061902060906101703160501061a03060604050409050c0d051606050415050a 80
    0x7030b11f00002095800d10206840c0038030f00481d00421222500310807204015400001d0074030710100903495015680ca03620056800355610b05002c54102105a01c8030003150140110315142d04040c1413010803582242c108440d100b2003440386003105c0e90445070481400c1001c0b02c00142020301c0300001d401800c10103600820314040c201c00c00059503050341c48401076900a1088840e03805404003600100e01c2640512405a0b00001d48900303550311510040246440c02019074803001d86e1040403c80507040b076448006164800350007500003070342c10003001358814212030040009040074040c01500c200b55015500b00c3d00e4095450f9100d5100c10822294488014102400200c05a0920390700920f030707a00074200d45003800382d0400000904070059a002c0e120040101d840c2924007410480105034000003200e26000300248602c0a584aa00e0f412015024902600142c50702c0320340c810755410f95403c100e052207404e12041c00300c0c81d10004400b102091038102503035100e850450507a041090711140b110180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 392318687 1250 392317437 392317441
    0x207050c0d033b0910030206090a0e010305010504140d20070b0c030c0705010207030804120f08120a1506080f2a0d0501060e03191407060c1209060203180612 69
    0xc072203402d0084040c82c00303d01c0c090040d00e050100002c40d60306a4440290b94000c0c0000e0001d0718001008040a40000780240703400c40d580e00c601b01e2447c1c02648156101e035510760800003813111480e0100c5030b00c40304001070041003003402c0003e41407003817855405071445903410304100d502c00d04000d45000350030107100c4a603c17107001401c001d81d030758400341c080e2845019241c400150b03940000b5400d0180c076031003003800342002d090081081c2da03480c10312000c0d6018400354680b240444c16100051050001c0500ba0130424540800e0320401c0d01d08500034040850082e8004009813548140c0450b00000c4d9240000456140c4440d01e20503166000000300d10801008000c41d480301305c0704020800d03000102014420b5030303a100b4041d207040290254658241d04030f42c041100b4042d8041801907001d2043d5070451500c0c071880c2282d40340021070341101780410541186581402040510740f481000c051400e00040f1b070414038025282d01500c1c200020844a414603502c4c0d0b551100b0940310760750200b004401181c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 392319937 1250 392318687 392318747
    0x6040f0305042d0806010f0b09010323040209150d141507090807140607080c0709060b0d060510020a240906020a03050a09030f0f030209030a05010b090a0207050c0d03 73
    0xb5001a004051501400030002a00d40004245c0504031001071035a00c2220b49405c01c2c1038141e84c0504807580c101543c80e0580021821294051401c1034a441d02200c66803800d8810b0241c0c00c48080c200412081c0c00b4502c081107503951102d45071449610a0a400d03083c43d03e07485407031403c8100e441418a54041c0003c02003810f07400300b0b1500c110380300e800c225440c1036902c00c00103815410070940340d508481f041100e50080342c2020001c059194030b502c212180c0725501d8080b00110307407071b54008001d15600000c1400d0308003840d000d403d0140c00202c8582c10304070600c040182d5500d000190003400e2900c035800400f404002000201806250060140303c50741e0070303250010007540702810742804a850300004c110b0544142c403c031022285d06407980c000355140c25205a40500c2c0700c0d2034103070402d5000c220207000e685052090070500c611400000c40c8021001040000442c00100208002c3c9d01c144220b0010920001e5007125440041e2005071001c140b5007401c07200800c200c0302e002c80c0c0c0b0b04044962108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 392321187 1250 392319937 392319989
    0x4080105040c0608060a031712040501230c04090905030c0a050604060516020a0303110d060b071208090c01051b1c0f050c0c19120506070810050306040f030504 70
    0x2080b407060108503401c2e5103525080d00c00040541c0d072260840f010348801d000040066402d4607041001c0712002d0f0610400043e07002821004540490ba56515a03480c9443d0108250f498444000090b10042c0145032200c3c24100c0790186100e07002002d40c40f0881d41e0188001441141c0407840c162040d20b81176162810003a981d00004e4608490051070580054941c09000610300e0341d6001643c09040030700100d403000c030081e1010f0a48242584401c105c030100140085c130491004207102180203481d0701003030400d409145840220003040c00100d10400000700c50114450544000909100742c0720b242c04c0c00740c0c035506004880360301490b00c01e81003c065110030713a000d6850031840310f507100e070350140340440112441d0017821034201250340030803644640d6160034a0a503502080f4100ca640a180e81c0b02c0002980c03204015007030b12160801024007611580c40718440d50b0180340f00030f03568090351401020a945100040002c0c0108a0031107040082500c100308940c020b0405c00741e08401d1058211034040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 392322437 1250 392321187 392321191
    0x70603090c050607050c0103091b090911010e01050d0e240f0106020313091d16060e010903120e01030b030d0203042301020606011407060507050319060e0601050c010e010204080105 79
    0x140800c482007001540703141c078400320343c4110390001c043d05032200c8107030054000e0191020101c0740308100c403601c1c442c0900d04c0c99009008100119010602c40d4103800c1c1071401c0c0b100c0201c141c0c100044024403541d140d0700541200c0440c1c0d01303508001608110114040d06100c1c890920780c1c0480d80480124101019861245005041015500c5802c2c0da99043c240d81d24403900c86c4100004000d158100700d0511a60720005407400c0b00c0034840e8600142d81803140c01d01180704000307141810000024071401d540440a1800c007802800c1c450010b50071911101c04c1712020b104c42c14208080040041c080fa4842d4120106000000d0116441200305010294890700301e80541c1d04040e078051000d10f0a6540e400003031100300410b80280c9820b490315001101c4030fa404401054040b60304220b83e42c00240744e880b070039100d8000b9664407500c906206400415503428490265805824a102270003039a0100c5040317604403109082c01e9a0f90703823a4035007140c0034088008541140b03510100d00042c1d2a401900b00314 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 392323687 1250 392322437 392322443
    0x270f0902010e010305061507050307060c03060e090706020307142a0f060f04060c02360f07020c0919050406050103020a150f05030a0b09090d1418060906070507060309 73
    0x41a102e042c400440440d04201e0b61140d1100b11000b4902c9003c4c4942c00500401e4083c0003600e250603919104d210556400241d00e1000039039500d42003294025505440c6d030800d038030001070081d480c60a28000d41c1c0c0c1c000c840340a0f1500017042c1300440d8910003081200c104180710121601c8020240181031813410742c0c80c21310b900814005036856001c1c9030040c105c0b43c0d0207420820f080d0030142005003c81e001c840c201412600004006040440112054040c0c003020040100b802da0b0702d4000d2030746040301c0b2405441d035030b908440c40c070900007120707000300d000500c1e2081651203494980c1c075211024088101c580d86c0019035031806042c08280600c541040f4141c9000ba41c513800103983e2000b005907030240032240c400c00124440a0401503a20540003590090115540490700001100c00255007400c10395065045601100c0c11050701a0022140c0709480e0900c0038170342c1810b803507000703c10003010b418012a10805000a00c401d02d82c5d22401502c0d90250020304981c80039407035060140c000d0000001c19 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 392324937 1250 392323687 392323697
    0x100b010e031615180308031e0903030901111204020904080409090311071401020304122303070b0c03060d0206070f0506010b04090b030109020f210d020114010906050901270f090201 79
    0x160100501030b0550200905041140c400350038515200e0122a400140c00844040604081c00c8d00c605844c1c40b007140130f55150806903590303040024500342143c0006a244001c000103129040d41100503482065205806070742c0f034130007580c80707282444081c440c0d034001603151490000c445042c940d1190104540081060484125a1b103e042d2540801030304520b1600690040005200141041e0485100b8038416801c030303c0c0e11441010f84000300b400302051107a0907030002c110541440f0b03c0461083d0411071400700d680c5541080000300d0460241d80c1400b038011080000c0c00c2e4108032020640308030742c0c0e4004055400310b503141c0704141b9266103b03204404805003000040150ba14040c031480703031b035980e00a2840603090300c10414400c5004441a0030321058007c044180c0da502c5091010703c149580399400041e1141c07090101054452060300541d90b160b140001c10301c4103032070704d844040c191022018541422aa2095007050002e03a00d1070146109080ca2985200348036103030409450341d03200740c81d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 392326187 1250 392324937 392324969
    0x1b01031a06030106200a0602121e07110f0706020106050102160b0301090f0b0915040f0603020f0f030304150801031203140615091e150705100b010e0316 67
    0x440d20129118002140e005008000401c580750203030307500c40050883d510213100030740001002d9a00b030000c091025038246400080300c40c01802c0011100d544080340b00210011041036003e0140c48880c0141588284103855003900e560900402601c44600300300412100c6154858a009010302190700c034260142c4210032001c183c02c00701c991801c064500188282d802d41c1e180c4000c45010300041441c000d1002c4c2e985035607850b240c0b2610f00c614400c80044c416080454455070600c4122800c145160700300e0340c9003c1e814401a81c80c0c000448540c0b2084841e403190030f00700000070b400c500c903590012460074909003414400c1b54100000a040340c1c0114034103845140318034026400d0b14280328822014298800003d05c06107813055075603080c494003c52040c244291900841c0d5840701c400c80a007900880d44080c100a4944410b6a018151130003642178189074480c0d5900e569802420401100d2680b0b5040ba4401031f440352840100194004007100c1207a40c24030707071403070482119001b0503d0b00034403850 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 392327437 1250 392326187 392326211
    0x1204081b03030f0a03090804090f0b030609010e06040b040c0f0603060501141207080403111009050d0e01090614090901060302090102010b090112020409150204030818030601030b010b03040f051b0103 87
    0x426100704000510f10140b5100700c3d0300c4120300408165104481030b2805000100310f82d80390740309800503c5000e100005840314913004151400034010078480381a8101001081a010701007203c0d6085640a4112a204d40304e518007070348480d19a4110840d02500503800040c100c1e0305400420403600700380c03680c03145101d03248510b55032445426040384c0103040c80800b26588601c218401c1c2da103c1d001c2d20b01042110782211100e0308000c803480b5030345005a2130b2400e0000b802810b000701c041040c12030a01c20701c5022524000303001d10040341b00ea80203006c0b80c06642584146c40c07004541400c40c00130982d5189684641c40039000b5007201584900640ca0a064410b060502d204154161148910304da03001002035402c100150024020880e01004890803510003452280058009140715100098455a450300205030351400e8040180c030940c0a80010000300b50050160760544881c0709030941d030b0755264140074a2543e40144024035500c03911024144122080c10703071081c0d07100d00740d9061100c840048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 392328687 1250 392327437 392327443
    0x70f0b03040c060e03010b09010f080709050f07080907030501020d021818150420030412020706080c1b07140f060c1c141201030b090616111204081b03 66
    0x1500140220b03504801440f8050090303440004c6218001c0005c0f035020011404200c041c40f0a0307002030708048000703000380450501400000d0140004440400851138a01c1400341016030160209042c4900103020078a070f04004d01418010b150494001c5d03580381039200b18940254801524021070300c464240d0080c0c94079020580700c2e0414072954001c503082d00c44980e1954400c0100e6034055200d0b41da068840642680509441307003900d600a41583c0340d10b0581811000d44111020700000c43d08005005d0203120781062540303402400841c1140d46800304c003c00106005560000030740144684000007070b03915006001c4421803241607806840e204486400d120741e502446020004940203200c03880c0311806030040324004103000d4039200045000201c3e21402e190300152481c00c841001c60014424062070700388107600448000001c0080741f80071421125441c800d840d9607410000015201c00308054200307c5101c1001c50f0340d42c1c0b103980d00e96507041c2e0750380d0f18448030004055041c00600310b0b803507107004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 392329937 1250 392328687 392328691
    0x503120103052b021c0302090a090903081f0308090604090f0501090f060b0304060e0304032316150c24060e0a09020d06020a120f09050c0307080a081303050d02070f0b03 74
    0x41c1d0014031591503500201c00302c40900300c02d10705c1007507405e01003030815503512011000284800d0388006400f054604008009000007450300c00459210516404419019010002180c1c0c00c00c00f4561960b003007100080d01071089070700003c0340c642010760305406004258231640c1242d9020364200400c00f003810290301507920074461203426074002c0c80010041541d0341c00100003c0400b0b000d82c2d142607100d65803103030240007144500c40788441000c04070b607255034100201c100d49038450709152411407400960001030b8481080c0c0314100b1070000011020010810101c0c0341c084003800d44161a01d0b01200108014201c078481c041c0440c4414001c50709a62062284809144c1c015080ea2280002030b01c52401a50000040340c007001400d1172010013407040f600c40c3c412005c0b403140010a1044840c00d09601d03041c22914000d20903003050070200904900060210041544261210b0b250109000e503c10b10a90326400070305240a27840c1e0030161241d0205103501610b01803549e20000544a000310180c80c081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 392331187 1250 392329937 392330023
    0x60f0f07020327031609050f101211040e0a031418010f0c0b1302130b060307110114040303050108060901150506030408090d08090f030c06090409050312010305 70
    0x20800c0700c038580d20f03003110041c02c82003600d94640c0c034800807010200b46840c004400c040e01d5440440b405001084850107903039045003083c5c2c007440107401c2408501800c20294414510b5041c94070300420f0420811005107455003c0041041244120042000d40c685010b070108800003029454032403100854603059483e001001c031902146548100010754021009003402428800181d1402c00002c2d81c0f00625403085c0c54aa0369070707441c042d4900c14829428181d0200401450402c0c0c1d214016403600300a80b0340c45009403a05254140006c0c140b0b5005100c04542c08000f001c1c03d00c01c0006164040d0031042c1210b103900d049900c160b80710b04401e401c81d449552030114091500000f00400d203814009141c0050080d400b5600d490614000540f52040e4000c04807030340500802c0c0c0c0301c610f2400280d841c080170000e0740034000c00844c4800145044c890458028881c1d0750341e485001c1444010800e59445001c41030f00700401d540c4a0604a54800d002404c2200a1402568100050700550318403000994 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 392332437 1250 392331187 392331193
    0xc140c0f0102071409071713020a050907080a150b03012408070e09150301020c16050a1d070314040c0f1202210c03070308030108061302100c020112060305060f0f0702 73
    0x10354082004243c4064030314010003492030850115081204200d234003031075403544000c0810b1b02d5441808228946644128461502881000100c0f9000041140c0c4000101000140c07000406008104815590031410304000301100210304a00c40359500350303c10741420a507009210300600304540101044442c0c1c00051540302508503181850381a48d50003c6c1c0e000c0c1c410f031840200101190880c0c0200c0e20307000b03c0c0c1e07010701000c410261245c442140078281c182c52102180b41820350b01e8405600440c4201442000f0100103151076129510004003d2106203000c90241403d0400c1104c0e2140c03030085448202c0b481a00045441884103104e200950161000c2c4403180c2c50108078045402100c110350840c0680403520b03216640a000c8a405940314114040d00c0b94104241c2900d018001008245581100d0a2000151f074841c181841003504030302d4600101052031004850440d580010b03000d00c42e082041c04001c0042c0860210320422041c1c940d124265501a1340c145a54400e66105026130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 392333687 1250 392332437 392332469
    0x90b0a080a03120b1507020103060f14060f0d0612060b03071d040203010e160e22120e0a03060b01120c0e0d021903030305010e0106020a0206030a0c0c140c0f010207 72
    0x2e004110f0720050400803100064240a1080401c8021a00c0c1240c020403420014126007117681501c14030b40900b4540540c20b00d09420501181e00c0b81d8410303111181b10304808600b44490f0407002d0100c07644140e0010342803001c151b654400500d8403010b800c0c100c43d0749080480605c140e0400090034011501c048900081000c13036414030b060710503c041c2080c1c1e015500c41e000111b035220304000e216075904d060340501d05803600c0c00030000742009010b4011a140031088461480941c11116541c12868004c1b2030f2010300911203006840d52248020100e40140300c401c000828824140c0c011030401c0c2084e21004031900c0d0040454080300d9500c4550070109580711400c4849051800d80345c06020b02c003400c1d10401e06c00200044000300307010703802100007a8903040180132140c0d182140c0740c018002400101100c88241d030000e5007500001703180d13452043c0d40c0d402c4101e04912401c0c6009255400c071090f03980c010141d030700d0a912806101c00c058001d000224110285510006155003118881c1d0034282c5c00d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 392334937 1250 392333687 392333693
    0x3093f051e0c0f060705060c03180a0c0b0c150c1c0207030914010e0616021c0503030103082b060905010b0408060412020a0c081b04020f030a0507050f07030306090b0a080a 75
    0x503da000c0c00550803203c284401c6000490810003a80203640800035036446c1e140081d03614080c004107101054140c1c00c842c0c4400c000500c2050703031038141c49008180c540c49038140c0411a250061441610188d414a60103024000079034500801d9090414200c5c508110f100c803800c101680b0400e580100050306d211420003000c1d02c24805042c24480500d01741c50310386011400250710750070107410750404192f000700020440c940404140d24101c87c0840e801000c0001d80c840503141d010520010b0605a0005941b10007403074184001a0031108002e0404020b039900e010010090070140100c002c810315001c004101411076105a40c200d6558000402082d6199601d2106c500d810309502c41c02c0d07110b0014410009619010000040e2213188020f16140e244181c2c0b2814114480002034003d42c4100700c162100d00c0c4001c112580701000000108454903040b004503024410031001515156002c1a00c83c05c055154201504480306168284082c002140800113202c110f40300704801c40e40811030401c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 392336187 1250 392334937 392334949
    0xf030c12140a0f14040b030f0601020f1005040533010e060d030e0a0515031603090c0e04150f0b031e06160306080a0807060c0c03093f051e0c 62
    0x101e1540c82ca020784213003100640914841d000780c0c101d100040d0f004030030402e4002c0642500c40e400b2000344001c050341100d004c51075403680060808034080d035403603400040501800b00180ca41b810701d0304812080081042c20b0382c6010309144580321050012610000640d036203103a0406000d007800a012450f8040715a1301520f80361060760b06540c1001c2c00820004841d56112004440c4081d05920566286408480d90306808024201d10003450f107003220003030109913560410000d03140d1050000b03090351102c1c1041c6403c030b642003200d0041c20b4146913407940e03c106280c101000c50001501240c0744e43e03c4090002038408000000181a68465000107540c0201d00040c40300014850800061903521140c0c1039007000410788c001d490420000402c41d0401c0440e101c0caa59050031498100f640c0c007000d940040000e002480360991900d2811110380c0c4079007040e89000742c40d0300c5950000101c04407810010307150302c0301300c04117441a019050050000f501071880071b07010301c61014040c000d00e1029004000c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 392337437 1250 392336187 392336207
    0x110307060806010f020127031202070602040302090a09030c140c10090519080a03030b1c03090513090221010b0a08010c1b0804050d030c060906050a0e0114130f0f030c12140a 76
    0x401c08401c80003919440309e480240074480c0618005a6aa030a6005000c12240c0103401c001a5514212420b404640e0100c4113015180d404041070310211440c1c903415140036800d880c2d00e07074840c449401500b14035030800030100c1100c0059485442d015529281c0080b4415181b08003c003e40002406200092207a4031150b40030301c0c02080c83d55a1020b14591841c0e510300300c0c804802081d1100c505000e0b620304141da0100c1c0e000c005005102c1a00154042160b440103a0000f00203600d0140b80310140c041d0a4000180354900074141d03801040c1d0f16240c4034080c01c004081e1101141800301401103024007100240c3d044ca4201c10a03524080c640340520102e640e0140b0140c1c200980a80c803940004c00900400603202c1c0100b030f000c1070a0401c0d028200131540c25004603500350b0302d4a524101d0720075010701d032968051102091140e20420720301b000c08400d02c3c001801008403007014440c01c1096004050805e0090058030100580106148141d44068440780c003020b10b5070b8280b04c2650343d03070f2165034450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 392338687 1250 392337437 392337443
    0x40b0d0906061505120a0605011e020c1216060e030316050c1003020c010605040c0215040f02060c06040b0f06090610031b02010b1513030807110307060806010f020127 73
    0x141155540084a2106803c240e890001480000740b01c41990410700d6456080301ca040002c01000c0c0c41c1030006071900c4419011440c00300740307440500001d54024855041103000190803118003650030b040480d110341214064408100d140342010640620030b440c1d044001303401a006618000203c810001c1030011080f084803988240c602c0100c064581c1161074a034403001d0748000d0385410031f040c03009003968044d8101c140558078014622070700990008000b90300301a500722101c0e440e01c0394208005003500703440f00a5000840098030b84d44c19880090700512030f41c010004154540c07520051521b840c801501c2c1254829080800f145107840c12030204200510b1900b0b0000d410700d06405501004203000d4001000f5075175030a44107c81d41420384104091f00400943e00c0e18241c90707020401c2204410f80409403204a01054500403c8004d54031401e1403807000f4101e0700c4040ea00d420080250000711002800100390b016001081401409068481c00044400c45040c00c02000c064400840c146400e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 392339937 1250 392338687 392338691
    0x61b0f080d0605061b06180607050a020f0304030308060a091103071d09091b06040305030414011b12140307090b090a0509040b06030d0206010b040311040204081e12040b0d0906 77
    0x1403903135404004020343e12080c0c0d0307052101e441c15960207051802c01042c041038020440410544201c000c141254020a00c0c2441c588894080300201d260a01c42c0002614a1000040c04000c2c1604407003810310a150465001c6505503d400e141001d03076600110701e0148100a202056805005070300c85000400b4014148a071101801d002400010003500c0502c01da400410328126242080c9921005e001001d50380c0c98a8503203140c1e1115568426403242483e0751a400030001d00d20303031040181440c6031400c907488041448160500c400c2c003800506519020618003421201032541c103000f81c0348070708c0107500c4803003409262480403030065000c40c540c1e41d80160083c0d00403940340e031801b400c54081d50007810355281c40d141a6060524020340e604070314056501c80d0340100b10400720300048030281c1e60b1160b03801035608140b40104010303000325082442e1078051034484900800701030301d001c1c500c3e490b0310007140d01640542c800500140f0690052002c1048100120354440d1041c0c2c00181c01e0320711070400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 392341187 1250 392339937 392339939
    0x2010c02090a0e0705030c01050414030c0603071d0109080a0f02060409140405010b060405150c010f0608030901030b060324030a080703020a050601050415052101050907061b0f080d06 80
    0x54444003080368070150b61a91142400518182004640d019150071350040152440322400030302140128851a9241d0342c0b144540d0a01da10144081c0503100c501a0040d516820102c00c042d0071010040c100402e01501d036410b0030655846a5404422101810058586444607440c0d49550311013150007660804000c020008016906100b45800900c401c4a00e562034100b0385030803429202d00c3c4080030b20810701404140100d503a4040e14092030700030b0344c413569034440c11001c11030f015100c100c4800302c5a5140500008140c1004001040c0090b400d0f41d04001c01d100308010032002d40400d486400c01c0400240c842d00090714045c0316400483c074010100c8158810b02d41d2820800c0e4025001100107801c40c140000400c0800c0040784d02401084a040c070100410051a00d0700c1202c91090700d100c1c032103603008079000512203e903103c018683c0c03000a020525110701c9190b83c81c0b101d03108010001d8075814400440d00002962035400d01d9003d0fa005140c401c554039480d810b9040554110034036995520 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 392342437 1250 392341187 392341189
    0x50a0e03041203020c040b0906060309010e0703030c1e12030b1201090c030c0b090114181503010611010b0a090e030d05190501050301140f0a06030209010306091719050702010c02 78
    0xa40001c1c40030351140d00b040c0e5a940340083c1402120960b15008904003200c4900310340e50f20144a40c0103406a400c1a1280c0c3e50207003441c09810f00c256600120701500d01c1c00700c24140d1184103520301d01e0103404000003031403030b4080b1420004e04134080544100102da0261181c288079802072020604020610780300c45084009180c211012580c0440c3d020343d003840304004001005826000508481c80c2c1542041c0300040041d001c0c401900d401c000c5a5000034020b04007411902d20148500c0c006080706040b00703548140c0340e0f4035500a01480d00407841d51028540b2408050080c2d6044407400b03030407902d0031464125482e029009007001c1003681d000c107104440e0002024400c4500c00d103240c2c0c1c4104e1003c0280302415044070010307000030707010380d0504064084c0c6d5508000c006401000800240c0421f6a458110300000c1c01e180d00025440780b45007000209100c001c0c1c101c25034680c0151800c0240b020300342c011500500c1007805903869207001302081181d8902410260503124010705240040000c070b58 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 392343687 1250 392342437 392342443
    0x5040c050c070b180a1503020306060f1801020111040f0b0903030c10021305010c03020a0b0402120109110301270609031808011e0b06090d3305060306040213050a0e 72
    0x10f0490200141c0c00704441c1d500702415003940b9625001038604948560a1101c8810704d013a55a210078180350b0000081502e94407850304560b04424030040e419200c1145100307409200d010042118015030904030400c001e8800001202c04803030540e1119044c05191030001c103036503040700c040142e0500090283d903688910600002e141e07921079a400594900360201c07444840314007504070904101e6038000c00d0002940000c2e44804070750f000a00c100341d543d101e10010361800c6c0f25110b031f00385079400e182c0080204001d000303407082100f000f140240480d680034100e251204c005070031601c10030b008990303280d004103110394040f00600d0700900e00388000c1d81058440d10079541c000d038407600302c60395071303514009519400c0c0030034050080806c60180014000000018014003450407220b12a000c6056400f04000418003042442104000e100700c611041208440c0650303940140e0708107040c1440c00040c07181c9030119155124550040c145085804142099030080900420b0700c0042e95494072034441b021020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 392344937 1250 392343687 392343689
    0xe0a14031207020d080a060b040b1812070f050d08120a09020409030c052109060c07121a0106080412030504060905060f01090b03070315050702210901091e05040c050c07 74
    0x5a0000c00304402d50100041912100812900c1c0b061f1401c402803090944500464003200c407007002207602e9120005001480c00110740c03089500400480c85074084039004558001164440c4d040003003c16038400500c031800d2800700740280079600800081024101c0044526013168901c41c0c0001c03000c80c140c0c0420200c90000c00240c01185584900307000300002000412021040c20392107200001240c0c1000f1094040c0f4200580703d008081220240303003108201040003040c044800441040441c1441e540510f2090707241c80702405a540041402401001d050f802280d00010803242485607560840080c00301a02c02c90340d01c2e45842502022a0b4100b08413070042010084201455140c0f6580d0401c4500610006000c0c1d00061010804100e048150b09091840b161000c581c654690308220304000001c0780015070103900074545001c6040d0b4030040c00c02c0c248280c03a54480d558503940000750081c00501440c08011000c903003404641003941081c1071a40b07060270b246081ca020344121034100145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 392346187 1250 392344937 392344951
    0x504030f0f1d0625030c060506040b0a0524040e070906021209061810080601110705030309040c03020f0c01060303170f040f020102010b10110607092313180210030e0a140312 76
    0x12646c06102400000d00ca001d40020b0200c8040003004068800b185112178148515881001c045044120700c0c0315202030020314800380f44042e0307038031030310380740450000b00d41501c0510003c4c10b00b10000c11310900010751022042d055000b400d05122600c800c001e81540172500c40c217818000448030000e0303500d5201c500a1002d0240d280c5040502d84880014425400d0f214015280e91148100304443d0314040308175925080d013030343d0100f26091070701c000b50060b00c100680407188603400100c1d0401040103520402c142d070f21035a541421520b9010381f40440314403d9441d181e03103601000c04507001881828115403414410f00001c0f1f04044004000b4141200c6549180040b80050340e0218030801c05001266014040341810860344e8100080b61007810420001a0303400071215800000341e41d04c40d088410014180710781403043d1080c20f0551a600108158201e000780c44200c2d150f50310303d003e0b00031034454a100c50024900000f0035107504601181e00080403d00340002c2185a6012191102141c41410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 392347437 1250 392346187 392346197
    0x40801020a0305280b12060f01081506010503130606030b070c02190639210c0215070309050a0803070c09051302220504030f0f1d062503 60
    0x1c1c0781c0d0005426514000e007082c5203d8040412219184201c845258201c2800340b400101c900600b008151014400d81d4014064071900d400c103e80b0b4004440620705955410342550091100e561810300300d0282904c1c05404190306100040301400e40c51710048100e0b0044d81c0c0030850f241d407612189600320055400d48002291451400300394201142c5910380b03486452a00c001051030801e0007451200d02a1201605548010440b241c4140300b800c114404c1010201e800044140d0f0300d0450390080300c03243c2c03511005590000302841580215281d04010350060404900300011040850280d40144811000c0c00560080498581c0302d050944001d00070820003980e80301e02d6411b004003c46200c0c4c0c003113003001d07082c02e0030440301554100140f1080d0394151000c001c50384070507103144038614205000d190700c0c614110800007030560000b664403000440d074448080303942e00c0120072950b01540034560080d8070302c0c4510340c40c020f040400041031090740070740410400b03500801d82070501040d500c2003540011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 392348687 1250 392347437 392347447
    0x4050a140105010609060c0506070309150e0a02040606030b0a0b0a200c01020106050d080f0310080303040b0f090c03030403110105270415080a111c0605040b0901140a0507050f04080102 81
    0x590400c00c117001501c1c150a0090303902503140d503005d664000013040503040540f541540010003c8084124261f41c1070b04109100003520300181594809803444260b1040341808070000b02e00340240308200c0d0031500034007118130031030a103030054030f030303a4455614030041246042c0801c0483c45e01d0441480070010760740240031030410450009081d0381d101e03080a84214880681d603070002c0d0520007190352070a1445134094595681701d1420301c05ca00030f6808811540030000c2080100014906404e11448800c010303d2074a45407050704980d01c03080b103401103405038801c00c02800880e180c2c1a0290072010b052401c540b902e2080118580038048848400d055011020b18424a51500e406403902c41c802c95140450303940d1a2600b0541d442140075406410048103600c0b02903513850b055441084041140d08103100704056243c5600102002c40d4103541409941020810200b018010704d45042c80040c401500c82e1184054040107100203003240b014003c08004881c0c9290160010700020310360300000680761 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 392349937 1250 392348687 392348699
    0x3140904090309150201050f13030e10030213080102031302130617070f080a081209120414010e06030f16050c121801091514040302130615090602070e04050a14010501 73
    0x40309016504c0010b5906141c00c0044c4002100c0f011a4403003c0d000c1c507410b462240d42030903500d400903040586c0d0407450703603003800c03000303d406400601e0203101142011003801c0e65200c02c14200e0000f9a120070101035400c0601d40540751862816030040880c29001a10b00c0c0d88116060b440d02d146680791205802421007000b0400c0403010740b900400000c1e01401c400220703592024164420300b440501c0c007809490125011000811045426112a5400550b11a124040c1c000c2030440b20040c3c42c0000c0118201c00a00c1c244030301a00e01440d007504110040c3d07160b403124625684188800701e41000300501c0b00b10702c603040c00c214841041e00c0d50358a8543d514691318920381c5500f04000554140040303c002081207125840d0480f0006d442803815400384150880d0a46541c8129440a07500502c0d50703c1c06080d811166002004030703494035513900d0903070003040c1041d910b15400e48100405070f0030041c010000c0c00b00d2001d00a900c1351291060b80d003484150350341c00e400340d4524483c1c1c001c560b640c9c0005000d6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 392351187 1250 392349937 392349959
    0x1090b0108010504030c02040906021308010608071a030c0c240612031905031306090b062b150908180307050a0f1a07080301120605011502030703140904090309 70
    0x14101c010000d0200385050303140540141c0c400c140c000c0c002e5640b240170f901405010703815214403200c01e100740310606a0325000325010382190302501c09079020b40c041c001960b0102540a00440c854410740501715130314490100c06503004070850008600444200100480054901c001c2d00f070030050007004181044018001c4100c411850b07069164010082d498103058001700101c0c3d1800e031464183da070b95664070603505101c01c04020007810309013000f090400b00009100a103101750f03400c3c0c0c1d02004400804d012074100d41c00b10000c503192041c4095940b801300d078462a01900c1c500c0c055002080b40c1039030355210034841d40050540c401c00e04800c0c05522480c54240041c9004010840d80b074850f02703062041c2038200165902ca02c20700c010203215003585141411064440043d0000f1006031a513030360303e45c1c4904402b48128126089481e2038004910840d02100d9900080400d074003e60a0450390b41c2c00307480f140e40140c000060a0b000380400d025998a900640c401c15103e561188001841e215034102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 392352437 1250 392351187 392351189
    0x9020d0c170c091e0402150c06150105030c16060204030b1602010507030b0a23060a090e0105010f0806040b0a0f0b040801050609130b0408040905160216050907050d020d050901090b01 80
    0x80f05001d481d06100c61181081d461000c000801d400c80349150304c41e03100213450280b5484981c000c0e2070001c2002480d0010220300c640c8a038640a00076110ba4104034011102407204440502000174140600407014600f10f003903148203031003008014503140d201d40707900f100d401e01103a41c0000c110101d07045050740c170340c280203058210a003402c4c24080c0d00f09010025008050740c0c007134543d0080a245038134008007250601108001c001800960b5641400300c0000c09100c424084d4001a64060f0000034195100d40207401b00e0040642c0d480a16417601e00801000e400c40310b00d2541d000c040307040003190020701d800750500106611781c0800d60301c1c0e14050320b00342520402007103107108014a008000192100c41d0a40390050b5202500c880c15950300d03d00a4a24081d41c0c10020840f450601084800b404104010307403034040c0d079002c90700c1040c4400e4003c000c07101240a104c0e0040201d0000c10780c82400707407001d400e082d099080054240703420b0f2801c03201191000c9690f040f1907174451440405012014010034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 392353687 1250 392352437 392352439
    0x20423040f060513020a030906020a08070f020703020d030e01020a060606020c03010b19050d0201140c0105060a0e0405120d020702120a020f0a080d0f03060305010510170c0d0609020d0c170c 83
    0x201c452450000004c4143d07580d1a00700103640d40024202c00d50724801c2d4890190030741c0c084011900e450f200040241402c5080343d210b00810031218403a0941800040c1d03541c1103d500410078181e10342140d0f012507100346c903c61018194800c0e502030b00c3c0060031034010100600f200340d000742500800c4004150a4a03040000180100401c100c0d040c202044c451105060707440565480c4c0f14080c540c80100c60302d1601d500751014001c008200c8070000a01074100d04c0c043c0f6411034003100519115010600000d100399402001a03100c6004054071003503400152044444c5110010700705041500850001c0845610000e100d400c9500b14034110b1030000340b40045840b040d16240d00c86402c1c070000c43d5880d607501424000380140140400c0c5100d100380c0000014591040c02405281000d40708020000503900416041841902c7ea40d1551000000c1244a4032070060030300f07292903c0c50300c9150040006000507a04110745410303540c08036560080382c0000301244041c91500c020059096400e040440c1125 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 392354937 1250 392353687 392353691
    0xf06060518060708130b07030905061903051012051c0309080a03180f060b01350606070605130c0506071208060d06050a0b0108220f0501020423040f 65
    0x2480c16000500d10007142501c0c00d5031120b6561546040410b03c07800340303100f605908203030f91002103020100c040103880d58a12a4444c09842030b2107404001060044d010b005542d54101c100100e0414400d4016980010a6030080540713103848074034a03c190440d1120941d010340c81503054240c502020941090741064520381080b5906803580d039030b00284a940c8404040540b58010075003c1c1400501001c1c0980d80300b0303e24061004a454101c01070180807440c580468034240000740703282801440c1d041503a56410002011800080d0000ca100601a242c550041810b20031800004c6040c42400e0113103031226402c0b0000005490800703000b100c00c0d0010360154905200c0200000c400080601c561100f509140e46c181d92082e0108100d510140d1014024900b01341c140080141d140c0d001c040140f50030b0742d8a900c907948405c5941c110150003100307030448003100009000400c0c00c1036400300c040c0303104500140c6455940c40b221985035100108081c900744040d0045005031410f446050040380c030300001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 392356187 1250 392354937 392354947
    0x3140304120f051909031a0405100c020316140f16090902041b091d0919050a05240906070806061308060a05010914040f06090c180f060605 61
    0x18151040c510410300d40c1409030000d0441c40540c000d00951306000824480350016032900f04006000c062030b07102c1500c40c00340102807030007103071013010f8100c0c412038012000b023001ca01404174183c0180000100e00c011800140403c003814544c400e080d642860040807070080b899144c0041a04105d0b1076010a103440d444821061407050404a00b00100d851503c000501200e080c0041000f60140c2c0300c0e04051041e218045040103900000e44105403212224640307013016074200ea25000010a0f118100240d1010203444140310101207401c0681d84103200f990a041030507a01e4600c0e041c4205103480700940d0310039440c0c0000400b841e101e40d0150340d00c07004015604200302c019100d080d02500302400f91100080c01f00700003d00c1c250000c01048100100c4140e440c2403a08a0b0080100707001c1c00d41c1844c10a200c41c052280b1000c0520b010315000341240416540955a002c0106095941191455a503c00c001060f10b208003c003005443e080c0ba02180e0000d9440c2041d040b285640c0101040c0101880 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 392357437 1250 392356187 392356193
    0xc0607020a030c030e0105040e040b0f011706010b030a150e010509070c11010f02011e090204140c160204140103060e010606020d02030f0c01060506040303120c230304030e1c03140304 80
    0x201020f582c68140c2001600c00142100413034091043d81c201308064520032060008125840200038441c1100b040d903501345d40d881c2c83c1481c02d1205501c0209440f540300e00014440414110015500b10040440c001480c014480000005804960040c0e400c00d8139140104424203040d42840d03070000b098905407a03400c410356074424006080149190400160106680d2000e000354025034141d016103a022601e0030000010001a24810000f01e01032820664021982e424802c02280501242c040882c01c1c54880070901d0003522200e5400c0e80c0c1b2030b4a50010400d48000c242c00c80d40a58060280410280c1800f9040c40c20b5a829510985c219800101040c0415601005441c82036012640480d610100b45441b030f0302414982c0c01481d413040e40080c0c000b0030160050311100070340440398000c1c03045481ca203030180c40c0c242900444070620800024a241c212000500466020348641401d51003030300240c0220b2120008500804412103180c2281e10900d40c01c5081d6000300100c0e50509459454140d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 392358687 1250 392357437 392357447
    0x10501140f0a171305070506190503090c0a0b030402090f01060819021e0403051c02030301030314360d0215070f080a021506040e0703030f02031b030c0607020a03 71
    0x18009080d071070000b02d4102d0301c0700c0c4184145039035a415900c00503090304021600114054011400300c2d818400c0600000d80303401c0101c181c40da8107800000321540201c0341e900981d00c0717a100804c4002180503564807504181d880c11864030142030038000e102c0e201d213031620620000c5000500030203407580b801401081403550100364103500c8240f003030341340301c0b00f14882c2d050001a01410507502c1d4960358400c0e174001d00107500c0020b08106c03030140045906424005507040700302c00950b618100141c20420061000c28000c99210a01c0503080047c5d9141a00c1000104000040c0481d040010707400350f44040c3c13401c4991070511284181c00c036003140c00100c0d65400175841e016044084105a400401c901c000d0144d00d015400c82d03107801541566594945041c001c0d19000b034100001c20002c00c6130f012075010f040c00d1144d1071010086800801e8091308540301038030007148000c00c1c403007148020880302c010721044c0351705a001d8003401c0300103544402050084034108a00142084110340c401c0c0031315400f00c2c0d444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392359937 1250 392358687 392358697
    0x108012108090d06021207030b0913080f0c01020d0f0b0105040501050d150e0a0903170105130e0c0d23010c050304060f0209090906061e0a06030b0a0302031203090601050114 76
    0x38120070b569200300c0c1e02041e8200001039002e40014800300310020044d4a0002c0d4500c1500659030030858101018100015840256040341c1c072102c44460600c00601000014408120001111400e20300c803012898260380c1b0084007a02200c0e00d8a6030201310340d0b00d030700824400d2002400c00c81d061a040030002020340c015151880d20b20350f10769000820351078143c803188019000103031005070b591038807451078806001e80e0031003240000c50b490003065203c40c15600c914161080100401320030810125030401800c5501c4a0083d070703000e80311105901e80d4540c1c0c81c0c9038440f4400c40c291000b440e40c100040c0d1180d47c0303405495400e070741480d003050b8490360b2000c1202e9100b54801e000003002c04400800100a000c4c941e03ca64001141800348041540d000600c144946411a0103030010310380c0d09401c0340d01e103140003c0c15030440080941480301c11b0107a0841c1d0000c04010340f0600d0416030b42d0300060302e00800340f240c5c808001400010302c18004e000b806140d0140034203082040000080803240d80042c414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392361187 1250 392359937 392359943
    0x70e0f040c021f0608030a0c1a13080309010b10230301050d0f050304050411040e100501020c120f0307060203160e0102100209181501031a0a0e18030f030601080121 72
    0x304003c10000f40442d0760062018090f0381c02220303120a05500090705084050300e00761803100341440d02c2070f6007213080400300f403140c3c2110144200e034010b503540d2424544c002400c8020255203480d04a02d29403900700070224908901c0d40e861440c0841c9100064140441200c0d410718850204018000b9440380282ca0700d43e00e034860500d22100c0154100503085008a8001c50303032040c103010b001c41d0700c000d448001c0e10a4559003946681580c48044004000038282c2c0304003409604076035004241440d1003065891403040754810b64081850101c01581140d01515045071090b40c040300380b04e0006034403849950200b1044c00d0100421507510b0003c0d640340304201da007144180d0006140041ca071202c80b00004481c51031014071036513040c0310209010400e01050f109000901d840309d000c1011203645403541c050f6402802d640358050a140da80302005000526075508090f0b0660081e0b035480d0100010002c0c0305004105545a04101000500c1d04078103900880100032543c01462403c43c054a0120744154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392362437 1250 392361187 392361223
    0x11b06051801020304110f150d0203010303170402010c0b15040e101b0c060c0e220506030a0309050607060605030307113c030f0717060604061206020306040207060203070e0f040c02 79
    0x128240000d001614231604141c0c0c45801090032501403038250069410790744a502c1c1d1640e0384103040c81001d410354040350041d0004698511880126181c6910250020812804030b810669803c0c0803406854100003014007a5101800c100103283c443d1291940800d001c115480c500c04840000070444c11404e00302905169a809407012501d01803004400b1400c40a084400070302e002c604800c2c890b00240d51203004e01d0b820a00040c80d01c0ca000f0440991040d070503100c1101e8581810b042c4406034200d40800c903400d6580d41c6d0b0210300c560301080600402403251034020203c22182084c084420100a462000c818030f08151182b5400b01c071411540c10791489800074086044440003914101540f1a00300103401108408100170360303892240c80c0307100106003c4a0a0b42c650300c083c442102c0440c883d90076560b044200340070001d40703141c0056402c047e00400c00b5060400799201e030800c0740d20a0320b0000c003107903458652180b2404e1030407041c1c1c60100112800c0080b6209000007944421240400f840552 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392363687 1250 392362437 392362459
    0xc060f07030216080703120203160c0f0203010540020105071704080d030e030703021c03020702130c030c0212030105040b010c080301140a080304051e011b0605180102030411 76
    0x10721a6040c0d801c1204a40e541c101e207040c1030708003110355a202e401c0c264009001e09480291908050088a0141175000b2840070910074071706080b03412282d02c2c0012a10001e0380c80b42d440259500b405144d000385018919605444000c40c8c040712030a0b40e03002d0000c0c403403000442c82d07144204e0841d801e03401c10390203003465a80c2d11042d2a100f50000421144e000031040080703400304040c01c1c0002c0501113444640ca0404c815081c1300c049540e40e001c1c5803030040069001400580200c01000e50340a00d100f823300b005402e01445070b00207010b290403a460342e0600e07940c61120b040d011398180218083d49802d0f002502a84050059541c410b1005005a50181b0b8032184807021a1344154003800b5202c0d003000c0715544a584a44a00d0310005484214610070141301d60082100d880200440b012101d00901c3d00484007880b110380d0140320540521a414851090130050f074907460981d5609109100307203030000311881d2102c507018000c94060b0030403105a105008000001c0c021b14000001040201e40c050640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392364937 1250 392363687 392363701
    0x3100b03011e0b01032004032402040b18011d090c070f080910140a200f010c030606050c0a11030f0f0c0f0414280903230c060f 56
    0x508914605240541075002c05200300c0c03660b6500400f2480d80983c0c0c1802075460544941d905442c0a401010b240001080100001082c514048406000c0c02d11000040405a81c0c041d00302d03040740e44114070003100000c100126000b81e000c12a1b40210900f010452800b680003c0c641c0c007007465120340d0048201c080407500c1c1e07032160f00c00d441045501c1060f00c418540f052916920030740100e600103024090401c41e90810030700600021240c3c001c66445c1c2c605100101034116090382c000c1405d8621142180410000004103004290300c0964040c0080307402d0f40c400b00001c0c2284c01a83c00a010000c1c01d207c0d50f5407050012035151600c41d04862084071404007800020b040001d0910640e174640300b4159503d41c3c512010960280400d0100c07110007800c000c000900080d5822040802c0007913103101e0004000d440341850351040504111400440c50b110203651504882084070160041034441c69102000041040000c0480b1a07040f005424000820750542e514000130385013030503c015100000b524 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392366187 1250 392364937 392364941
    0x5030714090d03031a0105030402010206370c080105010503060310020705010b0d0b0703180c21080408010e30030411060706020a0e0907230417010506030d0201060503100b0301 77
    0x403840000e00908550856190140003440600080808100c1c45c00102d0360a600410036207200b181c0603005032280d962590070300c0c01c500100d03220b0004980c0400b420484c0058081004c0c0341c55000c0c02c00d000626003a1420007400c1080c0c140d000d90304103c1d081003004580e0301c001c104100d282c0c20040004d6141c84441c40e1180c0900040301941d0b4208c10081c10400500543c2d100300c50160746262800c20200f5800b500d00206104002c1d4090140c01e000003081012000707654401c00c6441d00b0791180400422540c1e201501c0ea0300c99484681c0d142c0d1190301ca00c0d6a07103400d0008610703040f4040100c0c03d189041c00c0510300b031007000180d54514402c01000103030900c00040d5007100c420b200242555602c02c200d240c030b80001d402001f09100000c214022034604e5081141e0014050f40361a150700300c0101925000c214000050400e05c1e02001041c00006034021016100000304010b00c0c0000c10a450301509144c03030400080e446500b1a81004400c010540f0045810501c1275a4884041051000d440200340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392367437 1250 392366187 392366197
    0x6050604090213050d081e090a18020c012a0219030810090603080a0f110c311d070608070309140d02010906050903040b0f030402010207080601031202100c05030714 72
    0x5041100d0000600406c980c5000606800f101e49900540b1940e80795a00b101c0341c0502428150084003081041c8004218440b0081009009440c05486c06088455060070760f05c0e400d1807024020940d0052038104180301d00c0c5040e000c2e005100502c41c81c000c1c64080b00c035041c0e1016015040c0665003001c107450900e141f02034005050102030500445660340f0b000711203130b8022810080003c5105000a140324418143c40d54114a400c1c0240440084901005640d049003010303100350001007036140400502c0840103901d8401502d07000141080040c13100042000844842d0815070024002804540d07000510550460070386c6c80c0005c2c40340020301d440e1500c03c0000820343d03041c0c424020407001150341500400d002c2d0384501c000b8420784d26112507251f5a4000c03800b44100780c44060040300074214100002d55030042c014411500500c2d5686070083c02d00a00b82c1090b00c2004611102c41d04194040003050b04060301980d04100448031880000d00a00001d040a01000302c203116150100034490180d0f8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392368687 1250 392367437 392367439
    0x3090e0403020609010c0507050307061a0a0b0301180c17130b0a0c0905100905010302031905010b04090c050403030903080d0e0322080102030417070f0b010308120a0605060409021305 80
    0x5a0a2605020b5520141107404c1045582031031842c0c56158840c60998000c180c0c0301d8019410001107603242c0001c0e024041a5182c50b140c510110300c01a500e140c5036600514062980950741d5052544480615101c800350802c000d00700440826020f501c22005d81408002110402c45500c0340c00012029040c1410042c144944600901a00703a00316400480e01e008a525680c004555410034003980c4201180104040351240b6403c01c055400380d0020b545c0031010191a00780131803260740c00400c460080e0094100754030042028040b4204500c903140440c80d003800c0c40c505051856034014030841e21800010609400442c0b07003595041560400309583c00390344d058a4a44080a407650b00383d03512075044c80e50580b900340c00040d0341c40062003240d000301d420200380c01d41148080401c1d080d50340240c008903401d25802e21280d000c00c00044040d40a1072080c1e4180b680c68402c0b10ba40d07040020080c00a42102e49404002c210941e2854129021900c102c81d016031110a2409030301d803030700e109510031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392369937 1250 392368687 392368709
    0x31303111002090f0a06091502190b01080d08150411070b0114010216180c210b0405061828231b0d0218100c0203010e0a08160309 57
    0x4004000001d8018103c594415600b1002100c400420403c4c80c25840c4030b210046080b45500f4015480e0042820814041034012075561030043c1441e840c4070501d144098401c0f243c4200144002c44c400c2c000101805003625180c00355080108404104420702c400c441e00c200d5840c032840c600785500744c0c1602d4040c0e40080010280f5a5200b180c80a01903120506600502500d483c3d04202d0101c0ea1040742614400e400304014400303024041401480c4209180c8184001c1e4680c01d0f04200d04201280381810300d0742404180c01e9446010f001c140c41c400b800c243d102c1e1540c1d14440000d486495030303580d4440307049504100b010705000c454854640c456187e0315240c508010326580318070304007000b0030110849000e00c0d050031707076962040e644009001046000315910400440719000090f80180c4a0381c04919034400c843d82403d400581040c4e1001c4594000c074400b80c01100962400303106011a0148060103001815540c1d0340380151441001401381c0002c008541000030306116942c1d0310042d19100c00780c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392371187 1250 392369937 392369953
    0x609040f09050607080a0c0827030403080901090b0c19060608031315110d0c02042307030605010503070909020c07030602211612231602120f03130311 66
    0x41280c071014211050790105081d0f0001c503802c1c89442c4240902445150303650000703600d07003180c228007101da2027410b0010103040343c10203a40140144010301c0118418051a0340e901031040014084018581c8494180203080c844c021a82a000c90321504101000c80030075100403403490000028138458025003a10300c0042144619a0301051400d001c0e58081e0b42503100020303007440c0485488002d40303001e181c00c1c0c0007200480301840c00307806082c00740e500c003c10228483c54007038810000e4018800d019550f41c10311301b0602c004140c2520500d03010f05000c1c13a09074518030b02998090105c012501c11543c896500050600b070040d400d0143c80e0155600030340956482c5044d001070501080c40d01e415403aa00992000300741220000e0300c0503000720b1070640b1080f4903002c1254480d0010920310313415010320321a500800581100b03442d54584030b0798071075030b07060071994548400914006a110141b07404100421929100001d144283d031f500040c524840302c40000305140407540c00300104030540c800d00c11510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392372437 1250 392371187 392371193
    0x9010908100c02010b12030703081504050a050103020f0a0b040b07080706050108032808010509070309050a030801080d08060307090905030408100f0b010c02090403081e0408030a180305090609040f09 87
    0x104402d003030701c254024000007040908100c441c2c02a0800d07014503500030040580028041d80c041e542c001ea803c00100c900e5281540402c1c140c1d0821122102480d90700d000620451902c0e441e0700f0181d41003541c003410020b040c19501000f903c541e000d0b00091060104450701081908022203050550024050101d56034500420b55a60004540900c8501e5003082219402201000002850610755a219403d910307050900400c0b8001034600310804d0303191100040480c10401014100521036030b41c2102540c5408101c50600c07402d04050010003000005100d43c0fa43c0000e5840107485656900240100f8107180c0310340345200700d50104900e40180004440d801c000755015080282d1001401e12401c4829401152249000903000b940828404040740120b880340300002c1d40700f8080040e00c0748000380c112128003400301c01c446c11107801c400003040108030f510f05d0050b80303d00400c00f5007030f0060b0000c903039010380103010707040d101c2e4020400441c40e45c090389e5494002000440030544104804a0681 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392373687 1250 392372437 392372441
    0x80a05060a050702190f02040e1e0f011808030a15080106140103020324060904020427200307050f030106020a1119090e030f0f18060406080c0901090810 67
    0x555404100c2d260500042c0158008686028100d00d6548680182c0000d42d42d960310318030705040281d80003540d54483c1c03d9661820400036200c101c82044006060000d0310307200b80341c00c241540e90105070b410887d800302c102c00b05103580c1c1d00e016070048034207440b80e64010503000100710841e2403c1c030f40120003400180d040d20650108017a1500f0740ca00030300303000c60100103600b80e12054450031421108000c2e80076500c0c007410302d1150014401400030385403100c10000102a604075070000203800d66800289400300b40c175684c1c0c2d03922507030740664180a641d01e4028a00c0c2d012401812403c2074140000014076a18819000c070342c2441005040c0035103d5031034a01c02903543c13100f90b0003180c402d550b211156402c0d1030030390740e5042c02072850030382c07080101d0518071031301c001c1d00150b41d1855540c0302c140700441690984030081d241501004403440d4a40501340c8900290f04051000c060103003d0030041400280e502142180d402810f010700c240c0c0e94002000100c0d6100380c1c2d03030300480c11801548800000340c0515 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392374937 1250 392373687 392373691
    0x306050a0e1501060f020a1a04030309020915090915061003090506150102010f110a050d0b100c0c120803071b240608160515210703061202090f0c04080a0506 69
    0x99071240700000703400e001687c1e1045ca20101800040d825001d005588a4401c1d803554803520a15000c40c0904c140e501050340f810741074441c1400a28142414125030400c05003441e440070074200180607000c0700b15814014802d01030f1019008015400701a200c0c2406500800482940b28003111120300d0300c203826029100041100d5401942801e22140d51407c00340a0780160030804000d2a10305180b0780820703030b0998450410281480d0b02c8a41c889650790302c011948220410310307152040c0244040c500ba400c00a0942c000403140c0711000703560380c0400d411000740d9500260905114040042c005107140316402d41000c02032003808030701004080e0001c5018901d4800c2000c003000e10146490b400041c0d01c2c1e810716041d141042c4030a800402603454002c000420f80803070004a14a005070300102e041c0c10304094000f050b0340480703a04c140401c55502d4440c00c40200400d4054440e502d40030f50000302080800b030580917466a6490110340010398003070456006262000c212090103956103845074440340300f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392376187 1250 392374937 392374949
    0x91805070c15050105090f0402090705130b0f04150507030219020d020324070c03080f33030d0e061207021218270412030f0204090f0c030e070306050a0e1501 69
    0x444007c60703525190b00320003602070b981c01020400c681c2e5407644211040d80082664a40304410814005804907000d002040c0c000c04000c0b10590345c6042041c0c15074440c07040c4886d20200002041180b0200394080f90140035010300003404400c200729800024884c000d081c00195040c000d18880b038050705511010310444420156a1003503540d16240e080e40e8a0f040880c000d03001c070f4840c00c00684241c040003065a440354107800c00c008405c0035100c3c04000f84400c1d01082001c0b0b001002161400d103410407028500180e1031410710010000e20f40032803030b1400384001c079441d4220042d011030751160082c00311904501421241a448030341d001c0d1141c4c0910b040c44595401030301007071003204682e01120401c242007070b82000c1c20081c2da19659540c450180d11805d0a0080659a040005001c803590004100401400c900400c0034402c50300c070441110310424200050500c3c103041c3c20f00b900004260941180d4100301c0008003641c84110b000c3c00303044800302035462402a660b100c6a00348000c00c0d07217810307aa4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392377437 1250 392376187 392376199
    0x207030e030c06070212010f09030210050903030c0a050a12020f0714031905130b040e15040515040b04140408190c0201020c040c1107090507030c091805070c15050105 73
    0x400d0516885803099441990064020001403015003401d00c2c000315004002400003a00c4a1450f4416084036218901140160004210745030300d05018022a90480303d003201075072441c1040f4045a849101340c3c40d451041c000081400300d2014000c4200039207008004d10250b44d9a1060070842130554000340341243c0d110304d40d041c40820340780c0c00130549110701c000403551036800030414015948d9801040b20038549107000342c0041440100c04001c0e1001700902c4440c0b05242c00d01d980840031806d00100c545020b0340c945010840c039490488420460340c1810f440019030005040f000c540901010b05140004842000a0008021003280104081c400270315901450800007101150080140403001e0b0041c0d03c82d410485107031810b0340c0000700480580c01c1045074008071245282c1003a40d9940300001c86d40c4d84000b001503858040c0074400c0e42d50640d00d440103620b420103c403444000545001c081205036180c002669030f6014958069420350081c0039050a184403250f02d8000d0507003405141e00605d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392378687 1250 392377437 392377457
    0x20705011d1b06030601140424080901090f0b070210021b07080d0801031707060903020d0e0a05180921030106030b040207050a06090602270a120803011701060e0901020703 75
    0x82d80044500c8240007020790b491034a49030011a8400780400404141410400c4002003000000320b6242807542d41e60000050700700550005440d10780010841407450741000c111038001925038204441c4554005000c9459440b120350891404580c036503c0b0106500c0058407203140501c060034611110004030448551a4480b00010b48a40c0c1807005080481c0c0040c00500005441403d02c007941e1025a01c0b040c18105503807640016a2521041500580c010301d10821103990b00c48088040c2e90000e94501008918100104240c4100d542000e01501a0440070901c103100900c9801e40c41580d0710510050009101202041c9510030300c1502c011a00e458000c4825040034000e0b01c40703807074000c00034000f030f52100d44580003d00207281d411a81280e080101c46640001c560100c9030301100481408480d07000c15007071002003990f075001400b030900e1a400c81c000103021682264191803009490a85038000303103440b6400341c0869041540d200e0f0b0401c0c200b0071440c0c1c0560180c041940260b9a8240030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392379937 1250 392378687 392378713
    0x2030702031c0c140a1205090909190803100305030a200106060c080306030705040519050609041e1b03112d0616080f0301061206080d0c0501020705011d 67
    0x101401802c9a01240c1c0d40c12a650201d01c010503001180d54007482500c103196101e40d500742c00080403017110000308402094420050918060702c1d035004002d03100600c00fa54100c2407942c5500e1820301c00401d41c80000000800d081c0001516400031a44001142d449a01c0314a014046122080300e4107450131080c03038803580e40c80d41400741e1012242d150301d07010310b070718026182c41c00541d2004040a030107111308400050729886621070148104100c50203982c00c0c080e0310221000340c1b40e0141030203100b01ca400781844045141001100c0c1e43c44200440c40240300311a1074411480c1d40084a42c000d8071b84603150000622400c048840d20722142145c491108151907440034960740041c2c1034500b19001c403612203a60f242450001054501001c50220310348030381ca607072013805543c401b443c500c80f1587c0120040200c070342c02507a02c1095005610052024908101c21541d40705032100c2d0314410001613901d0740003803100a504640c84203820000070300807111441c1c0310705000942008025207030302c1000c0d141002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392381187 1250 392379937 392379973
    0x1b03042408090a170703110d020304140604030c15020a05030a020a110603090d0503060a030c090c02120408061306020f0706090309050102030a02120c1903080105011701030f060f0612030203070203 86
    0x100d07805079441001c040c4040b420041e1703400448048091100008003038404800c00c0003040c1664085500840d070326410100e01901e0390300c0120b1030901905050009000050f1107102d4001a5280490500190803038150700b00d03c1c12034518000340c8140800200c0084440d80400c01100980c081c1800841d03404600e0306102640c841103c030450b107504070107541d1043d40d1043c8000c540110780140000310090b200d40b219100c01c4141d9100080c5241d485542c41d10307840d010f02c00c0c086081446158541490300d41170069031641001440340d61195142402801044101c1d415a00a400f4624110f0340313592003480d0030001051220005d4021514421001880390b00c0002150007400d4154054942d00801200416441d0003c180c0d56845004a02040d030450820001034505540242c0e42c038011549420005800c121307120802d0340740c2c0303201c1c14014400b0600d810f40301102d40b80c0c080d00c006400d1110002803402031110380c00141c4105952000d0728185940000a0f01740c0038004c500380c03000707a050f5000c9000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392382437 1250 392381187 392381203
    0x6090e03030c0d39211d070b030f010605091311073f1d030a08070506150303071a0a0917040512030306030d0f0521090d090503031b0304240809 63
    0x900c1000300c0381248102c10316080340c42006581c84d140b030704030b007406c082080c200112600306000341400841003008a40c0c80b92105401400d40341400c070714041902020801080729000b501991503151103d90b400005003a084401c6d29030441c9031507007501c50b0f6a00040f03900604902c1035102c03800c0261036a02c200c040c00c07681c17103913403540d0b8a41c102d8142e00d15040c282d9a4602000481d0b041c041c40c007466010481d1040100000c0340f050024000c00d103448102e00d428215000701540c025801405000000341652200845100100e02d402415981c0c03044010054495440014211180050780d4030713007252580301500650741c0803181914a080311042d010340e0380c0000c075280d0394594481403480000c00c4c00b881c0015020503407890b05070324042c0c0c12103d5501c0b02d038000040b50808114602000b60105080c031006404080e03038603024440070302d00740010380d5078095907408410074003141c2091203020701c042080300c00616000a040190117901c40d24850708030424003581020900303c1c400200000b0f40414454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392383687 1250 392382437 392382467
    0x1e020c0a05040e0c0d0305071b060c030302160c0801050a1103192c1c050703022512050a02182a07060e070906090e03030c0d39 56
    0xd40054078141c00c02029000003081840c5900401d042186103440e41d10714180361034060b8840c107030b854000d0300c0e041ca02c443c005000310002c004030307900a212140c2e000590128640d01454050707118000d9040e040c402120f1112300410303840324010002070541064002600c221103100c003c003c5001c9802d10300030640310454000403102c210a285094503071090740542140d42c41805140c1000c0d00d00d9100ca1240203080710841e415910039406184c028801c042580c400740801c1c506a0f0070000d040d81d0180d030365410010764419a94504070010b81c4540c24100540c018074540305100c201e440715041c200d803290b0021a040c1c0c080e1120348002d84841c0b904244c018018115262002482221650804c542c0410b0344240d442c002810000c500204821b070107410700a015080260004a107400502001c40303017141d201d1840136082c000a05042038002c000d0305d0b401154005002d5540c241c22a404000b404d015484d0019181080c80040088251002450f1f11161248042c1185081a4400e842d004810030401e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392384937 1250 392383687 392383699
    0x1b051e0c031e120711090a09050a060c11100212010501090b0a0804080405041d3705011b020706031401052101060806090a0201080609041110050c0109031e020c 70
    0x35807034100b107080e8040e4498000002c1c0e0340300c2c04600201c00b0340c9501804050319150095542042c55280c2041a20741111206c4010000c4031095569162115031500c0041c004582e42c010140406000b101c80600013040542076441070080c020801d0020340190185007002440c81c030021030b442d4010b05041c0141c40500c1d8003a8142900d5800c01c40c0c584600034011115034406120014107501c540c0a00c00a241080c0c040d5100c200c140320500e40f806581c0300e0607141c0e07507215030180b0500104420208480b01041140c41000070801d0a02d240500600c2e6911001e10701903641c2c503105554041824415070711655414440b04203a40460715401c3c40c207003e141d600c040d040c0d48108c50b40d44405440c3d12001d1600e000414083c1c0c0e540c00035400c0c00012100061282c1080340e50208640c0c1c010003159018104507192940b504154841d1152107410303080c40f5014030031125141c04068045c500f41c52500d00001d009101895540c5030003015108811514000c14201522500c0b040d40041100d807008000030f008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392386187 1250 392384937 392384953
    0xe16050604031b03050717150c030112050309030d02010b0910031127150103140114010c020a24081501020c1e18151806010f1b051e0c03 60
    0x3a0f14203002882c01070303860300d110704000000064000c0c0304540040600703181295800c0307805980350f81030000202c0500000b03926803040007018408201520306642281a40554004007403404500d50b2040c6001749a1600c94150100c850075415040f0551010080d80d1402064842244010380d402d401c1c08001d0155800001d01c101c0303401d240c2c82020720100f50385106400c00c1111000415007000a0341d24042a01d4600c1d1781e0502940c01d401a400441281d00b8a004a5850517032a419203048000e40d01e41080442e00c1e0b480203541c0ca0044803c0608880921100c0481800da40d00e0344a0b14010190400b1460950000e05210220580144594010380161016490b03680c00c011250507201c201c81c0012800380c640d0102a22004a09400130b402440200d080e81412014150002c414800c03181c0b041d55102035148a801c40c2f200c400750001000e003040503180c640741100b07440c440c1c0504100002031b8000320035613041c001c3c00a284050418901c0e60140d00d001e0303840900340c5a086902200e40c05a0000c14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392387437 1250 392386187 392386193
    0x110c0304031b09020d0605010e0f0f0609120712170c0a0b0402060f0f070203010e030f16060207061406010e04590d030b01120e0c12010e1605060403 65
    0x4480d038003448001c0d042c01002a2150220000c07038000f0300c103001c021696018240100c0d40c0009482c2882e050407a41103000040b0580040c1c00d002d241c00c182409090b01180400841e10303820f011030b401240d0141926140c40d2075002103038031440d11036016661211140c40105125102c0000c58006201840240c2070392602502d034841c1d440c81c041d0003280c10060410520901c142004050704013601740032416565850140101820f41c1e10704120220035410070030010390b603035031484222200800e09064803000c035a06802c100c3d000b4081e0800191165003401c1e4902112029081d0042c8110800d0321f520740700c40720800c2800115a014140300d0307281d05240e03404403041e21001a6051842000c4012000f019040c41c4a5030681c086140c2040224210381d80c034250f1410080c024444628010b10f010802e6000c80c000003064400880405550181d480c00d8800640e0014040da50003064080d0400c9032600303e0a4844e402081041004c41c410300494180c0e8618103141c02c0000100c58005264600f0b06085807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392388687 1250 392387437 392387453
    0x70b06010305040311030a0207030512030c0306090c0715051f06140702120d02212d0c0a140d08041505090f160e070e0a031403040b070b0604110c030403 67
    0x283c0240c0c1840009540342c90024010402881000c180c1d5003c2e003c414507504c1d200b45004d42002240d4003d090a200700004c0c2c500300c0702a6a40000c1c103c90030840c503190102c2c0b800d05807040e400c2c068651504115101000c0d01550403180c09081c00c24540c20955040d088031808080d004c0c0264000076500002c0101050a81d002030480d09000810400d80d202150140b0f503e1702c102d0b0b0800b4805604660410051250b03030300e070300700d078030f4001c503020940750a680c0013034080c0924441030b441d110785c2414080409104400f00c10398000c0550a030488803c01c20504114081c8030b0501d81c80c0000d4424808030080c25440740e000c050299900c51340210102045025400c0504002050b580c0c0c50302c12010f2200b6220020405507590b04110715203540380c0d5050401010108030024981c41c188540320350fa80c83c041c1c803416400011a9000104040c00c0747c024050340d400c40c847c035481458074900100380e5030144800c1e045918000d0104a0f400c21004128910300500b50040032160380058001b40003c2021440d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392389937 1250 392388687 392388691
    0xa02130213030501060302101701031712070915030e0304030b151005030402040c0309030e010c03020309060714250311030703021003050405071e0b130302042f070b06010305 76
    0x400340c1089800c4451507410000790340b0607070b40c0c2e03915403600f00150f0404c4c0c00740701c4072200b0510300703a104e440f1002c070001032842040c40000d105948591309415806a80800e8a074009000c4102e244c041c10700580007490101c881c042c084e62805000324801e14540688070725100d0800200156050500d9901c0703800302480300924003161302400490301d440175600c501001486a8041d1103040c2c49041c1070041c00212403c0041a20506240a2441f40401e030440d83c010300031042442c1500c1e048005103001c82c2140250000640c0010012510100f000404548000380a1001c0c1c2150074940c000c822209000b1001c0c06583c0044c0c00050f400d00c08505100c0b680341d26110081d00710352a0f55070725800308520707010400040d40040d507600240000c004c2c00703019a10052082c180581c6414040f02e0201852024030700c20301100d46400165022108145481e403001103400800c104184507000000c44044469120801110105d800b400c20010700410141c84513103400c076a440441c1e41e11480194014440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392391187 1250 392389937 392389969
    0x1903020a0201110106180e0111070309170331240201051f06050708040506040e0105030118030e0126010b0705060a0510140d0606140120030a031119020c100f020a02 72
    0x2541c9e0490303801d1004900915000e40f1950329080d52605d020781d014540031303000102c0b4805400412003900302c03038042c004030310541c0b0f0150400c81003a03060800102c3d0981c410750141401848060706680240a91244041e0944140d0021f010075a41d00580c40ad42d02d070241540c1c0d01081000030144401403040c1d0107403221a1180198615064450340021010381240e4440e0603180f48900c0148402c3c00c0030b015280e074410101c40742ca4403102c0e0b29030b0003070001005100f074181049840c04810380d050a8030b000c0c0c10a101041105400707503584400c041259a030141e00280c2d445e11801c030124005a1007407040e10300c0b0b2166420001c0f01582405103019001d40f8582800303901c2510707101e000c804141a4403caa00510240d41144511500f0303030001f62903d00704010142828100e448500610070b000b00488188941904c1c0018a000848c00d000b01c1c1350240312003090b6910108210000d4280d000034003020390b128201d5104900f18202001290110704c5041aa40160400c401c1c000050420307950003019801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392392437 1250 392391187 392391191
    0xc0324030b0414060a05250e13060b030c07050106050a06080a0f0f05100e0703020a080612011d010213150f0806012105010f0614120601021903020a0201110106180e01 73
    0x90002905841c04c4419501c0e00c0900c0e940750207212072225001c040b072688480810002c45d0400000e0b102500b04211502810300495410042c4000c030640d55100201800c20b03485695102d090a07941907a10b6000300308110303042c2d8601080480c0904e4481100d00c1103840301d40e224001030791a210420050801c50368501c86540e25a001001d0884950240c0d501c14000344164062040c45c04409a0105101600e80014140304002c840080c0d9804460554801c0040d1342c2c800340c5000c00003449006061925400450090400c0c0e911000c0704190014004840c01c021000701258a400c1100c0011106d030000001152440725900d55890150001581c000e50504100904003140c0c0003550780b1950380131100780059030307c20040c42100308405c0e049000e03241929000b0905c40c20302841084510440c50392450010024000880c2680f00704407100800d04451100c698a0314546406561511031860480c04240d00e00002c00c40b00d02c0510480d812101403c5100b100e119101840100602a084032450655 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392393687 1250 392392437 392392463
    0xb0c0312090d02060a0509030a0509060f12040506100506031503071707170f03070f0f02040f0b03060708040809010e0a03051606080702030a0c23060106030c0324030b04 74
    0x18600c4254980308640c0100a04403015405100030b0414500409801450340707008144503400c82d002043d113990381e100707040543c5c3d00c1c41c0c0e01c4005803460003a050464501c8000041a103001c40c7c0719841580500e20560494030540c80b00074004441700420700a154001c0810b1001445604004400c41032490300542911038044d00c0d1501d50201c6103154104191a034807001d000c11a069a80f044002c11600c0c1c9800f80201c0c07061842c405850b0b10920a000e03025801c00b4412a05005880e074000e112294024010800c42100c14800c0f0054007090b034099209008200010b01e8007405000410302c0b1b164050019031800c000784005407401030b40080142e4210030f4400000c800540100302040800242114231402c50346480001041d50381e00030071907421508240060404942c12480c0801c403190321a080c02d03124a04d4016401090200740c14002030b61003080000200581c155000303089480c05540c003848400d0080c8038005400b100310700b108429161820003000411040940190000e00c6201543c1200e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392394937 1250 392393687 392393707
    0x1d0d030c060b030f0c1003050105211204030c0608090c011205070302070501050f0901050601091203031a0d0b070824040f0209030703030f12060b09042004030b061311040b0c03 77
    0x80c03025200c0441319031111042603e14a02040440d00340030b40380c54144481c0d814840810840200b400302c0100b01401c8089215010409000700801c0f02c0020a0042d101d95990500c501a00c104d48203202c00b050030a0b0100e1030055010901d0810281c06848000015440da40404000c0c0001040d6a08156080c002d001c001038007802140d0003024040059406030400700d07005421680d0207420310b030500520030002c01122408041111078a41c0605000402d0102920300ca000701500324080c5a108035510080020441d4941030107000740010790f00c40380076940780071188115140320700490845c0d605081102d0107520709031308400c56160080501500744140c90700480e18001968200b100810300c14036080711065404a24842c1412804000b40241484c049000810384176108100b80215110722204015110000c01805015801290076503140c0d92801c0c003880c00b55054030000d2143d078202140d550700d02694041d0307a400c0307a02442e81c20325040c50300480c2c0d060341c2d001218805c10307400140504255 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392396187 1250 392394937 392394943
    0xc1209080109030503060301050a0203010602100f1503050d120501050f09090a33020304121107080610050a09060503072c0709090e010e07060f0212030a09031d0d030c060b03 76
    0x241c2d0320a84500392203003031044c2090f0a540b0002c010401c0c080c8107000400009034001a10151401c9642000480340c804540711710140c00d02048001d44c040354018004100702000641c50f0a40240ea038544d20382014040350f00c81910028411144d0150140c291a405d80c600030380900e030460b011004444407a0f9440e80c0700030541702c031305d11101e41c0070440305449500c000a600c0074140307c12502000314a10302d002d944c0c40466a5001d000682008804c050400c80d02004101b4500a488450300300c40e000d00c0d107040d0b4640220300c0750280c01d0160700588000a840768450240b0000e07500000c011b040300d0303400c3c949145140c0c46a1002008820014003440c400450107440322030080007140d075800441c0f420010707400103586040c440c050310340c1e01d0503484040014011880c1390070755a280c6040468840394403001c1346820541d040d8240303100800021300461911590041000501c01d80301d00750414040c05207500404110201242c0209003070440d080064410315500d5910b600c41c03900014624250804249 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392397437 1250 392396187 392396201
    0x307050a050d060605040e090a170c0a1a010501020c01080c0322120c020411090d02010e010228030f020a0305040605030618240f1c02030a0b070224070c12090801 71
    0x4c042400003e00b40450300d018200c0e20303844004c820052803030810a0b5145082600781d03015030801080c0118010303118142c140044074402d901311244502000c240d51104280e00c81c280b1480c1d001d84034048100402e0350060060a1040e81c2c201891810755496204c1103c0e1400080035100c0300c5010941c0d0040000e80810403002d004841e5a01d815100026106000845a10b0002409000414414a0016a590124004061742c21703e0046003054207100140d2030103050081207070008000001d0383d0318545000c21034441da40e00954805881d200a400140d8a03450f071041c0c09000118204028480c80e4081d100840d04180c0180000c40c18a680e6001103541e108256400c0200e20031580181400d00b40a50081c1b003800d4040b9100700109001c100024031400c403182010303000c00d444254913000c2d0750342440040c1c650b5802c155000090701e040e4800035100d84114810f41c0780a1000c481503c1c40b80d80748442c1912901407511003c454408c1d030344410f1005d405907601e12040146007100810307003800c280241c0e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392398687 1250 392397437 392397449
    0x810051302090c0403120908100b0103020d0905010905120322020a030b160207050f22090c060504080d09030c030201080a1b0e1513051e0607030806040506030606060307050a050d06 79
    0x1d40c1320342c03d40c54401d43c0040c07500b06d644108143c4240c1072007004008501c0c0100c01c603507401c00051590000005078081e010780c0700c100092502c1c100c1c0b050140041034002201303451285095407054a441c40b019111030200b6201411280c511f17408041c0d0468200c02042d07807050005081601040d0760b039403000e103002c0c0c0071904140001184203410002a40400100380640b50481b205c0c030103400080e01044640300c0000d0244000c40900711a078a0081107135010402194001a905207165101d12000d41260310910440181c0c2c072640703035042a0240714000c082c069a900200541015165030011104144094803d12000b0b641e00004064440366510000814000e1340b02d0620040d00c0c1010020584021130042d080c50301d08000d14a02401003000341e0098440448a910200c0c0041012180319203e00301d850b030308120006001c07401e25421415280c40f07100c00315414071940d500d0405040e00d0701c80030b542840d0000401c0c008510b070b20340502c0140031403d5403480d140f41451130305010300c800c0c1c52041d4854 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392399937 1250 392398687 392398711
    0xf090804061d1e041e0b03060114030a06050703020c101506020703170a11030a020303060a0506070210030e0c03120d0509060f04061802280807081005130209 69
    0x304551a00540c18200e000d411040c00085a0b08030800b01e00540c422140b02c80781d0700c031103000b0800c803507a440c0d111071101c913082e140d0003049440402c8000000c014051085105c2c1c880c010000525502d0500a2040c2d00d030064090904c55810f681c5807405850701034100d0003072540030f0054584402e000c00c01c0c440480648600800c180100742454080040950404003c64200b00c1c003d00c00301d58604030440000040482881c0d070740105400880d40001454401c0145000015946000660000c041c0d40254001c4a02d421700755a50384c00c00200f4807908a00075000385480c100004118040d41c070120700461a91f003501c40302c10200002034200341c10003a41e041603145c0403039200c02d80200e038441c0550144400004041504086401607147e000c0108000c08154480121202c8198040c0354004540d0b80500038039150829203d8000c420a454030041405042c00207000400c1c200010b1002e08456803040a0600300b2508106c18000c1c0c80d0090045060261345910400140c4500b940c661084044401d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392401187 1250 392399937 392399939
    0xf0f0c02060720041a09071107080708070512100b0604080703260c1509010f020a031b050a0c0b09030c0a0b04050c030114011701110a0306030b010f030b0c0d0f090804 73
    0x40412040c90f40006501440c50715040f958120354142200303d00103c00c441881d42c83d0340d802011103a04041142c4a0300703a000b1007100041d45c260005000c020b44030201c0a0721845900c0d0700500103902506c40c5001a42d43c0401c501000101080d07118042160001c0e000c00e25041e2220152444c01101e50f00031101507030807100340e08110008051105c0d013000140c400790315020060042c0b580c2c031240351007000d140c04c00f0715010500c1031800b540100c14210311280c0954594400c01c1015000304845004d0300d52080c882c0602c1000b0500c6402101c4620a09403076050410144d0f40396800402e5005092003102d110400400c4c400100c00c200d201c0c0254800c2c15410414901403410340d04040460307c00303500a0781005400c0b4558511504070b581900c41e026024644901640405405044903021500315403400162040c3c1c007a9041d00514203a90007041071143c2a6600d4001030300d9503040e031202605800010000c502085800c0c0d0003005860584440416027001c0002040d048a050b03000c21210700300b0003e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392402437 1250 392401187 392401223
    0x20120070c1e060f0201140a0b012d030b0409140a0c08010c0207030f050a1b0911120c1e0301090501050406050102011a0f0415080708060906070f0f0c020607 69
    0x4070003015050207050a001e070a03035030540d0300240c401405040244500f460700c03524464402d501c202540b40041e080c80301030b82442800640109002c00000740003c1c1e80310001040c1c4001c101c0b5040100800c030b40302e440c0c0c081ea61031003100100920b204c85070b1b1160300e40fa90700700030aa1101c1001c00030144a0041c00c0306010a2908100e1030b00550702400c060f9051400c64a4455000300302001107d40010b040464801e00d850280e0412403030840091101c400920b0ba8ad25842d0000c40e41030a54851b202e0400c200c0d1011000181c0324040c00006c04500c010314000100000070420240036801a202c0d40e190000000b500524604d40090304036075040b07940c4a00410440c40d2500400c401880280001c11200711586c0c2c0d04180c103640030420f103001d41c495203411030494030303280d014010440c034106000e06582d407a1420140c540145209102561090074003082c0740000214003d80206a0380e00c3d040303000281d640c0c065810394080e4500d00103105030002c10310090303100e0030020305146209002d180354a0070002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392403687 1250 392402437 392402453
    0x40e0601090516020a020f06070b0a0e16030f120c0506090d09050d030e15092d10090909030302040b0703110d051e030c160f0605060102030a081602012007 68
    0x9085100c0b0746182203c0c41203840d0007040c0001c0c0359805a44c84600100c1c01e101050311840350400092003060824100007800c0c50592002601100a1080e5440343c0d103000202c000001050002038014900f0010b11400100c00b0740300070340c004032941003483c48042c0d1a19504e0903c0800c031a95102500410044005550302211509c054032045402081080c3d00b518000c144188a8500c50b00440e0740340c000d030100700c10f40c1050304d8014100800e80c00745500358003c507140030300c00840022042e6001d0822004986082c0318045105299984d9202c00289000e9100010b40044202501456800c00002c02e500740b0f403c0040129a011303450b41c0d5101400642c60344d00d0a43e644030500f040001c2403000e40242c031002c14486103a8840b10741e1880e200c0c2c40744c01100041d8030440001191000001a40d4010401c1c80040141380c035024110400c01075581900580c1c5078807580c2c0d100000030b60410300150914071420307001d02c1030481c1c910000445c01c00e18180542c12045a40c480083d091b00818407008018100e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392404937 1250 392403687 392403691
    0x110c1e031e0c03070609050405070c0b070c021903030e0108100f0b0c1c0e04021b070f1e1802071a07030e070609080a020108190216020a0e0f06040e03040302040e06010905 75
    0x950040204c14a40000101544803d000d421f00c03032902c61000c2014503115502400d1080d810600410590070144c0024010301c00c0031070103c0c0144088080b40c422051207005113000c4a406494141c10560007800441e06000018010b0490884820300840c119200c032140c1c0e405800082c1c020380d902d02152140c0f510b840840c4188507100d5124070a4042c480d5801502c0c0340f2010303400d80d4003581300e26604840c180400c0b007410f000076443c850380000041007805558800d044420303402c0f071180d11035815541c64000801c2ca00501100b45040e0704e560020007807682c010080280120044070b01e40b000c0c0b08003050f9040040c1e9000c00001e4031460303255010482484484000e003000d0400880b4980b80404050311661460400b906210005000418021405903c208405001e02c411560f400c803800e00028100030f1548141e001e5084480c020034014240d00520b801184040030130516690341c6000c2202034181c1e49488034050005010000043c0c07118010490080010b00103070110f5810072091104035040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392406187 1250 392404937 392404939
    0x40f0606030b0f0610320d1506020303040c050d06020904050f10050a032103021c020703030606050f160507150c02040b1005120901061a0306030d110c1e031e0c 70
    0x200d003009042604580c0d01800030707010800fa0016808866a520325880c400941c0380186e141c00224540710b034405500480d004c40c204a240b511903074403031ba412641c9001c1110001c0c01c5502002003030020b464060740420100e0f01c95076000d440c003005017000c00c0998009603405d010140070181801006030188020402074101034a4024040d45161984450b50041c01c8404160410f2001081da070f00d8865011142126608059007044440000da030200039840113505400080c640000868080e00c10000c407800c10741c00303403500340c2012a9590261710612090b4021600780c49071007000a60781080310f40140c2440b002c0d440310f1510209034010720003918050081c0c20700c10070207150100d800940110940c1c0f545510301074200059501c0400190052129820403000d10780d44041d420ba6800a030801144103010a070241d8208204a81c810b03500302001880074103c80e00a414040080d05000a400c18915079040b50820404070305070200341060340d01c14100c0351490081e1000ca40341c1c80d04000c1800da40b44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392407437 1250 392406187 392406199
    0x1b07080f030f01080d050a05070203030c0a03081f060e0f010e030601060e0301050c0f031314100219030501060909020f1b0105010807270c050904290a030f0605040f0606030b0f06 78
    0x5811700041580c0308003043c0400340b01c00890341f0400d545003002562600e2518100725042e44040f03003006044400210360460005c8152074003030b4113a48007081c109049950907200c01d00040c841c2d80401100c0f4121540440c1081081d89000c0c045540810815000300190b40f00c1c20382d070781802010701d420340e9801001c0820381c02702040b2120035042a00d08590b0b0151075013422070900c168030310b0001e00b12035407400690814031a802141c06a421554014610082a841607490381e03010340c902a801d0369000d124550209003400c00800c6024410740040c1031040101801a00e01403038504002c560003c0e200ca070a9850707564000500010804004401c06400710840b1100d40507401902d0703d00000c500c0c203d4100c40c0340c0f211800e40703409024909698010400410900042c0005500b55807114103280e071141b000d4913180c101c08000d0401440c0318094a80201d00640381e1001502d41401911024108848620b00d4041400100d5020302c15a8090340c13041c8200001420514200740300c01d580070300035600c518 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392408687 1250 392407437 392407453
    0x3190c120e030301180b130603080d06150c2303040824010f0306020d1119081303080c09060c070e0712140f09100f05011703121b07080f030f0108 64
    0xb017030012400748040d08600e0100f151801c05010400e10743d0440c0001ca45c00c2d092800100400250b0005001c030364031140c5040100c56952100850b5910301c40c1207504c0800c024403003c00128100c0d403000307410419a642e6100c0d08040300301c1010300c0d543c46640080c059421160807210505106240c40103400c500c40b05011a079418400d0281c122201448000d02b0107600059859620303000b03404c940c211400d4811f100e0307203800b03100150b642d80320103100d5031600045503080010b2104480c0c0c01e000b600590160340e03801c115940c15003807400c16844082841e0b440402808504640d02c81040b148024000c11080c1c100c0d1070038050307405003103221144401000c035814200304100704882d00980c150700c110199107100480c1c644e0f5000c6820003000c1c040901e035490501035140070354403c0c0e4100a049a807910030780694100303a110407503101c0c010304110300082400d080c041500001c003820859845600001d00515000582e607c95003998403483c400300c201140441080300518a860341c0500601c20040600f004e8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392409937 1250 392408687 392408699
    0x1605040c1718010f0204030f0c08121606061703070303060b19030c090e10080609060f04020d03050d0203011401120c09060c0c0308030106020c030f03190503190c120e030301 76
    0x5088001d01000b0352105070380507120080400d4000402c40811804111750751a102e00f00500d0700704a2400c20350701210f07443c0e000078049000040c4020280794203013042d82803065412003031030040d2140346c00b5a48542c9950020440c520072550400104c4424402983d440101d0714024080d0350540e40800d01254040c001d0b0401030420b081a0700d541c0c4528074001400082d800310650b02c0d10b803140c110054003040c0508204400a1003c081b40980d030460084402d540c5d81c4101c02ca6807407808584078000c0e2861600810010f0420001001800c1e2281c10828140708030b00ca0b0140498001b40d01110001c4800703d41c400c0d903960001745e40c003180c00f0091014004003902c55005004900b980c4161005c0003049081e460a11051480c110043c56000400542d0707941d6903c002540c5110204101c0c0c841d0003a4101e60b82c0503500003089035581310354810004100d030440d55003514507400050540d64490410704890458400600c120309004c1b840f611075902d80100d00c2007400842c1d98a448400040d40200014807031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392411187 1250 392409937 392409977
    0x1e03030601050a120507020c0f03010b0a030b1b030a09061107050604141e03041e0320040b040e01050414011512110d080315090114010c05010e1605040c 67
    0x8804020b003002c960f1145038410403640e200500d054000301034600f90038024400c0d404a1103c08101007283c0da03103003d40444c8100350899880a4189078441c12000c4200001060304007030b580e100f5030f00031141524240f20600c0d1710640e0710440380d0360b4245a8502c0134108108140c40342200050100e00d0160a02090340d07141c5640380700141c409080c0e801c0100280300d000d5802c01802c080550327288034030b0b41000c1c200006650b0300d030841d020311b0220031f00a1113071012900c8030200c04070440c0e820204410070603c03590024600c1e90340d502a1590020b032101551203035500c9a001d44001d00187c0c500014544c540340c28000a80d003500d00d401440c590401d03440010707509180340c4540070f5650f031880c3e01044d0b5416280404288880700202900400c032140d01070305012001003c0c40c424034103204543e81075001c550070809034002c00d0003034100b03400c0100008240755215000214242c2c5c071400002940e0354400ca00301e46040e95080c8017403c400364001d0f0610240c2024060b07d80340c5003885c140050a41449140290 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392412437 1250 392411187 392411191
    0xe0613173601050702010810050a0b0304050c060a050a0e03010612050a12081006080613060b040602160609031b03020301020408030405010e040204080c060a180e070e030610120c03060f0e1e0303 85
    0x1042254440100c0c0360f108642078111300401c0d00900e02e114041cbd603214061095002203a080e50203000e11021581b060038010112801064995101403400c00c210005a1301ba01070390301c19503051342d030702c0801041801b079006070030f41e1543c05140208915149454a0032280400390892000c1243c9181131242514030707000280251a114103085031580c1e03e400204084110802c10b046015040c02c00004090650300020400c3d80c540354207903102100204294000003525202d407100040d480c00081022034015000e8450180740c06880101031546c079000a03003640c1240c0c0007420f580d003000400b04100c0d80c100300a1181e50006540035402c040c50301719070355180c09984850b42e00540c80066641e01561180c924039080000d05100103c182ea1109078000390104103d4401c1c011500408166100b40f42c00200140310750403c464541400e4140b4132070100d41c02440d41c0842c0c40341441030022000440030700913003070600a1140c000842d900c1070b4601903e00722420390840c0110001c0d43c03250b25018400310441ea = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392413687 1250 392412437 392412439
    0x712290a1d01150b070311030703080105010f0c0206190309050f010c030f05010509060d0f0b07091d040b01140d2f060418150e070905010809010e0613173601050702 72
    0x391a0170300c03800c055601610103440011940130004402042580084105040c0c80d02a0b8842d04a01c12003d026105442a1000a588076406025038155500c0c0c61744d58140c2c40b4014640402c01c465075544030352401c0c0355030a071407460340d44172012822511340c10302c16034070039002c03800c4103202c1940b41a003c1081117402601103406140c3c0c1001c1c190901601020b0310179032940c45009070b01e042c40e0a98000388121000d01410650580c0e510190300c60846d020781c03090040d90000940401a480c240180b07224498801c0ba00b5003000408070444046040180385001102a082e00c02160407034070240c1c5c4c00b85602c0411191b120301001c1c0014450301c4880741360041d0040000308006240400111844105c1291780d00100c1080310f104200840381c2c1d40000030138122942a210007a483e02d03880380c014261520100343d17844070341c00f0744001010b2012104040130242c0c018030360703261102072100108090341d1200c689240003d030030583c5032050741d03500b0707503a14407000d504903401c00d812101c800000d0252054990103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392414937 1250 392413687 392413709
    0x90901091e0c090b06040509040803040309090c051b07090204090e10110a0e01031808070b06040b010c020d1415070f0e09010b1308070816080712290a1d0115 69
    0x8902603454081c00c84011f00380c010000e100b189071a02e06000c07140d10840d000c038002030a035140001d0028903130040c00344a07410b82d1901410175158490b280c50b040143d640f03255580c4151240000c40c2c211b188010005000c18140201d502c0707602141d2986401c03440b8002c000d40070701e003d54985040701858103880000c05a8a0070760207401003a030049028101e400b108555185c07a500b10b01d810420040000e00c186032007442e9019440e5102030810088503041508a030114000801e1180117252002204060911a03240401c1c0c1051401d005ca280c20421201c100880f5011402d00c0035040c0c010315809404d41e0715182100654000b500441c00568061091a02c00c11011403031101d1940e07030724000f00150099034100c4a800c0c1d136401505955103080382c4103490b0710451040100d2101004034180c416184c090704a020352400307541c5c03044014854040c44000802003c245032507900c1c2c00760030050061003611000300b0780c8000c0364428500181c0070000e01c0e400782c0c50f11803901039035070942c01c0220845002d040c80c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392416187 1250 392414937 392414951
    0x60106080a0603150608010f0506062d0406110f0304081c030b2214060f10110109030c06110a0c060b0609130207050624041a090901091e0c09 62
    0x922005030015800040c440c00b0101c0c4407a040580550019040f1b5203c94002d00c2045140031054080b5070042d80c0490f0468400c0040c080c00b5064224101140342e03400000c40c0f06800100480c0c80960001e4010b013002451030420400d00c42c0c010802c1e04a080e9140021354540344c9440d00a613550002c030b601c0c9a02540d048402c03005094040d90140d00d40100c040c0c809000c1c0c0340400c001c86210610010001c42c49481d282000f0b080e4058030006521801000e040b104510300f04031700304005400180c2541d01044240c2480b142800001c3c0a980701c128401c1d29841d00c01c49031440c0800558402d00c0101d2409031091181400040e80214980800c80d00071400082c00308120000c580e10b88280c001c183d8110410302074151207550307107500a201940c0a00c0c10707074500d41c0f0381e50340b080b0b102d084c80b45002c1d00d04100c8032415140382c0b400303038859581001144102a0403840081c013282c480c1e00b00300d4156030360b03035982c171894000d2001d440c05d101e82c04512606441240f21440da510317840c001ca680600c800207599038903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392417437 1250 392416187 392416201
    0x110f07031e0206130504060603060608132a080c0105160209040212010e0c120102042303070f320a063c1106390f18030c010206010608 59
    0x1003503030700948501e03562000c2c0c004c104003030401c9216403409940f8001c2e000035814428480c0c2c3c3d05440e05507031282042d403294040150100d4129101361254403030700346034070801020710400d00c0720306640441c030904652030081003a041c400000007450500900300403400c0c19400c2200b4881a090b41212803190a44682c0089242800c1013035800802d5071070020100044940024000c0352100111424141c483c1d10b500a00e0a0f0301440c451103200680c40004001c09410581c445002410040c0840303a64030f0b03884000d11007581c0c0c154016440124185000840114203e42d81c05086903480300c243c0740481102c0100c0e89800851084070100400c0110400111000f031b4030400d081304e082da41a1003c5c442c01e18103241d41c203528440010106051403c0040c000201050350b501c01d01496484070f00ca0b510a082d442040700100840c0f0680466506c102c0004040c408054003143c0e8824442a403074031452088252159080e421640c4a50300215030f42c816a0b9000401030305498a0345081001900c03601 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392418687 1250 392417437 392417483
    0x90b0a08130c0f050f03030f0405091911090f030114190f05010e100911090d0204021204031101060902040b030403030b030a080a03020d050a0b010e10020c0d060903110f0703 76
    0x11401040c003503602074000f441c4408503c840341035641c101c400b9028010750008055407442007441c03908a02006000c04c0085207055040ea03a44800c00b41c0380000040b00c0c442c250812640c0c1840310341c00b490700103d05244103040c0301d403000a143c1000c0d402041200940500c4c4404010001c11004154440030404a1103e4940d0060f860038410f9080500855840e04114800f609044030b0680c200340000c1000608400c0c0e500a0000740d0451140d1a445d0050034028001030003004d0200342d810136007c203c039103000d5103c0f00102c2d10407402952115200c0b01c195200d1401e42d02294010901507006001c1030103000d4445040ba500240d0509000820203c1000800c0c00c1c043c000348050b00c0c140b40411000c02c1183c142e0001c1c0300d010402e0b0300400ca15600d0030b100301c0032100425111400555641d400091a040109142500d0603060046440d28901000000d8a02c0d810356000c4400302d031103040784c2d010150812032094400003c403015048400044054542d0792540303100284c0907220032072800030742c1d44801d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392419937 1250 392418687 392418721
    0xe1005100b0304050703030f0503010f0b0a0908030c1c0e130f090203150405010c260c0408010e07050a0f030b040f03120905010509060c0a0c0b180304180606090b0a08 73
    0x7203411a8981c60310381026a19a02c00344001d5008c6162034000251017440384044a050300c102c4900d16038910b0400000c0340940d00620050410310540e43c0300420754001c00c002409140c04940000e0942c8416940250020080307801c4090070300219101e001c08640e14440071048400e000c000c001001002c24103908080c1c072107684003a405000761414000b01c00c00c0d00c080940706a0280300203020700c0c5081e00e001c03a01200d840c0c2880d9a01d111502104004c41114841d044d04000040282e034145070b01d49050a00b191688c03680080180c2c028201003103242083c0c00b800d0300030882070611a990500c3e54035080c00481c0005d00c020283d000f442c0100f800c06000b007800c5007a00100880822150310580380a0b4000c05051343c0001c000e202c3c060015008605030030443e8440600c13940c6003810283c0300e50b2034504803000907044514191584c181c0b07100c80c440030030182004180c0b44007038812003010200000e0840d502c0b0303084081082000c10050150100300e40889200f01e0803468500c07070b02d65419444004800c09 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392421187 1250 392419937 392419949
    0x61704060b0d030c03110303040c1512110408010e0d0509060a03020c031b010b0306060f0607060603051204230a0302010c08090a0f0602010c18050103050402031507080a0501090e100510 81
    0x48003039014141640448003104d818441d0326010300c1c44054112071a540d0004a90080404089290902090700d41c2840744407541c0460901220b400c0d480c041c600305075035280d58101c5950301c020408110402c000d005012071609203c2c00b8014503120004024040e105400909002d21000104022040d01c40e604903400c0b040c82070240d0381c594024044005c4a0420400455469800c00b00c0c04001d9117408904903020700c40042a41030080f1218085c00035541109a06490b020340c0c480002000c0380050083c0c10b001d08682c10304c0c65803542442984000e0042c2004510800e200d04400000991078080d42d400550790242080e00301084a4508015940300b100c27041c90300201002e0b0006020070039007040c00140d1340340d03800a00c84c01e085218221919880340e480300d100d40010070000c101e5540241e000c19041800902900c146c00d0040c072182042c484291b4503a00000d594800304001200580314243c0900800d00c03061044110b241d0319070b40d846d43d1681e0314a0815130389802241c81038074001803d6000700380d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392422437 1250 392421187 392421199
    0x403021804030c05012a031407141b030318070b0a14041809050606030a030519020129180105130e01150602030c120705120a0309020915010f0207061704060b 69
    0x599440903030080c58504403090318900710b00c01b0b0b040060b40280a494076542070b400786851961382c1c804089403c9035141540c22a0102c08016003035070003106c0c1e480103403d090b0943c02540d490408030000012509441c241d404c0303540061805000c2030318a00110b41055180303240651030f6054884201c041849184d020b00d0302e400340b214250900c455540c0115444c0d9000e5001e4403080e5a4450900d9200c0081c028028005602004081c81209001d12a144c016000b40700000740781c483d803420380115141c5039018010040c2d400c04510118030304200100300040003902d13008801d500d000301207003214001d20344540c240ca031580005480d00d002540003515000b901e00480c61159904c40001c0c1d203da004104210440c02003c4030220301641100888803d10380c408003c000d4040c0c40300f041b80300f41e0003401200c420552141f00f480c000d60349030f02c0c10501a4401c01414104181014000b4196640d0100e404065402c0380784200700c166045a542c2c4a0b108a44940c50181d9440b440d00d030307008040c10040594844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392423687 1250 392422437 392422451
    0xc0815040f1a01140301080c01030e0705100504031514040f0f0506070c060f0e03040302270c09040c0f05190905090a020a0818060106050d14010305011a04020403021804030c0501 78
    0x9681d101c2e600100c00820380b40d0101c0115080c80100f80c078031003401021210750024034001c02c0c0c5d51080e404661004910001d6600c43da1310340300091340c0d1406420380c28001650102d410310900440c27000650b082400b1050400039000a18101e2800490080024009880d00c1c4002d0313042c00b55805000302102e900c90140c90251801c0100540895035018054540929292058400f400244980c0c560302250b040118206461a804c02458540c0084200510300800c04039140c00400350201d01c1c002da0401c0c0d000c0f074960401006001c100c918a40501d4204514003058045c0640c1100c101c03039040784a00000700004070340c100e00f912002181da000ca50003c03a868200442c1451a901400e011030960740c443e460780d01c0b155545811090311101145180d00710354010013038240107200501811207182404101582908685032021030709134010340f8541d460704c1842c1c440c0b0500c200e01100f050400c072021420182541c0100b00842a007001588001c403810011a0a150140868071051580036000740154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392424937 1250 392423687 392423711
    0x90e090a140319020f03121b040602011b1b061107080c0703120807210603050a0b0106020709180206030403210c080c0705030d090606151701090c0815040f 68
    0xd601850340f580740107001502c2100b04510104d03042c000110300c24011420452107401d03410840e00701070401c440d41c050340d030f41d0440311031140c402400041500350000100d1294120005124011041000c01081980181c50b6004825803814208042d040391000440c030001000055041c882c00c4405025801d01081180c0e942d2800581402030b6482400000b03000d000481c415102078a050320958041228520203c001008118207100040c60098010603e25600d40b100303401c041550b071058400e00f500000510038143c0410a01d0002d1151042c1000310800c040c500001d030740c540f2030303009120303000000102d424103208200420300c107411000d4451801198841c050002c0c200107012002080c2c40c0320000c0e07203075148c030030540c0d21040c0c1040c0590f10b00a65200440000c2c100c07264102e45069890300041000070440400e40049101e644078214181c1c0d00400070f40c00c0c040c059100f034460609140044d01002d40c0f00d44460b400411324801c421119060b40009005800316000c401300c46440d1945143c09 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392426187 1250 392424937 392424943
    0x4060f0e0a0911031911030109120315120f060c0503090c01081f0f290301030303090c03170a020106050d02030a03050d140f0f1003020102190503040e010b28090e090a14 74
    0x5c0c4c1842143d0f0b0100c203654030700c00e25080c1c030078170311005e000c004000022180307080c0240c20003800240300c4043c0441444d16003d050705848100c200581c0d0070f00048620324100020b612a640d5040101d0a0a508520380716000302c2e40c070707184609003504119054000c1502c2020f001042603400c2214200d001d41a03407501d06011400d00a4801d05241c651940c0410f1108070143d01844c07625960016968a50b0303003103880541c050000040b0448001c213030400700001290302107101e00000030052b5026a6910034040c0001d00b50350107908910f11071800c11480c400165000103140c1d1215074541000394590107518403540040003a0308002c40800b031098100f140798901d403411780344644404042010542c45000141ca0b1940c15404003e0140e40320120b040c1d00014056190030b1498461703c1281d00c1e0548540300440785200a9218261081000c00c1d21191400340b00c840d034050017403604ca00c039441c9455080040041c0c601c4c1c820305030b00c60348000101c2c42001d0144030000c0d10982000b00d001e0b24071459410300355 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392427437 1250 392426187 392426233
    0x60103020a1110090b0c040302010c240e0304080c0603061311040b0409021c150326071a16020c010f090504090c05121b0906061201080a0204060f0e0a091103 69
    0x104c2e40c521701e00041400492400356000c0c0c1ea011307036401c450441c3c04e54030f01e030290080d4101c001c0d2983c0c010030314104511083c0601c546080c1044007441d01c1d1480c145140c0c0c0f0707194044804500c036081c02c1c01048400d845092088140540c41800410301c2c51031b00003000524495034114201900c00001e020400d20700c1c54004140409641d42d100048003000340d0502c0031140046111010030122400400219a42886481104241c501c0d2503500800000846100c1d5008410440b45003078450041e100c071180184400781e014100092441d00310310040c800944440c01d642d08141030100030710405007200c0c0700b400891f02900000d001003200b031902e0700f0100744e20f848900c503c40c40303207020405101c00c00030041210042400302e440840d0000401c1820048854002080300390801814400c0d16026600c0b130304928028801a000342c6071441107401400103445160300055140d1480c50340400100c0181c0341c245520070306114000855202619001103074a1000012a41c0351141400e102c1d8840d0280885034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392428687 1250 392427437 392427443
    0x6050901060c050c060304020d03080601031122170a03080411040f0b0307060201020c030f090f0405040c03050d0f08010e070201060b04060509010e09040f080c0115090c030b01020a0b060103020a111009 88
    0x2800c114581d03013000617611085a00071340001c6900d50150000c0e00444d207154000c1014140442c9108280c42c2d460035942107081010003502410101b190ba040d400740f00341c0301406c0c00700d0b038420f180c0d0456030202d030fa24106e03800e005040088800014003803000c2000d0801e5400c00080050000d44a0300007507101800c0e1400345144240503400300015030a0052085420b44000c107405981081004082d1551542002c280c1d43c3d001074400d03242080d655254842c99210303034840c0c50402c40b41c6045080813840d020b02c0c81d4485c0c0501c0010080000d41e26001400141111900101c905c00b0b030303a03200d40c01c901510030742d0f00c5500e8642c4007280200e50070350000058098110207036036450100103880100100c1c01c00541d005080c8580521408012400c00310007003592a15180c0086800f801c45d84504462aa0aa0201603160390342c5400d118810f40c076002d603481d030035801d10040105030415241d981c80100041d08140c1072580c001000301c3d0740782c0619a84003494400c941628102c6030500c85e08805403092030011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392429937 1250 392428687 392428693
    0x12150c0c0b0619060e0f040606030204030b1302091305010207052d0304030809010f0203120106210c02100b03102316020309150c01050a0b030601080d0203070602090406050901060c05 80
    0x5290742815a940340720040c031a102c07143c00900e441001c1d00e5460300110526003240d004030104455031128040c41e80100241d03500165218554185280143c0001e0103024220000002042c00345ea902c0007071a0304130b0707022015540c0141c000c0c40d0090084c4541c403002899802000344429003a00d00700c400c00003a11551040c0d04059082e82a05612031045020007401644180100c0005511a0f9514024403c440c01100c4c5081100d411740c0c14088030903400f00c000558400403145000302d4004003d4000640c1200c240074003c1c4600b4040d40741d0128541c0940019a0b070824000c19550400c40e1120800c5541b100f04029618031948000000880303038080745c414244004640e040801c0c2a407085c211440e6800b039820407101030200603408101c011002c059a501303101c02e50b034210003031095500540e0000390000f098825a41454108503050380100302a400903401410240d8000c4111034100e07038403003801640e51035080006002044990802608050b41d6800420481d40003c40b4241e40c500070011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392431187 1250 392429937 392429941
    0x406060911180a08060f010f061b060504030306090905010e1204150f0210051305071512050618040f05010501081b0120060a02070b011e12150c0c0b 65
    0x140c201a1954140d10104000c0100280b4194100c0c0328040050810010005030b59182d4440c0024680402550703521602c080890040000c00060600603009045500b000070003501401c0305440390312100040503190310746803000101007610992004000c1c02c140746040001d9815820014020401050354501c2845110806000c81144030255421604510258a03400407140b40c00c655144d0344034805825842640d10b0031403403202c14059980b107400f00080e800740300260350a003145012511b6000c451014620b4a5921285178020007202a020502d01f001c80c8035141c01010031480040d02080391003c0f00d010701400100304001c02c045a08074081c10083c89540d0700d030030300729071280960f40c000800c0d20494120716520754040c0c3e404103150960311240c07101c1d10500031003840c1008000c584000f1004d82c0014040c08101940c1c4a65000d40000108021959410b800c403d480c40a103000b40c192200207003003000b0410125810403900c10668860502c144502d001c0c0150005034800c0301191840f2030000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392432437 1250 392431187 392431199
    0x8090a02220f1b020636010b090a24060801090902030708030c01051906060e010c021f020f070b03090303150d05010c090f080c150c0a0206040b0403061b050d02090f1305040606 77
    0x1350005078405542d40941c950150303400d0070400c0d001c3c080340b61b0b000c0e54075245034203a1130351003103592407003030328100c0c000f040748050300b0001c030303400c0d00500302d51900c1c0e41d99034005000d9541d011624506413a64514000b403004120300000740381104c19031007132800748400101d980114406410a600640e01001c4144138503061010709403d84a2600070400041c10880c007002c2c480d80309012040d00103002901c1d0425888100c5445901b00c080e902c1500090b07442458440c500030001c0020303000074559440c060f410350610141c190b13281d22001c1d00c0b101c010100c04401c1d015a603034483c102428581d2040c02040440e40c100000780c6824117903c15401104c1120800003820380c00800c0d00183d09400a05001004150541c10400b940000000c4142480740405030760068031400020006080c0001d4003d84940c9140f800f442520a002040048a50050640124107420070155200740362100c86c0561240c9444022480400c1620440c50707001d21489810300080800c1d40c0901d00950013038000b031101e5600c6078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392433687 1250 392432437 392432461
    0x501110c0627062809080307060912020304050904022707020604020a05100c031d0604030b04020316080604350705010c02010221060a150f08090a02220f1b0206 70
    0x203d8086075910514a940c007240111118108408042c101032120340c0e01d61406d18903640051000300c403007070381e0f50203a8024015400e0011910540b248000d6207880d080401054403002d01420007030081c00850a64035084042514090005c04103031216803141c80c00c002e000755200c0c1c00b5030301a401500078000114441c209554001103440894403440721004091343e00719416600c40c80d481040090b07a0249850701d6950b03030010002140284098240c40c24107004041c1883d400101d4040407050003801000440804521982d101d504020b102c8627001502c582c0740c600000701910090840084c040241404003070384e010300221400b9031700800c0104140a0300303908078411400124002820702158005400700502174950051018007600c51946d65601d4004060300f01c2c08a070b0000c03c90184150540603030008509520006803001010480e003203401040c40764226800346280d01e007208003843e030b2007200d903001103689403100101000324203051000d20000d1400d04888600500410001c40c403069461 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392434937 1250 392433687 392433697
    0x9050f0d021c0822030309080d02041701140403050a0e090c0c0115060801050d020301020d09030c14010b0d02010806040e1c0e0102010e28080424020303040b010501110c062706 77
    0x141820304c500c1144c070180120b0b03103101e0104400f010389a0207460002854a0040c22081c1c00d982c1000d03864134140310040500c60301410000c6040d0380360021000440c09844a410b400c2905810010f6071441100400c8503508241301280790040c0d0b181e4141f03c0c91000400042000c8100c1701c00801c081121030400350132000c124891030b400200746100501c260700d00400303100b10040c8001c00040c64040d8031806071068688030381042d00841d1644001009011600d8500d403600c2030154000c2140c0c055200000d0072a48603054040e0401900308d000500d55151540140940c0003444101c540328038903049000001c019025840000a0104032041c540394014060340c0c45080d940e002401d1054503c40f0701c00742c000008180f4011004443c013031b140c04030390b0100007400a0010500240e65504282500c6505990104040c0301158001c1080101048030800960b041d03400910f0114405403000d0012844d0150308101294000780c0000d08254030b00f0305008414000c5001b242c2d88040415100410240b4052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392436187 1250 392434937 392434951
    0x3110c06010608070309150203071701060219060e010504210f0203090907030b190509070c031b03140d0b0405150303030103060b06071707050124050409050f0d021c08 73
    0x20005000c503038000c20206901c5804e501c0c00196080345a150389003a503000c1c01c40c0716500c55000080c0000145d01103114035000d50302c80ca00c140e02d940360141c020b641d2064036051028000c0070040507001c0040300e03001882c0b56140c840003840281402c3c00c0150700080c00380c8040e818100700c0150414914014048281d507444681c024508050990080c0180f0500003001001010380d59061003c7c0e035034450015110404950050000d0310342007505004107100302400302028000c01c0c084180010380c0c40701082d083d00301c0308410142280803078601903030301c15021004504520300c08a107112068070340c6d03446405414401c032000e1000b0b03203176124900010403d12a9654041e001000107101040340da800448034000050300251516030280c4689041e082620300c08400380f44001001000d1210900901d05040f0881000068510952008181b50704241c41054002c5032580ca600c800d1003400d000400300039000e01c059900001034490000d4480c01d41684070300c0301e50840124240581c0c4501401442072034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392437437 1250 392436187 392436193
    0x50a09120b1017070b090f0a0e0a060906050f040c021204090902150315210307030908010b090114010f03020405180603060a0c0e040902060c0106030501050115050f220e040308060103110c 82
    0x70030200500b01030780c006c1004c075400003002060951103886103a2106e00902c103a1a0714061810300110042c290361300707980711442190410f00c0500003a95002802e00f14107608850000352041f8421050b41071407080d07440025a40b0000c20002081e013555040300c0d000c00e2003124041d0080f40000010f1009002c00d54401d8075202905035039030700f64103080b2036020080302c001d003950307080c0050118200e1440e881880c00301e00142201c84200311442090192002c9080105e910008542c101f540380b00360224152241410001c1d0351a14004081c081e40c11039000e400080e202100c84103440d804400c2c80403007528254024802e00340002d0034042584221444540c0d542c0e85c412025103500d0405c00904121078090340d100c2400c00450303000380002d104032801103100303100129284d1300d4610311a40c0a541101840c1c188078080020284038200c4004560035805052030740c10a0b03426101070b002c2d640585800c0444003c49503414001456001510203218160903038042c8034030b1100c41d02c400380714003800c0301d0005903038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392438687 1250 392437437 392437439
    0x1a030d050c1905070b0313020907020d141b120a0e011b06020d1103090105010608060105040308041a16030513060c080d0b0f03031314011e050a09120b101707 69
    0x85042c2090a40c0c00b4030704540513207454010b0a0f9030717a0302c240d603c00c46009124100c00114204401c441d640301c2518000307070414504051014110070961205081031190000b50b41e02d815540c0a0480c0d1481140070403034541c1c280c5032100c005140e200c000d40002007070710100178812541c4200c025031240c03078035020480503800c0c6c82e50380c0a02035000703414412130084e210007290715a0030703c41020b035202d074505030004111540340501c0038001507005070105040101c1008107101250004c01103a00701c40141e0005010718034481810030150007031050012550008100d2b56060640c46805000e4210544200f03117402540c458003981c103028148801042110180440e140d10f032442ea104181404010780044100b04110000030704691000110303240b0043c204800b032240c80e12004610258170020309050100403003803402c1d4209554408554020820f00003886078030a84a02620b10040800c80e0642042070014a004110918126240c0c2e1403074034074040002e040c6041d20b040e24100303521304018101c89 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392439937 1250 392438687 392438713
    0xa0b0a0b0c03040b120f01080c01171b07240b01140903010b0a0f0e0c2508040504110c0f010b060301050f190b120702030c2e1a030d050c 60
    0x41c0c00144280c07015000611001a50f402804028510030000344900480c61505c03c1c1320b0720701c00301c1c103070040c090315480f00b400c0d5080350342c00080740049010208000000c40c0e0340c030b104c060300c0e08901402c21503507400c000c6150380401c20040d040d96124241503205800c0701140c40c84010480714203100703142c00205c920408021251404001381040040980003280311f88800002c152980c40590240d02d004c600e002003040701c100002c07119908400509045171030002c1403105280340c001d0000030801c0204a050703c00e010040101c0441c0c00030b0102034418070000c0050081401e007500820030031f2076103000c2c01401c0103050106100c1c00f02440c1e4020001c50441c2d0030b04091140e00c119080729203420048503404102c100c1004940c4400030070700003070f8007583c82d1184522a25400c101605080c1998011f0161405465001c10184204400080045c3c0941c0dd1200c1607c11000400d0b0b403140004c0c82c128040c00d0994050000148001c0c050b4111a0b8110100d18100c50912560001d01181d400140d4400b060f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392441187 1250 392439937 392439959
    0x6010f08090312090c0102010c03050c040311010909050f06090f04051005150a030c0501021501030b06010e010c020d030207080f03120c0705070512071d150d03091703030604050a0b0a 80
    0x8011004581c1410210083d9108548003594a0130203980900807440d055a82400f691607244042c0c82c00b84000e041c1081c500c1198000c50100030f01400704c00001c00c0044c1d1043e03032030340c00800a410301403001341041c080b502001541038558500074849000000c401000781340c006802141c4c0140100300c202641e818840042c4030103030a10803203615481180d040c0381e4444148001541c02385030503085207840c0800282c03500801421108000011400402c00700d141e09c0505c0703500007000e00f001c107035181c40040120f814010442d4020b44c0200c200c0c1001007030541c0048d070181580d411108450400300d034800ea0550700e0003240d4010740c42d02004c5000a4003103010300090604a80300f403082364011a26400001c040115a040c40c3c055070380a000204540d900c0701b9200144007070940680901d50401c050001c2d6069200c0a0213400380e841504550300301840b40c1c44420092228410004801100b011901d0b200c0d441901c00030f1140f4104004144004464403504000d100010005443d00d03140610000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392442437 1250 392441187 392441191
    0xb0102061303030b030709230601050d0507030906060323012c070e0903131e09180501060b07140607080f09150c04090f05150607050307120f08010e06010f08 69
    0x400c0648907021320300b0315101000390102610003028080344070703401c0d4000d8500900081034110918604503003070100740c1c2d030450102c5000071003c05002c01d032681c81c000181c0181c1b002880003402c0a00e401400420b02c060200c00080c031400b820a401100b02c8840c1c110380c2603801c1002561000006105144041326440e0420b408000307809c0d040c3c42202d5514046444545400c41d0b10450070f40001444441c2241e03603c130703010301400f520311107802e281ca028055166594014092540b42585d90807441c00d101039040784a50b1165408802844115140c8030281455048404100c40b900580c1c024100030741d0010500d0752042c13025540b40102d594581402200035030b80a40340002e00c2c0504c103402c549594070090440c0c42145100d121564070707480d120400c000c4544405a5240301417030103040c00b00c40246890307814011802114042e86a050a00303120b0300f1441080c0d030040c11801035002009040e50009a008200c1d40507444844c00350b130381c0342e1141003501800c542c030a00051080282044443c0036000903a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392443687 1250 392442437 392442443
    0xa0c120c05041a0114041a2803020d0c0c150216050a0f021804050c061b0102120f060907050702130e0a0b060307060504051507020117040813090b01020613 68
    0x2440c895a6a404241101ca045680400c00300e2000b0041d891035030448201c025620319030b44050f18081c1750129504d1401c6000c03281031004d142c0000ca0740c000d8080d803010944180700b0011010244001850090000c1d844100e000034041e04282024400c58003540d2800c428a4011080d1132128420107003150096012508141c41c6404159603c0d01058080004c0401540314901006400540380100085034000e10074903d4a48400c03810040060404a0b0304085803000f42c40c1c07903498090f030120b004100c0c45a4191304240e584089200d00070031282b014620301500b01c010b001c6845407140030501c0f412160854908000c900c0400c003030001070030181c14144564101c1440000c2d094421039480f41407010b80b407002c0d11089100c030300b03000151400b0b000307420050659003481860030740307080041548650040701d840c3c08400d0100e2081c1c25a40540d115222000c017900481000789010300d400012900f0001c0b900071185922080402c2c0710000c0e00c6100c00d102d105800810444e43d40760210001201807031011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392444937 1250 392443687 392443703
    0x80118170f04090204050f0f0303180609030d02060a0b01230315180a0506010806010f050903150108030705010b010203041a280e01021b010507020d0c08070609030506090a0c12 77
    0x14042404201c015201411a108015030b8441c0382c00c08200a02c2c1d4100c402070302c1001c1208440fa0640c1c0c0000031280d1072544e003040107000e480d4600000e15240511003220360503000e64507070b047c1040d50100e0114410030118004210003c0d03600300440300714120480345400005100c1d0f03102010101480515448040d00c40b011004401280124100e03c000d004200c80c8040d0340401d201d0030340000e000e00e41e448002071074041160b19204000a101030001c4038548103000001400304103e49043c0900c04052012151f0038407596900d007080c03641c90344181001d5885518041c1030050540c0f010048804485104034003440d41540204121015403000a00d041007440b28101da40c03180242e2060011090380036201c1e01740030420714002a003820221508034003140d50400c9810626038004007900e5810350152000518581d040ca0001c40000c003d411000491042940025695a0100d4807909882c880c4003503990584810858507038407443c8203c02020400161018441410b481811742032040c081d00301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392446043 1106 392444937 392444947
    0x7120f11030301091a040606020a03090e07020601060f02151f0f0b03040f050316230f0709021303150f0c09081b1f0201090c08011817 59
    0x5141d41c0c0940d00c440e91681c1000c1401820b9102c5d1000e4800c003e190349811001c0e47e240306240c0114002130050502041c06c80001030100d025101e5a0001c010030b0342040001d441c1030f0403110954003144a4020503440c00c4a0240c0101c4c0200d20788100c00304506c44d46440c1c012010040e410011f00d031386914000b00035140003541220b602941000042403c5a41c501d0150304511460607002141381d01c110031001401595260341c1080024a1060b0045ca00c044c44101d8032079420340c0e101c0c443d5400c9400100003165103500201543ca0010454405035034880d030b1610792050958802d00030342c5a84401565038045d480c4264001114607003405060707039147c407400c07581d80d04001010845907641c8100c0741c4040c0c2c840e54400e03050301d0403080d40d0200003110a84000d00a240304541618405c00d807640020b41040d040c480c00164012090203071040794030b280c0312001e665540341e820007641001045 = true := by decide +kernel

theorem cover : BRFrame.Cov 392266187 392446043 := by
  have h0 := BRFrame.cov_init 392266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392266187 ≤ n) (h2 : n < 392446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
