-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:39:18.830842+00:00
-- url     : https://prove2.me/submissions/79caafd5-3d74-413b-9ff8-634ac646f108

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617266187 ≤ n < 617446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617267437 1250 617266187 617266211
    0xe0706140412260705060f060a0e060f040204090c1206080309011101141503100507050f090406050301020a02010b010908070f06080901200405010f0207050d11190914060301 76
    0x9460407540001c400e88107150701403a00142005407040c200010f281d414000030380826481024044207803080f4120341c140d80b40d684400101c0381d170465170b01d5172000c0c2044d018000200c480180380c3d0420070207040785c0c194a07480e40c0018280d0f0050703041004a03039a04c043c50248158404090303041c0c500300c024100051810819483d440e4426040e00906002048504014101b0b09500c0f0318250b000b0704082c4e0209041a41a1149126403a0b09441c8030b403280d1106810412698400c92380221241e03280c4c145807040311f910454068004250142d40207554501c0001c0c0d03a1400e0000303010890042c1d00003c3d5a022420014141d440d194204030407950051105101143c070100c0d1200540e841410301800503a0342250b51800740c09007800c81c002010340802a05081602c0101510584a003603c420400805e400ca04a80d64245031040f182d00a2503030f131030040840e42e40c4035800b84cc4400a0280ca05040c629842030782c4040700755015007400340c2e40300c0307941b109115000021504540110020700410701c2440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617268687 1250 617267437 617267477
    0x60603020c03040e061302031e01140a140d0609081e070b010b09120f07090b120c0d050f120703030b0402190827010209043b1608010e0706 61
    0x402603011070035180c00800c1e080d6171b032020503102e06044120255501e26048000c40140c2045d41c2c43d0103411480080040356080d03804c0140f03800c07010061720104d00c0307625020300d0f0084510380345103040d00894006043c00c003103000e5000b461f520b6400360740ca0603170710b015034040ca100100b00c0007075000d1140c00c10f2095800240b80c00b252141181c00440080d52100c549200040f91850b051154080c10710415100080c000800f18000048550414007004007807540c00900890580301c4030036140d075410a40e1821241e1500b61200308a81d8003a07402c0b22644000c000f400c9140c40c80b900a6000140ca002c01c0000406901d80140082c0e007009603010760800d21304605030150070000a04080600900307100040740e020b07880c01c11000700403950000e6014403001c450348074002c0d03100303902240c0514140030140d41701c8800e00f00e58103498010406001c062460000d1001d9011000c0392504035603003d006410300d1040350300100700d0003814506000090410009041c14a0003415500140c1400740d00e25440d140e5502003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617269937 1250 617268687 617268689
    0x30307030c0923011701050d06020c15090f0c030d0e0918010203150f0f0d0b0915010f0815010609150315031a150f06070204091a0a060603020c0304 65
    0x503080c0030903072100c48601036910030542e403c031104080c21540784040007a80300c60510350885003a00d64071103921a60407000041d140c24050240c006440e90700960000721154001c0c0302c9605044159807010340e1604151489010544101c407c560140c1c440e002c00400034000600404c20460050002c1001240c014044036010000244682c0030000014054941042d44902d00034591001315620b182c020b80c01040312800a40242c080d04844414903030714100500744580440d4024440c80c03140d002c90b0b540310b0340d114000b4a50002c0e80190b0031001744206801010078042c040140d1046055414140414500159090741400110800004101d2944c11103804000c0e00c00f0140500c0000e01d840344290b010f010b07504141c5000c04c544100c00401c0c0402149944407c44102c491800251102c2409040d484010208a81d218aa00d8206045032801e0402040b01c3c0d40b01420100c0d03c039229442e261801c6080d0807503040410341c14020400c1030b0f001841121702a1044d400d0440c24078190156190b1380e4021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617271187 1250 617269937 617269951
    0xc0108010302011b0b0c13120803060907110a11040b0409020a050616080c0105060a120804050603190203040f05071203090509151e1e011b08090319050c010804050303 73
    0x5252040351408845072010381c40a0b00f080c4c0b1902c00741451b0600301c01903800451500b20424607024046034200c0c1c00503030701ca0f44c282c0109049040d40c84034004c01000100c05088030081c404405410401e00707030107020124a00d406202115210302c0e40800340415603400241c6180300c0c51604c000600140c0d600c0d100617068540a840381e98840d4a842c0b1490f07214000c560001d0404000820110600307141500110310a200030740303140308019903800924078510bc602c80c1c003c003031810a000034025414068090340c1d1014141340040144c98038070500c0c00882c0e01c00d4405440c51602881c1c038405000d03082010800800300100010300404c55924000d003200c8003070152a210709800000700f603601c81c010880301c035402c03001442512005081092030840100f5268002d00505190101e240b03090f0503040140f48801042c0c440301d0a00b68040700e12103050401000444501e4800d00000800e52000c0044048005510400d449000007a041003807800300b543d03145504010108e001c004c0054070100c15280c110807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617272437 1250 617271187 617271197
    0x5060f040302160e01170304061209061b030506152109100c0909060812040303050a350603010507021c09080d0507061b090b0d02070b0a0213080c010801030201 70
    0x15249012400c140c1000390318290029940c40110701c0003020132049040b900846000b008900c009054a6268000e40c890140450b180d0351210482c0601600721f0311003188108400984281848003084042402e10410300010b5031310000c000d4142015a1b105101d4132442c02c0321401e110031210001c06003510501c13900345102c20071012890f003610410141d07501c845244c0381802070002d45c2500810070441c901c52444030505200000803446404602c0e101403000d00d6140c24645030854034242d031a0361006034120108948618080071200c3c541c42da048050041d50440b42020403100c410075003000340030f00703840d10a9142206020640b4ac000079505400c5603070401115500702402c0e820303030740034a0507403100303100d400b403010b04451315036010005145592060301c081101c2d010800c000b02e111041110b451001c2020000c1c20310810321800c0182c030300c00341414805031034200103903148811003074140c0f00b1400746070b000300354402080c1101005c203026040e0300c0000c00c020a0f818000801e6070b1818480641808 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617273687 1250 617272437 617272441
    0x306210606060f0906071410060806060d14070806150105090d0320060901050f1521030d090f03111203130606350c0901031506031a0403080f0405060f 66
    0x10042010b0b204c4180c0010305c496154001800d01386407510820000c1d08103405070308000c1c000c4130300b180705034802d45000400800d03079550f52070217001114900d03035400d0702c1807026101c4910300c41030200041d4011b0460381001c1d00030ba003441d1803034082e0480c40e9095035062040522180c86141c559911001000b601444c141042d102040d4011100524241901402c1d01510041025000c1c054008500032800258020881e0b51815003a054468107a0030f965407050300c240300d42807454100785002d500d10aa11094078600000b603c0d2400840310f2504048031000d8601145074285500107620b22140b54030380c0090080e00b07440c1c8042040c44d120050403164071018101d0301d041444002c0d80100c010b009140a0071448401c03107580e446484643d20400e0700b600038001e00600c036810000c01d001c4480c80000e402064a0b90a5075582c000c103a00c40340f880b12806990b01743c000040f079541042d901c40c41d84110140700b601d0030142401051240018004002a1115410300c00021400141d40340c1c04511448541038603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617274937 1250 617273687 617273707
    0x91101050f1e400620100e0a0b09010e2e09030507060501090605010c031d090705040e01120201050f030901060302090108010c03050109110403120905030d0302030621060606 76
    0x20301420900080f4074821001c8a045001c00019200103482c00551011145200369540030100400e4041c800000c1e120501351919514210409180514420190394900b08001030040459402c404444865031281e09401e0030300400c0c003407032500078a500d8002e00400600070f840e03660724485d0020b8446900c42201007404c0c080350300d490090303c108030000705004028481c200242a5000100150703200c9242a000050180e504d00c95201240c0060b1a40700150442e6201030740c003c03420b00c041c2c4954060700d0100220a650b54072541c0c0c42584141c5980d9210350620316080c00350001604400d0b0201e85414103013015071707080000d4659003e40000140d030f07265100d800184c05032079540d1000303401c40f1004002040062041d00900d000411039602004076030399a60b03440d0b05841c000d17442d0041380f580812090000c1002c0c1c0fa400b201c29103541c20880c0e640340d9103102092504d10342041000c0040c0d4003200b03224062410f01760790000c0c03030f0f031018003044903c08100d14283ca0310307009090a445a540000d403502c0c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617276187 1250 617274937 617274997
    0x32d1d010c141c090501120e0705010c05030405130c090e04080d0e1603030906020114011a09240304060e0a02130f0b03010207050303010503010507170708070507050a0501091101050f 80
    0xd01004444520b0204080c224003400c0030340d1350f02803d0302240d588540b10500100303510070504038400c0070300213252552505006641d002200302c400c0c0c65a0004200100d055200c000c4802072000f01c00b0030020b00003295000040c04020729030410440441c01506100c04502880207444080060b44c400050420000c0501858211103180205844246440000903d1341140d411002c540c5560000e220003c00c05080100403002406102440c036080e00c112024541802d029240194014010700342d80120300108214040c803032200140c09034070000401040103014060010b81d2005800140b160704000d9000411241007200c0321006d0b03d681c1c403d094410f81064202e0301a40c10702500866503007009090250f103d91003400368900275800d04d40440d03045441800c0c070303124000c6080780010b001d440e10613040341d1811010300040c0c10400107003c5400850400d200e1302801c50b100354000078186102d45000c0c10341c04101e904280c10300c41d00b844100c004d00c2c82d20044404102c8880e00c9900401d18108410309 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617277437 1250 617276187 617276203
    0x1103070b220b07200d02030d18050307150b04020304030e041a0d0501051b0717130e0c0307030606020f1009150e061f050a03060504032d1d010c14 64
    0x3040040e07403428464070903009030b40030b0801c00e843c68808251460044d0300030703543c400d4152064010384c030411a82c004124581e01000c0080d4107004c40c10042602a1100c5140d17800210081c2d030000300003800d1400c01f070424881d440074060262019821460306440141210001081d41d50046484034012000c40100e650b810b40344a000030141f054140c1582800d9000f4101120003d2800d07440c848480540c0820306d040d80c030401e0703000744400d0036a0002a0180001d42021100c4c90440841000110b006011007203401d200700c900d524116141d1500c1103001b4192160382d071101003550400c0c8130b9205c1c516000701e288403507980d0b407440c04110b4800030300c2c0c10b4505400049101c01c0c00b500e40703000d00c2e200980202720580941c40c501220400701840c02c07001c40b02190355110f541d500c10031840c403c00c001030b4aa04616840707070182c00d094442c0c80e0420301c01e8500700c03440318003120344c00311920006400d95044030007603618002c0048840d00100c100000a04007503004200541120400e4500502404ac10030540c0303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617278687 1250 617277437 617277443
    0x603030c0828030903021b0307050607080906030a2f2505100c0f020c0a181e060f0608060a060302161b0e010e0708062202030903030402011103070b22 66
    0x54441e202c9490001d0082c440900110014012811003400810791100c60003005000280a415080d10b000104423541e40020070884c0c10324410300043d00c03030343d80c2d190213584107180d0800040380504045003004081000104503c804191680410703e50309481819240f0002141d914401d00b01c1094211102160b0800741c0100b4a20540c00f8002503035120f9000144500007075210034015001c0104140c0c0c44910b10144682c02107a0300408210703d400070b0900001d649840c11000595140304906001c025040c460800c203020303180c00041204400e0622544001c0070b00703141c416000c1c00e00c40300150600b42c9600c03e00c020507402060712a1014007400184004580c00112104d00c05070005510341104850311400c0d12240754440001040c094291002e482455559500c440369583c540c02c11501d80113042038100312082c07c2d60003100d071404a03c01035014428040c0215141c1c6450710004200e00c0d04500064903941040c004000040e2507401800e030400d045200010100c80800721a24030b040c0c0c00800a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617279937 1250 617278687 617278747
    0x30e1f0b04090813050f0a0b0f07020a0e101406070201050d0c18030f020f06030606091e040e010501213804080309120405100806042a09090603030c08 66
    0xc8951001c107600c2c04c1c01c550b4141e800e903845841c2d040c20000e101c0e482d03200d1314104901c10003c803000300c00d511000b0321115200500d40d40f09507481d2010150a0701044507000b40c8003004400c1030101100000c00034855100c1150390b2803809600c1e0340020400e024014404001c9921581c02100c40e0703000b4220604004643c0341520500340d941d0a040400100d81c0c1c000380c0c0158400d5070403101508080d41201d10403900581040c5c81d04007035000380302c0001607207440180c2c40c000c440c18010b1680d03901d0107074100c010418030000c100ca5052103541c0d01c507190405010b911015420354680c00080a20a034134200b03034110800c1200b07032914045044020034044007159052020385040000704843d904c080c44c0101d80383c20840c0c24564032200003110b02d00c10350103010f40c001070b0320300c68101d1717607118008441d130080e00034002050311000046403600c2c080001c801e480c40446000c994000c0a64421460001000102010b00c0344038550b44015221700010760340035003040e0f00018205580d034900c02c0003640300c1c0701500507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 617281187 1250 617279937 617279947
    0x503060412030509060f011806030602030711011406100807020f0d09080c04050f0c0702010215150112091104022a06240a0918120f030e1f0b040908 65
    0x103240801c5150308800420b00c0e000205441140c000f517a41e00c9000380c0b0110f402c544c0d00700b00400d020010250340b030003003c5488a40c0840010142e0002d180180302e1174803010941c641800740b050a50b0106d507000c4101d29045010041d01d961112200f054145007030502d0b00060700c0b0070714102c2c1000e6141a045003188032308402c0006c410b42c403100c460708540340d040c2a901000ca401081005a44041e40d024118000047c007054a8081c004020044584140120350003259a200c18160800044500c00c00100c0c1b2a10750398559604101c01c0070104585c00d2081140c41d540381e07146a000e10801b0b900a0040f0341c0030500100800080d108c8080c507802819101d01e03030107410805540d58210489542e034120711048545c406104610f0591a0343d08002098036954504010b900d04c0140b1005d0300c0290300b840788e00054400b18259201c031049010302540c030301392042c0e003001000d000d4a544401c80020303540321b1070740a01d03d500002200c120141420f079000c03500540601c0042c0141c40e03c0d0501615908001031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 617282437 1250 617281187 617281193
    0x2091e0616051912080a0e07030308090a1e02040c05070525051905040e01090c0306050703020f040f03020906090f16140d1b1806050d020409020d1d0c01090303110705030604 76
    0x1d0f031401c2c0e00040e40d40000d1940d52102010582e010504d003074907d507002a6042c40061700a02c60306511010741d804681c00905282c59084811047d40c80c600d450406101c070103815420725009800c0b040e600740c284280f500384a41e48095031000408100c954420407485499a100c0c0c22003491401070200400d242150804040401403401003845020b02c10392902085580d0b0a0041c006e0440854101002c920503511b0354031000e01404004001c0c90405508012400104031030001a0024000d800c0f1440c0c00c01e811031050040d00e00c40540744a116017003404c100911200ca4800c80796100e010700c210048155507807002661070800301c040c0d000c18002c000c240c41a12030410740c00a0790015907041400703103550340100d080c1e0380c0c800c2600d601e0381800c030071810500400303009000900038032404141c010300c1c1654400c00704040b6001040c42a29035901d8200178884076101072202d40e120441440034101c64401080041c1116074503100082c14040e850746c0407540210b041c082d0f00300820016050b114189071502d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 617283687 1250 617282437 617282453
    0x2612070e040506120706030b0a0902040602030408060106030212130212030c010b010929210f0402040b1203160201020c0a080a0317010e06040f0213060302091e06160519 74
    0x105031900991600000641c28500f450305401c40c000b02c00e003e01240f608000c4100d010b04604556103801914000001a0502981c40200300401c840e0f40950380300d5040c2f000060401d01e060380314204040c018003201009e030000e81c81c516002100b42ca01c404001407288086415800852088403880c000410402003424040d0403850120900740d07200c407410358440490400104c052500204000158042510311104241c02000190350400b01b003000500105c1d51400c0700e0001303c50660040107100240821400c00d4001c01d820b5078402c8500c01002e000400e441942c0740605507040c0f4001d400b8804081c12741e4000d0000c080710040140143d0299916813550690392030f542c590403000100001d840c0c0058540315a0002e044c1c40d420290850b00b5109d40c002c01000d401651121240c1d035500b0090768014440c1d94172001c008143d55140562500cad155403c001c0d00644486101600300d41c1c001840b5030607a01c1c1d0f81100c00a401502e96181c8603100c1d400c02900d00b840e058105508150b244400d502842204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 617284937 1250 617283687 617283707
    0x308030709080a080901111002040308272808030d0b03150f01120804090518070f05181b040816120201020606010c0302030d060b07051009261207 64
    0x151500180715a84004299880300110000703407a28078203000051041d03100d0b841980b000d40c10803084904021100c0c060004a1380b180e8802c40b0360080000319030204200100d440c1d100d01e180c01400341d8041c214035010a0400c101407685100e100c001d200360407200c1c612007000c00701a0440c00203c03901e032528481110010124581842d00c40c1c8180c000711202802c51034980f600c42d1040101c1c0c145030340d280140c000e560101c1c80004484803003040c0008204507006100303175071044030b00e1101406501007070a201800c0c040143c1120800b100d1041c5c042c40980c442682d160315046980d0481c00c802d42e9084040180d85a2802080b5001300c00018002141400040c000c10000c003100407281c4115510154140042005100240560019400030ba03140d03000b5080c20031154002c6c0143d0780340a004080c07400446213580c00c454500d15000c5081400d015080215101044024004009081458980d8490780c0e0368010440345000c038100e0390501c00c07402141507400003221202d421086052642000e0700441c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 617286187 1250 617284937 617284951
    0x21006090203062409130516030204080c0108130c0810050603010b010807030f2406090f2601112109010603080d150f03050718090201022a0a030803 65
    0x4221011030086440c1c400c0302d014500052040820100d0b0352003540300c901d041d01c624490844184514a96501d038480341e520020311041e00010366103000c0102c04038040c07212403004c04140c81880705210602001070b11038051380c001d00303140c060b554480611408034402d01034000c2030300c120400700080004c0c001842440300d9030011028401c583e00c650925080b41d40d00f54005000403480d0010940e0780f40240d1249461001c007820201da40042d600b1034a4200b01988848201500460400c11405a0018198001e06246411000c1b85841e20282d0742c24812820409250601a00b041856521096101c0300800011031401c40e2a111041c5524150030198410200b81d002020001076140d00706200325400e0329400340c1c03214148004491000d004044c3e07000000c440389002c1d9804a89850000d00c2c0f80015880761005090503802c10072440c8010305100086650103047c1008200140c0c0c0104411156031310112900d05036456083c4104021700800104940022084001209015000c0015441052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 617287437 1250 617286187 617286191
    0x1502040b03190b010e010f0e0306090601170106030209180708010e03091002030a140c0a0203070e07110a0b06010c1e302708060c0408011104050108270109030210 71
    0x40e511400d9040c1d404030f50304140010b0408040c00e507507601440004c0e081d40e0307140ca00032407203000346c0d0007081c6010000d41c0c03c201158802c400411844005504400407240410700074015249036a020440c018400b418100b0925049900c0400f4040200100c0d4001d1a00600911481c1c2070b4155054490b40581000c0780110005401480c45034000411241900f0880d61880100301401c0607958481c0c100e02c3d89036466004040407007001da541000094050000500b14a500b0304280d5400317403030103110000c0760030aa0002e13401d10000c100c0485000f40c2c4440f082c01c2540449640c4d1800320661280528000d80b034403c491842030900c03c003561551030082142c02010b03400218140461284809060300300006450340285481e0b040c2e03800041d078240b03914010410f52060f02d070180542442000c13944003180d0400445c0400040409024901c010280700724410314050810000910105009202021500324805032030b46c0c0c1d01040d654502c2003108000200400461840e00a40f40c2407070f000200c80c80c034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 617288687 1250 617287437 617287471
    0x1f0302030709200318240f06030c040903020312011508070e19080606091503030904090c03050111030a0b09150907020703050d05040314281104060e010608090105090c04091502040b03 80
    0x34010840303448004010f50300d43d1b07640d42c8914004000d40d400600c0680c050080d500c3c00c0d900b47c0c840e8018401751038400c0e0090340d21100c08031050001600d0580c012180c0d698040160b00c0c41d1a00160310582081c05403030310340b2504a004000c100307000401d200700070404d12807000005041001040311401100111514000f54440041001031f0350203000201d40d154000304103000c00c2d850030303520604c003441c4685500d03000e0950f01d445403800c48080305c51074140008000f04005414500d8850300c02d04070300c102c807449100c1c10903102100414026180c01800345080402041ca01c50003000b40d0760055071b01200301c030480305134508010100d81080c402151907407582c4c40e004002510208910440e0840312130014090310004110101246540105035114035066181000350b885500445000c1d000c3c8820f514100d5141150040c00e03000008d00c450701c02d034544028001c5030701c0e01040c5481d50b0381003214081000d07801810885034558001c0711484d102c600c001000034042c406c0d80c0c00f85204621405d4a65400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 617289937 1250 617288687 617288713
    0x250803181501050f01140c070f09050103080a0e030316060c1704080f0a0516111e150c01020d0203090c030c010215040b130f0b1f0302030709200318 65
    0x1410341031400042000720360010711440c00d1042d40c5803034a600502d03008905404080410210368840e441e12109600401414404845020304410041c105200200301641c90341d20782c4100d500406131810104142045145081c1d81d08000751500c000040f0220100a116841c050b00181010480310003c1100100ba51448103442061305210f50b81084130140b800d40c00181001d0075038807400c070080502c4424400b0300150000040784070b4866101c1c074000f10b044000c2d07508000c00c6440241c103140403507038004050390050f03c071032680c0c000c0704400d0100651290300d64004180079020f0900888029440030040202030035000460111300314094041d1541c10950000491315040c2940750000c82001e214007090026010b013400c41c3e4001107101401404d120305641e48280055254826202c021001c420302950711002d448200d00b050206c82400e90091035075000c20340700c007202c1c0318186d0041c1e528207180e2100069100780319203250b0404621940d9242502e0305404448503a15040003c0c410f905c421005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 617291187 1250 617289937 617289943
    0x20310030312020901020a1103031e0a020601090e0c0d020a211101020601031707060b060403140c011e0806030a020a080d020601060513033914030a0f030525080318 72
    0x2013401c1070740548a100159212045c19900c100000c5170144400c00c4409501803203004441c40e40344401034170700d036141c0d13205100a14200040e003003000c1c1d051802c2010054807900060500310400107a80d202004881c0b40001442040540d00055111205002000c0741c1d00040a00302103507072003041a81203900d01c0b0001265141003d0000404030003424a00240c402200009002d10512076130021030b021070f041000c102190004da200311001c070501614038601140a1180e00030700303002032070120344209110552100f8800c1032524682804601000715803a500c080c010076104580251036940500d41d41d80c104c1d0b80d9468400c4403800140035007000842c01c0c6100c1c000303c0d8002d0080e455040707071040c110307140c40c9a03022001903200c120b41c12405421501c901c2e55100916590703100074420520615121020364100455000b1a20a410000d90040001c1c2604040110107426181c0151960089110300d11000268004d40c40d464546002340d000b0000030500030761042d0203a050070f000e0100aa02d0b40341ea = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 617292437 1250 617291187 617291197
    0x13020a15050304150603050304060809010c031509110409110c1204051e010e0d03030e01060b0403050303040b1009020706020a090914070521010321050c1b120102031003031202 77
    0x800140204003140103e01c1c4030101ca40e101c003210100040302c0303651f6980c0c589164819440003001c0707115041000000c060a2180843e1644c040c1424400520180401d0401d25500e00400240c0c0d03551f5003c1e640144200000c0d9406410341d01000c00001d08015880d81080c0c10109441c1c41e60320441d03400b929400d40403000e4070b0854201030889544031140c4100c244030413211703000c035504012002a219405945995503000050b000341c600240065001b105142559040d8101034540c8004001c10000918000304a03a405038001c0b0701020b682d1a000c036032a549071500d511003000c46001154050512209900034082c82d90140c0700c0c80c001e01e0782d4105040a40d04a12900202060703a980000c600754061001050441c242c54030360003a200300e050300c114181c1c0d400c0e0003c1c0e80721081307030f620720000000d20680d903007804846051003030511103d80b0700903070f84661150f03090b554104c050000b04110303140d1054510000e003201c8020b540b28540b064900300500502e1205030009030013030800a10341c2500b8804c60f1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 617293687 1250 617292437 617292479
    0xd110307060f020904050f0402030f190f020d0807151803050901211503060c080405030d09020a0f060206070f111207020a1a07061b08060907031413020a 67
    0x5410404581c40d01002811440010428580c00b080280801e903035a215981c4150500082c5821508050040c0351800964840c0c14100350301101c000c0304005000780c0c40d00807040c0d0041c0001c202a190384049104401c40550042480c08d0104001c0208140c60302004030100300181c0c100070707100c4001c54400a215100a0103404990200280c01e550b500c91880c40424214011041c040244e004040504039002e000c030450702c203025401d003030081003100d00031940000d40625000b640f0341499180c1c1500da00c2104c007241800350340d50700040304540740d0f030221100818544001c000c207180d41d900080d4036480e040f121040011000186417070024000c025a00f004081c16000f4a40d8801443c03807040740f83c0c010041640d01065a90000907600b0303411040d80480005084801d032a44494500345003620f414620440030702150401d1450700390760040b40258040c0040b80d00310390300c1d11085000c1d0001c141c10074000e103103268440100702c03c12030110741c0030501034429540e1910b00c0c0e68502c0c0c01c40b920320000110b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 617294937 1250 617293687 617293693
    0x2306161514160908191104020304030806060d0608150403021912030e01020715060e07080402060324040507030c090b030c030c0703050f0307180b120a050a0902150405030d11 76
    0x214484030341085070440085824109943c510362141e599525001038081c0003204954011509402c00c5201c40070343c00041010b40c1c0c19821410b040da805044442c000f0b00180c003c14010030040c1030307008a2741002c0002c09421050360280c0855128040622004880030f901600c94800105605130020190003039035a0001d420155483c0411011070250514040580f041d640038005030380441d00c801c403070800c50074160100107041c81c540050005400c1000703110005100d002d0042001681f1078804a9610007105199004900555581074442084050703150381c000f0700e464204070303901d9016400810b0320039040d00c3d2100c820b130740e91a80d030015100c11981504030724420300c003041a440010018200080c40303814580e0a05514003603411107500111220030010740e1403080300c000040020380590103007444c1c4101030301d40300d10000607840c40e1101802c400e0301c4a603203030006480d00d40c0950003184501d50040c07510380d01102039218030006801c80d001d401c1c46801011488049180240e0703529840005403000303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 617296187 1250 617294937 617294941
    0x90f0f0c240e060a2f060907062a061e0506040b0604090504030504080a05280b070c152a05090901030807080f12040c0602010b0102072306161514 64
    0x1444880d0f04549131040c03d0207028501d01d506000b844401400d8154050082868000c002c080280341080180004101c1c3e000340000340011a400750b0009a16280d800c005001140d800300a0360a041590b4000741c40c0030718140c018240c1e0b1095801010f80c01c00b6151082c0025280e6000300412110241e0469500100400080140007a42c1d0402603200f07010342002414240d1380c00c0a83c1c101380e94000100e42036003120014189040d440102017884c0082c0300d418801c92403c0343c0d1160741c940009031a400030320010100c40d500b00810f6103d031203801400002c042c404030014100c00003427070400c4050341250500c89052103251610420503103012100083c40e1080c540d19507124001198030284040d50403100801ca9440380c0c0c84940001d00201419540c0c0d020245010309051f4060b50180d00441c3c110790401c1144251aa40016400d050f107440c7e0006001035180782000c404508680c2d840160404000b00f42d614584880c9500700c1070381c1d80180000242c1f0190740040c10122821080c2404901001c100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 617297437 1250 617296187 617296189
    0x50105071b110a08030f0409060e130308190e07081b0d1e08191e050a050a1e03090c1707090209010e090f070212090d06090f0f0c240e 59
    0x441004258400760003443c00d95216000e40c0d0941c3d0041c001d450520700700040406c0424202e01c60b1034024131035240001e1240c200740410501d04e40301ca80001c2e04020020021444084541c0c02d080c00d4403c0100b0308101008402101030b440e80c610384220b82d41c60051510301c4520b0310303500d0018425110000d00e01010301d003903542c0301c0d402d44048440130140b007000c4c45902000211424001c00c1080300ca5034030051a90b100480003003030306e020040d081141c0c041c400c0b0311410680c1c10005540c902d031464107001c0e807144141c00b001ca07401451541890341c40a144c10880329269015404008658020750b80c480d0510b0301d44241c1000c44160510401070759115040410100340280d010b0105c220051400360154502000000e4a10400341c0e100204080c40304140b1400da41c0400050141e03480c103400319400e106401e40010b100ca0400200941015100c1000300d040050110400c0d0b0016032044202000a86600742a805003200e4042c0e0483c0c2c2d20301c8001c5480c841030000c0407425419242c1e0703036400003041c840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 617298687 1250 617297437 617297453
    0x6210203160302070305041e0f050f0d0209091005040c06030533040209060c0105070806040902220914060402040605220e0102040803160c060305060d0303090302190609050105071b 79
    0x1340e415400c00c8014800410103034031441890490503242c0950014040c2808400c0c0324082d2940c0c032407442294658402d501e140c9030341aa00f64616012a500c0990f41c0e0389181090501030601142d184403854082088100010141007105440540c1d408114941da4048a4207582d01020520480d010f1a000d00304600840c0d4040091290400341000d81450a6040031540c01e40205400100311303515202040680d41c1e0140125a20040841c1d003401525030b1034001c1803482d80b82c1a0880c0e11300c14540781c901c64038002c5401038040c41768828030300c840701d095404000307444a2054030101d12a80c200100011140b4143d001c00007466102092500e40c3c0c000303450b01344000d0950581c005c2441d5000d11002500b054240094542e40303c00d20860240c81d022450300c1c1180c00e1060f0800000d00d49048140119503c40411014881d641070500182c001950704040e86000e10004914021440d01c0d00c155007045804c0d0485041d40c3e100e100240413030b48540c1e0301900c203585c3e11031540d50a8003076000d510003c12404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 617299937 1250 617298687 617298697
    0x3031b15091a060a05310f05070e15181c0b040309081b01030207020102010e060c07020a0b1e0708040e01030804061d0609130b0402030c03180a020108060609040b0a06210203160302 79
    0x112a03081c2eaa50607001c0c8101a82ea0a02c0d031f0900150b5598100045641c100006001c100e204551211100e003603034203006000e02608603428000000811039550689074180964018604800004d4541020789480d1b403814204646c124002000e03000d000840000005111180c81458610381f1442513503440110000c0d04802c0059046640b68501c2c04a501c03001d0001500500307508050594038520790041c40310280b080d40c4180882d010802c0580c54031082e442001d49401c103d03140e41652581c3c81d0501d003025024941200403825a190700002c01c01c92004018812240f01d0340f6542c8445451a00c42c00c809044049820341101e000c106105003454940c110100c804840c03440002c500f501c1201246c2240c00031100ca102c0b070b507000000e00030742c034410508101818103010300500074400b003079000a0401a0260052380249400b06150301c5559494010390501308016100d02d40040d41e821740100b46408070034150300050107105010300d0301d03403460080f00e01c035406140c00420440034100044000b5440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 617301187 1250 617299937 617299999
    0x20105071e05091f020f0a0809090408300f04020d0210110712230d1b0b1906050d08040e0705040f0b070204060f03031b15091a060a05 59
    0xc029052896540380c100200849000d104d8460020701c40501a29100545440c50655408000414001080c6900310384d4140707415074201409480d0343c680500c180c0101040f07090510180d5041e04e24070715044059814441010f0000000e58642501d608100d2400f0b40707003e07400c41034040070320000d03080288507619841190301d0804156401c04c49103a0411503542c00c9185941940608007003800301003031031549146010802078401c4140f01c221241d0f220400c0000c2c1e000d00c13014625802c011108401c80e102d409811004c0c4012600e403007a07600304180140103402c1d212a28180e0045944d0802078a5440b48540c0884107a140c0f50134a01540b0110f0402000101001070030403020810b0302d00103003490018162504500d840f42764920411040c0c0320582c21030101810410340810201c0d80c03280c000c02d003100c920014080350714010308025000b03a856606500c0024201286001000010940ca4028000030412809203880e210104000e4a007240308447e40440018034a0201e2060001c004030341ca50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 617302437 1250 617301187 617301197
    0x20c031806160309170102040b0d0f021612031407050a0810050312031b13060e010c0c1d10031208220c140301090c12060b0613050a06020105071e 64
    0x32001840d80c000b400003550440000320040700c01c2081044030080945c403c1a414000c0d401c05080000318645409051200b0003825210a6504110070a035811241016025101c4006503481414402114541c0380c80074000039107072549406400640200d040e000d042e0302d030349481c903011500d0700444000b06c000d07101e410149181040043c0903070381000801c10710743c00325501c141c59240824030b603400e81c2e4201e80c032910781d003004000780c04c0080380f042c17610002d03544141007880d140d2421500490b0b07068100c5800038002034203800082803041c040c00400301d02e03620492005030151365602c80c0c6500c900c8a40300080a103541041c0507075665005645469001c074a0722013400401140713101940060074040010b03904912109011312940f007a001c9000a1900190001d2009281a0307031040e0080500d403040505000b2244084c104200c50340e0002c01600320001c00301e07500c5a101d0b1680d940e80311403030300c1000c0c81200c84181c00074444d4010b01807035100f21110b8035215519003144407400e0f4941403489041013046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 617303687 1250 617302437 617302447
    0xc07030e030106031a0f01061b0602120f090d020a0f08220e0601120507020706080a06050409152003060f061209011506090b1c06050303120910020c031806 68
    0x81c400b40b042e20700460180c1e01030001c08010241840c84400c1c084d10700304150141da0018041035400068030f80d0032601e1072000c000180d401c1e00700350000b402228010450610403070207209041400d10130860186206105813041c0c0d000c0070300181ea6031811880300070000d5082c1200c0f8000310380031034040e050344400c680740e01e9002140d090621030403101c240c001440b0380c91120300f80141c550b8030100b05090500c100b4010803550501ea00040e43e2800b0500c80c000801503104009000c1c645190040700062501800c184000c00c15031602c20350900307610841d00720300351500401c5031058914840b40344504612101061543d00c6030300600580004003a041508200c0410050000034000a0740c14402c036515800099402030311001c00c0c0e40700c2110b90100302000b044040500400740c180044811221282486a03c45200ea10156001e0500c651006030f05000118440c9a62030314800041c4c42420090161038003100042c0c8803204038000c61100c42544d074000c1c070280b16010bc036008004d10f4030000500c40d034200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 617304937 1250 617303687 617303689
    0xd05070b0c070c080604030507031404120f022106040501111303030f1e170705040b0d0203100b0a050c0d0c2013020d060501020c0607020f240d0515010207030305030c07030e 76
    0x5c9000da40c12800144001912030078103074080b120f0340c0300700c030f0848080345010b26004480380c613501000c1c400780c040d0001c441c0300310443d502c10b610400042c0760501c1c0e040040082e0f400b50b9894040454050310f2035420180920449840300089400404040c0003030384039281185c8040780c0c19203105644905202d480001006c0c194480f129440c4550342954608140f01102010054001e0001e4a1441403003418031040c00801c4814090b6446010320600c0142c8030754034000711440072201640661070072a8002200c0c0b02d02584040141a02060b55007120340c0013021050885910280720000307080f00e0000b90184001d91103684140000840050440380700c807400000e6802281e12060300100c6041e61100108880e503014400244815002c8588904100349600403d98841c4009a001e2290303898410400c03000c0000315a04482180420403952900c2541422800419099519203052001c003404d001496100040c44415603604daa960b50039501c403840080c6640e00450790407411301141b0710080510f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 617306187 1250 617304937 617304943
    0xf1b040b0306041415190b0d05071107080706050309100507020d020c180c16170703080105100903081812071d04051b150a020601080d05070b0c070c08 66
    0x10340400000c159803424860300b00012600b01141100011015608015400b490444050b82d400c03c151290781c43d40103949850350101c1c1c0746070402d50200d240400c56000342045a03011600c101100e44810386840a8858000d40d03d1a040c4101e100540c0023007000d015030b6210300b003d5a001004031040707e084c1400e501004c03003955001c845250040c0c1c030180403900d10590400c061140440240ea96100d40c0705181200610518001c0c00048a000e00080f04d10341000000c1110f501d5582200c80c40c910010321540031041030340316040c141c0001c2c20150010909203400d5180c02c143e40903030303112070001d0303891642c401405d5000709800d0050b4060714204004c150702d421011044000c80d0f900646622800e04a44451038000010b8401300300318503d04001c001a40014240c00000f2050f45c00e0504082e80d070f0025040d4100c1c0765600c08060750100c8e4071303001c0c50780000f103043c10b0312060001d403050242c45040850f103074080d242001d0314002952000c100112143d000510031107000d01d101d0021103032520500c920b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 617307437 1250 617306187 617306189
    0xa11011d0105160905060a1b080706050f06030c1e0607050a06050a2c0313080105071d0d03030506120d05040e0105040908090f0a0509150102240f1b04 66
    0x98080800e14440c0200e180a114040e8030264a02c121400400e1060b00200842543d00405000b00ba0004041864038007400810701841508140560740004da4903200f62680c0040c602256a5410302c000f1800b40c4540d00c031164400d810140c010021820420300704443e00740c0380701d411045040b20f00702100441d140c00e0010403000340648010111094146003c00403200000c01030b40102e485d08100d0500c01e4105883c01c00b100100165290328485a00c80b4a804c40c03017140d0803550644900b44001882040642082c1d100d40b01581756510300008076040703450b01041c440390b840c0e440241c0b48080d00029001e6408150812405004c801100444030005032408007482161004500c01090802400204c241d11a01401c0c040c5c4090160b6a219510060315014595080784200c85000c03c841d040d48400501000603c030040c2980031030f041c10040c1001d036805881500e0b005000d40420660540c0d800588200e0340310200a000c01e465543ca0320001640d00040e00c100d14800c25906a44152520100644 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 617308687 1250 617307437 617307461
    0x21c02030d110f01060f120611031005040b012d260609010605070201140a03150611070902130b1e04060305010f0503210307050702040f05010306200403080a1101 71
    0x74120841c04000d5600e400007186541d64213030f040c800240128071920210204589410b4048441003080c0c3c90310001800c0380003580303080003c0100800845141802404085410617202000b2a4100074011540e618220600096178040944035202d04ca60940700c500300c1e010f0900e42190b0103412201443da204082546400c4840c642609202640c50b01090300f0780100f019050043c5007214543c0081c02c4804002055840c4e840007255200f0500c0c0280c2101201e90804134003d03030007a807980405084c00400c0092025541b00700070b00442c0c100703507901c01c417030a100845030b000800382c0c5066010521030f0f1142640409842802a418500c0040c19001e0005055075031400f242a42c1011141e54880003664480c40c0300b54000303402c07a5041001c00c184030034500700f1060b40580d07a5442140540e030b01d2080501c000c0d000b600e06043c802448034145d00c9a4181d0340301d010180310810210841505040d001d00e0700c06071001041000f08006101080100a1014281086100304045a15a03821520b01070484 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 617309937 1250 617308687 617308697
    0x2030c03030109060e010602240a270b010f0b0909100b03010306020306030d08040b1308090604080309100f0f03021c020c0a02100206010807140301110a0903060e0613021c02030d 78
    0xa1081d1703c17400c2421800344c0168802803200000d810001403858000014101c2d50090401c04a440300199410481d49100b13401c04c5480090242d840300125060403580940c1c00e6203201c0c002042c00007007006290b08480707440002d14100b0045204102a014000e410041080d032036400000700c02a0307000142d80214020000141c691500318245420f22451003d440d04100c0c941081000040c0e105000325089072015000034681c02007803600c22030314071624101c1940070001060014040c500000105821241030f03401c00ca100c0081b29061700e4000e0220f60030f10109000d00a50588588039038080c1600703242da071071940c034480100581c40c0c040383c2c040d1140903905d4100010b10020740c00e1444004050b5103c070b1005010303940c0344c14034880c0c8418140c01803128901e50036a11100c165801d4200345070f10b942a03405030ba61800030300313405800c120551004079225418514209242e130004110644145a0b01210009080302903003003010007221038130203c041c5400408210f01580b002c03c85003105900580361 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 617311187 1250 617309937 617309939
    0x9060521070906030f020a05160303060302060c0703020406080319050a050412080706230105040f140109140703020c030901030216050d030204055b05072a0302010f02030c0303010906 80
    0x30080a540002001c0b02e4521b004200441c2803076488401c46000e00121490564021000d00e001c501410403940069840000428812020040426800c044901c00c840410926640b207102584902400243c03c141044880307000406a0096000707101e41550307860000d2034292100d401071540754446100380d0b404200401c0b007070304100240c0f0406012140c91a8844070722000316110035002c0005000b15800b440d201c020507039100e503079908050114444410036060070340e1a0b44401c00241220b101d002c04450540002c5000d56000e4407c880101026201540c134021100005501950000602c44400e400d502c0b540300c003042050101c4c02514084d641e0260341c880c502420032400001000c50041201c0000701d004a4000c041144c0c030118490b0f07054040000c4090342c4402500031140001040b8000049402864a560040003014054400c00814022100030403010071000da05600b440350030400c00070140b0143d805544417481003540b80c0304aa2902410b000c0c1c06065410a9128030b07551616400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 617312437 1250 617311187 617311199
    0xc0c0810050f0622111b0f01110f040302040b010e10110615030a060b0d050604030c0308070c030c030e0a211401050c07170f041d010510090605210709 66
    0x24090b0818021986a030320704d9110760945480c0071158011824080c0d03240035190310920300c041039401c0c940e0760b10f0f134585003403a00c0035800b61a01d04800c412000c1d5441c150f4800e000e12142025181d41402e10203020703041609503400d0000622120900e00d051100045000200e80d40e004048405001030f0b989030909035401070850362400320090409103101c044042d1110407a1000103501010070b810500120b201d04203100420740203c0704110181a901840c030410085c560083c0044078098400e45d5001002c0c0c0c0c13500390481e44608600c1c4014001111580e0103400300b0304c14030b00d6020450b03004000c1e483d20366942c51401c26076403034142400142026071a2410900c108550300c1301100c1061310080c84285842804061a8895408014080b01013020354818001d104020740340d003464078190341a540c6450f002c60292690144440141d022100c00000c5039904040308881c02c50b41d55034881d440c0e110704000701999107800642c1480c0905200f40501c1c1407569200e40c04900408141d103030000d40c141803038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 617313687 1250 617312437 617312461
    0xc190302070b0c0c30030a02090406170706050708180334090905071e05030115090b030106030206040603020703020f06041209081b1203090316050f0405090d0c0c081005 74
    0x2070800d6900025440d16181c4116041035401a03d08180521702d59030740d45c440c1c40f00c009000308071855030400c0c60041c0110b072203510542c1000c604c42c003403022210302c140d4641048900e4401c0b21720050809c41e09003c2e4440001c00700da00b108007500b004064035055108400184000c841090301603c404e00805805040400c40121000141ca4146014050103946880e040e903180410b1007840713290000c0030f00c006500c164501c0300d907004c3d000c01002842201c455142c0082d903001107020381003c00d860220382d914246414414801140d5025001c01c0c101403400501b50000c0d0020744090301580a110f4034295440c03410711101e0b01c100c4c032440310150881d40d2100000c251070400d411040c1260b12110382d0200c104110310003143c040404030f80c8000d000000c482d0450460140803400794151241181f90422400500c6258007036640550f5206101451a000c1005580d400e0b186829107403c0340c801811a60700c0307011102103190040c1580c01100359a1012a8544013034094000b0394995500144400c0c00208 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 617314937 1250 617313687 617313703
    0x6020d0f210b1c0c05010804020d0b09030a30050a0b0411040e090d0e0607141e0f030702010e09060409021002030a0e040b10180b13080c01080c190302070b0c0c 70
    0x1914055003405595a202d19a0000d0107170380d040c4000300d00003404568940345103c5401d036114200860504215080c1e03641c9410080401e0045902e5960305221441ca40b244046002c0e08090001c0d415000c1d4140d03d0000c04010301000b10755a2036521049143e10f8600400c0820b45020000755692494003001a06148000d44402003503008003000b5011152302c2211a46e010400301c6800e80c2d01e55143c0740c10f2000408090601c1c201d4003d840200860029180300f095403030360100705039500c40d00f40400301522071043c40c0e4002c0c08103024018030b8500381001c0b154580c0c021005040012105416000100c40d50680e01d04400103074000643c0c01d020651007410b401005170203407000d001030715154000070750080030425070b90100020028024200c041c0c20122b0401420810b403d50f607185903d1a80e004000c4150003103c48500c62595130b510154414801140325510342c6150a0400c101c065084034810042d0701c940080540901031200407860b009101030185401c400e100391b4031409000c0f035505000207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 617316187 1250 617314937 617314969
    0x10906050105072d02041b021519050c0c0111030a060b072102151314060106021903020102091003060509070305090d0309061107080a090b0406020d0f210b 68
    0x90000c24001030100103504e0b1144200a1401c41142c3e2440c030001c010103810b080179522500705051190041901c45190303070005010b60135101130f00c10304070b06505279040c1070f10f000e80d40c1c0800300000002c0f004079511a640010360654010b06d040310f01345c401400d451802000000c400d00000502200d10303614800d5a00602014080380e080520130f0300e680b501c0341039030703440c0c2e01c0c6011080211885243c0b00b07010401c03140842400003c20b03800d0120703650044000184003102c00d406400c10b1030800350000105c40e412640e031540102041240781c81c40f1404222114003c900703540d000d1040c2400d9907504001c00c0d4983c00d8640c0e00240883c40d180800116807805071801f000e061920060043d40c403000b00d0004038280090901051591203450070740010f0903030248400507110702185404c2008002402000c00f00720720b07654400c480d51196508402c1d84074501c12030300941d100c00001d420721801502440503d8049003050031421010722103ca01089180d02c0d5441c40d282e80d110b4150003442d0005202305a482 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 617317437 1250 617316187 617316197
    0x70906080c09010801200f070b0703290a052107081c0c0c050111120705061f0608040b180105040312060602010b091f0b0c0304060201050711031206041508060109060501 74
    0xd501c840700b43d0706c0d01e100f8507041c441400044001105010b503040b0b80c8200d0b44003100460354904158020300814011a08040381d46149a0081800745981c0c080a0180303401400d50410b50b10300410440400710600690701030310001c469040e0461018400388008000d040b0203482c44070304050b0710613070080540c01c02c5014006515500004207a8500b8a481940d00c00c0c00d00c9100a90301444541c582002c055840b110820002020010002c4c0461750500842011a409501c21a0041040c04415450040b1000180542d00150100d0440060310b5044403d80c0c41410444100908141c00d481c001c1302c05401203240c0306500d0403074500a106140007021103100030403c000500d00000c641200c040c00614012440340250b00c0d58284d0126141d00401c014117005039554080002a9102d4201d0300c620809546448000368005018a2020401d10802c0019500d001010403c5401c0d8460140a0940040c0d45540310545429280c003c1c2e0064402440140407941c546811344003510031a4120504200d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 617318687 1250 617317437 617317451
    0xc090406090b041a010e0c18191d10030215030415180b090d1b0611070b0103060b0d1a090c090c220f061101020909010b0403060f0b01021e070906080c09010801 70
    0x2038156800c1e070740082204c0302c8860b088100040020031510620003403c081c41827141001682c0d03a820742c4c40510441e211104a88143c3c2c45000d00244801e031480007a41101a0030300007121540e5960056501a114162440070400310440c01b004541045800c0d03e1241204010f0340c081c0070010041c82d0b40401d10400511900d03900450082c2500d000200c0f901c0d841070349000c60030801060f42c0105400c0e407a88000103456610f1410f01822040e428441a66803514008244400b801c2c00941c030704c440d0b0b03040402c501c80c0414020b15021101d00007480e2981038021a541c50f0300c15034580450300d0240b07030345c202c849881311012580c1000141c04400c0085040d0410542000442d008018030340440314135050444a900c140c0202501900c202c00301c03242c1c019590000482c800c0300360f001400a890140e04104085a400c03c07004c0111520030b04d41502680c401000003446841281c9182500302004066522899072081c0560680c0e43c0ca4200400310340000b51022101e0070a65102c5004000c3e00000740402e03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 617319937 1250 617318687 617318701
    0x50309010f05041e020301060308031005180903040b071401060602060709091b0c03120507020a03320d06030609060b031203010b030a0c0e030f011407050c0c090406090b041a010e 78
    0xc09020240b142139801c40c0200ca90039960700791302000c0290782141040d5964600142420f10022540c041d9a02c00d000984440058400719070042c0e1042c084032000b50701d040d05190505c00380b034110307460840384c2c40c0c10303003c2c003000049007802224024003947e0000c0c216810303e008041d2050340303127811000341c5514021001a04680c007015540d00b400301814401c0000105040468003030402c981c0c0021000c0c105020312840941c00210400c65602a0740d0f412801100f1b20b42d010750f60086000003e0400c210345602c05080800f00c0001c14416086410018955660780e43d9030f03082d00e03c3d00c441644c80300e42d074080840c002d081c00c1c00740c03c01c0000000d00091556052a0400290740806407203808101d0f9903155424425010381e41c0902628001811585400090032100380601001d021420403101c085022690060059090b0b5114201c080080c000219900e02030008883c0000d00580759242c40c0d85a240100f108000c50b503000f540030340c3c04880d003110006241541101c06030300c08a103082500d420440c107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 617321187 1250 617319937 617319953
    0x609020906100e0609030304030c03050a120306151805030d09090606110d050a030b0603091608071a071109040f0501060605070201091e0801110a0306140102210712050309010f0504 79
    0x399504413159a2107414440c00700749940074a800041561404131804824450006007080c1100c3c072030040301210600d02c40c1d044050301c500d40304a680440c42c0400c00010b090040000d048a0380003003820002495071400040d142100c40b84a520101d09240d03000e0100102c54010400034041a0609040719044480d0280d5940c01641d0603004200300490031142040c800e4104143c086002000c058803030402e40b065030b84400000502071043c00c1070010019100e1800300d1024111603941d0200304c8804004180050141d100b69402c5520105812203d103090f640d015400e4025400b90804681213000ca00d8120300b120781c00d400180c140301c0e051082000503a03021529500f654504100000f40984031840840b08004c5500030700507d5003490510074542c2d4055000e0440e51085540c140099a80d40484107032580c412010305005812800d41441040030300f075a0752207900590203c0500e4011245c80b42c3c0950352980c02c0100c0022000818055408824001c1180c2c0b1860940100400c3c1400d43d28100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 617322437 1250 617321187 617321207
    0x60703060f12050a170c030316110f030901110c040501030606030201090807030b011a070f060e15040210080714040e060f040e0604030f120e06010510021501051306050d060902090610 80
    0x209480a40c070449950b11040e070151118400503c01f140d0f124242070b074070b41100c6103000d0003000001d101401c406420040009034040d003040c0c4600a98541f1080000440d56103c00c400b43c910644610101c0b100e244d00d40d481003500070360042d800082d001d03095200050020003076134010041940441024004074800181440c11218000d0100c8441a04078070680c40e0b500a101d40501200182a9a1407d00926402c910b9124400105030317800c50540b0125504505001d65002e1f4000341244c1000a46a016560854200701142020742080c1e2041142813800e5009070000403c0c01b15210030b0013414207100e80d85200e000c20480703082c445150303000040c1d9600c5a004101800300202d0340e000c081d129000e05103014000b071407887e00f03010119504e108995505d4082c07207814000c202e011641d00f1402d2010441c0da81c401d0540007026800c1c1d04e00800c000008001c40d4200641558a0b000002c007503440200a4402d14841d440c0854004520300400416090080666004004445d404400941d122541c90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 617323687 1250 617322437 617322443
    0x120c17190c0506030718170618120301090f1a1c1119030b01081c0c0305120405060604060b18150702030d110105070e0d11040e060703060f12050a 64
    0x4030406040d0400e88001c0785594490b9401820010030b00554a034401d00140204940400003a1090760f1290540420600b102c80306100d608900045090007240085c44001c001d110022981c41032115884210541d00a070721506010707a580305d4250741400c181c00382d0883d460b10904688514107644001c26400c40c100c541241c200c0078509185820030002050340040048050224012001d14064140004266010551324402c2d172a00001c1d24800004400c0314041c040051044103811610082e80c407841d210310120b0034000140301100b00191200607162250740250010b101ca420101c080c402140d80c903801a4803c0f5200300121a00030003012120405106c05807100f0750440003c140000c6140514180254940607075500c44280c10740c04640e0034000d54a64000b0051500c500710b0907102c41d40070400c00f0307070058100780489002c90b03103070041f900384880302400204e59901e95000c800e0130620112448000310b40e030340b0307014004100002111710117442c250b18800241103480d103c0c0d544e5030a0041c0c0003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 617324937 1250 617323687 617323723
    0x4050115020f12090409060f020f0d0e16031704350c03030f0a0908160e07080f0a090203012406120504080f03090a083019051e01120c17 60
    0x12082190948c4145090400810219110044051804400d92082e10345524060808412a1280001103000c003c114000c0c0c0590403007a26594403c1e0b840031091070b0a4100d541d050100058000020071102c8410390043c012407625202c010304a5486020306e02c114843c1d40c000307410001c59440000444084000258680b601c40c4d800140c00ca800d114560001d4410340204005110304000c00d03080c1303c05440c0000c1e0420099a540c820466144e030701144d10aa6505508021500c0b001142e80003404407400503001141c030a0344520789101040300201c108058000b498010000680d0003180003400b00d04550041c0028180394481050354001c406001e41c0528002000c40d02c8014200300d80085103920010060304c552100f540c2d400030800c002040c0c006580790b00a40240901100d078490704c01c1c40003604040904004417080350040c500241a04a0010500c0c1a502c462080c604441c2c02003000303000503500c600291501b0100409144c1c03090303292001ca080c907890f640101180740205000000c81c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 617326187 1250 617324937 617324951
    0x114090a0e1213060305070f0c0206030c09210c010309050a1b08070608220f0b0c09180402030c0405010e0103080a020a060606050d0b0307080d0e03030904050115020f120904 76
    0x901d03410403811152502000500055942814007010401c80c115441a00d080040c7e5039100001d95405020107400c40000f44c42c41c0028005260041c05150000c80b9031020600300700032038020451103a1030000495000381c00e6101c4c031407580d02c1046444141c20081c0307002e000c0260035a9559aa0789122140144500382201501152400d02d15028008001c00e5044034042070303070740d0005403a40005072500b507800008508520442c0d4a42c80020743c0c0141c0c0801c0084100c0c015850f4440c421030050161311b29814100f100303e40b95a100c803040c2d42d01d00c40c1d0829800761400c1600c1090b24103018061528062810300b030042000740d0729181c450341140c6d004a000c55840b0403400d000c900309007584600820141c03a0050101c0c4450b48200070780707075024420b00c0402c1101094002c02d681e810880c40350074403551041c0d43e0203a10501c01c4042c0791340207c0107000c072030400941400080980fa0241c215101a000001c0c00190080e4100440c29030381e03100714003030400b051759000f00b0409071140c1030600d4011919808 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 617327437 1250 617326187 617326211
    0x140a030809041410080c01020c0604090f1d0718060e0f0a02212a0906070203100606210603030f030504030507050d081914040609020a0b0a03090b0114090a 68
    0x82070118503c00003019402c0d26103103203c5801c0701c44600a8840c144500380300c241d0b85500000b0345030341005008280300e040620701505840a8101c2ca8052456141c4800700c032040b01040c0300d80c2c401c1091281c0040c110243c24103e02081c05030404c1d1002d41c141c0c0c00c0203002c1000790302032402c0c03a810590807030750941c281d0703500741584bc00791107003200d100200100ca0103124084054151001d026039031442d92210fa84c071894650101814440000c603000480c10010801103141010007040064405010744d400c10022010300b9003111709560004020a0501e11a20204070040801081d61440d00504002c1c041c19914020f0038420341a5201d800e0695070008501410b024000395440e2903840f4040b1a0104811309004216040c2030316141190640e0b0a0b00d022000c0242c0289159401c040ca03a0f940a80c3d00ca89410001c0c0c0b04040f01641c024819050200304031110100400c617000c80c61702d010501091501e0044000d104c1640410152088071001d0f00071542d42111880d0092001c0d0b00105138544601 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 617328687 1250 617327437 617327441
    0xf02010807021609051503010c2a0f0b270a060c05070f1a090d0e130e07080106080d03020c06040201081b040306050a05010806070f0c1b0603021201140a03080904 71
    0xb40d00042c60440120001130b00350080e410480c4540420161401c006000358189809c0e54209126203021590406580c01e070075801c0030516204820f00e1491622418290300e0f0050240d26140040e04e04000341d0081090407500c3c9048084010042d001c0740386c0c28004040c0c1141c0702c090300880144881d4540b90080141032040081e600381c160080e040f800103203140c2c505144e1540503624140800c0704203a00040c00d4040c00729501003480420380710f098048008a082082c40c10b201e140c21540750340d072780302c1c7c0e042c0040d41000414080c04040000051032802c201e509445c0500d650482010140100001c2c10180008250f040c0c00650a0030151910748821509a141041100520f8202c0101060002c00e102c541e80100c0d0150700307400390400c020390b00c8500b0366403219002c4542e0000b1804503191341445500c40c006110219000d48d02484807032241c0c1c1130402c0c64141c41d901a0000903008102041c042083c20403890050000c0c25166882c4507a403000b04e0702c100d001c0e200c00b0b0301002c1c02040e9003d03107490795 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 617329937 1250 617328687 617328703
    0xf03030c0c030f04080115090e030a03020d020f04080d0905151602040603020603070302091302070c03022101060609230f13090b0f04051504110f0301150303051801020601030f0201080702 82
    0x4420f07081d07140d503143c0030200c0c028650140020401581030714001400070a500c5000b950110410245190141201081c0c0207544052042c00e4055401c01016414045c0d09000c0c00280a4a1020b81155a100d40000384100d10a0700407903c0340101421410b003200e00b100031550840703180c2840042c0740c2501c0c00020000d08450344060f40003c0000104620990315600401c4503007011160408400d030540f50300d100306d00461800614101940c0000e0000d89030000311421007007400d001d48013100c03440d8500e075829103440e40d11000c00b0404095003880003181e07802610701c10348840300c070101d452001c032000a48031004034228079000d900e0f40c0d240a140450382d40c120940b02c6400002078521410065071132800c0d840d040340c090f076107402841800d62403c44101d208500035130700844800340e2810300c40100030b800d104030f0030304607459035a611400104141d00150000114081c1c0c40f040e89030050844040d401d0702c0c40544003411274120380c1c01400001d50440e584d03152580c080c40c000145a0741d82409919013009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 617331187 1250 617329937 617329957
    0x3061c050a03030e1e060408070804090608070303030e0a0c0b032a070501060f030b150a030605040f0209090c01020a15020c07080127020616030225090e0f03030c0c03 73
    0x107540400710a16400da00704c026503148240072101c5200d0a0700f244415290f0307652800f40e81c1d800800204000c1071020300948031660244010928142c1d41d040d04030215182e55000900341c2d0406c0c0382c200140760305846003184584941c0040e09a409060760380175401d40c0300303000d006550480400810301c440c60702500345860310324000c154894807640007921480c6412030042200c0542c00c064020030703040b0010891004599014441e001c00c1d80703136040300c0e6290071240020b8940203485000c0000c0811454061140241e0007403144000c01c00c030754010b001e2081e800402c01745142d03000b400c01c0080c0d664002064041745810070040c0500303d6098041c1d0010b072160344501c0c034491042c544e000c43d0401042d8080b0070131041c00890b20314448401c600c40185811000ca0103503001c0c2041c40100c0a09610402009901c0c0c031030300c10368410303468019242d0710780500e0008540880d07100020900100d4201c0c419800c0301481e8000801d0071021a04040707a032440b00802d290300380c000118001a00c820200180c4c1c9100c40d13 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 617332437 1250 617331187 617331193
    0x51302090414101a0a080712020105130605090f04020f0714010204091b0315050108040206090310050718090902030316030c0b04030c05061b0405010c030e040e01140a0e0303061c05 79
    0x8900007007203014155640e0483c501d00103400382d0741014078100d4012030403140700d0401f0388082031500f0304501c00c0145800b000d80c140901048a8601405280442000380a45459803519903900e00d0500c100c1d10b83c1010300b01d01681c410030101102190800903105801c0d4029180841a004061210b019018941c40892828213020309086107141030000c400b401c010950301000035100d1382c045c0c61400101403250b94040703003c80e804100541070180003042903120240c200c84c81484800011411680100d510100007644c002520384c21521103020400241800501405850364035000240c4902c100344c0b04011200c00c160181082500440c0031440540d0001094a540c2c030300b60270082c040312002401141c03103000318400940500c003040c6071100b84481c142041801d207030800006603489400458154188a084c0c2c201419aa540e8020050b076901c8400c00400e0326812006404c40c5a0405070280841606054083e40c194800100356640079500b214900d52041455a0403100707056001c0000c0c001780 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 617333687 1250 617332437 617332453
    0x15301b0306032d0b04051f0b01090608011508061c0b100509090a030302030703141905060901030807060207020f0603090714030a0308160201180b01050103060504051302090414 77
    0x198041d84041d08032805031022980401620028030241092044103a100e4085a201d24011894401c01d10340c0c080d10813003c540f250001284d50b800f440e000c0c41e54120b4400c0d184e05401c1c802d03580c041c50340c90081c030003401d0110007541403607038181d0100c1a11004104000ca07040005046544d0a0480e4121807105400350720411003900701520003030412a801244154048000a0f403410103009045c46201c500b00980045038090360200c001c0d51002c1c055004241c0c030740030b038141071003421050030780101d40c9100d8000801a9810016082d21002032800313100d020b5940040011405000c00c58840c15804040140c0d200510320004060031440041140c1205002c41042600e5400140320026030f50145004004840c00e0000c260740c80111680040002d6001f002280381018056403078800020f0238000422805d210744010706400e9203054050360244034440042005580500c200b1010f8841501c09000500d0085030031008104071400081c061540c1000041c28051940100c20b821070300c1b030080c0c440b09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 617334937 1250 617333687 617333741
    0x15051e090316082a01021510171e030f03041205040902070605040507052209050a120c11060a0f230309030703030f1406010f090806010608011530 64
    0x1d0280b44801484044440c2886611540300180301c83c4d0240c01640100120b201d00300114442e0ba5016001c040c00c00000fa1000c0f411840c500645840542d41100614403102c1c076509100008105041744200d80e0020454544a40308640480384d0140e08110801e030303040020304045895200da5031042c01c100d84045400010407090350000e0b40180d000c0e5084900280c0c443c0f0420892440b003c090780d15482c103050903811000b2054004c4803566005200b80d407003011660701c50900c041d03031400054001030000803e00d020000703408849aa000015140d16062600000c07000c1d256041b0510702d8070600130b0f201e0b48000d80c038280d50510580280c038104032a45a06110842d69900c4d005410700310086030612603a458070451900c1810100c0341902c0290125071101001540c8c1461280311503030030402120307008a100e640401110f4001c01e0140e41c1e5242da5813508a1484022041ca1050010020084c9a48401d00b20b1a10102815411095060360205014001500404111030900044007881e0300385044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 617336187 1250 617334937 617334943
    0x140706090303030e060609191107110a0f080703020111190c051201021c18060c090905010b09011e2c010807080f01180e0a0c15051e09031608 62
    0x849200383c406204082e25220615141c400407500c540d00000704400003a00b14a0f8400c215042d14860880003a107803115185000003584084400e403625044034500c1e00c030034140010034500601d20726924201590400e18920b407160400c1c44068100800c1e4082141f01d84001d00040014000491807100d41078503a2030140b42260407482170b1480390070a540a003c50311411b000700c511101100c2c03001c1901040300040d460090500724410084c0600c100954800180300b40b082c4191002c1c0e58481c070740c0d60b030702e0450303120705441c03050700280c50030f0806002c40900c50f42c001041010402c0d030382000000300615404211030080140301304c4400c00005601c10310700c01d1018103011207170306000e0340c5910103542c9a0f8000c1d10100c80a0300c00303c901c0380e1700070010801c1070084200e103000003002c030b800818040c0c0300010703140c41c2006da60000e031b43e6030404900803c403800f1000907503c00c940c0f4070f0030282e040c6005901c04440500000c210380d034034110009402e0340c00340d40600020700e01400c01c0311004000da80710841c00366 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 617337437 1250 617336187 617336189
    0x411041e03121107030f08040302060a080f01120f0b06030111040f03050115080d05130b190801170c0405061810140102010b100f1205090c03011107020a0e0414070609 73
    0x5504203500392441c0e034852142c2510610700398070f00010502e181c51940d51070981c00080b03209440000c010312011005954190061440301d40315076030600313242001210b9074541e5006911040b82c003e4100034030f9001440d403200792a01c29030408418422560b07001c0100b40034003004600c4840b48900050b01040e44c2c0041d0702c0c1c000c1524042d03402002110a20203a00e680c00400b4010004c2d6035100e100014003082c0b15070003d011070491690b2400b51a95900074101040d00088402d010044141150f0110b0651021065004010241c031581c000c2020072aa19212038044030101d00035038450000591589400c21901e03000b0300d070615034510501c2c08611b0155240d03410701807101c2e520404030004459600c14025241e20309001042d4484100d150394050301d110354249011810311071210f03025000304400c5e1040c2e900c04c0003440050503801c0322803420503003103500142d24807043c114180080009a202d140300c0c0c10544a00a0185080f6262400d20305640c509044201880b071084440100340315500c1007500d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 617338687 1250 617337437 617337443
    0x80402040b0a2706031106221412060708010b1605030a030c02060f10152c0f010302070b0609071103160b0901091106090604090f1a030a08090411041e03 67
    0x503d1000c40140c034070903100d151101a10342d0583c5248600d0f54030f020030003480312002c10b80301e004c6000d40c544450110200e40d580301414040f4000306440d080e007841c0c40044c911985a4000c0c10b21403900d544060804001030040d00544400441e80c81e404401d245524140071345c00004a980341d480048004026140030811100180070303400200d1030f41c417580c3c0c000d14001c1e2a803220f030039412030030300c0041810402c1c0b05410a0400110303424106580406008448a066690003040b4101c403000c4280100249129001410144100089404136114500c0550009011600c43e50b26488814003102c0c90140032241d60300383e0100085440d15240700c1c46001c041c09101d4034007551941d03150794540c4e0890b43c150790060003040e000e648101c1180b40032001412217100041961341490f44071a407480444800319900f0307a01594880c00720080440050100d111004102c00818200d2450b40e0303075401d9030280403009409141c594444c503410118100c1a2030150200b08400141c610428807040d08540043c4400c1e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 617339937 1250 617338687 617338739
    0xd02041e060512060f010324030b01080a0305070f0302070b0c0303060405061002101d0d03050604050603011b1b0818130b0a030209091501300c06080402040b0a 70
    0x18401c0d001d50250303150440c0c00b81d0550710030341c0da000c1804054901444501d040582e0742c031020a1680d94004202c002c50040d0044541440c10351078180203c8006030418040b0358011500040000d6202044425a42e070060030300b0008403061400381d2406e490b03604031900524012501c1d442c1d10708000b000e18442c2ca0206d9081c04551101000e000860740f00b00c000e403005030041007520f442140b658110700065103141414450341d059580007541003241a4148a0020341c41c3c4080c40031074641400380c01e41000044000b00700c811364030162a1040c095025168040c030101c408204030300141d510054800641140c0d6442e80d0b088620070301a40c040d00b69070002d1041071502e0f541e84180030907110304048414054a40002141076800f04a0007410081110000e81700302e03262209007180f1460480d008080b00d2100003160701d0012070642e201103036000b44131850301c908100e032000304507030402d60b004441e41420081125121800410082d00c6840c500c0d540242010b400098041c0c24098031007140003448841c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 617341187 1250 617339937 617339939
    0x6181210060905071e0e190e09060601020706180506070326060306060103110c01090615080312070c050a120f090e06060d050606160f2a03170d02041e 66
    0x1032008403203040e01c0b95000200740048168401480d6009401c24071a141000919081146e000401c1c0d69240081c0b0301800301c1c01e420402c240caa507510f0711900200340801601d068505040000d40e02c0b0458882c2d0701c100308103103a0a00900c01508001700c003138040a41290341d85d82160402404910400c0c162000640c4448094108082a211410b0240b0b0b80100541003070b48542e40114054070102c08890112030b0304002d600800002441105481881002d0206403e011507161000012042d404501550420800702428114444185074000c4032414803100002d014181140740c40e0f241c00004111801c1007001012998000f84650700c03820183d034581c20902d44860042d016100f00390b817440e4010a050141650280c80340e0005640204054a0f070313820028035002204002c5a405026981d007401a0b400200f40401f840c00444644520358441d6812015990009005c406a2001030500119034019182c4030662004480040f5061081551215101e02d1800300c1180104114809420a804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 617342437 1250 617341187 617341199
    0x6050f0a050709170c1306081e03070209070c0219090507050c1906110301090506010807050c0c0d140304060305061003110f160206071103010b01021b0618121006 71
    0x1c0c5500c1001c0340e6403072400081c5031100030810340343c1d0104a01111700595040d802c568448603180032124141c20030108031645803100d458200b40300359407410702d07114440e01303800f40354040041203d510981c103450824480d62400d00c00c0b10017640030a0300942c010301908140c01c24060341d0805070252404541d082025481d400d405490794410090002e510f41c00c0051512807000e10001000d4500e8080c9901050041e4980d6218280d54026007090098507600e5080c0142543e0060000e43d0010142c2841c031b191404111415980f01213010315540305074500b01d02c007020405440c403c0b01c1c10151402c01c403919281c40348805006001e00b264118040d01201819880b82d5104e802103039420007011101918007291070556444680c4052705d01c2d44000c246c40e04000060720b5040040200c00c0c011b440d002120340e00b42c4105801d43c1c800101c00d42c1103500003000380d0586100c141d9103450044080700d01c241d507201d00d006112064584120181c0d0b112049082565540b100440e080c1c103000701410082101e40e445070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617343687 1250 617342437 617342441
    0x90a0219090f26070e010e1e040f060f0c0c051c091e12300207090b01020f070e0f0a020406020709270837031d0a06050f0a 54
    0x8800c0c04a1003820b18410404581d0200d26080b40880b100c1c000d00e010444403a000e40751031025441101c940910900400c4040d41030311120f900141c5c5003000c000000200f014500c85044054030290408046040e00c0c0c0c200851a8003801082c904960700340110414414054449508200c06035685e0080003d1000400340c10320389403141005503161407080c00c1c10308602100c540c42015048124007880b450100700d40d41440d110305240c91084640351440c20920b61040c0740780042d04030303020003a030308040064102c13500032900c201901c0049100244410320000102e00d418081ca0b01c100481c0110440418642d040c800313080e11550000e4108243c6440b45101c07102240b10364410040143c104540502103140c0e50b4104c0d85a52070700e4030442c100d40e04420002003083c2e0a006007211910360009855040241d20315008045034034002c1180d11818601178001c85150040c0600c008240d070b507000d84840841d2540c40c5009000c1c2c194104e80c50b048492901500a02e01a500800448011000500022a14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 617344937 1250 617343687 617343689
    0x1513050603151305100203010906080c011d0f06040801020c0f0d02060f0403090806090601050a0b07051e070b0705030c0c0919050703020c030a0e1512130501020405090a021909 77
    0x2800030045110700a060949070b4201070304042c01c01542503d40e50204204000c040c1503903400310001a5a545440c4400c0111340c441da000034903e0304582625140303603070042170420217a241d12950074110080c200000c2c01500d921160300c0d84c0031b140820003007140281503000c0c0404641c604105d50401c12294201661960610640c2e80140c0c40100001d2144c41e640c2e4020750441d00c03d003880c080541e103419801e4201241201c02000950000004201b6444c062001d13100070907140c2c000d20314203056a1221078603040201000c50320030042c440d04807046801007205100401c0f401c0075054071904a45001ca403268032120350044a17120b441c68951151400c200e01c2e0740074542e240540d0315900040c1d10340c14080c0000400020500d40e080c80961ba085a00f4001011021925607411a28140342020003040451102001c0d150440078401d4490131221801429000301400c038886807100c020b441c0071406442203810190300401c0c80c50030700c241240c5603000342c03030074009022404600f0310070903c045460010b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 617346187 1250 617344937 617344939
    0x4051c1e0c06030e01020d06030317010611030d090c0b1c15052d030d020d03060e0720070b0406030b040b010c05032d040b131410050a021515130506 65
    0x280e00700400c8258026070000c2c1c82d0814141c00036007400404030365603040b159150f00a0b00410718410034501040c140c0100c0b01d0252545081c00c50000c075416121666034000c0b80440c0b0340c0b07590f54600d03003001d00956242e40001004000d404554819110020840d1440c0c818220a0502c0c10001c4072090380142d009050b09a49014001c03100e00c02440c03004004141700700d450b02d002125a1424003143c0e4805114070302004a00380c000b05104540120028111415075000c181c000c2c00740d40c02d0146007640280074860143c110480300c040301558102c001c2c1003481c2640703d00c89000300000c00007166034164000001002e000c80b07003008121141c400545270155039150003004c0303070410420020700310007658a241c00c10350040445240700b00142680c8041c4d40c0b080e00052480040440c5501d0000d8034000b40501801103035400c10003006445001c9980f503c5203031810401e00c400131919002281c820000e2003e8400c040710030321141c4c20b15041400394051403803813890107542c40c0700240e417034917032240107117801740c1c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 617347437 1250 617346187 617346203
    0x10b10030207060b090f191a010e0a090e0109031b030207051201110304110306060a06140d020d0f1b0314130809100f170606030703050c04051c1e 64
    0x2040090032030080d4803004084600956403075042800c0e4465807950380c8241c3c0b114400440906140003002054203100d0000103c081c105115184506c05000c00c03080c14aa00f820000100f40e6413070f0010b044898150801c4240a180260044a8101c150400a006400f0342c8a00c003c10400043c1c120201640d1200174026030310400b010030060410f00301101040c6411800090255940c0f40349500342c0d4405d0794266524407000d4802c12940c5402d02c40c090f00036000301c8032010402e00e0700b00060000b00351103d6004d401c090208440218880e650101c58000e98080c1c02002840e585802e0f902c01000b40b54040c21038400120f014599890280c07080e813030181c2100318507030b40541d80c8075001d980c2c0700d01200c0304443c4c003442804441ca8945808824091b4a035980e03c86400324031450000500310300c00c030705250401030704a02c00d000060711800c0c11640c0060003482c020542d80d4032010000f81c10312541c0c1c00241c001901c00199100e0041c056150340c00548912021401c0319913295079034200580020010f031501c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 617348687 1250 617347437 617347459
    0xf0501090b091509060f0706110c0a060e0c310501052407050601060804210507140a14030d0f0203090d050706060306050c090405070201050f01060c030c0203100e0f010b 74
    0x8030700f29280115448440c00250301c0d064414000c607086800404610b0755008010404038100815800b0701352041c0000b161050503c035145042555540030964013800c8640c5d0364820040400c800c0c0140e0740d164030003038499100055a00089504481c0c2c1c0280c42c10341c242200c00040d41c03041540562412604000e20310319034000d5007581500b803400400441844401e04110b02c60000f08180030703440c02080a511103900c01d140904003100d52003901c0e0081d12a42000f500102c0700780e07402405945103c1e420214401204481c4200c40c0d25218500d0320107008507101c0090584410000401011458101c0c84240441c404094003082a03000603211407610390050f01e59004420720400103400e0b014001c0b2400300b00560743c2d444010495100759544a1071040010300102e02e410b0034000c1580051640c030080042e031521140000705114103001e03203400c004aa92082e402c4c944a10380ea410f115400400b070310451710721502c00600620150003400440c1c0103080e25029661010300c40c0f1251810b0207840440e40d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 617349937 1250 617348687 617348689
    0x10305070c1212150602010c0909150314011d0115050a031a0c120103050115290a121103060301110a020703110a03050d0807030f06030507030206030406020705060f010f0501090b09 79
    0x90303d00c00003202e5030181e0340c2418020090f25401010018091030300001003140d917140006080b000ca6400074901075041020750f034079010784429190116904040da001c84c021201000074050480b054038110a01c405907240c2560004c1940a18003600712503a02d49030880c2c0c5d40d000d0141100c01444041c268154107036900202d65601c050f6150b0001c000a040343c40c04403211070b980c01c210001e030015a880d0790340e210181240444224804060446031502400e44002000c0e2030703200744289c40c0b01090001020500382103460041c00034120804548106100c03030403083d40005002d41049507414130a40c24040100020b03000300c000c543c80c1d4038840d030180003250700315151a04802100102c1c16000502e40d030000020030301c00e024407195107070165192070240c1000c490050594002040b40ca94a5180410403c0000e0000490750b044960585200b502c0b035543e801c040c8028003840d2006052802040304000c521180980c0301411381d020398006008103038840300115100d406a0040d180005030810007040c1e2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 617351187 1250 617349937 617349947
    0xb0108090d021011090d0f050d030509030706090c080a0b060a050f030d180e04060507090f0f060c0203241e070804061a060c010204050406091401030f08070b15010305070c12 76
    0x2200b4610444034030b0005d50b42c000c281070300b402e8803084d2003101c0d04003a0a01006401e02c071702d40a10350030340780900c4030382081c4081320b850784140d9000400c0076a41c3d81035070b000c0010403401c41c00140902da0030303120103480364104034000807000c0b074030075203e41c2049501040784e01c0c0145078585030b118040c005211a581d552811348022200307801c45444103c0591000500d04a40349400c0d225500c241c202051509001e500600310441035006103010800b030050510001c2b00c2810040125000d031f241116000e8441c0c00404d0805d01c0e440c2da221400c9800500e01502000c1070703841d65000da150320900c5407000ca44846200c91540f03040d5441400980c0500200d170103d401c1e0b03008481d80000300c80c40010140203400c00a0160750180604c1c0903a650082401c1000303151500c02d034070040885503001e001c00c04009248000c107100502000380148000d0942e030040c000700ca000c0d100d0340c82c1d04c054814098144042100340c0440c40307103010b03800282400c0024002c0d80c440c00e1004c004550200d1402011102007806a078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 617352437 1250 617351187 617351201
    0xc0503061c1709030d030c120c0302040806010b0702091302090408030601052b270602162f12060a0b1c0b060f1207050d1401020d0b0108090d0210 64
    0x10050340c080c00028085450803000003032402c00d00342c010359940e0118003410305203105c500030142407524042041010f10f070010b20000300c2c0791990800240842c8a01010340090290350008140c5216070400817440d841c06100416146000311002c0c00075660340408101e035940d048000a41164040001c640001d410310061070304468141040b80c2082001d094442c440e461f060030702042c8a10030315070305551b41400c3c0302d807501c000e000300f400466481e4050300c980403102d00214000d0006030f0025001c250744010007064000903902985041769000d5409000c001c195504d408200700300c881014007981c81c90040c01d08500c082005003c1d10303044e1344200170715008081404000743c001c00080e00752011402218201e01400d03110708d030b00c0b0710303107007000ca00b400281e001000c240c0b8020504280701c0c2e490031000041450813a0411510f01004040c00c1c5041c003003000020102c8509980042900400700710141c000d107141d400d00b81d0b0341e070680d556940e607035994980300c0940300c3d40540c011003240c3e0007121464006071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 617353687 1250 617352437 617352469
    0x705040911030615192616031401110a270b0d020301150305061e1f08090111040515091c031e1713020102010e01050a0b03100c050306 59
    0x541c90280808641081c504668513101c038100b8076424509460204040c00b56250340080800744c0a04103200b406c0101289000196080000001c0d048001c0c8100804c401c05454208840031056030307450402002070900c40c0d005000d50170088403450904090090768241403480c3d50355501c07401602c5441d403001d03c9405000ea0410080c0d9004900144c05230018000c20309207000045e5250716268103512190004054074081504103400e0100e1a80c03441040751415100002d8a06030b03003020000542d2007180c1c620300c3c82c40c05240303140c408140d540040c001c1d1301c40c2d51300300024031407080c911041c28003610450207001d034401c0c13100703218685107034407a4050004000c001c0c5c4a481c8200a01d80c00300ca11482d4010b044001800850b0140d40e407075005103955808032483d04100300024244a2003080800e0000d003030580c0d5078600b00c444419a0702c01d410580303480040c03d001700003500b8003004200181002c070b000e080c006d11841448181d046080d202c0c42482209a07a289411621510104a80341c030041c0d0000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 617354937 1250 617353687 617353703
    0xf040809060a12110a031b08011a090d030c020f030a0314090102120f091011031b0115060216060203030f06121f0204060305010509041211070f030803040309080f07050409 75
    0x143c0400546481400031805034410465218414040f00400740e481d004100080503010a054101540c0c004d01c0c201e0544804004041540f495112031200c1401256202540500040001400d01d44c000244a81440c02582c2c1c04513400b070a0001d2681d40c1c00030000c000c0000e911009131080341c01590015241980051055481c2d15100c18802c60701034201c580c44030002500083d000e0340c9450264003c1c07a5100c21070414214500c0c1d011403180d03c82c000c0c2d40500c00080c81c0400002c0201000b98408010920b9810404c0c1c201911031200170365035404134030201940c108c100c030040340e8503000005980c45880811403c10007035881409128080181d000018050b02c1803401d09142d81c40c04544420b403e0400e0000180ca46240400c01001d039041a80400d0103441e004c02030002017445810054001486400c0950b55681440384103413412a4560240c0503c0941c0d0201200300420b4030b0046016900075980c101c1e4a5031900703125030b2104501404001c00e40d01c001010420390409820164100b4014246 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 617356187 1250 617354937 617354957
    0x2010c0b06030f150f070c0804030f0611070b06120325170415030b06040b0d0917040920040f060c06110309032106012a0501140a050f040809060a 64
    0x384510b040500000c134076540700644201301400c400422400e6000c10a07240c001715451751038499a030307507129a02001d07005004982c034a5090080715045280218905204580d0712401414500407100080c0c1343d05d88540a1985801c24040000099944d44200b085400c0384899074000b1811041001040440303000000441200c44141038002900052040c907516640035082c041d8018100c1d02443c40143c450b41c4148810b1101c1e412503c2035031003107501e500c0c00142140c0d06040c8640c81900480c4440d0b1400c10001e4040341092260300006000b4070340c2d402c42980303195200c02138621070149004404001584d4001080040c4c131070000c0c0002c4501680c07000030000310190036a90700da40201c0b41190142d0000a111034a21020700750265a8a541c4030301c002c40b03081502c0000c3c00704003007180e92065207088505131180b000003260540849503000000b0428015910401d4184c200c0403202d00c08081e19010015918410120308240308603801005186821420020000c142c0c0000411104109805003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 617357437 1250 617356187 617356213
    0xf0301090212060f07090303201e0709050c07020f130f090b01031103010903120b040f050f010e100b25050a031817120a1205040321020702010c0b0603 66
    0x94030001c403080d0000c0e01807131500100009403e40060101020424a10020404240d00c4104048a0344680c5151983d10032040c900b035240580721805512080507100c0c101c1622800000c5610032695104010301c207a5440415000d158015510003941103d0919240140c3d4545800380c00700d40706420030001003440c10070003581c0c1250003031041210600c1c2c05000600c140088410300780b16400044000748000c05181e5030003030000841005c0d440d1800c2d1502c9494981d507540790400070b940c540082d4100150720701240d0240210000384a216000030b100c40c040703100e9050700800b82e001d8900442401e40b44c000d010150030b0540d42e064550840c0ca00301c00e41ca4000160051100001c3e5038060307034a0285565104032a452402802d0348140080840102d840c10180e10110b41c2c010b1004c485141d050320ba2071b03a0f0106850b4400d060058082081c03810302000704144d017001140300ca444030203466084061540b1110350403440744a40c0640411122886031001407005203089a1018026090740d00d02080a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 617358687 1250 617357437 617357449
    0x307090e030a0927150302030a21141c021605010c020c03030702030a0209090f07090204061701080c040509160b181801030605040501021201062d0e0f03010902 70
    0x208540301941c000080c000b00d81540071030440c0c050700500158440c4420080d41001c8082115281584070a454003081c20707040c5c1c1803e422000440e00501550901c104c06d242121030031410150480c1415100d40000c2c007602d200d41180b001d0051049107140c41e1050760f1245500d0b40c8c104000c1c0c80320380c9808108800308030004401150400784290001b00311000300c1e04020341464103029001d400390784280580340140c1d900103907464030b903074043c2c480d204151194504503040c000980100409407084e2138001508206d80c3d1f000f0012603020703036559074460130348001080007484284103025a941c003030715140083d0310b4258806500003031001c00f142d000010b4503031034818400f0154800544c01d000840d1a85012004503442e0080c031038112040804007500c0e252100c803415060002900c800d955100003020080254102d8801c28111580138105680d01e41c0000d040440c86550f000c144020440c10403441c441e514400618080c0c0340c0c0750502e080001c00140f10321540441e603880c1d455902d1781c04040150304c9107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617359937 1250 617358687 617358701
    0x21090204090b070f03020910110f01021614150a23070906170c0316050c12040312021203060f0109030803010e0609070908061306200315030102040305100902030709 72
    0x4541c2c1210358644200003800350a2030f401004245801003022a400340d03a2645405009140ca00303065104284d41c3c2500c1c2c1c64402c503088550704039807000581e00307203950700b500c1c2c2c402101c0d205030307141000300c03401c6480251a04100c814140140107070070007040e001200d6404c05003841c0088034082c40201c400907c40410140c059a1580100c0d10019003440203a510903214460b4040c040350613100d07401c0880d02801c0a120060a0a084009040c8c004209500c68011030310440003100844048403507404070303480d999026220845000601008000d2068004580c2000c4443d031341c00c055043da030310f040c28494405031920075541000b0748500044001f07404540a54040c00a000d0264540d1400200303200245402420100a01103028400c00044d82e00080065100a4000045d808403072107190410142220711703000311183b407c00306020141e5250a028500c03498500000d54410902c1d14203040c02c0384124040030305140c01c140d0038103110240f15044403a5240c80501102d420607a0303448028111606 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617361187 1250 617359937 617359943
    0x804080c0d08011809020a05090709090204030c0603050a0509060c03180610091401080a0213060918110114031f080a0c03151a040e0106090231062109020409 69
    0x45005010a03450310b0148910714148013403c11492180b600001c203090361903c40e01e4480c51807400080d49561180d42c40600400d503800b801d54440751203181c981c0d01c1707049600900300003a103400c0000b01d05c007a4500503240200801c83c05442c8a840b02000c4140a90009040920203185002c4001c1703541c07800c100451194003024056030310981029240d400b0303240310500311580c070302128005000140313001c145401c596504503407a401000d031141c0041e02034481c0da80403034240d6140048000195040b00d0442c840c05102d00381e8850203402c4c0c0e20066802c5818251051050801480010510b100040410a120458a05084a00741c2e0343d04141e28141c0074410481d45640b144000b00104a101c200d030803503260100b0f00034040301450120002060030b001e01094030407a25002d01c1151320310203600500180c5a10f08040d55241840c541c6110f802c03444807650f065050413000318101c550b4012034424151002030b610781d424a900081d141003492080944101e0881d035070712045006030740d288102d40d9550b00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617362437 1250 617361187 617361197
    0x1020c0f01060f0e090601091509020c1005010503030c0c0f190305030406031413060f1e0605120604050a080307020f07181a010e060a0302090d2612070804080c0d 71
    0x20801060805002d4590700c851050241321050182c503900203d0540c2c15070300c04241c0003902405448c0d50400c21503a42d405800f03840c0c80003459101c40000854000c2940d01da0300e03000e10150340d0b10b0081c0f66803889809603d5019030030045c20f0449501c0c0000d803d100c881c900900200386850f0242d150915400c883d4003c0b11950b000203810020f858246c0500003050704400500d81c00361518440b23150184000c0b1700c00a280942d40d00c02d40c2007900d882e130b01076650b4074023200d00c08070101d241c2d40e0000002c040a0050714842c00300414584090400022543c3c41168440d01924845885542d810700340e4001406010950080f02e1040807038401c01c010102c0201400000249032000c07180800085075141d0142c1041a20b0190b90814a80d800444003001100c040d1000c5588000c0044114020700030b15034001e0f4401d05101071001480100c0d00f0030302c02c0c400f40314029920803c911981d0700c1144540e4400025014008000038000c82c040d000055015011f0300300036151001414003c0d09100130034070b0090200d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617363687 1250 617362437 617362439
    0x201050c16051507050a03050703170108030301050112022a0f0d050a03050a050f061005090301050109020903150f0105090a020702060c0703030305060d03140306120a121716030e01020c0f0106 84
    0x1283c03c00101114400c8040218544442621210389035100018050b00b0711000186110403d88140c2c80c0c418064920045050156100d4413401e80b0f0303500a21170380780041c40b11440c1d0000801940308442c0c4e40c0d880b05d010741000384040250f0742015282c40c000c10031240500701c3c145800c10000c0c890404102004e584a0355201d07083c0c000030b0215a00038084040b01461304040000060012001070b4001c0c904032030b0051a02000841200c2c28403070a08180d4041d402c0100000d20419140c01501c1c800200f201138807594038461141c3c500c150b4040703131041c150000d28001000b01c1d003801c01f1030035001480b08101515121050300451015400856244c28552040b0810800e00d5070500c034a54201c003040350f0780008001d580d20000d25980c081e440000c020722002011a0182d070701c21016180801c0c11320b0503a8070340405801e02242a640d10300b0300c200803a00c5024540c42081000040600c40c2e6000400b182c0c0703240c5020b00480081030f08102c0015950341c00c024001042c2e00420004100e1018180040740c0c032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617364937 1250 617363687 617363689
    0xe0607060f05250c08130608010f0e06220b0d110307080303010b070b090c091003060b0d0804060e0a03060e0a020111010c051918060305011e05010e010302070201050c1605 75
    0x141d5005021030624891980300b402c260155507000c0c0c01080c010704d0094050b0005080c54003c0388241504101c1001c00384400242c0c1c2a0440d08aa040f070f0850303852107207d5641e900c54a01210402c44450b6400000003600d507041c1c021108003603003414240600020100c170308801003418a8080741080e2903e00b131640e682903881c07404100c11000707850362001550455140022000a40c01298402410100200009004130702c00b004100209400100810420304055443d07040e445418003040e60070b141032101c848018100f043c000d004455010114614040c079001d0111018801e1403502e40d4400030101d40000480e0782d81c002c03409900e01582c042c0508912a00c005003910851681a40440e4100b075401e50703080e50003000f6a50701c8d800c500040fa5550ba03424000720b400751745030004669200c0300b600c000300d18540d055120606941c407100340303861048910040201442c01310b20030140062a6000b05c01000d5202e44c0152a130039106051490522070010700b201c0c1400386501c0540000f103000760003003040d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617366187 1250 617364937 617364941
    0x180c0c012c0705030d030b03030f03070c030f210e030c0d0203040609080a11060307090b180f0913080a200d030b011e200d030b120d05190e0607060f 65
    0xc414440e801054494030f400042a1212101c841c08400d06a036010581c0e843e49042c021a00c40d0304908440316500c0c80c1024014100701c5210200341c2c00103100c40404841503009507128541603007000c8074040110b104c0150740001e0110b91740c1809035070006101141d040c002c10016005a034401c3d070082c6480d203040c1000240941c5155200c05550380c4045d4018001c21440c20f4903081f00e01c030079580d440ea40d42c0c6406040e40c140c081c43d440002c641000060300d00c6400380b075808da42880c24007100c82040108850003000b0030b96100b96480d40d002c0b641010071900007010000202104c0c1100d0600302e251030b106c1104e410480b000811500440d410001ca110741580d807502c41c20444901c2402d02d0085000c3c07030703159040c228441344800010700041303651484403040140041116245000308441d40c0810040c8000e0141c030814804501a000c4101c1114007100c0214080400035200c2c1c2c0c5030f504001e2407182280748802180e0040c0d0a000899030b100315181c444000501c0f090380550030100d03a00c140b18104800b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617367437 1250 617366187 617366261
    0x15130e0d120c120b030c06030709140d0b1333060803030108071202180c090301051503101d01111801170601031d16060815180c0c01 58
    0x1d001c1d454841c420200b9a0442c0810030703180741c0750000161100c0c140d40841d19080300f2800c01e0f98090808010400000c0c0e00074404000d85100400305003021030b0750001d200c2550485a0002e00c41515100010404810001d1852007103001b10733101c40003940d0015100e00c2d48000301525120507108881c002030038035010b014860044c03e241d8001d41c0b440d0f14001030079403201384600071540c42010340c2d1085000d42d594900c690010b032400d214031083e9410840489420b40d840440207602075402c1c40700050780700803008600c2008071005000780c1484000b071040b000080000f80c0d20301c01c2c00700c1c0940c28085403040034070071102944814198240d884411405104107104950415030412900b03180409841c07510b1031015802c03007000c0c00c0202d002010249140540810041200c3d0740f07204c0e81010741c0b102070003d2148c4044032510313100c1c0805038076070f96450015001c1a00c010f80e0007801c2d8040d2020300c2981400b01d540d1003c0000c96050070003410300c0ca01425580d118011102c0318010b0019030b1010040100d0b104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617368687 1250 617367437 617367467
    0x10b0c070e0601020d080405010608010513051501141002010e030a080403021204050a0317071a10060302040806011a07050a060c080f040302150c07020a1d13030815130e0d 75
    0x401c2500c1d0110000b90f5501130700404c030040128450105041042c00d40104000e08170010003072007917241100d001c070120307001700d8000d40301885148900306c6080481d42e600d81c103880c02046c2101080c8000307010301c010608101c48180466580d0405481e4041061001c0c0c2a6003100343c1e0b8020040c1001e0400925080340d507d13000444920402041200e503441d1818142144e41c450641c80d6002100c0400d50410b02a440c4041c25000041090f20915201c5a40c01d6200ea02802083d80c54161180c0d8110308a0003540501202580024014081e47e0544c0d0055001600301b00c038074604c2c0800907a0742500740054079900311903650700c0c0c0034005060b0303401450290f0b0000c034004c8101c450703160a480080d40e840b050304040c5100b05518001c034054000081c115210540c0141840040320758030b80542e042c1200b01904208200103200100e030080050001e0154aa50107941e80c400b01e0302c5212206110040204140ba80070805008500c400b40d0380c0c4c0242151420090302402076049507200241c443c0b08890910 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617369937 1250 617368687 617368709
    0x6030d3b04111603121d01140a090507050f03030403020a0b28021b030c06130f0501020102161113050901090506250e0a030b1314010506010f03020313060203010b0c07 73
    0x2c064070400500e11080154040c17030080e042202000031403000304084004900405252501100c3c072a205404c4001004468440c011035a69000644000c40d101c843c0d0003031040d00046070800c41443c1c101144000010010256460036589600141d149a915482143d11817004200801c00c0585803034000000303501c010100d40c06c1c050103c002500c60022144034042d0140700c0090321055201040310318a030a034090700b010741d00d000c0c081c031134643d002140c0301329044160080004101544103000761101d905c0c103da01c9a0003611503640300d81c0c10301c1d0380c140401e41021a07007030024034800050040a0051220310000140b2104074100035003400802000e80c00d001c0c1c00d603400960050300750f05a1001040e0649802880b841c1c600000a0004140d80d201606415606051010007402540d1171032010707100e582c01e008101c5044440340c3c240d400440f0003034045035485a003c41900d0180e001180d0101600d01200c40151180c5e85100481c0c1082c0c0241226450110315545d0014003004a4000b52211220b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617371187 1250 617369937 617369947
    0x1110a0804150609150329160c0204060e040b100e16050936070807120b0405010e10050a0305030301030f0f17130e06030d3b0411 57
    0x8003420000c00540700608200003204110310984181d031080700940f8024a00340b04c0392094a04114403007615000c15111601c59200b03141e140c41e9461500030b903011100045400c9582c41e60f8a24880980c1c4031000b400348034040000070b0050781c03a4803034000030b407a5400001001e4201400c140c14041c0c00140114100c03100e03504144a8070312501241c82c3d100341c1d19000806c002018440c2111180680c5001c01d8020514010040c0048040b07080300d030713605171645a80c81429904520014070390ba42980c4000c0070440748808034072100e101741c2c1145488414030401003401d03201c0c0000301e01150004d1340103040048180050020b6150600e40c48001408100c40301c13504c1c5821500d481da20303444103220040072b4400494602d4200920b601401c000365400915002e80d02403510300044183e401602240c0c155000c0c81c0000c68442405e6003910f02902000c0c004244a000c2d0a50544040c15112003810f00c00b000b5114500b0416000c1031030303071800450000d543c400c0e01100c2c1c081c0002d643e19002c0808503032905000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617372437 1250 617371187 617371207
    0x120316030e031e160f210519030504020a1d06040c300b06040801060e0609070804030c05030d020f09030c0a061b020d020a060c150e07050621070f020111 67
    0x5400720b010a0350742c1c1d450f1881000e2040f055050340041c54001e820200318140108611980402c2c84000c82066208046c00001c0b2041c1c82413030511001200502103071720010380300e5404643d120b44090a551003043d124610500300c00080ca030360a030320340c10303010030051a070415006501100419050020b400c0549440408a840109451030404d9072041c00e000c0f0344c00300d55003110b02204805020a5540d076124144c0703901812150140140c9041c0040100c1c2c5141003103002e0a00c02d00d6165100c0215894556045502100620003944c442c8030078401d00e48000d080e44001c0446182959100c0d564a80d100103140c103003c0a01e51041c40b400040f4420005960400a00b21006400e4648400300c100305100245121003180b8001e90058200100480c0c45034020304104a814064900350800305400421001540c0c41c03000d140e07640343c001e84402c2107503052480103400c1c038801c801c15808040708010107094418000b10703074140000704c02450100e0650307028891060704038a004425450201021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617373687 1250 617372437 617372467
    0x10c02010b060f0a141308060403091a07020103020a0212040f061e08130606080d0306230105090f04180b041208090d0c031806031a010801081e120316030e03 69
    0x50b8011300340034003c50a1050310480408964000c0c00c0d0f800400ba03034586441081e9510760003250101d001c62038021001c5030341140c81c1500364501c00140a40c61800000380d0045020b500507238100f000b076205484030702c0c158a0601c00608080d140484c010b0030b00c1480d0500c0105564000910301c00b1807501000071022242d800005198051146011003040181c18071300103004010640c001c500d02d00070503505a20042d0304da0404000c8500740600901e2000e155003103000210f11015129000c90030421120310070f800d1405210302141802000062580f102000e1403030b403480d4400c41155801a00c50801003044603004e0004403400d107a02c2c0c5041a481c0034500c45a94841200e80c04061100c1c61781034604040c07294542c00d001c0751113440001101356685401034007900f140c5c20003032528010161420201e511500b2014100e0310680c0040000300b03030340d03200002c890744210b241141c540203240c10b6484000c0004021401000c400c440342135045184540281101d440000382d00300341e04108007200e9000440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617374937 1250 617373687 617373697
    0x20a06030513060207060204050a06030c0e13200702331b03160c0603020702010206010b031e0411270f0a1b170609070c080307031d010c02010b060f 65
    0x18100000c541d202d044040b59240000d400080c000350002030700c1010400180c000d0011264155821600e40c1d88a09003501520f41c4030b000940000d000040710102072401010000206108240000e0710005000030f1400c0ca8080300f15403140a04005061406c40c141400300303003440d0384051007a60802c5407a22100189540e202900081d02c04049111072590ba02c0c0314a260360f444181040301c1d070ba1100c0c0d40f00c1a9445c50400301c1aa42501505000641c0c2c4c0d009000301c0c0e03003c550590150515a0a2845203d000e400141040c1035401d034045814420b1503008540e0760096008059246500c2201000c1000810348114001048030841e024440725415101c04180c01841d0003070b1403040d80d5201403800d0005e058608600d400303041d950088a203401c1d003006d490a0201010010051144e40b00d90600500b24019038514000400010811011482c0b81025581050031454003003007074050091a4201c4108036415080c2a03503594034121841502441480d81101c425103820303060042d2000c0f42c002074050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617376187 1250 617374937 617374949
    0x515040b0a260708070809030412060204090207080d050a180b15100e01031103270a0b04030314060a0302090c251b09020309030403032a0b09010f09020a 67
    0x2103194071503a40144004500c00071090012a001075824000d07101c101020b4942c42d010030480d10100d61442c0c440e008a500c226000790003140f61910b030010b928032541800000f80c9450340e00380720209180342c0c9400100ba115000750302c96912501d111980908a41d0041c0030382c12060310300008032400194481c3c00e8203175103030404060324059481d48129500d1b0035060701c10a0b03008030406d10200005410803c0e80c3e2400200303030780030001e05030014500301c440d00c01561482074003010310404c0c4840e48620500c00e0182a40351050342e6075801250b882030800303401601c00b200800d441d00b10340d100c04201c00c000d0b154490400c4908410040c90b40c1c0108549010141c160320000c500042c0c14203280540141203500000301c003002a01007071071420302c222400e10074143c24a24100c1e2000008032107200d070085d40d000d048440050340c5898030351340d03007558041f0422484002ca84c80000c0c8030342d81205410b00c680c09260040800e550030345051238800342100c0c03007e105140c499147c5500203015071940803d010950741 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617377437 1250 617376187 617376209
    0x6080c040506010e09040323120c0c102d02310e01091a01020601150c0c1701060608131509020a080a0606030c0f0b03150a080a031107051504 62
    0x50300030040b035010131010001600010280c06110030590320520a80351039045e6021070490000080000c826486906841c81d80307180c1180120701500700e01c500410341005280212408200d000c4c0010041d21491482807603100c103105801440740742003102c1800744581a00c3d04600d40b040b039007141207070b024268040321036051800c900201100f10000f5440c0180044e4200d4030041c0d0395800300e42015100c2400703001d1451120482c0029154000034000d8161014440d0740d12188200510880b0300707450003401903a105014010000da2411b00700d4a98803282c1c01100007050050901901500e110340c060484081201407844d003a020405002042100e1001c0701d40201e907442090002407180c0940c0d810030b000b18001c5060150411004e6403002c0103c0b44200d078064442550b401a000a40340b10348281c03c01d800d010000660701020070603000d00c135100d004026540b0252a0f1003003e20b0700e04214000c4020502d07159081e0005c100801140c0014803003141ca000c003500741c90b010940c031070141d4401c0715a491 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617378687 1250 617377437 617377441
    0x20916080f0619140415050603040b1f0803280906201e06150d02040902150a031406040c200a0f12120b09150a0302090f100906080c0405 60
    0x240e19646240c195840c074815801460307450b180081c10441341a40131903c501d00e08480da440484444080d04c0440350000c10b0541559a00c0d122017070f02c0c401c0241558122918880d0f8040b007121950f45401c00b5100741c000858446103000f05c0108007144030340c0003100e000c00c1c403c162140c10b0340c000c03064000e0b6140751501502c0841d203260b0f8a42c080300d00d85103041b00c2d40a00c021f1421040309220301d0f03000b500941c81c00c0b1581c54550300000000b425001200fa504404480249005030074a9080381c581c040c0701424400e10b07030302540303d010041d800080100001030b8440a4425003e680c000e82160405401c80d002c005500d00d00744c0c081c4c1480e52450401303445202801d0300341000c1d20140070a2428070f4011310340d0013600e01e05203030100f52241b074420074101042d000300388010070101920801841400207866071620351a0100c1d40071010707c1e121409907108d050484080016259540e0183c01032120400f044240d0034105202403408565422000520b440c1410800040350300103480e555400050300e00003525 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617379937 1250 617378687 617378689
    0xf010e01150203040f081f0b0a030803150a09050a061403060f19020a090303031b0905040b04020c010e0303090d05034309051504050a15020c030f010603020916080f06 73
    0x600a1740e000c0011900506030001d0f000c00302040505001601d0401c00b04440184d9540743d04503800003900c00d4214690034000c0c0006080d0100035908080c0ca80c1c09800c11085580000e00005d02c1c0e90844004030340c84d00c0a01c05214240e000c1c1c54003801d2000307891415a90b900005c02e0340d4100c000c280145041c00d5401150321b407118503102c6842c40260309170956441e040a8005049d404961004600003803821080004030356010810540c202c0e240c0c2d80d0409403d1410f001c12010300205045030754003650030410280f43c1602403048408101040010799100c4c0382030f4681a041c0410052000c05015041042060310103c0007020072620007140400c040698441d0700d80d4021840300b01c0328800c000c0149407024601a003007140c00013168004c641c00100a003154000410900451050581145804c0340601021b4007032448600e4090b07142c4101c940c00e04551000901c0d04030100010b41d181c0c5d6541406000754140303542001da1250000000a440c111140c500900e4000028100e001c040c2048022034a0303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617381187 1250 617379937 617379943
    0x1a01080a08071b0e0117070e13240207031d010908060f0403200604110303041202010302030c090604180e06070f0f09090f06091a09130618080409050f010e011502 71
    0xc1c0040000044d40d560311500c2c00030810b402c40c00034020910502c800015262902c0c101d0901c240a124102400b002e45903580100700340c80f0b5094819440c125001039003242000e4070142010300c2c02507031480340910750780803d07007030018420040c00d041202e480c0080c0220400090075580140c816240d20429940e1824119500001d402c40c4070408a9050016034103404000b42c2c41d40110300411488040f0040c01c0101a600d10a0f8481c0e00701500303108a00d00051f40c0613601955201022001c1586400542d40c00100c6582c401e070040c007455a080d200e468070001e1070344206107104c09180c3c000c0c0418104040050000c031a00d060701010442144a030195443c071410290006042802d014090004082e400c440545190300603804c2c0c95140c0221408460300030707108400f401c1000b40003200261248400c8a04803c0c0c1c0560541c1d02c1030311a00369000c1c241280603514051801216a151103a09000c00314013603c0300a410008246080343c011b121140780140c0490440c0c104050032011443c04e880c0680c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617382437 1250 617381187 617381189
    0x4170106030c090b01020606030105070801120c050904080c060c04050f090a09121d0d0803040303020f250c050f100f03110301080a02030d08071205130f1a01080a08071b 74
    0xca10b00b0052030018100e0501e801a40b8005000d07005c1d01d480d581c6100906080303400031245200000e04041c01000001e569908040710b990040c4c1e06540810344620205001300c1e0142c9d012a4040030000716413884035010700c038054011205064941c5420318010008004060312a4075500c1416503030b0116960f00f005030311000a8136031004407014019420b04024040c00c405591180c5507150b80b42c041300702d524108041d00c24071907006030080e00316100e64070200d001b900f003401014038210080107020300c2c0c9500c01d00791038404003583c0b03144503044203240f40086900900340d00c0240614441144400c660f6655042450812007a10706044826590354040740640500d9280841e01d0200200208880e1400709103a01d00c0d0b402a01298410b00b8400801c9407642400c884102c00900d900010340420500c0d60409a00040104400c05681c6c0030760301da08401c1c8626690480300421710a41c507640c1e42c41140d644034010f15450000e80710034a49919440090305c10203900074074044100700483c01d040f640501001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617383687 1250 617382437 617382443
    0x1002030c16092715020d0f0603120201020c060a0209120604060603030909020f0d0b0f0607060501030519050615010512160807030c0f0302070204060f171605011407150f0b150306060417010603 84
    0x4c84a071003d52090002230190303000503206800300403030061803e401402100c40d16843c41004014980d01c000d0703a00b000750007031040c9942c4500c9080300821002d10401c1150701481c081c003c0069014510300d009400d0442c10360004d2005401070200d0f0308201c00c404107a41010703001f0140400c94040c1c003400a03204008003250b440d482080861202e084c000701c0da0041c1d041e28802d1080303485911920010700604001070400800d5984410300180700c4a4564120f41400342c8107051440c1098902d0040d8a040201122803e1541806000c902d031120b501201072a04031025080802c40c2c100c0b510f10042800740e00700e0b03919003410b07000122002103448542c0604001d28910304400703c0c25407200702000495425010f4509144119903503040c02d101d2801d0020116181610350300c50213010102582d40f1600034030300c1a5070810b0841c0000254520354002d10483d460301e40800034048030003200300200550000c0002280440600800c981502c50380c040301c0507904902c14690b6049000c0c003140e03015144c190001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617384937 1250 617383687 617383691
    0xb0c1908010b09060d111903140c1911030d1a0901031515090c020105040c091e050403030e1506100c150e0f0a08040317090f1002030c16092715020d 65
    0xc141a060034180d41f103a030030315580c00380b18040008030040e0070388506542461050b0f0041290315031280c005442c0484034409800c1c01c40d40c0701070030a182e6080d0f8021190601101d5140c03100440c0245451850b0540100c0480ba01409035055031590146841d500ca070b480e060729079034031210980c0100b690b25000207002503102807201045841c0c00a000c0e100a071812142c18481c0b00c00424200007078000d000d01c85207202d0194800880b1070341c0c000040c0c01701a1080d42410303a030708019a10340b007090240c1c858334503111048202c2c5040040c14007a0b181c0da2141c1c000c040040d4542035038000f403640e5400c0c40c44104484404101d803035400c0c444901740079403a100c0d0100d0f44a26121501000141c0010740f049901a0100220151908100340d0251159604055229640141c9004030b880c2605241c0501440c61041f01d040103c003018a074074016200b0315000300d5003103000c400c00c80e200c03046c043c82240c2c0d4a00740d00b20410610040304800f40c070445a41c0100704410300e600070206801280c0c1640c1d18511a00c40c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617386187 1250 617384937 617384947
    0x10081603052205030d06050d030509100c080c0a0201081806060d11090403031a0111060a0528091407051e19060c050f160e060a030b0c1908010b09060d11 67
    0x3c00b540c0e03035001c0300001303500074140701d00024030b03203404082d1f080000d0305a00c40a103404002c0c0300700f00248001d05444801d00040d100207002042c040c0b4081c0c500440741200605200e4541c2c00098071b180c4005100b20302051020203003005108020030031a800c510140d4007a180d08202d4641001150f20501c68a900a4400010803050643c1a0080c00c0c07502d00c4c03210280080ca20380c600440380411401041d0320183c1c4280c1c0421881505030b0310480e442200e26a80c00005060652104490046000382001081d00e5a64010910541d40140501070080c0801040014900750208008400c210510741824408030300d5a00b0a40380c00310400c2d171050686208840241c2c4500340902200082c000c155000d100f0180341101d400d40008002c403000030002115400c0c18a03103103000703c40c01c100521441c2c0100750408c001000401010440b0700039000d841c0d04a8644090303c28604440550300105000c1040d1500100000380700034044640246040e50f1550350340740001071101c050889080800345803040099 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617387437 1250 617386187 617386193
    0x31701050105270315100b03040308040318080d030902030709150b03041110030e160f12020609190512030f030726040b0612030310120c0e07050702100816030522 71
    0x9249440f1b0082c143c01c20514648400210b03046000413075004020030b03140ca0210340824042c1c000840d20418a2044110584d2109201d5040507185800f400c0070079200e002850443c0340a0112602600c94420100808076003021811042d4002e44101e90302c194001020a05100142d200c940280c0c002800b440c441207000c41004005196004030007a80d07018061507040c403082d400e440803007150513003880080768a00340b00d00070710402c000745400c07039000d0800c00c001451600e0341c6400c0b15115540b0303606081003a19080a01c00c4202c1c540300414a03a40080200180c015580010340b84c00440074030f05100c00c2075000d0001450180e00e0841035001d8540c02041200300144112040c1c40b4500582c0c21013075644040301c00503528002a035064070305900360350052181003d2400030510860182d1a0717403030040d582d518611000c04055a82000280e000a880ca095023403d120001449101c8c3c5000c9100b40760600b000340c5110364590241080540702c0d40482c1d81c0ba100200c800590001802d078170383c00c0450510f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617388687 1250 617387437 617387473
    0x130903090b120a110c060403080601020a171b030a0c0f0f08030f0a0c2c42030114090a0f020a020309030f0a03080f09010f180317010501052703 63
    0x3908008550b08081d82124010644c00c02d64004e03400c120300518690312190707000e03503920700014122030440c4980810200401c00c10102c0c1d0040082d400d03e10707940c0e02b40c10141c03a4087c0d0502e5a81e1811903004002086016a11041d0200c0c1550030115201c500d1001c0e18154000440341803015040d4071011040c406c500c801c06e0916801030f410030b00100315150000d4000d076020b512036546264030000074644080b150198101c0880c0c0f00e18003d025051800d40400102100358100c13924142c149010080e4100050002c02c80c4c040d0a103040036294115803500c03100d0355079419800b2190f030090b07050744003040828415412501107000040d4055481e000e1251009680340c2080c207280e44244a040e00c612526200802c18500b1250156101d40007641c802c000c1c4036036100041c0042100d990ba0300039040e40d84d0001c1c41044a160341280301c0191081090034014844070301c074541d88a400c1c042c480104010381e0410300700c603005008005c04c000c201030a44c104510f246c1e000d900c0c00c0d425009801568010400710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617389937 1250 617388687 617388691
    0xf03052e0e0d0801050109080709020c01090f030f080609040c14193003020a02060f07020a14010f08090607180f06050c10060312030b1c120f0c02130903090b12 70
    0x555110b03d9280e0b40c0b00011190110684110021a004040d05004d140d405400500c01e10707402c440040b4410308680c3d19510f6206889105600140786060516001a0700c150441d8100c041120448140d04058440300d0401c0c41d240f00c0c0949041103411100c04079211108103649070070750000003414041d035401401c3c607200c10303c4800b4814950110024031fa980740c04880484056095802400e07034624075030900c09a81c0c8807842c0031514500a2140b41c0050f0b03203440109001c0d001c2c0600086140b80504009082c040b188001c1070700380101d600400c031000d48009606507020690340781405e00c0304500601035032100019040806040d102110110700541c121004182c1c9103820421560750b5005509480d0031550f03123000042c41c58984c0504811100c0c0f01e5005106403003401001c1d9122100c00e0030030080c078206026002c03910444da50f8410880a038222140e6071184e402c5050016070940c035540000d60104096452960b4035544040c2182418032035503489001d040340c008490764501e0303040d05101e108002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617391187 1250 617389937 617389963
    0xf030b131401061b0f1b0b0a0507030f110a3201020301030c08030c0d05030a0227030c04150b070302150405460501111b06010f03052e0e 60
    0x4e10041400d001a0b2015400420380042071410019090303666414192800c18440c1b01d80740c40d42601144030128071000304001c40c0252901507035030142b464050010a1180f406a00340189698030341b120724808500000c1c0ca41e813102c0440300e05a001003820104091210484034000925607101c81160015402141680d00603030881440c01d50720f0314001e5132845195460301a41d000000c44000c024050005550810540c83c4054100005590700d00701a60140303031100043e1407000521101c41c201031203600040c10050b20144103080c0ca091901c2d0802180d0721504815a00004030882418800e200307902c081000c82d0055802c8d0b0074503040250340e54450600c14607440009071001882e6010b00f010141d00000724100710302c0c05540c0b102111a1041c10000e09035003654850b08080380400c424802070580c0391080400084444074080750718070b0003d058020840702c400c446403d0022600006080c100c064034080c09010102c1c00d420002500010b103c010040d01c3d0501082100c0d0a0000c82c515004681d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617392437 1250 617391187 617391197
    0x6060f070c180e0d0305100e0702010911060c070506070606090c082d01050607030e03010c030f0506030d020c1c150218040b0a090905070b041202031b010f030b13140106 74
    0x4102e4072001150b40c036015200303c5038010200d41020340c1c06500b040380e01c819901203601959941d07581140709094100c4071100181d568108160030800105002034810340203451650404aa030904903a8640300c3d03004152060001054a00400c06640c2240340500703c5441c4c1800900c00146015220001c00d46a9041104814944c036840d80c1c50010032310440c00d100120100141d10b02410320000740c0c0015000d40421101c40c0300004145c41c24080d02c4504102035a002840e14058074601c2c3c120345c0c002d4107003031003600718400005130b40d94005104246c03103500f110401017003400d089078030301400f0741d103200104030500e0107018481c88076040e40680382002c0c0d1102d0110080031a03d040000700c806810700c40390f1010b0211018802c11903507a00860640c0c0c4038800721241d1a0711740325174010700d41103584050002488850ba030001c40c103081c009000726140840d9035200700c3c540440060302c508508404071003010b689080030402c640d100d090521314015440d8003006915000110b807440c02e80d090141c680410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617393687 1250 617392437 617392469
    0x5550309240c080a1a0607150c080105040b09010e040305031e04030210060e040c06050a03020c100219080103030c020f01090509090606040b10170606250c05060f0a0806060f070c 78
    0x9402c5025000c2071812000010203012008802c00080d41c0040311f00342d0303080c481c001c0100c1c00c602040c80340410ba00c00a45544459601d48020070048e140c142690502690000004000024a49029540180c0d040c01e006840380d0740e09a200c840d04050f002d0380c054503031160040c0410b0640104509490203c502428000e00d52603a822040151058800a0142e035120104121152107480a090b10381200d1402601e420486111103140648114410b08050740c00514904403c8003004010021406424100015071450720060200c40646c80040d001c0d902c8000900e0380342e84501c240001410004049040504100341c12030382e1013504a5980d0300a61a008030903480d0320f8181100c5a9000c903680e9494144888a1141041d494000c3c1446400080900c500101036000304d00c0314100d500039100104000d4030b28100301d8548282940501e004807810021300d00c04504100440d0b40d01d8900c0d0600382310380d80f682000310b419440f810f8640c00c070340c0344040380d088100000751010404030b075100b125842841c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617394937 1250 617393687 617393701
    0x308090406090501030f0b040219030503120916090c0302091503040b0a05190906090f030c05061018200309010617010e07031205550309240c08 63
    0x703d000b070001400b0100341602c503800040e005117685620910150044555101c03100c640100002c0e41d41045a00340c1010620310304284081c06202d42c05100302c0010316490350401101d2844480c2030240100c1140c480b400394014a00907011140c0d412009004480c4805c090007406140350002e840450390200e0b05808986444c17428060303980680d840d0581d5040025907110544020006018111000fa40761030a200109946140109206002c0d40729a02d080035249403550034604000c0400c2c0ea1aa400380c002d22041300900c83c045003ca0b03040500040c01001d1249168104c49a02e1030024080c00c000701300161a4019004101211462901710b0030300703c3c4040748c1d54240d8089007626440d5030300131082000402e10403403102e580c03a1014184180740c61806044c0d5a030003007965580b1401114101d04090300c00700101c03c00001c0c080c1030b840d4882d0080740300c640f80041540484070344082548403003058051016040c0b1694100d1558004211044034201d03004000c0e1400c00c5404010441d680006850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617396187 1250 617394937 617394941
    0x2007030b0a023a23090c012003030f09030d091b050603131e06020304080306010f050a020615030f1b090105091003171c0608120a080c0a18030809040609 67
    0x8241c85001c29a0000f804807200100206140c0c13080710b824140c018400d2070214010704649005580d804003070204000d5031000546116004003041c034000c00041510400f001011061304d8102d07440c440410342c1c648415920500d11f01415001300182842c007a4032004210705000c0b4101428402101c0081d81941c880030800c881c00125084c2e107001e05c90300c0e0704400040169a0701a00030300e010701301008004481e01d404040784c1085604445444000050080d00d40c0c200e501c0303160301c6034286021850300300100c80007526500c0143c5080084404c0c0f9091226564080c0321946081c0d0b075038021550440c3c0a0072814000880507413410740604098230020070a41032041d1654400c0c60302c8120030004520f59560000000180c10b210300001e407060100c62070b9480107030000040c0c841d1000700416246d050407074080c180b072003804410454081c20007030f203300c0740e030000c50180d400052890003e8444a9204090328151000551016180c400800200400040002410b102c280c107442c2040b45917120101102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617397437 1250 617396187 617396257
    0x708010509010c1d03151810020301060c02012a03020123060d08090102120412060e0105060a03031b060e070e011217091201180201030f0203072007030b0a02 69
    0x1910280c071900800d4001d9410942c2c0c15400780c00c40d4401036080c01844401b80c020f56035440808040c0030070108195040100c60004445d8090444c0b441d45020b030060300405601d171000b0706003c1d840d0b005e02d08803c0030000100210701500c8100201c1e40071840c00a008200600740140b1120803140c0440c00c040d242030310f40d07126140291649645454948482034580c005145942c110310902e29513003036136481c60010f000100196400074020800c1413a16100b9900300c601752042c1c030781c984401c100c1c03c0d13940c1c04501c40442e6007504040746000804090401554151000509010308000d402c02d038008000502070211a0341c071030142c0b203a0f600c8030b150030b00401da00b10f005407074207005800c010280f0003080020940c0c1c0c01c00400307030b800c3d00b286500c00c9401d680d820010801d0b40d0241000541c29544c05010781c5121128030760003185546401400540f4a4900e1340c03084840c1c501340345215a20282c00c110860103150400b0380c1c46464034001420201940c441c1c4116840015903c2001c61281c9220f04a45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617398687 1250 617397437 617397461
    0x5010219020f0a1a0a0615050c06090a08030a112205180601020d050d0b151e09061608070501050f04030f030921090302090a0902010311122d09070801050901 69
    0x1c1c408151040303241304856400f412007100155280c034005019040f40098990500007602d1700381d103075170401c1c2019092203030040c20f00040750001000000050958401c80f68040c0c2d001c0305c005030342c09c60b4404e0f4040601aa080402c1100c00c1e08032002c0b51341c0b215100d900111541140c40c0781d081c1c0044070000340d080d5010744201d0301581c00005d4134544d4901410140c84200d059090003e0201c000c04001510180004c1452050f000c0000d008a03c0d80f83d0402c4940301d840e11850200d1905007102c0118031544100b42030403400c100b000054100b005401822034011707542010080c0001c3c10000c00340020b602c0c0a407000c40208124240a403002406030107040440c84c0c10034414166081d840307220000c420b4111100004000303506070040b0059603030b400142e004050b01c0701d00149c000c00610014040307030030300070300c810507004240294806d0041c0300741c4407540428039081a603003440580100c14801310000c9841c400100c0958204507040500080000441d00313200028041c45d01d561106038201d035643d640407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617399937 1250 617398687 617398703
    0x1e0a06151403071a03041e1a13020102070e07021501090501080709050402030616050f0a0210152102010318030f0f180509040212031207120203010b091c05010219020f0a 74
    0x4c071580003d00000317998082c3c01006440421100f00b01c222810302c0d200481141e0310340e00c06103200c00040c0c03c0e11b030090b80110116400401c503040d03600040d540e20503034841c8007002d2054000044c100c910030710103c190000b600c0c2e00d9004550311040b04002400d024052082c0602c21040001242e841c0d50269070b000b107801502600d2185c450680e2840c5403144040d044060003410003c0b82900d00210000b800501c0440e40540703030305061401404180c68401402209241400344184095500e00e00000c1c003600031344e40800e00c0182c052005070064030040d4841e00c0100e02c83d100e02ca003415081800510110001e43e02c22450314122041a10701c5201030004541c1a0348100c4140401d062529000d07030000e00050100041e5103840d00c96518661295401c1c1117201c1c24801401441a002146880500420a800d6040d581000401c040c94041e0b9220300744120051015141c519817290340350741d102c9400100a65a400030b00c511140d6035074800b028140103200b8000d00790910710001c41da078046150b000400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617401187 1250 617399937 617399969
    0x30510020f04140307030b09010e1e030417100f0506040c03060b0a0f12020a1806020304080613060b15090a1d0103021011011509050a0e1e0a0615140307 67
    0xf904041d43c0d22140059054030681802202041d51002c03680d02c220490000410500c0360312460600700f0084c5010300c07101220710b1508a00c1e040c40801950107980194500204201d01c9800d440e2a242c081400c0031642ca240c21300c505541c0110b070300098410b107003c1d20b00344442944203138100d00f10f6620748180403080300248440102c1e14841c80d441a40541d15140c0602500e400c20102c81c1203920501d001c50224419540d039008141c0b0144620f002441d1034000395041038a041807094842100a001d4031464100d00140020800c0740e80c00400078000103000498548003860b0000803603031211040d03034485c0071450000508240e206020f45c901540401301382c049a440e5500303000c145145108020305012041c00240002d01c0d0902c68070030484203000d13544001030f243c00e154000f00c1e600036100044040c2004004801d5000004500b100c44030340c0860b00240d4851800c45606152134143c0080c0190700f0715040e014807041c0c03d0901029900c6204214028401c0b400801d0741c0c1d20228800d04100510981c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617402437 1250 617401187 617401199
    0x160806310602130308030109050105031903020607180306051008010506040921050c030d0c1e020c10140c0601081506090415230f010503060c12041106030709030510020f04 75
    0x5020340e02410920380300410741303903a43d006261700241c10861400c0e50300c1004010b285410820740d5420038261242580011003034500a4652500800c0c80c3c0620542c004c451804c0b0680c44007090003560003d40400c00b81c01c0490040080d2001803095810941c20900421441d150900c10030641c00ea0020001c0c00100d0021101d00c055050b9410783e006100e0b040c0070345140442c0500080502000c10080010440d00e03840024101c58050600011070f0340704d621715541c080d50001014403401008941c41d14482854040480360b00c5110203010800c0e680102d03180c07002140002d60a4142e0303181c501947e03505802c102cdc0040c00380030100d81c43d0364040c00704000306020884069110040c1503920720007051210406a03080c0c41c0780500000720030010343c80020030040c0400202c6080c00341034110094a00e44c188060603100e81e01400303614945142004010400308102c103000030780c0c491005407003a512481c2241015040c41300c64401503e0034083c044180f9100b00ca0b510172680060301490000f41083d041c0b20b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617403687 1250 617402437 617402441
    0x414060415271d060d05010606110d05040506030a0e0a020a12140318150d0c05091c0507050415050d05150a021213080d050406020d11040506090607051608063106 71
    0x1307064a60802180100d11000c500b0030b003e2076001e40a10b0700c1d10300710715108082c174501d001400740c2401d04104081c00180b056a8800c5c044941240341d032500030490240118030035050911540c0e0003075000e14003a44c001f079061050b001c01f0b61264040c000d80c4a4400307041030007a841c0c1c482d8800044030350079000b0713813041c1e0751030004000041d0002440c1c07020709040c0c9078062174045802d00c410300c0c00800c0010901e07580e50b181c090200180450010300d134040ba84003a81e91196200c0490048921554a03655980c1c8800c00800c0c0000042c14000e06401c3c269410317040c20380d200c0300450025003400d007240001404401e860f0080303500d007c040c401030684a130b0f0356500f0b070b56500c00042400c0b1a608000c114281c0174040c0c50207058001c0d40190710069641080140c003504982011912171881c80003480104981c1da200420307112142010384d07900d682c0315030f20b00d003150810004100070380d00888811004104c03403400044079480780e2202030711941d6030014060400d40380c0041078078030606442e1049010000031a15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617404937 1250 617403687 617403691
    0x121050c04030b190e01020c0d23040e091207050601120305120a3303080d1b12152402030f1809060f060414060415271d 53
    0x108454a003090b07103d94810820150544110b42c130305400491070f1501c1d00007132240413150601c0800842c0342c11200080c1c2d070340710708001c01010248145402c2c0c89610b41c0c02d200071030703407480201d0030b1460b40c82c1c0d00ca1060903040482511203480307500c1a5007034280190344203011142d80c01c1d0850000c1c6100d03071800314209118100324004408101d028000c40d980944200c142034020390080d1408070740e040381400b00100a5030031915060076241e0604c002e0510801c1000a2404d403504098142ea40c1c02d894980c0303401421200010061002d82c0c000c0a1002e01d50061300c0d144004160501480008003410700d030a150f01c03890080540c595001c40302802c484140c56403110500000b130060303074184006000d050440342c001d08039080001d100c14100b4100b91511804159121004852551124800303c0108e1024025801400d492030782c45080c01c0219642c440585000b482c1030f071100d10304001031290013005071100950211008040c0301300b650001940a42080c191040c001d1205003d900c01244501d20286c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617406187 1250 617404937 617404951
    0x803041206090b1302030c0306010b2a060403020a0c05031506120703140703020a1d06220501090f18031d01030b060f0a0801120819030f15050f012105 66
    0x358201d42c40014414250b0907116402804e10f40358511220300525052038015800d292081c2c0088006000b440310fa034050b240301121001c407110144401c503840d5030b250803030410400c040e0b10900040008040d40000c50120307041c410784400c01d11780c0c2d81d1410306589078a5040c022020300c04210001c0c040d030401c803940c20b40c07040b0084122205181c0d03a840324442403d403080d01c10b60700d8000800c03d100f0f41c182041c0a43c0100488404414603c2100600d01600070001d05080d00c40c0700c0b0705061400e21240549589440702481408100e156561110400100440344024892134180203454a25182d030001000d20f0503010748400b45226108043c444907150f200d071142d8140359907083c0940b00e6403980000303403102c144020001c42d03403440034101c00760107580c050b8408070100154100e0f0a00150b9034030140c0d20039008070a103141000f1444603060b4080c0c41c842c6440c4021902d818080c03404210011011011500140d40b040811103440004482c222411700840e803da994441e01568810059030181c2e0340010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617407437 1250 617406187 617406191
    0x20a06031802040f0204080f03030123270610050a0903080d110f03040201110a150f0e03130e060a031e0203010b120a2d1401180c1505040803041206 65
    0x202d0b03000500b1200c1810104c16140d134003040601c2140c104118803603c00b5402c400550456240444030352501c1c0880b41001201c030303c44e681c030124075200c0d90241d240c0c171001891007420032400001828000502101c1440c49080c50b50300b2001d8841c05a4100c448040881d03a0f13070142c5d6400c1d51912421a441610001c000d10303078a05001c1c0c140f44610001d00f507001702d4104860760328209400014018082d0362461100354006003801e000080408111002110520401080351010101c4240c001e21009212001901001500d508a6400c881051060301c9011070785d0798440e03e820043c002108014000107203401c0040000b116a01e60509440c24207510080000c140c0c003c140010510224040072802c4560b40f00b01341c4401000381c1005503580040c190010821032071414100140c4402c26030402401d503008124003000c5001003904041c001070391121600380309042d145000c05405415119098141c0c18840540014510032800c98080b80c584800031402c15003860500895440110002c4030329503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617408687 1250 617407437 617407481
    0x90d12080f10081b012003180306090712030903020a030809100e01091806050303070f05060705070b070507020406031b0306050604051e101214010e0607021c020c06030f0106110a020a0603 82
    0x1c130741510001142e6041318090754448ca0786000f40d1200015868805201c1d801c1001048045400014a04125828001e0440710101c85060580d1100f15540019400c5a4085004018045000010161200d0030b88100c0d048911105045455141c900318180c0003d10f8880c04001200b4240c00b0080040d0002d40c00168140d03407000042e140d6130001e0400c49030540d00c0d030846418042c0512445a01001508040e80b800005944054614000601c104d0a20130003140b1102903444541c8602d01466001c10780f103800d0f4500c140015130181e0780748003c5a040f4141030000343d081c10310303002d0f603409001c142e00b8044025140c2183c41d0181200204a81a031a5a82c0d40025500b98000740c5068040e019102c0040c0701070801c42c140d400c0d030b988442441d5240c7c3c024002d000019500090030b007130a12080880c24031031200c00c4c00480c10302020031500c540c000804018000d01e00020060281225420740320440e512000c0c4801035102ca07100d49020b5802951075000f000000e01a800c1030b0112110b03501412824 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617409937 1250 617408687 617408717
    0xf19062106060e0117070c150914010209030c240703140310051201092d0204050f060111070e2a1303020f0d0f0206090d12080f10081b01 60
    0x21101c82e4400700018044044050041d60072180c20f000a100e0b50030041c14500d485000038140c80300e401030052031403c2c01c61809030405e16a51201c0c0b00907500200701c480701400070071268041e400950340544280159288c4100d0340c43d0070040700c0c03117042200c021802650a1703400010400d81102c40203909006c11160441030202100004500c5002880c070304840340c40c146014003617180405803c0b403105030b00d030074840808162000c4107012101c1c81400e0035008004040d058503088140120002e4209080005200c007040d040144c3c140314020a03602e03030481c400c046156558070700441c411480ca103c803d20100300310340d0380d8404a48084548082c05070722501c1100a5150691240c0200f0604042c080014411890042a200e080081c100c0b0440e002c40025100c0504040d20000c00910071000042d03050300315111484030350b05154115407404136221a100303024000c950b04491174a00030482c100001d1070415082d44040958000400500c81100c0d0030300c03214241c8071245c403410305010302c082d507403607103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617411187 1250 617409937 617409941
    0x3111e0d030f020129040b0f19090c0201050c180f0a12060b01030626070302120312060102120723061f1203052b020403110f190621 58
    0x1110320a03a2400701e020084000242128940102e05051202c1178041958842d410351070501d0042d800c4900186214044002910000420021300d4004200710303441c45203a07a4040c10502100c40b12441031001c005000c90403422101c5c01c0310714403034082c0140166501240072020211000201410309101c0c0380c070844c0010b0402101d94010000c0381c0b40224108100201c5000b18071010f0002c0c00c00340b00f4142481810180c02c03035030304a841d6019084280140c0c0780d0204110100080d500980400e040f04e2104602c117032a6480030420902c0c800c0300502213801540b0000d04035907180312040d00c450414026075100b100412006000d0080701e0b0402d07012503180c4405210b803078020000d42d6001c9003020000740c0c0300c41d501c1a4036840711030340c101c1d90140d003000319821404aa001c0021780954244075009014130340d80148004410380c900910204000c010070040345006110035008a8104010005140c10801069480c65414200321900102004210700841c0040301c10020a04403406141003031860100b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617412437 1250 617411187 617411209
    0x70503030f160c0e0a1b1e200109020114120406110d2405091017030c1006140402091f05161208010e161d030f060601030e0703111e 58
    0x2c45440d2032414803500701c42900c5031211550000e060315010740c110702c0010340043c0e0740ca02440064a59216101f54051007178440a500076254020100003804507040e81d402491032100803030118000d0403a8120590b42103003030399415060b0043d20600340c0e6480c0c0c0d91030081c00c032030179120102d998144202c80c2c1259803406440c084460000c0000821100c03101031503c000d40e5580058003a00d0400d00380000069140500c00a8442c50560807a00c480140b05651441c0f160381c0c28582c0c40c2c00ad1840c44031412600c0c0e0030840440d072071003800403100c10b810301c204003c074400d407004a5031111039030043c800c03460490800300a0400050030010300301400e0705280c034415081c185044419120b0040c101404581206013940504400c4809064614021075040c0180c0c00055a04041c44564210803080149880003001040806000d07228400d02250025583c5d200c1640c0840c003080c1421281c3d0600403000400d003040340c1d00001c7c1c2c21803500c4d00d0005d20003e54040c400c04003031701c4132a1441d00342030340b00da9900c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617413687 1250 617412437 617412449
    0x3030703080405010609020705100e0a171908160c1106040e061201020c031210121412090105041a09040e1506030c012021040314070503030f160c 64
    0xc4625207807403d0350031640d00da004160054030520401001c510300080c0c035091442103000004483c00d4083c0c0c01458080c58040c0101407038042902c401e00c51100b440980700c80710303040400c10144c525800d020b8035080c90480d2284804c144503141030002a01c1003801c0007255000355003502003e0401004541e084c0e100b50400945800400b040c0f1640d42407000c0c51803415030750301c4001c50402c03402e0500561248900041d400d500c102c0c14021032400304040000100401060181c105101100e01c0c100c1c2104008004541c418006c503102000e0700074aa908440d036850050355150f2410342860340c401b200c5111908001d40306d18081c0000d0000e5210f41c840c2e2000640e918004000003021694100304502008211038000d42155042d201d91342d0300706411140c0e540b0200c400c1038003016802202d914105100a18142c020013032100345040d00d44110040040c1c9008101d00e151100c40061443e41d503001520505402d0b034001c020700c16200d034854020709541c000500c40e040c02c1c0190b9848141c039041040d0416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617414937 1250 617413687 617413697
    0x200a0602010e190201080f1503011d1903080a0e0304080d020619061a0304020609030d11120301080705010825020304060e030c01021c0c05060903071a01080c011404030203030703 78
    0x841c42c00a020080041992400340025240600643c00206880c01c00f80c0f0710b21b400d64414000c65641d41e24121100c1e804000030303008010389590044010498805240c110700207000c8d04040c26070000614007034003102ca4154446100680301d0045c1c8000800c043d01d00034425000c140008100d102007408010112080d41c1e00400246c100300294001200ca6007404002e058034004040003002000e041916298038507804c1181c03242d9450011070b031035101c2c803200c0b40d038503010381c40c2d040c0316a94020003000d0010707a1000882e0307444c211482141d00c0d103120a0140782c685070b014400811856210740c02081d8041c268841042824030700e0061002c42c811401d8540b005600081414426540c1c00540074813982d41c01c81c001c1101408201c0040d403150001c0161385082c0076801c901d6070195002d41c1005400c603034071000302c84942c5000e404d81c40e126080070350101c903200007040d81241d4500180e24030701e050f908014007420b1100102070040d42c01c9810014141a644001d000000c00b695061003d414014025220 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617416187 1250 617414937 617414951
    0x30f02070b0f21090d0c0f0b0f040c0501052a0304030807060b03160e0a0c0509060d0204080c01020f07060813121d040c0509060903192001020a020d200a060201 70
    0x7455070820006210f40c500b8903540e010400b003968001180250041d403410100680080c90511842076808900040c161000c10000d0060700901d441545106901860342a039207991a100110752611801c54078031503003854002090403404591412003204d412403011030740b41c15625035510001307400007402654038aa136a04080301c50305040c031580c40c0401d41042007d102c80c4c240184418034100c050206002c15580b41007414209024000310707010342c0c5d40100b00ca51039800005d1a00081d43c003d020b07207222070040300303000245035000085410b6002c075450083d080c0e07103042079400c40701c80400034800700740c0d150810351507000303d040005c4d00600c0340c3d82070381c1e000320800301d00e41a210310355030070380035540224600000f20707039403d500c503094610004046904580d5454034000091a1400c41d0302885903105c405040041001003010005002040b81401044c00d03070000e0005980310400400040d4020004607a544001015913103014101c44500c0050004090448042400c0b19481e400a0b4003503995024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617417437 1250 617416187 617416207
    0x90e0303150d0308070305090109061104031e0c0e07120218031603050706050d0605100c021203120604020a03021b0607090b0301050a0605300a060504020a0c030f02070b0f 75
    0x2541844000c030030754082d444489542d42c014040e03074004144800b0566104d0104042007429048050b010780c110790705201580c41090030f568150b001c0c0c4011103a021160424040043d08007914900c0d00ea003180003400c0481c540582c0000e08500186802d0810203003401c10041c1403401c0c80a00404d0445103004002401c400091602d00400030461100c0280401c00400004400069200c02c0d910189070036a111300041c2207003c05003186130046075003c060751410500c0d156012964041c114004c403400c011074a01415450f40b20711411880d0084180740c03800003600c40c10250003d100403012481e00600d0800c060380e0b025001d41b0a658070780000e8010209000c1d50030740c4540300401501c03084c0240740c81d43d4503000c005504900030340302d0f82c000d0110200d4900f2a42840310401c03622078144a12505030000210940703009510b0844985014074540840410300c0c0c03c00340700340d4981f2002521940320400140e11b00750341490406042c00114460800302090342c6910a0140c2546194450750640350910702c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617418687 1250 617417437 617417461
    0x915110d0501240f0203120a020c0c0a030c0b0306010e0414041b05240f0a09091401061d030c03010908030f060f010f03111209150a061d0907090e0303 66
    0xe84900ca009189000d01e0100c40199410f00e803141c1c06904200b0065002c01d80180d0450103000d00f44101f44104204005000d20785070002d0a5030b0b90740106030384000c0d0780e180c2017003082604ca00000c0c0229150601c14040c00604200454001e44141007085014a804002400b506e18000c45800d50f503403079000784400c00c05e40102124003a00010541c032152414140810390300003e200e802c9000d15407a070300c0580b240300140211030a0110340040d566956130001d05c00380181c19140310703642500785000c0e03170521004004d09000381a07507119070755001c1410000201d207074080789000700c103507142c00b07110040310490394248100d2078207034030902071140c40e0303d0441e800c111100802407010f4043c800340000200e090b0f9000e902d03104240c895050000320501c46c104142c1071801a19100034100c011718050000e00c980019520f01c90317a8820110009555480b41c4210550300c0c01e1040a08000046592407465011000507230b0740044844112030a056503a41d801c41540c4e1b0b01602504981c10000074040944844 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617419937 1250 617418687 617418689
    0x31909050a0b07090b09280807140102061006031d030a0c030e0402070209010e1306050c04091a0616112e03050c0304060203070e0310062607030201030915110d0501 72
    0x1030708100c11020302e171044110442c401c3e8044644030360344003904203403a145030102004201000721619601603031500c40065a07081c0e00e0003084208225802d034414158800184540b04aa0060811101e035107409001d40182c6001c00f461042a1144d00403105196810405130003104007a40c0e9008040c80142006400c0814240d811401507004201328005071b11044041c41c11155501000c007443da03a0500c560300e008002c218020203050928040c80744025081c0003500a0f2000d04200700900940310a021190f0080f90030050b82052080c040c1e14031a142d42c00390f980b00e00d80200c0540529990500004070724115001c0010440d41d401c00c0d60244440d10403505900345000d6050070000d909140954000c2d0380001040102070f0ba80000018100c00d105010324208144c0107000c4819030341c100c181c0680a08458014101d8021498182082e5000829039040e586403681000d4240c2600790b400442c040c100c040c1095521071950524005a0b440620581c1442c2c00710350340e0142c8500f201c800042c1907d40c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617421187 1250 617419937 617419951
    0xf0e1c0b01170111030402090c0c01020403050714010c030228051501090b0d050307020d0206040b0a1e0905010905091f0602030a12060e0a0b0f060f0c070b03040314031909050a0b 78
    0x140c481207030710b1804d0901c1201e0300310350100c41442e80c582e514565080c3c0c80c492428289102d50001c80c0010412030001018019076681c0d4407240d0402180e03c00464811110700800780050b400b10220250441e61084101580b15a080e80800c05085a8917a1403500c140d100003072880202040040244180f14414044a903000700c0d5803031001c80380b54489568038000d40310040e10650380000704104569920003150002d1071b145ea01d1a07181c00b940c51028050510301a6420301c0ca14019101d0544207119880850550b041610750181c100d00b044180101380308020311a090340003144c0101761060b900021604024102940210707990500c5400040040b6010000702c80d02505140043c803108010f103010176401103100c40c0005c7e17000c6072400018480c50946000b1130304288000742203583d2140c40070080650f52281c1040f6045a40d66050401c098402120302034001541c203002e18910100400c000c54000b512180814080301011260400700c44007044101d900c0d501c08a6a4003c000107460070951000c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617422437 1250 617421187 617421191
    0x302150a020f03070e040b100806090105040c0c0f050709240605030112020d061b03060509150d1b051c030e0d11010c0302070315020a0809010b010f0e1c0b011701 71
    0xe900300c880d15060001a184806000006841c5c442c16100c641c0600ca4140c0700504640e04502c1c0c05601030000f41042d140320303020303000301030010071a0700f45801480a64680c96941e40f41441094070344881705502c80c00c08a8043c0030354900001c2ca1203940c0181d040084000050b00e62102142001c80c03000c203801e501043c14004140010040d803154504041c04840d01690030501c0c10015241501c0281a07990002101620741603072030140a901d80d0040301564025a00c3c0c0e20700e0740b1ba101d0410b801c8540a0720241e80a050368000038005098001c44c403008402d400b10301607074651580001420110b150031040890401d401c100c0c8141603210700140c0c007c06040d00c1c0e1030035030300903502d6088007204401255070510030000c1e01102014400c00c51407000395001070700c181c1c0355084900e00300301079400215480700140030ba00200381c2c424010311410101039016100c80c29080b004507416210002c41c540b125030303c80640384164403060140c040044603284940b10b01d01613507040203815008c0d43d0710003450712080c1c5c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617423687 1250 617422437 617422447
    0x90303021c0c17130501060b09030706030b060304061815230702060a020a0207080f0d0206010602031219110d0905160b1b0a1401020403020102070902090612070e0a030302150a02 78
    0x182d04075120304041e041c4011240802c1d5501001c020409078144001001e940c03031f0410010300c0f0780032003029050ba44402c40c10703913000c1681c841045065640359080b60354413034400c101140000c0c90951002e45111400424031614800030b0303c450960b800101c44081200b5207840445844024140150900302641e182003411802e00604c000d60b100c00c000d1004404c079900040c0e042e1914001c0001c54018421001100c038400d0900400707549410f10000c00c100544500000402d2990000c01912441c06590022200c555107001d0520070401c6002c140d0700040b5500c041c0960002241030003001c648043d81404282145180780c0907140142040200e481e840c0f08020501c84d5a40e030000700c401d81c802101d0410079142034038079014249030741c050700200369101444021381020819009441100c0c001d07000d44400c05d60307802c02035060f03110341c515040c3d0004040248880d018082800d240e00061280781540350008140042000d4041075001503001d039001081180090100b040599408040b4240560a00b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617424937 1250 617423687 617423711
    0x30f060f0504112b0f170f0f0906070c0b130510020a0b040501150806010f0e060109031e060e100609590c030d020319030b04090303021c 60
    0x3c00024454620504000013202c05018100030b200704a0003007211001100300c4d103441c00740940491200200d07490b08440741d22804503480c181c25952035400404595291070600070400c0d1059201c3d41d00d1550140c0b0503c8510301103801c0c1c16581d0040c14000e02a655034180440f218440c10026038003261081c50300841d10881e842d4089926061b540c0d00415100303154071680f034102d014000d01c03040d184c01c100030604c0014143c8000103001d8100c684521090340040d881d40149800d07000101d4040c0d01040614404000140068402d1219900c0d150a81401c2e5040d82c1d41d08000d07a162224407819a500c900350a09104d003040c0300e03500040c0401e4804010142c4034002442e030960b007410305034548060b0f103501c1c08a14601040036541200695003240c0324001c0c0c0c078a00100c80b000d0913072034034050710812491001604001490b15284162900114200040350a4200320703070203100c844208040e00e03040390003e1611240904500e05200752070158071500d414090b0009000ca4100304183c01e41030048032a94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617426187 1250 617424937 617424953
    0xa060f063305090a0510020a031b021008070e0306070306050a05011d090417030c1803032109030c0f061e150405060f060c010c08060406030506150316030f060f0504 72
    0x409a2181016500d912414000910044c025440300d07400c0750410211030083ca50110700ca003902e512944a1107581031400d001038845107070580c0000d40002c5100c2c2480c1c03006019205903036102c0b0203454401518680d40d8003090401d034050b074142c0007103501e404040c004c91400411900140c0380a02c0d19850300300b20b90808041840c0301040b4580901103040216081c0329180001400102030007032500d649080c03001c4900d22075405111120045800b504191802d464080101d03403112180000158000b01301c400c50640d800d402611090b5207100405c001c0f8014441800340c116000c0700c00001e010140351801c5000680c0a50030500e4491181010400c005062001403c072950001642c00040daa6100c8000c9005142e40341358160b400600480d5003e0030301415000a0501506582c62184907147d0340103000c00c0d549e0034000140aa0400400503208480211201c04034900050072504201140a05404c82d618030b90401d4551600719643c0c00c05001040c056a8410b00301241d04207d02c0c039064850b085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617427437 1250 617426187 617426279
    0xa050c071e1e11030f010b01140f090a06081b041412010b0d0f060e0c1507020d08030f07030c0305090a060b0a0b0c0706111f05040c0812070213090c06110a060f06 71
    0xf0070310000c100c90f007914164009a0750008005443348003000d40b100b10280001786c080312064000c112440d805280c0c600b50f2400d0764208c840c44441501c0808002d030400140094601d103403545036580742e0b040201c694900b6810340ea2640510900607041d20f03a42003000c10b40307281382100041940240d0075404e880d120080502a0007255006154a4003100d100040f010708001e0742c098a102c9000c024001d05d00c0c180380c0c000c0e0251180f51000c0000740c1c44000e00380c0503140c04803405005604074160a001041482d003000061910052822204035142c40085c01507800541c40c1c04400d50144400b400007640003104002c401c0550b0f4010b02c4801280910040150f0380e0b04031108134203469802040400100070b10f083c01405114094402068041d0321200480d042501d080c1e2245600104800a04849210340603d068004100c440c555040000c1552000b43e900b4611406200d00b203040700208140e84100c10401282c1c071000305070b0501d0040c5030266070318003040301c18900e4203202131194404d41c08c00c0c11b20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617428687 1250 617427437 617427467
    0x90b06031504030c0311060703020a0806031f090804030609050606030d1e2d0324030c0b0c101505090a02181002070f0e0a050c071e1e11030f010b01 65
    0x4d40014610f2608417003100341e41102c48068400c040c2400240b607015009010f0488440c0c4d40d00641d0b607500d01c1090354401020242e0300305c81200034140707520700c03003940c001e01170441c0500411490140e036035440b24115882c0c02c0d800d0700d580d04a0710602070b46142c14051040400002d1400002c0c1c406110341d81e88c0401080b40045003440150352048109041e40c102409110107070b0082400e0082c1d842d0405000b604240007046040252001e050703a02500c00c030b89074400d5070742120300048400d0810f0000030340f40e070204917103a026200b00d0824900c10030003400781010659890300c12403811032800083c89510040a807042110340d0040c010210080c5c4170300c01c0e501d4a010100c400d522506210380c4140d013400d03d2030b00044496000c0540118100f00305441c80e038010718010100704090380e01c005090f8910f00070510000c2044020700c020318440c502c8100010401d030b000751480840d282481000c2242c102c0705a100312015244019903800514062000840c200300300002885920803980c00200b11203a512408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617429937 1250 617428687 617428697
    0x80607021b010804030c050f0a060b060a020a14070f08010e0606061204060b010e130501210f0b0c0f0a0807020c030d020c010507170f04090f021603051803030d090b0603150403 77
    0x2506041c8500007486c0c08a401400f5200407080e0080f00c0c1e91034030f148200a0320501e00b8041031a629051407011034407841450760280041407995070301c408981801d40c8a4001c68401d0740c1c404142c50140d2102035000b07000140000541081c2407814509190000b440644511401e2140702c4c03401900820541c1d1165011034001140440e820060381c6407110100515008084041c10840240c40c1e913001030706031602c10207200c0007440c1141640c5040c11503404014114140050420000703001150f4403a088014068140d080c09880f6041d40365035040b140303880300000c2d400700c11301048a4060004168061041e4094004d001502101a50b502e102c1035105040000001d411800c1c41032005034842c00b04009980c05954401841880c42690424010003815915011010200b00e0300c0f131081307030560309440e001d0610785001c5c0e88058425402c410b11010b4403461035070a40070b03a030703078184010124185501d40010701d03001d00b0700307040c9400308000f803c441c02039200044691440c50000c0d0711540c000ea0620705 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617431187 1250 617429937 617429941
    0xf050411060a301802031c0e0d0f02011704050c1210090f0c080d140f07020a0e19060b0706180507060c0b15010801060e0a1a04080607021b0108 63
    0x2c03a52402d00ca4901c0000c0199982c2c0d20038003510480f03840342c040c080c004061004034200f01e200c12032202401402076244c2c1c4111806402d244c241d100740c1c0300e0910241050070901028002150381080c071380c8000c8840c0c4107950020001c56070810800c518682760b080c03d0b0805850251343e115510030481c1501c501c20389942e044041c41c008104404904109610400d00c0804018502000d1504003400704840040f41c10ba40496011400140501102e58560b640c601404040c07400b500d469008200c40042030104004800160b140e81d40a04010180c0211032101c03803a08001d4581140b035a044105101c4d0304042040040894100a803190a03400c00c0c0001008000c05940c00302140c5030b50002445401600c1001910f907810070140304e0402e0144c0c0c162000c56444c00e048005ca8010610000c0c0422400030041c0011841040f41c1c4c02500c0300581281c82450700c44d2150511001c51495030b0280d0880081c0a1000140602440e5040600b0b40024000c41400641202511071a030030b00320304002440e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617432437 1250 617431187 617431207
    0x5122d09010b1201020316020f0616092301140f121e0103030504030605070306230109090204080303090d0c0312020c07030804091401060e150309070b0301080706030f05041106 77
    0x80100307050040103124900f042c60914a60303020b5003048401400904881100701449400403a101c100b162509002d01101d558002e0b5030315a010003601003104001c6001000702c0c1d81580f0b500c0c555500020104009103100c0700400040c404103052040151034682401101c0d80358001c0c41c01d442484c50384107625000c6035100c154003074040c0112660500c012400170000400c7c10342210082058a02078081800746641d40103055041d01d04510400710890704036443c4180300d814880005408103014904010b00360755a1900d0810790704079820040458100000b07000b00d130f01d000c0181c220f04000f1814040000f040548014110040300c0d00c802d9141500027602c030030342d400280403001c060f6a0007000c058880d921401040f0041460400c0c00130302e40003200002c100036004000010380088014291501022254060307911030f007014000380203501c00c50f003010442c0f003542c1010703501030141c0754000c10015182440007019600c6104070180c0d2145081c0a020100e4070300011240c0761081a141e0b19504c1180e00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617433687 1250 617432437 617432441
    0xc0507170906040e0a091b08010501050409020d0b070201150620121b011e061701150521011a100305070210020c10050103032601051e0d0c0605122d0901 67
    0x2540c000c040e401058810010345024000070420352345400007c0101340e8982040c4803c03906118400b0798807080048025000507403008a4582c801018400825600551418103040640c541c20200100792b1f1406003e1101004440c11124540da01000b08020707401d0f00404209445103400b03100c03441c2c095040f02e1800030002d400101c07013800048081ea603540302d0002ca1400411080c05001040c080140402d8903180c070500420f041502e41c20303407900f80c1510348410003070119210040c0400b01c5500d0f03841c1c404100e41c20310810300c00b00520001200b1444008041200b80314440c201081894645000d001c49903500088500180c0300e0b9100040c0d8441d02c143c041072502c0c88025401c81d48a08110011040540c0b000884000700e074108019020300110440d8044019002d02030f060304044844800c003681c90410904030081c40d00034041c881002c070309494103542c0030b80c1034000d0f8011820001700901c003161009019036000a0000c0184e241001c80c03100b464804044c1c0c0c4180d00781107202d0340403501c00b100c01c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617434937 1250 617433687 617433701
    0x11240406081803070303050a06060e0907260c09030c011106010506071a090f0106080102070206091c05030403030512010e01080307170c010218100e0a031e060c0507170906040e0a 78
    0x30b0308a80c1c42d2141c6260081c06404d080f01da1420503400d007640000c159000b003192960034100101120361560329510110381c0413203801140844000001131f41800c0c1511b6a00c807900030085d11155175a99411070003458a00040301c505541000449100341030913207400b10381b050555504507103541d03580038603061522030200003104440341d4005540078800161800200c0e03c0801d94000d00a02101741e81f441014201c0c003070304001a40001003000010a02c0c80d00c101c0c20007418030f021590300d04500032500c034989176030401d8004030081407000441e540c009a001088138014032400940e40059814148441d84a00513003400610880381d070313110210140c0d01201a920303150340c0720008545074180041c0108507005112402da011b28002c40790220454443c40160038070041c00307402503003141d203103554041703040e81000214190071000200c07400003e400c41c080d5a140318401d0381e031251501080d09080e40404c54078008440405003c02008015807035500030349048449600217000c41d581c645540070094507030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617436187 1250 617434937 617434981
    0xc12090d20240906070f06090812060409080f0304210512090c01080402190b030f191b030b120a0c0303020f072105010b0405041124040608 61
    0x1240e15025804140c68148510004110307291200c25510924541c0103401d200d01242101108014001c00784c20603200914070948502040e03001e082d45a25031008880d442c4000b141c41e101c0004420314080d00c081c003c20b07009002110204020b6940303507100c04045c4076101014800c3c50001c000070f4140500319400002c926481e0199442c0c0c492400c1e802171541c6d1008c050142c0d290801c40200d10700410000d80d2011000e4113031619405600c50307408000d21101d04111000544500c048042900c0e440100a140039400c2e401c005a454100945501c00d1003241d40351a1846031301e41900ba05d240c140340c0e41e280b146101e0506002035500c06040200d000c4800d2548004514880c0350140f80401480c9450030080301e00903803c2e00c0d112480c4084480c1c5402003482165600c0c02409840f2505100c203000c0031074014420400016921141c03804a002d60300e0456040e00d03e03003441c060500b03640c00d02c84400400c0301c1c950307030a0500e541070b00301d90507446010318002c0c0b40811400d04001071210092440203044000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617437437 1250 617436187 617436203
    0xf020612070224040b0402011b080f03040c0605070b072123061c0303150e1302040e010c1e051c0905011a01020a0303051b0d06050a0b0c12090d 63
    0x50019006951a030310f240c025001406000c214201c041c410b0041ca5006030340c0661a0482a1215001101e0003181c44960703d03506e0118140001c002590308009103550383c0c040c0724141d100c1c034040c00c0429114131181d014170140f0400308128000645540c2080303500004500380403408400c078046940807010541c0740e44464610340052805c548129010a4000041c80036809205c1e80d0307418148080704c5951101c601e003520a6204032000280240c04c1302c103024a1000503041d0190f905d603e40054003c041d56203603402080c1c201e1020941c00c0900480d0b80c290900380080c041041242d000900c040f208a0001448001c00d80c1c0d000006072041c1d0446400701e4102c518801d036000146607036401071203960380031104d66180281e0050b61030050ba1500880201c160003910030114691020313400383c1001010365202e008660762504504035101c01400403110302d5540068810306080c00c0c06080c264582000c141c03c442031151940d80007000801c40c9192a1208a00752500c0d0070f403021400d1038416402c0105404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617438687 1250 617437437 617437441
    0x5090a08072402060a0504030521100b0a0905010509030a0b18060709030f060218030d0201020a1b050d2102040e1501081501031d030d02090114090d0f020612 69
    0x51000a44102542d414240c401110300160103500c1c81d00841c501a4409078201c100000c2c1c3e0168140c3c41158018080c6c104180781518100c92001e0035106400891b582c0002e070310600c41c15a4030500d082001d003981380300c20786c6000201e00000d4a1402948120303810040001420501905c0030300c90300b0540d03940f0503560030143c2008080b440c03c000812041c1009482101c001070740300b600c24052402220f4001c3c000c0c3d26620f2071f90312440c011b0750059402c103014010b0b1140c0c0a0300c07a00e0070070030300d0305420700c80d800180c550500c010000c1c00c40c40c1c010702400b030b04405814003c001c5800801c80300b101103003909040040c1c0d9086c8449440b501f85034180d1100b96440030034000344001f2100c010318032480110007807440f1006658015100001c1c1510780c140f5106c0c0c4661990f010b54082e0b40004000c480801c0300702202d4114035001172039070340815141c01915402003884a101d5030001607500d6009207400c0c809041c0103088002c85c80210b002c07000681280081c0c50200150344818007100d24600410088041d18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617439937 1250 617438687 617438699
    0x25230d0e0307140606010903021e1302030702010f060e06060a110d031401050607030903110d0b04110405060d2a0b0d062102090402040f110307080f25080705090a 71
    0x30b4000784002d59400070a4419a0789048010803001d00c1224141c4a040c00301e070843d0240804603405038020804101c685d1140b103450340ea250110b1210320048900980e50f0f1070441ca0003400e403000e1440c0402c0c080d04000e0280901c4110300c50a6600c180b040c2c40403501d074402c9040131142420040224403586c0545203504030103d42c5a040440c2580d0405c00010140e45d0b5801800414402d0403400380c0050080d510900004006800942020b0300043c0074403502809600c69840400d400d41d022200d43c002c2c0200310903030b030504e8012503500c844100c62440c0c4c1d03540e02c0c5d01c426000242d0b802101e051090b100c003803000801941801100035004101c080764844d00c0c11082c11000782190300400c0710400c034410203c81c8808056145d241e090740d000d4040c01da10746981d402d0002829803142c1191031561100c82c22100020f400c405184920380c1903558108606210100707a03d03414011b40f40804100ca40004c4140c07004000f05801100d0f1001c2c5040c074219174030741004507418012a40000c1d4440e042c0744000501c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617441187 1250 617439937 617439943
    0x28020901030506011508010e04122109060f0c050a080907030803090a05011a030c1c0b0c04090b09101e0e150301110a0804120c0f030825230d0e 63
    0x1070701e85c06101401c04d07a1500714241c903500024415001e000c81c1e034a000400085401e6024465941141041808402d41098281c1c01440c400011081d00e565040c2000602c101030080200794800810100442c019048004045200b21000300c024480c0300c5001c02d031100c00401c800c60003541c004101603128240b003601d55844d40315075481a40c3c60b6003031060403045104103a0036100c01c0c58000300200001c0f851b100c02e004e40c1c00c0f401020307000c461001d03101d039402152403685460700c12111502c41c03c1d0341d5800c000145089554144440707001c0d1045000b006200a4104010300030340381c0070001c6c4100d0703071030781289441c0981c0b0703030b8001c1040b120078482400b0401010a040422080c000c43c024801031001c00c1815416010300400400010b1101c00400c003c100192100e202850701860034a524002a8540038554429818105e0000d01640e00b0002c12840c1d608124103540c1c0383d501c00c5d5a01c00700d100300c010040c085500d800f040040c0c42807002c55a021700c80c0112946c20840e8002031065010100350592 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617442437 1250 617441187 617441189
    0x90f15070c14010e0f0906100513032904080d0203180a03030e070e04080a0e030f030c060601080c0306030a0803180a050a0c1a0a1b08120709050406082802090103050601 74
    0x10200310040c1c01800186098602c0c1c403000d2074007900c902c00a07581c07013040007019032000348c9030b5090107010400703c56050304896460010354040c6c00d440c051000031074524408586503a00d0505030f0045e00c0103020025422004650b0101032200303002d6105c0c0c0312040c0d181c403c01255912a0502d00c00c2c5000581010707055084015043d44c038005a4007980ea03100d4100d490710800300c0300100761180c10071001443d640203640014821201a08450301404800d0140340781d6440f40050303442c20b6000900300849503034000c4841e0f900021a056460650411034046540c40103030080041c01e001c2c0110001c0c504103007112a2310710404035907044580c020b44c0e42c242607843e00c043c0701094139403500c1c5142c040b6458021010a040d0714801221070791034200322100864110700c3d140e1000f006050010884004103203101c0c041c28524403019914034880c1403100015000458070303400180541d051450808c0303543c030082a900107200d00641003480d200144207188a401540e150002d500121100011041c03100001d41c1078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617443687 1250 617442437 617442439
    0x120813172b0c0203070f060e010b0a0609140607121409060f03011802091f3605030d020a081b0f060103060c02070e1315050129090f15070c14 62
    0x3044400641040b0713282d20900001500710b4030140078810005229501001c1c6034180b0b003000142d00412480021000790039984400006080c28000b480b49240310200d88120324000c44443d481d00c1103503500d50003e14142c1012406102c0e468110380e8099601a0131540b510344020412039881d0b03d120250780715500203008490314821081103052122100c2d208407100800c2c001c162481454281f0060f651160b6103000b48800c10920107440e80c0405881400b0842e20803604510041926100b0340c0c010141c501c55210510036807111301401c0045070049920501550807070304042c1d07981c0a0ae82c0d00030022099544900e103074422080385000d90071000c54100c2c16648540b07824085141143c404903960540313809208922050302c1c000c920540115180101c3d22441440c004101001c01549041161026403003801003c96a41d03111a01c103000c0080d9004016401c42c201d81004d044101195141440400e4503008400c2104a89481811242a02c40c0d240e0b01055040c4140e854028410443c1040b110003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617444937 1250 617443687 617443691
    0x2803140411010518091f050423090304050613060f181401030b1801060f0507051c0e03060a060f0b18240d060905010509062206030506040c03120813172b 67
    0x846c076031600d4001c41274017140e81c500340450002004003410007034002070850061448100030003d03054854401030300040d104001c1c1501158500704024152042c404521420490301c5011201401c0c02e269a080c20303030f44c807041c0302c2801e258400016801003458a07441075002103201d08401240404185140c1a201e00d03903107440a044a01d1400d4401d805503030801000350308013209024041c851a0f402c0900345019160042c101100000031038103015080c0c039501c0400d92101c0040c80620712041ca090010322203041624601100e401c0752a0a00d11425841e078811140810380100c80140310200d644402c00040d40e00380d45001e80400040140118440c20490038140000007603285000b18601d0300c01d6201030904c88101c2d4000c40f080b88901001e800700070740c450359450040b010031010000c0502c80d507c204551030701e250450810100c401194440c8e001003041000401c004040310344500d404c842c4d807280e203401550400c48000329542c000c0464514625606603caa4101d1700d440741c02d0b0511044050007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617446043 1106 617444937 617444939
    0x3040e1909110108070c031e050c03040608010e011202030c15040f06020c041401120807021314060109060906170c2803140411010518091f 61
    0x2050310703204030542c402a05543c110306560703000500340c105030a0800d5665001084ca228128250040304106842c1c4807410780540250344468081000b80c90710385441d0b40300207208000c248a000d1404a45000019146d8851510403003c5500074001c3c00c4421703000020f00c45400503410a41d29811303001c220010f0415205480e401c054405a405026410601400c101c01d4641414030603600040f0000100718402c2c080b0070520b41203a01402c142c0c0c0307a011500000d0080c0f0356a04c00b403900682010070703100007584140301302441180c00b40c82e90b4401c6501c812080300d030080140610303408103204e0030000041403013002120b548407100103d81d518100c0f4170000c00c080940354804030084c1c0308040c40411100307501802008404107034071a100c0103d00d09034540c00880520911320314140100007076080c407010344515200741044009044030b10766007400001c01c4403000071b80481c51140c52403000 = true := by decide +kernel

theorem cover : BRFrame.Cov 617266187 617446043 := by
  have h0 := BRFrame.cov_init 617266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617266187 ≤ n) (h2 : n < 617446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
