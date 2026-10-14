-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2740
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:54.314702+00:00
-- url     : https://prove2.me/submissions/f29fc8f4-39bd-4fad-96d3-5436ff6810bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492625899 ≤ n < 492805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492627149 1250 492625899 492625907
    0xa0512090f12031e0403050d0c050c0d030605060307180506041d09010e0a14030d0c02030403120905210a02090a0605180105030717120d020901021011190c0209010305010504140f0d 79
    0x17900c503100381891800c1015080d90300041300c003007856440220b100041c203440108002c01200c603101415117828001c0c18108008200640400742000f410300544030b01540710b000328040d0844c09441d024001e1501c40741c0d00c000c80381707078051480c201280c00700c3c071000405d003170306418021600105603400060400e60300c550355841400102d0307601c269641c0030901800c1d0345075156015009078941c240d4002c41c0c8071410b40c00c0c074a2646100c01408024420702000c204410b0b181e120100515079000300c0340000f1501402a4039040c1206030703a000358800d242104201110f86568002000e84034242d42ca689001c51000b10220190028050151305230b021410801000214007000d010f000005401d13105c034500b40040e00c00c1c4580190108500c220b8011a11840c00d5904001d100c02603c08044184100c810810341c65840d0f200301449408030f00548019420390314098180110000d1b0b0180041d0004c0da90303414203500030318095900301c0d00c42c5000c401c030101c2e60000003203943c24400071030040c0c02c100d800510280d17 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492628399 1250 492627149 492627151
    0xd0303060e090a0b0711010219050c0d0201140a0e150106091d01180b180106091d15060918010305070924150e0d0605060307090903140a0512090f12031e 67
    0x801c00d0341d001c1001d41c030600e051803105036581c09c1c5900c0703107520b4030300000f0a02e0174103400c0c00034081103a150990003c1c50030714204200c0e800401140c0d00141c200c0903071520034241402038144844040c44880001807407544503816600b180c1c60f01440044401442c902e40d91a88028450001e0032138022041856000140c1e1015413804401014606007601141c83d040000400f6400240880d51100080103a0703103090140500e01d12290841009600d0260780024001d42c00024050181c000821100c002c3d8035543e05031a5101c0141030309160540c0d4034a01580c1d1030b4401c5c0030314103082d410217040f14029583c4001460071407a1420800c41c90341d0030400040310b4211450940c600f0403c517003400303000076200c0c1e9001e181d01c14050003008c0380303c0ca07051003850310f080c02560007803207074510f803a00e0080401d03440584c01d01c1d03030b10340740c11000e6035452a20340460311800360070b1112034076070000414807400c104002400c4044480ea20155141995102d09018881c0411174520400481085040e8100175081841c0b03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492629649 1250 492628399 492628427
    0x10e0a061515020109020906041e0e010f0f0204031419060203060f04020706020904060e060102100509010b031f0b0604030c030206031305030a0905010210051b180d0303060e090a0b07 80
    0x9000e059a0740d80035120844402d0802c4000742c0d6440211509500b88112600d41c400130030354090040c1180051402014500f10218440003640c507130420781c18010a4200d0400184405000e010b0b50f114038032000000e5009220858446160030904004c2c07090119036042d04601c000381c0102100c030a44c58401c041d500c000d1140c3c1d8024016000c24041d0b030780320710185c80c41d02d01424006880d4000802480200c42681e00219007281c0c0d07070f00400c090f40e85d0000c1c01721b01542401c0d070046119211802058050a01c0d4031010b681401605107a4031564400410048003154000040c81110a0b10044c0441c4d40708500010f401c840001c041400581001c000039031304091600a0402c1e40d440b203484460a41d00800040c2000590700b000c10050f540e4108410419403d02da80204454202048410301e84461001540c0030040c0101e4401b91030001072030303254045407000c0c00d00c0b10340340e40b42e2600500404880c040c1e00c0500c1510401b103030082c54005568030403103601c00c03407160844d00c0d07400382034400c0ca806c1c800d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492630899 1250 492629649 492629681
    0x7080415060b0a03021803060114010c0f05030403081e0c0a02040903020a0f05030a0e120a1106070b09150a090302060402010815060c01020d050c0711100504030501150f0503010e0a06 80
    0x100041e0940802c0c02000c03503143d1030740c0041c2c4560099070000d0301d02411800c042e00c03d0703128400500a040e221811000c1402090801c141d11107903514140e56025a1000050701c6400049800030501400030000d1075803030903000090341210026a69038100f8080c404940c02c90b548101c0e00080103003450752040d0151402401100e13901c2c81641e0300e03000750f0102d01c03408507055003002c28600c4516811100800500380122210f060b4104034134401603072070408c030901900d442e14500e00701460f0389500003180c03607082d005038060001c0d2808039091541ea0100410610b04541000001030303001038188a005c070600c5d459405051039403a55001100c01207005400c04210061340e00c100c1c8407560340c190042c0804034092002680303440b1a0429002122001007200d0301c001800c02411001401c3d81200342c201a40407229910355015a034400c40d001e01032600028065840d0068981f544403805008400315407002401103030481d140c400385401c0c0e41140b00c01590395402906101c1c0001c0f442d420059070f518107150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492632149 1250 492630899 492630911
    0xa03140c0d02070302040e1203040807020f10030203010302010f0507150b040e07030606030507140a0b07050c040207051f021c050603030d05191b14030a1401080313080607080415 78
    0x121641001d490140d07900141c1d2246a04200f1802c050041010402d49403019040409154124124a1200500042c018070000405c0800c43d130b83d01621441694028140003000c81d05500d0180003548203020a038040f900034410f0904491003001140d0b595580080c9100c41c1404440400b03014212807107001d079002d501c401260a140780e0400c407601c000c602400d0045000c1d031542c00c0040c14460749400507810411800c4103400181c8a48580104982880d901642d44503400d041060902e4069005030f5446070002818078203011001a007540505481c1903230114000710120f402040303116080144159401c85102000707889015800654042c10140650345040b60907201c580444000700d46c409600c5034803802e0295070481e240700da0710500c13080f1091b00364012906400646419018100780e44c602c0e600000141040415400c1000035400f20205400d15507102c140d400e4482d0000007804003a8400079200090004001030320318001c40240e25100f1854495440d00d0b000705203148507115005072030704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492633399 1250 492632149 492632167
    0x6050603072102011403190e0705031905030405090411040e0d0f03090f020d1b0b0c030405090a020d050c030714040e0408280302040f05040903080606090d0501020d0203040209060d050a0314 83
    0x24004522890041d610701c240c000003540a041100e01950841d010f56000385004e2149860003d330448000314034030000c3d80d8402040c07800a1440c0302eaa0481174003c1c0740f1105000c2001101c0c0c80610350180704070703020302c2190200c414065540780440d00010010b58030041a02155000b40d100a0f0f503a405900e84000f201119004214039950034042110388200482c508480f40c0031031401748020300101e0541c85e282241c0c002c07201c1d41c0d9002e40c1c00b40074821740d1007002241c0b8003142941103c0a01c1e030220000e10461806e0440350080e0b4008a51440c0400c180b0303115003000404041c00c0320203903541c02064030700945598580202580000700c84404aa6500ca0500501110031980214600c3c159070f000d6621402c4c688840240805540001e0140d4200f046100000b42c01c8448c00354020b00a4410a45515000001803002c006501d80642503510001d803031008200141c004500c654000c2e5a844801d03192642440301d410b40662005d0030341d0300041204d42c0028031400d01110544910300c651401c0130048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492634649 1250 492633399 492633437
    0x1927050f010210091a0906010b0d020d0e0d03090215070b010b160218041505071d0f040f1505190b13090c021608060106020a1b03050109030c0605060307210201 70
    0x20f81550017030a4440d81c06007464103030400c01da105e40c1030710281c0040d51501900800310700950608002040e004128001c0481d0241c0c0003018543c00e10003207034610721000b000500200400744090b0b000301300300c2c902c03441c248858000311001a98804e110003031983c0391041c0903c03350025501249504ca41076142005643c5080c044820b40c1c40504601900d81880e20b00050408801122620000d081c00c0821840540211541084103040c800b2000c00254620001d07810030001c590791684140b9124031078007030001a80c4004503a5091207040d03505207445000300580040d00c0c2c02244500e010380b49080c4980106400605030006820550324111600d441981c8195450f966100005030703c8070074210000507060740108010201c0101801d059410948020f40f00c0c48950006805003100003d540010400e01040790000c50b00400208030707840b0ba03441d0040500b1902ca1007915083e0030f2034045121b40c6030104900b81203c03c18010440100d2807141c51446090700030406906004110103444100440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492635899 1250 492634649 492634661
    0x30f04030503031909030f08040c090e0304091118011206051509031603170c1e010b0316061b14010f05090d090f09020309030f1927050f010210 63
    0x201d903000d5030322031070410038221002054500d403003809401c010121010a0304002100e00760002890701034541c0ea00c50921070204030f0503a01080141d0b00d4200c16100e4101c000c4003800c10fa440020701402200c0150700c1054480c046e28100560030140034464101943c024600c4a040321405180131551540c0d603c002442101300440302441c141c0002645055480c051081411010394031448410032811a03c40e482002005c078081e008818002540054003181040384140c0784c060510b82d00c40703c108903800320b4040c000c2901114002d1040d0751041800f81c4250300f01500b5a8581d0f520003000c103c1080c2000c00c60441414199800101301c00500c100701d00a000e03400c50040e83c1507000c01c807420190314039803800c051500400100040d02d20107018407140045424100c80c495840075071640c507901c2c0030030705500c03c60009044100000030129150388031100b91005030ba020351034201c070680002c008204445030940b0070280202180d00240b01c03c1c5851b0708503480112062044910901e0444090011144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492637149 1250 492635899 492635903
    0xf071b17070c0608150f030f0102070c05010806010503012103030207080a09140f060414010219030e01021b010c060c0e03070308030103120c0f0b2503050a0b06031501030e030f0403 79
    0x40000d886050000b595a0803008040d1442c20810914055800c2c030701c49541008820b100d0214400c12103441e69040150f00400c014003c000c66848007113151400b16400c55100c0d540c0030236038038400601a0760050040c0c9048508856180d4141807280550089140703002c1c070110149582808030001264441015080680301038851ba0040c13401c1a50369504880b040702c0040c800c403000c120710881500c860060700d040798041d20510040c0c41c0c0043c0181d003404400e424090040d138142c5504001c0c582c2c4040c203552040820303029650703450003000741c98201500b280e00b11400b1507606044440050751603848005c001401e8900500d4825174000002e042507040d500661310900044014001e0042c120060459540103080580305c2c0304103940c074003280b601e0301c0030058481810500092401c2c2e8464245143e035202c1c109000380900003451015000f44030070b90780320400034a080042036060900208482c0078858254601c000090b00000441c040d1003440d81d6128140401d100c00400710003294081c00c0994 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492638399 1250 492637149 492637193
    0x403260103150e030f04060516082745011512020703140c07120f05010b0111031b01270b0906040807060b120f031902060f071b 56
    0xd940c400350605a0f900100b50311461307041004500b0a98070340504540480d061810901c2d107810f0b4140440c5d407080103130600a0700690000804100010550b1071044031000c07090aa130380701c1c40d4110f0602c400030345031a03014807601c01501d000032040c0c0240d0113492208209000342070113850120603501c0c0724400170307407041f212101240701d10860290400c0c00389400c012001011030504826482c001c201c503040200b0b00034207020003d19913146001c184040c1d800b4026000c80000c001c40c0c2d41c40c3c5040089482101502d81e9481c0030140e403030a62080c4030381050649c01c40019801c2c1200808180003000241d511540f1665841c9520102e46508a9031010602401d03c8076441411072410018054500240b00b884503400050401000480500035905003d4003e40000341c00f1040c00b0104400e4602000e0f0840c40d80300340b001e27a02c1c05590000090849904601c41d01300030013007040041c0d944140545241e5400b10040300044c0000780b080e4610420211a494011146642c0744c680440d0344c4d96800901680c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492639649 1250 492638399 492638423
    0xd030305280e0f060408180a080a0b1801020c060a150905041112190314071a0907060c20150a020a0c06080402100c170d15120206030403260103 63
    0x980b018800d4800b181910006004140340c80d684108030f0b0301c500285200740c1007054007201803944031015041d002c2d10740b40e0107e80d402c034030301d062040111008072002c40340c4900c0100000031090040c000e4a805440410050109444aa141d07001070f0468240d1a8004614084002130f000381c00d01880740514000d28851400d40038220510040d00b48904015116501661589500414690400f003c10f90103203031a00b104020b40032646000d01c64140041e245454911441c09861480c0c80c0080c011909901140c1c8200d80d20042601c402d003503440082d018070010380070400742d03491040c14108070810040c004040c441030841582c1141d0000406100141c0c45000580d080211a9000c8409880c2c117050560041c0340c00d50018140c0c4075100886000c0101e4811a60300700000c0c1004c50716070012110700f04d900c03045044810303402840301c4102074146140a0600041841a55800d07011864000d02040e01d990f8541d142079034134409040c03201c5459a030101d2606e403044000c0303880c00d01a40c800c1c1004003c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 492640899 1250 492639649 492639671
    0xe100512060105070f0b130b0c0c010b010207080c060315040207031736070f170106050f0d080307021c0c02040e0601060f14130807050a12020d03030528 67
    0xd0040280200d050102c02c200c82c1020070540740b454007060360300850014107580c401e0b040080c03100400100411520668050243c034040c800701a000c95146100200050120140120780e100214490010f141d0815074406c1098102400216480f07400400014108071001022500b00c0e032051a060f0002000d010040f030000c0209201702d6041030001d8401c00045440b04841900340c00490500d0b41244c0a2444c0b07864000014880000241202d9850341205503030750020704442c40880074822115464650046818a019402d40419a0024003e015401c0c15603440d82d00d29031000e0144004e6200c0c04502c0401d80f2050400a0740c401c105075980d840c0200340b0310502040d15030300786481d882c03900800010700c500c542c0f00f50020b040059500e01106c42a0000c03c104050384501c04504440348100c0300042507918001480508640702515007040d06aa107480c4441c1c0808898002980000d2001c1d64070003281c401c0c0c00c40342d004108030b00d018002c0442510320160180184140b50302180d299000084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 492642149 1250 492640899 492640927
    0x2090604082d030a082d011715040f020321090f030303130605071103030103060603030f1806080408091801030c14130504030203090312042903160e1005 67
    0x81c402c8151074656820b50b403002400c54481c068410038004100c5480005840f0864070001300d4000c0b68101c80700039802c0c051031100c0310552000d0051031046a41d07519543c442c0c3c41e0001d5010b200c4000310b0740301d01194440d0740d03480312040c0003408240d0b414410500022a4105881e54509202c90000c510303d81d10880b25050041160314001000e10a800510400030000d00400d0200c00c11035000c180014180c0e2642016035190f01c40007030a40c11b0384004000070080152a900500aa83c001d0300d810110b40ba0b9658100c4103140e0081c0d844440308110310f0200402805900015041403041c0c1340c0c18200345002c3d020030380d401020100d01e0620b0300c40400400510074200b101501600f2461800910002c1c1302c40840d04205401b1038102001d583c41c40001c051620070320a440011170002c09848080c248405850401e80107070082815500c46202d03d207034a21010021900140c5142c800c0c1b606540d82c0661500145e1a916100d105102000d0f60388802c80e50303a2550414044140e0311031623210f83c03103012400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 492643399 1250 492642149 492642193
    0x303010816230d0819080406060509010303090603020309010b040c0c0b010e2a07020324152b0c18050a060f0e091204060e0102160e010b0a02010209060408 68
    0x1880c1d032810101c80c140103001642000300000000d0703440024501a13450007059a100700c0702c0c10705251301703401c04100341180e004000314000c2e401342e08240310341a00c4001f00038002400384802804244101070410a090203a0043c6601c665110f0001800107110404603040d01d400e16050000507460120640400244c420214054501c2d200b503808945000540c000d80c001202032030a4004c0074504103040120b100784115400703554060140c80c5100b00b409041144400580008005040220000303010210207603181c0860080040c0101c404884a10703171400703104a4086022b812500481505000c190f140210300001d00d9107408003c980c481603a04982201c001610f203180003401c2510401c0984189100c0f00c0584003420150082c603200d0b9a526443c0c1001d0000500c113545001c01d00041045d040304440ea0094002c5e000d40d0750b101d00b18000380c03140c58140d008452442022800500420155502800f00081e690000600e001e0008001584540059000704019481150024035040b400ca03201c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 492644649 1250 492643399 492643409
    0xb0f04060c08010602071e03171b01021801111c11010b0609061b0307061a130b091f0b0403112409011d09040b0702010c020321040c080303010816 64
    0x41210350520300025292a154890403a2a41f504070780661580211598400110307400b05c40300020308101d21000035035070400441c0c02c4011070340e0305014000d144180210f4150050190911352008800d13001540e840415003d0055548200b81d40e903400c0d8400204100074003841c61321a41011908129003e0a40d200003c600380602d0042c4507d0510703485250035202d001881e109040c600050080403545180038a140103840f4601f444030000c500f8216400b085034080095034041124500d03219000155662050843d0300014040005014101c02d8942805000030b8a010003a8080d95810004500e030010380041d0f84001c40560708140300c0c0b5041038009111260040c0082c4120100218050740740580780ca050305002545400e0810b10640c0307400c004038248014a14546410207007411b503441c00e42203401c44050761030300100c0801c040c000015505080151142000000c00130340810484c8a0090400c542c00e4504a0020070390505c03c6c8095806006080700130305d0010340035011828590750075488 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 492645899 1250 492644649 492644657
    0x170a1506060503040206220b0405040f05012706150e1009050108070e03010902040c0c051203131e050604030c11010513150e040c090608100b030f0408070b0f04060c 72
    0x401c1280e02d800c881035980c000c3c0c040300c807540c940c9844400940c001c04400c117104464402d044002c1241d00385440030f0400d58806840401140c40e01c008440f0031030f103003030080c510344074481c1c1044c0030100d40d201f0592030804010000800c41d0395941d4003268445880c1c03003041c40030800f00409080e96061100400135403260303510780600c2ca01d20707110010f01040005001c1c0300400440844403085078600750041020140c1c09003003000300b40b41e0444000d10910001c07078212542d00814206250f010310210a590240c10360760440c4807040c2c419661700016465207504248240c0901c1102c001240c3c0620202c1c0c4110b019480d060354002d29880c1c034800648210f000203041c84824015030700020300404829081c2d4544500c132400d651004201a90260202c46466a115041100c01c02c00b070b40d0b21002150440c0c0180c1c9070141c5035140c0300c55842140300346004000030140140000f8181c4c3e6484803401d038100380036603a040d2810000b9210074124083c121a120340600404051004000144c40b45005a01c041d00d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 492647149 1250 492645899 492645911
    0x20f0402090d0f110a0308120601020d020c010c11090901090c0b0a0f0305060d0507230102120904021b1c0f1d0906131d0c0d081c06170a15 61
    0xa41071450303058054400e440746941c81082207015895551440300040100031110b951f0f1a00c070a41e43e12040a058802d400080410071550000807800100006030700645141c0d240b0100444840c0c442480a442e052013140c20410ba688611102a029800040010400600a08044003880035130b40c070807085c00000b00080202690711105c07504080c009840c0200e01910350340c000510344410050084c10078028030000041c4c203180000401407548207240041c42c0610840d005907258405544e0b0010342c450100100c0c0030354031780740c0e0050021003460081c0c03503c000e100d0300ca03051a00d00e0000c040c444c00c02004000d5051140c02489150a4206a10384840702e56040f4910203440382541c05498081c98480300455116a914002402c2c00da00552081024040713030382003010a0020501015110300400c5060012410402c030003d5055821000003803170150382001020004030241d6a241407642d81d80c20100c0c540c5c081e0b912150060520500600103581c03241070010300e20548100e84003205140c28 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 492648399 1250 492647149 492647167
    0x50a0b030f0a050714160b0705040302030703170f0f030108010f060530011a12032502060706050717220809040905061608070e0f040903030b030105070c020f0402 71
    0x80780e060b0344085141c0d000302e85034803400070581e012511038a101500701e9000c1030701620301e0920a604c80300d660184101c0d01c41c5840d03001054805124a00010b500350300b280c0401d201241c0c078503103003440c4030420490403840c0c6000265103500c10307082101181300044002004102c0a0000d000c3c4040880701c840b070401c02a4a03000c0003c51b031509042e000f146144501001c19901c40c681c41c001030070b0200d444007c1c0700705100c9c8150707514030b0100c1d1102c5d2032080c80e1940d11407501180001c241c4002c01c100c4450a02486402c8c1001803c0006028040b81e101c6010808a40000c100c0d005040c0187c0c401e84461840c0b40401d4403500301d8541c000c01e01c03e4a010004000c4010711259441414885d4020f01c030300e80d407964450042409001ca001000d4101d2055105021502c022182c0040e00004140d456031000d840c0c20740f0441d10682000c003d50350212810051080354500341c0d11110f11940302c1d0400195030101c90700801d003034480464180d0003280080d982c003002c0d820240e944050281017140e0840c41e1215003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 492649649 1250 492648399 492648421
    0x5031906140418140717061e04080f281701060e0d1a061e010e011b060f050a0b040b0307120219180b0405060102060c0a03060b040f050a0b03 62
    0x7002850b4030039030303d41c8440d00400f0b40ba44011000d082d0440d443c849480f80c1c000c1380507650074441c410781204c048040042c42c540315000c41d0403401021a2224480c480003003076010546004007078400d03110007008200c180451070b2444018480c0c0c43c440351201c6c412908a00c110340407010806222010300512440440c805002000c005041d254a4280008514044408a14061010b0400030202d41800a0050518406c0101640b06510480e41d50390a020b000500c81c0b0340618a44032180468490381e650038007580503048020f80300010405100d0180c2c030907203031407040e01c206001c00c42c499580c510038030520321118043d00031615029207060103200e20800109603111720300d2259401801340f88400404555902c00400301e0403a02900c076440181d190343c089001c8201c0c0f1840c02c0003091070f00f603403001c0c2d07401d00c0d000b041d214500c160040e0a86ea40e4003039061449a005071001c408250340e8001c085400641003003d40003424104c00c204c8405801c1906106040c01300340c01c00300090034184100b1001e02c140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 492650899 1250 492649649 492649679
    0x3021809060f090102090d0804050a05010507081911010207061407020f071719030905090a18231501092d0b0109030605010b0306030606100e09060f1005031906 70
    0x2400301e2294150383c908048600900030031700e14039441080c0c100d1040030b214402d005082681d2080740d554142030340d1000191542d00c200400100260780c280322040f044640402c000f801c9c2d06050074103080450038204d030203007261310881c81200c805540c0c042c4240034a01940100d54007400b18002000d2280031501855940c9015215510004120801c001042401801800b81e1744242c10006c910054030b619000d04400d81600801c0d00425104001554440050140c105144649400c0c07460041513519944000401e4410f090400a58102924040401040460324440d03154115242c2c40d414941c07a0015207506480101b0403003000f05020302c08000746900300b01014414a170000c0d95080c81c2c00103883c42c650031341c0060061840d19000059400150001f144241c1080301034030503070383e51b0f1820002c020192055000029500d200802110f080400246170082c10003060b01c01040d6001c1c1c00a548500c4580e041d0f400a40084240701b50303000c490017448071110034800c0c04c0c8102c82c00c01c2d401c080d0f0304131 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 492652149 1250 492650899 492650911
    0xc010b0603060a17160b0c1207030509061e0c01020714030a2a0503030f07110f03090132070203160311130f1a0312031e07021c08010302180906 63
    0x920184c40c02601040142541c00600015658001c40c1e581035801c4207500205140010b501542d540d070a1550100790466840d1030345a110700d81001c100d00144142500f1041040000c001025580c0f00b02d41c5820019040207010311001590301c40e91868994015400301c1c40c562a2034dc0244651503031243c011000c0b4501d074648000300703030382d420403907030701d040c0700004148050480c4c0000010b0100300c0c043c94141910609458441c074030b441528114065483d4003410300004180c0041c01014036a610843c448208501500c44001c40c80540c124101600500d0303486d807803005140003c0c01000c5060902ca00521086903070340300b0301d41900d1a01e490f814031149961040c03007481a8142c40d8030884043c3c3c8036074000101c2100400410f810f18108110710401c0d1460240700c1e200301d001102c040341100c41240c1c825810304142c0440000da4405032140e581021b05060301b540140e100c8864040c0801c0080101d00d036950343c035070105514500510240303180d088561008089070004202201900149154000e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 492653399 1250 492652149 492652169
    0x140108030f07080f03070314062707090815011d07120510080604031215050303040302040b010504080d2102070f02101e02060a06052416020d080c010b0603060a 70
    0x251480c98980458842c54104c910040d0010051040c9030b60b1503032140061b1600e800c011a4651124820010283e0100d404001403541072000600303410580c80710305400c80c0090601c00c00e410f480714603407410003481110016245a09000401c1002003100d17405e200302ca10102c2d03000c810f04200790002c1640d0340409031000740d15214400b00e1540d0140c408141e005141c0542501c049080c0341c03a009007840415403020081c50b0500751308100d004a032159450072604000c00071032805103990700740000f40c071013140180d06001d0184000520030105002e481c000074801d5507400080f20b440c481103084104100082d080543c41481f14000203881d0080c000d5007950101c42090791354175515011245007284a80b05031341e00300021195020250001080303809202941c0c010f011483e02d030740500c1124411901c00282d0b404000b442e102c0b10106460040065003170700180c448040740141c001c1040d01e00161070442c1c11b000b0006900c402101c0a2285012940044408501d1030421000048821006004a11400b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 492654649 1250 492653399 492653407
    0x30601060e0f0a140f0415051207030506010f060215010302060a05090f031207030806090f13030e0a0609140a0e01051306080f010204050a08120403032a05060901140108030f 76
    0x9665000201800b218018101c140c902e440715206101c1c2000220041e02a000c5a920261149020b0180d01c0640b0b50070a400a849442d02c0200300c00840201c005401d240103220003c00030032024051a0701922030150b0700c0034543e280440c0280303840d85120034012a240760100510050b542d4100301d980d8840e00740341440d250350865000521048020448507414465011081032106262002d016024001d88030380344243c0d40c09040c0001e0b060211610009400303d80c00140381c18100100300c002e014080d10304002080401c07004543d072403500da00064086000c4680c02c1010040c0103060641000003551030a680901d0541044414132040c010548240c4025400c0810310b0b07031a44c085401007644904803800c084034841c8080c002d61050240a0250781c00c044003044c2c000000414510300300e00d03009014034052650b10111014100c00340500070b0f5001c2d00c00d0008807113a4000c440d4045a0092016009505000d0f00c80350860f20b4030b82d51198080c00c0d040040081600c08000c0e141e40110310f200682d62 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 492655899 1250 492654649 492654677
    0x1080601050d14060f0612010b10052503080610020f0a0221030f36040b041b02010509070501020d05040510021f050103020102070b0f16020f0a0605120601030b03060106 74
    0x34150751445440c03c40d00c101d10400020001840b00036001d0b002c156258003060404a0516080e5005d00d03c00c0da4010680318000e4903100e03c528005c01782c1015903000540c0ca0350f03503203000d01c0030000c0f0083d054000405070740510802c7d180188030b04180703008500080c24011180c128031501d5401164000e4450b21002c4064000031f1140300341c0c20070703881070407082c0c0380d03910120f51420340160400c030b03000684428451005042c0742d070140e100190309142072441621820f000340070440581100d0158036000342d19600300c8541806911300b00740f0075007041e8001041c1e52400b200e4a0303240c00f80d03a0780201c0c110351141041c5172036070b07802108441c00c1d1801030b03d00004040c050941686030400301803111102c0c01008882d000841c0c030b01e42c45607060301d200741c2c2135620050b030b02c0900500368001e8001b02608070008001d111140c242054a0741203a510117000e0b4408105803e002524407040c56100b100406e5000038540358600744030382d03581d038888400d003070801039610440c000c02d40e60101409000700340030f001d41c00820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 492657149 1250 492655899 492655913
    0x30c112d060d06080f0d02070503100f140f040209070906090b03180304060f0806030111030f1b0a0201061d01060c17090d03030e160b030c092e080f01080601050d 71
    0x16250302e81281404140c1d80c1d10304059865440c64103610f02d40c05500c9042175503510101e030600c11200d006004144001004040400030303c90754141c0180c081d6038400f90f100718050030103c0351246101030756902841c41c00c1d0040c40f441c0000208204204001e542c0c09100e015000000c0c0c8003900d101000c5513403a5030380d220907030710046000c001400c00b5100214000903101e900040d00b0200509940c0c400d070740c81d100d07081410309a402c000440c0710981d8080c00001e084074070740508a540507007400300141c00403035464071280c1c140c0e012400703410061351100e01c1806520000001e40e8290900702d5a001da856142c547c00030084154020010200c54034001e0410041203d54156440007000070000700c0741070441c1c50301500801144621103801d0050344a80c1d00c590303180344030f05001c452080808615590701e850080000380c1c40180d4280c0d000c1d070904002100340c5814801d029901014421204e0850300501d03029011441c0100b00e002c407042c151005116180c00482e0030350440d40c0a40301f80900d60140e2410354 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 492658399 1250 492657149 492657157
    0x10e04090c0909050c1203042c0c0d02070209070306080c0f030303040f0314191218110402041d01050901171c0509040f0f0b0406050d0f02011b030c112d06 68
    0x3d500c1444506003d000c06c0000c00140121440c504289000d00007403c3c3d000079a0001c0050f00c1d1710584610000344045080500801c3d00c0c0807220801481d1000030350018000e160140c0700680041d544040601038518200318584101d0000c4840044c440c002c500000c1c4c0e02d200c018030040c034280c01c42414a0405004948103154545900d640d5502e0b501d8103140404003102d81c03802c17400012650101c1d0000c100b15841890145d00780307400c0c01103001c079407a240c0f070701c02c4810f02211340c0d00650308010021f08002941e4072080e103440766040d183c505516000c200a8800810f801441c0410100100c03854480c00000d83c18261448150103181502c0d04100c00f603510b805003d4205812a0401c01c7c8110816426400002181d070f04d0320342080301044040904c001c1700d02034050740c1d41002880b1400f03000300e901c40c01c4d140b034941d03c1403414404100ea408140007016001d0203003200880c0188082208005181140b60498107043e0b401050b01154500070100081d42122003d90a5220201c02c08040d240c400c111 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 492659649 1250 492658399 492658423
    0x207142805060c0105040209010f0e0a09080904020711030708070f0e07050d0e06070f09230406090207200114030103020409020f0303030106090f08030304050c010f0c17030402010e04090c090905 85
    0x343e49680003526018080c0408a07070880c402d03d40c08002041c0000d01d11100300c10758180340044030b102da83d0600840010881548152003080080c0580d102c41e50b1180001c007001c0344150300785c0b01c202c0f8000041c1454059960003100941e048410188060041076401c0000c4800000c01251142c0f550a015102841000c206040e01c0c0e060900081c0c48000000d03045009080e180c1c1ca14000750603802c811100c200740d900a407a401d18591a00d2030401d410f0008002940c00002c00000c0c4183d079400c6040e00300d03400040115800c0050f030300761420101165042c05c1d4402d50a0070900050060805844e01c10711050000a1203a42da03103801c80c0035134a910b81c0a8a210f40043d007103e03035030758541720082c0030b2864074419552900c516850210782c2c80c0740031003540c3c001d0390312800904042007220019070f44040119999030030465404001004034819101c40039004000c5803101d6642e05060000408001d10703494198080c900b42000080000c10061061044034103a240000f06150b8a150aa041440004030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 492660899 1250 492659649 492659659
    0xa030605030102071a06040e060c0a17090703050d1b080c031e1b0a020a210c030c050901080c031b012001050604050610081303052101060207142805 65
    0x140042201d14181c118401d2005e410340510356031000200000e541190800f028075800a60110b101c048503007000d03201d1202c4508091002c2d540011501c805408121520a40c0c1d80c0602410814000148124900c0e940d480c03405214410101c061020451003805000b4247d2030000740703410105805009031501100d210b50500b081414100075843c40703801c200d5002105492004005002640001b00c40250607405070180590501c0c2250f0202203e00c5090b0440040e920407080300001b0794a20440c102a41c4501c0c60b0b40803550810003400b00350a0305800500855105410400c1142d900080d01540107550340d004288082400c80101d0703c0b10382a03804007420b12112010a410403206403c070a2060000392401c1046503a020100041101141000b4021541140219a0141074a840882c4a40c00f1341082890540a10b01050006200054045030505100010b0101e85e905004410007489589421030b02080e2100000303506241540b05c596103003c00c04040152680d202c50000020710740108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 492662149 1250 492660899 492660907
    0x910050d02130302091005090c0702040915090b0c0f180a05060c100c0816030f1401090902090f0106020316330e03040e0703021b01050c0403020a0b120c0a030605030102 74
    0x1d40342d1680c0940c007040380b0400c0114002444460504094000c0302c00050103e203443e1103007480980c1d907a103c1c1c0016600651142e81440118041c2198103050703074000440041c0440303007403d0841440320040e06812150004101c0038509044200c140c1e050844c054426803401d01d882000501c0d294a01e0f0300c003640042020a019903140c03008150082c102c00c8210b0f080c0101086003170100c4890784104d0b80d2000c01040c06004003a6144a5401241c00c501000340c00920810281c0c0a00012407003680652000c80e01c401150046041900a0039005101c405114519504140001e501c0340610311390b00d4131003201000d080c1c9c280800b180383c01c0140054114075084001900c4e00030078500d00066009d480b800c4c00d02c2d140d022540c1c00001210222151011040d00f203464a42c0c088011f94482c280407003100101c520a501c510744c0078800c09001e4444c5020a9942c2ca00d14411301c11136070415400b440d00d003802031000c06130186900504070303444800344d0026540d48038110320917001000250005501984042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 492663399 1250 492662149 492662167
    0x160210120609110f0a09171509031e031504050f040312090b060d1703090c120d090504110909160212071a0903070506010b03040312090312150b030a050411030708030910050d02 77
    0x1c942c84641121000011481c9d036100d03402c07075a882c07190306000c0c6501c94640d070a0741c48060400c1c2c00307180c21003956002c0081184880000030180d4006581040e45100c0f90001e000405030041e00c13036040c40301d08140038400b0642c56151120315441c01000c8602921650f9040000c100c0205604800d01c2c400300007058403410041c1c040b50741c1e00c014226080c058500c0c900071040e1f0881c00100b1614000300b566558900ea42000180409080c214071600000343c020f10070000c040d0740311006603115240443c0302c08800f0340c03040c0c0b009281c004203250310741100c50100b02a00c04151070041030100b0307041610b044101e60703c81d6009585144144400581140955400031600d907030010700031801180a60f41e010022003030501840304403140ca46008012400c030f1a41001c0d0000740381c0028014083c00140104410798865807052154800c9404c424100d80d2402004204042485214965102603000f00b0010b401e21402039070342e00c03d400314944a102d0210700c9442581c4503100f11920300b840124250340781c2d0745031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 492664649 1250 492663399 492663403
    0x6020d1b082a16020102060c121b0c0f0c010305060a08070905040f022e0302030705180f0406030501050a061e0b1315110609010b06070206160210120609110f0a0917 72
    0x2003c422030041c000e020104101444080584a00031341048070941241c0781e035952070340103c641c5000c590703513650180074401400000f849980111401c0c04090060b0040001c0010225000104071610901031f00c0300c14044d0460004203502500d4034110300061503155030801540341022000d00a40c40f4020700402d4a507006541a8200c40030300402042180500c0c0e1f0000f81d00740c1c04101c0300040014010701420103400c18509080205410203800c055030846014085000c1c0c500c5508203030741aa45076824008001c0c1c0d280b08e0480240300d14800c003801c0d02000843d18099100c0d07840750b801131160224401721072700980309607000184030174860170a4600c15a10081c1051034010044c2c86e1901500000442040040c0104803003054010031403854510280c0c2002225006610b03020710541d000c4111200686460914030072000d06a180c01500b443d080c8100010344407a40c101c504139600304070300d558451076000c003500c10780781303001854903250001100d04440e55000356000300c0340d10380c155244c10781280380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 492665899 1250 492664649 492664687
    0xc05120a030e0301052e080609010b030f0a080f1b03040f030203060708010e070f050f040801091e030903020d060b04060b0307090503060c09040903021906020d1b082a 73
    0x402d07181e44407440c5640080600f00d0320212060700c901201c00301007400039003810040005078034849400301d9007151110003940c41c0c144201d03011845a0341d5000c02401a143c208480324080c4009402054105041c0c1c2d1644404d02a02504c040506000b0a461001d100100601380c103020200041380c0d1942ea469955490648051000341d0080c0516404280d84c0ca108a050f13a050f2521248050307602d441c1c144049030142c919a41280410009000100d0079650200080c002001400f0003c01c0c514583d04048810080190880107443c03035007940034001903001444032003244d0301120302d401a0440f80c00e080b8050042c0c180c1041e4090326209010800d0a25100514003940255655498070307500d8000741075481009590b0440c0d580800e03c40802c07146000d4000200d0144a84196156618230a809134650317010017208a135100e80110b00c101400e039443c1302d2845015880c00510510407070540c3c1c0a090740001510382c5c4400c441106034041c4c001c0c0d01c0003103418808844400d85d642d699404024088030301d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 492667149 1250 492665899 492665903
    0x1002030c07050d0518041802120c060706050f0106050705073003021515181f0b0d0c080601080a150518010504050106050906160303150905160807050706090c05120a 72
    0x45c103514505628149440ba201d41d40e5008038400b81d108010350204410001403456068262040103114021901d0381c030080c01e44544604800710b41420b00d0744080e000400160001c408014040c00841c000c9500040c2d41c4d42150707c1d0040b07d044440707110f4040500c0c008000d401d100310007071070070b54078040580c0041d5004014191480800060b2680301d890500703000301c910080d921030b12011241d20a240b1b140c8030a50881e80c50444044020030b0503212103020320050307000c640c24440100346142a840e003406810142151490089064a031400010b016110003400698040c0c1d42c0341c1010080780720f03090b0340030040c0200030440e0211088212503d02d40c02c5007400b074240506d00300f400008030940180c00382e400501c0000c0c4414180342c03a440540350310004074a0280c00309034030b900d00304601c4080140b2200141045500100e020301e00707202918160300b01204c007041000002010007004075401410394105650140000c10106107a04000c81c100c0c0440d00290b920000541c1035442c10600003400c201840c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 492668399 1250 492667149 492667177
    0x90102060702030418020f0c0706271203050307140408070302040b030a050d1413030b0601021905070b070c050a0f0e100b070b0c0c0a080306211002030c07050d05 71
    0x15407414012078aa018601c42e00814030000d1044540c0c0314250f0300689003d100440e401810320002d941a113141c5482035014402040150340000545100320b40041c00500704215804250340c170b0500c0e000c0074030380d4415000d001c1110200100d04c03410301c1071262150250498600035202d5440c1e5406070f03100c44040c481244903500e03100c441480e5090202d074500940d030b00f1402030b203010304c140507003510507c1c0f20803004084060200000302072440000c030340340c0c02f0390f00560714031141340342c20000039282201030b1481d15000c400c0c1c40e4800300014000a4450103030788045400e00d4a55030585000c140709c00b034580140f80d0105074600e0200702070110764400812240a40030310b400366101e4500260300c1015900a180388800100002c0c0302089242e02c8468100c102508543e24002c40341030090304001e00c4840031125a0400424801b540ca06030704058072072a60f1211000f480c1c1e400e041d402e40e403528445c0c1e04112090b004800100040803040c10303504c2d102e802c441510307010311000d04020075603030020030b2904140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 492669649 1250 492668399 492668401
    0x702041418010608030a110f0f0703060b030610031101021e0307050124051005040306180215090904060f0908070f0606060c02010e01030b1513030b0106080c0d050c160809010206 78
    0x38814043c2c0000c4907854000f8500d0214501811541c070b01d01c40042c64054450b8500c1407038260b008000c040c1c0c10b8031b0709001409a40342180f501905880080f4407092080e4060340a01c80c0740c4d88000c44400c102c0758482e4511144da00790f940140c2c10500703850344020b91000600c00650b40725001000401006224600030443c2071600380041c09046481c140018910303841420620940c03c00d50a0103090103154207115040c180d40703940d41e000752011280c0d16204200c004114101b1400e11440d048442c0801001090402c461040801c880d0b100c010405014151550111045d03148190300034075800d9007020740f10303a075a041030130034a10100030214116011841c0c41c04c001540351060b4101c04040d85d05a480b0a8060130b000011030240524103006948044410080324122003008000d11140d03c0c08c01c204440340385941041d42500c4016408481400350b0710301040380000c480002c81e607901e0000d68000800751500d41100b09940241c052201401105a801c4c0d03051000c03810140030708071026800c507211 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 492670899 1250 492669649 492669691
    0x70806090f061003171c0b03010b06030121060b0306010602150a091208071e030f0b0f0924030d1d0d030f1101020d020406050316031407050a0507020414 67
    0x20710041120400c443c84030b114010300004a0301400038010703126880103242002c014021200c14100400944108140d072042e20009a080a00031040d8201045441c541158904810040c8010408440811201e1081014800c000f0558040d10700280040d0441c1c5466842d440060760301c6003081c9640044400180004440e500300f03014510b00c044e800706c041c0420f09100481601e102c0409001a400e0050164401d060400c0c40c508030b0011903410741d40402da00c4103030104c1c0700445144c9000c1a000d51042d41a101e03054580e80c540c0c6800550a00840c00c1030881c40e01a107039100c40031842a907140c0580041090791680c080c2c20540c0c25108100910a41540c41082000b850104c520040200f503c604000031414041c1c81d80032103d2041d0b40001d0b2900300c0482120040742e00c103070003036000b0440c080103001d40c3c0d05588064400c81460303820f08209108109003409000c1c50700401800402c000016030a551901c0344049d600d240d40d02034028800c0e0b40c0c92034124440041c089a1580c1c6140c407480190304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 492672149 1250 492670899 492670903
    0x501020304120912031707020328111b010c080d0f05060a0e070e040b1c0b010614030106020c04090c03020d0f030e011805042a1106071e08060a08070806090f 69
    0x84d55164640360307000c2010004401d20745800509410960000b44400c6440500315203c5010140c04401e40d0589010410005800010640308954a940c0007200800c184c0c02c82c0c1003600c2e403480c070908000f0344201e958945030000c0e00c0b406000d034911a0514101e01000503550308401e0041e1001c0700c0c6141c5140d1549058242518100c4904001030032940c0c103541281459800b0a03c03114000d40070789032101c1c42842ca040c030882183d03811904d10000c080100300e00c0f0390000c9803280382070109542c41d142d9490160001c2d6610000240d4621550fa2141e0b40710410100e4124000107580c0a400c180941089003000301c410f911000c81030b00400c100d44450000f40d0710406507000390b10740c284440600c05007003000740401051131215002010b58254009001000e040c400407800c03806a9592030f0241c01d403006010f0074490082c0102c01444a12005150711501b98036080000103105d15041105565403400511720f031042e98007140329809442d07000b0400c8000801c4a5102e20804e004035400d0210300c0c030801c1c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 492673399 1250 492672149 492672179
    0xc0e010503011a010f03110d060b13050904051c02070e010603020a0e0604050a0e06150c16120c030303020c120c030a020615090c0c0309130624080c0901090305010203041209 76
    0x94001000d8175002c0313a0f4507010303911681d5401000c484981c01d12441900135412a080364000d203d59440c04a4819003612007901c250020b4241a05d2505603400c0c141d44640e998130b5013000074080c040c00555074000b0203200f0484000240051b04d0040c07190350307440d540500294040c0c00c001000600c110034a81e903a05054003140e048420107019141820b00d000f02e81c080040001c1e054903840311094510b5280c00002e000501381e14440e0b0001380a51510900c898024800c8951000702c220005440c1540816124040c400c12aa01410302581d151002a40141484150340165005504c04603000c900520008042e00080616800310b4005868010200744060041c440180d40004440e0018224059040c0900303403589035002200d043c18407100002d003400c0c050514010301240d42d840108000760082401042280e484419060b0003281c0d48001424950700600c1e0441e00700c40040c0c01c0c0340070703482115140000c5810074001c6440b41400d18160704602d4021860382c0008000c00000f0030301d024030038448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 492674649 1250 492673399 492673451
    0x2a0e0a0c020d03110c061f1205060402040203071701030c09060603050907030602090307090218210d0e010c0204050a0e0f150105190b03040b18030c1510030c0e01050301 74
    0x1056100700340c8000b20701030b25801350f2240040c5410b001910340160100b1210780154000c5021b04a4880c0e80c840c02511422540d1251100d40a410320100104a01040c2c00c0c3d049601901c000d652607840311415902c18109036511041a45032100010501100c007004400b070b00c81c0f950040c02511b65400c0b048050f50019981840c582e00400407c0001030003c3d401007a50f00c00c007070103840f441c690301c0811400b2030f04a01054022112800340342c81e002d28001d030240d010414013038441410a4034001589a913003145c0c41000c0203002c0c208072480344a03802451036170701e200d600030024045441c19900280280c045460000014407429500c0c507100da1010a581c000002c500000e44550ba10340002c01c0910310600309121b1030040c102d20b0125080280d00c005510817401041c10f66128103080c0c41c04a004c001c0425481c541e500140325030034409401080040000381545020581a11030b22070072480c445546c0d00092240c9485c000c005801500112000d04a50044000f088420070380300145508080f0f500035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 492675899 1250 492674649 492674653
    0x20f1605041d030a030903020c0103020708120c040b0a030b15030105030a080a0c0c08010506090c0f0904091b080d090b0a05090405090a140a020f0d03020d05072a0e0a0c02 75
    0x140031a00305036009206a12822240551008014226a0655001801d40c4001076120010b65040c0340d010080300c2d850030800e203002c40c5410900d440d9424240109103818540242860220310040540d2041c4c0340500180c026450385c1d000001c20250013850100c41c01130040700c1f0003011002e81d46681c02924101c484c05005000c000350b13160754094003a4000b400e0001401544c1d80c0d19008629466074800261440c000000380e2418181c0c10400601c000902d00c0d60050810054004503440181c00c2e60304080d4103030340100703030194503141c00411503245024003103c402c80042e0004241e0400241d45a03001a56150000c91755111600c2004521544803024003140c0c0c10009102103041650000381c0c02072200f01540c560404039034400004805030307443e510140d48025004015440d00d14030b40345034404200c07862161000c59980c06901d600354131428000f448000f14820060240c0620740c0c400404e40c103114085200080c0801d101800072a001e080b81d101d1036040007400a501c00d229440b046405030300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 492677149 1250 492675899 492675943
    0x4030203030606130317031e0114010f2106210206070f020d05070602100e03090a09110d0903050d0c05091806060708040b0702030c090c03011208120412020f 69
    0x91101c264041301141282c40c0c1801000008038420100c0d4080d00b0a14015540c1d403820418075401c81d14504250203459200c03403000402c0031540d608500d440b03602d02070030034540c01420640c003500c810386a445021841d2248201340c140b0150154044000d80d014000d4268071058580a070b0707010344a0b0703010002d410142c01c01409002c40c07500ca13900d01036a072008054a44120683d92600d080113002d5001002590100c020080104098010460302c44004401142001c000c0c000046100c101031150420a540c5c64105695003040c01040382d01d00b40e04803000b88801071652800420075801518040681440d00c5200c1810501c54001c98141c044000c18420640f50384118600c55444060b181d035a1019003040500009540440a0002080803e20342926615980141820040b1030121030744100f0120b010008504103000a0320306440304228404214190ba1502103030610072600461b01a442c0c2100b000f04001c040c0c1c4d41030503030201d44d0f82a81c1440c01240c1540b40c0d140015071900700210742040b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 492678399 1250 492677149 492677161
    0x9031b09070815041503080c010e010e03070b0103260a020303040c1a0706050a0f1505090c032205011404050309040f050907030206090a050a03051005090d050301090f060b0a0302040311090403020303 87
    0x1740201010903241c010302003103140d50b60f848080942c010b81180005075110b89440440101c01e20601000580030409145000440d540701100810140002009160390b4142c2005070051607040c58035000322801c4090343c0d2021361001a55031f030070032682201d820100303103c0030030124000a003500b14054201031843c1002042c1d40c07603030050040142821040c0360b0301c01c6030307c0044c00580507061018180032000c00074141400244140c4000c001d101c0c45030584c041003400b00100720309000107051b05011003421490039080c6002800741800c044c1e43d0b0840d11103003050005229000c070040030f050000700c0d02003288c240840da00c441a1041201d0b00040c41e00301726020400340c01d22400820b030045008000c0d003401e544660010344d1983c03454005a840d54842812075921568512070986c114540d44014003080b4071044008100341310500501c0003040d115400381c5070b1f1007403a81142028001e5208955192039070701000070020740051005070750b41c2c200da0141101c0c50a04c01c5004d802a0b4050f805545555149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 492679649 1250 492678399 492678401
    0xc150712020c221104090c0306080d020304270212060405070309030207090b01110a06020702030f0c0a0b0a1e0f0207050913110a0f030609061407080f070509031b0907081504 76
    0x101d01c3d040c103880c0e10741c80f900c118031580400a001030500380500290f01402003000400310307942600540425030100540e0301140da000015502110070240440108040784604952261841e802c143c00c400c2c004903103481c0707440083c203caa01c50380d800d590411050399070000442c00d844000c0300150140e04600303001d22515070a0382245900c84018184030101c41203401e00c891801011140a44000c3d501054400c01c620f002c0c4042ca80844000c0c000b448a801110000742c100c0c10103100d1111035040000b803012006002e070040074400e201c401c00841d1a034800e003001030b0081b240c811030740006004010380800d848c0342c0000700d0b07030284007407000c4807115000070354400e20b8801e01ca0043c180d000d41c412a0005081e4010940710000d14412200426508640e240500030ba80074000c0b81c40c2c202e101c4104102041c1c0d80700c60100da00407080850443c0b1501c541c4000d0350f40748225140c5135054041d403420b00e47c1140500c5004c032203000080e50405034035a10008100c442c1c08059038413085050b01c0e641d40651602e81 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 492680899 1250 492679649 492679699
    0x2a030c150904090f15110301030c06030203071116030c080703150902030f03130612050610140405100917011b0f090b1c05150d0204020c0c150712020c 66
    0x4082c02c001450100c90300d07044000e02142c4000c40c0c074040301d840100da1150f0301c2e00881c1038420202e002c0605650440eaa2544500a180100d4003090341c080005016a8445c280024103041410243c48c06c1c4410440b20100300c1403140000c0e00d27a03411811000030485000290314088a030051600b07030100e1902000a006044104000d0783d1601c1020696038252200b0700080c5600851016514082483c2001c00f030070725054002c4035001c0d646000200a580d4a4550124100b103415180224582d154036081d800a8040ea800040d0000d91400314140040d401038150004d8490080d075500740040002c0d044d40c02d99005240c3e00401c4c0821040d10b4101c203004040003a58035016042004403030361030f40c441c000741d038000c6080e42008400d520141012020984a5542c01100c00d030b0107510300107038000200306280c40d0030074000e01030303a40043d01c080316120070720600307420369401000c00040c41d40c1000c0b80b215580026900b950030205a850890b00703980009601c106c83c05000e04403113a4074406800c80d40c00100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 492682149 1250 492680899 492680917
    0x31812180a03050609060106030e01060b0304060b0d060e0c120307030905010516060f090210030515010513051e031912210504060c020d140301170f2a030c15 69
    0x601ca12000c00000c40a225807446061204001c2c449989408001416078003407103805e017803036458a1000d000086501048030f60140e003202c23000c142d114003440812108071000c803024202038601000da212554011031001d40d030340c07400ca59040c2e0668608403a035031644110000100403c140940410180d40071300040c00344a04150020480b9070300b2074480da0305460394001e011081550740d4180ca02180751203c0c0580c003902c0380d440d00300541d10380030500540e000c0741908420b041c080301040003424511000d003100301a18000c0d0100c3d03c24400103060307805140d4140a000d2080c0500c00360a0742884c40d582100b94400d410103d11441c5031501081525003a03900300074134507802c00c200c60200b270510642c090b0f5401107100e00c2c000102c60309200802410001100d0350b80040240300d591007a4104042c0b800d581c150740312000b00c1410f030048032641c1480c0c0041b0303041100c0d00303003d0444012041c1014424020b590308000c200345442500c05020152034066101a440d448240310300b003404203220300303405062518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 492683399 1250 492682149 492682159
    0x4101030c080f0f1b040f03020114190e03030912010b0f0607030806040f0906150807060315051e1009080c01080702150405012301030c050405070f050307030b060403060203181218 78
    0x12955900c81c000e66172064004112a46038142c04008551b03212070340c1140a10100c80003401c20001c0ca20900500c0032090002081221107800c0c92102d41e02441182d030180001007040f42d2500c0301800841c0604080071007140300300400c44084449082c001c007141d818560680c0d0700702c1c1d90380e603401c100002014079010380100306079150505400520f50f48a41c6812030385a0049842040c40c103481d5a14000c01ca802c04130070103003400034800000c0c10b4240c0500c00e03600203e403218000000081445041180c150050381c1c0240301180008003d90440300050603500c0310b02c1500c40c0d82c6001401594103550a403405401130348044801c003000002080134540083c480c03000842c1002e400038080d1300c0c800014190f0030400d84401c0041040141100d041e900404080d14240014540100060040c6507240c40c0301d0184030f40000050041c1d80b0a50007031054010007011540c0b165280e0520200940049420300015040c06031030100014001850041c0310084141c2c60f80b0300b00540d00e00e240c41038401a5002c1d001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 492684649 1250 492683399 492683431
    0x50d0906090503031506040812370306050d152f12060907050a0f050904060b0a03050f0408041205030c0f06041a0705044101030c080f0f 60
    0xa0581d01640c1411401100110345070308102003000040c12920090310321845c42004104100440071602d101d2090b00290703174030380342c04916028260b81c0202c06d40412440441201d41c0100310000541400201300070381d0200544c0340c40d030782072000310740718620301820000442d800808841110340140b00800100c000402c1c5074084082d0340e11214004800d2121403050103d40d8001d45201854003660055044a54244c1801d1014003d0114403480540d48100403070f13014040c45a5000300100c90307015001400c100b000c81ea030748004c0348c1c2c5600070255460003c0e0500010513810602041d50303d000c1c6030000303041c40c40c00345015000e003a20f542e07107001118030f0b0000740f0075504030308001c3c0010416040010081c0c41c851074207107049000d04a40e101d82c070803960749000901c401c05501c042036406480b80b041c2703001540464240040c1e40703500c4031340d2441030452000d040c011b12010a18a4410343c81003c0e04d051040801c200b0b0155140f0700e044a03040c0004101500040b008aa68682650010b008030040a0a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 492685899 1250 492684649 492684653
    0xf070527040f090c060c0804080d02061b03060f0111071d0402040e1f020d181b060207060c0b0703060b030108061605030c0a03090213020d0e060c040602030a050d09 72
    0x142184200420325034016140d069aa04040c0280030960781200700802c07005034640e03110894113056000c0d42c010000c80c011b20f00d0410181c0b00c100e4000d06404003c807007824210f0381000b59504d05c1220408029203a60304c080342180c2caa90b069034041d030030003490032008201603801181d2025240c4410402c0380320b89140000d241000e042d0103020302102c0341061905181a00601c82907400a06c1100290b9101c00d11b108140c1e1000100d000120b80b08130b10140c0e40d41c4030882ca41c0c001c4d01e1010f40320306082d440b030202c0b8010070150100e900036007201280394401135076480800740d0f01d030f00807882100c010030004c2e0013100014200b0364a40d9402144c9080001d0f2154640c4004122900242c0003401690701c0001805445640d01203180c000c031030140b40403499407500c002c0e112202e008064820b07007896200c003520811592091100c02c684001b4140c1151501c03d0142850098400030f100d492060186c1008140516800b00c1150240d51040e0000c40c90010020021119035001030402c1c0300b400c2da51200400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 492687149 1250 492685899 492685927
    0x50d0c050d060b0702310c051b010b031240050319020418120302040302040501050a05061c0b030d03020405010339180608071b0305030f0705 62
    0x2556001998a441e11203100081c01011030341c00340c1052a046200f4480710740107990702c13181c00051100c1081704507006210190540325800c2d8038000815950706008804a85541c058090302c021640c10400510003909918198201e803042000e064250f0410f40075401c081202d103000b0161241d0311015640c0141009086103280d0312080040c0c00d40d44007510301400708074040300341030300035003002c07805003000b083c500003514884501850000c2c099910341c0755180c9a4460300342081452900a12100105001c1002c010001e6006001c220f01c50351074540086845d080138851101038842c0541840c1c03030549050100e0141015040301050700c1a190780500040ea10203004454034003030161000750303c842c01d100000d419200800003088911800e40d19600502c8500d00c0d100846c0d00a0b045030903509604400d0413a44071084c6038914081a19025000982540c041200b0740f048089669080d054089800e40000d00140a08080e002923400e0021a00580c000e0401a80261083c14581d24202c240c0031140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 492688399 1250 492687149 492687161
    0x90302040c170916121103010603061e050c0304112701090b090603070515090402030108070815070c171b07180902091303030e06010b0c0c01030603021c03050d 70
    0xc00020110001210103030007001240b600904030b00f010f00031224180d1011100d9003c5480740708001214040c3d090180304248168034030000c8040d000340042c54590400d5006003520240b05a4000d9200010345131500a41c45080e0103000c80101c0c807441c640f50303034642e001250301035582e0580c40114851400410717824101141072940f05c07503042d145950300d408440f004481940c1c0146001e031200c8000c0100c0c540d000701c4e6007030aa07a01207440d601e0741554214550050700455090681081c0300100100e1403800c0007914808503800d5004a812402485070818446074069032010042411000e141e400203509a00f40d01d00e103a416026507041405500c2c0b1b04009038040c0b1081e5007581c224520610212900c50700748c1000005012042c028000c0c80c2d8081442400e004000d012080440b02080c000c1511941000003020f041c10219250382d40c48141003041d90703003c42910ba145104802e0503110703550080c01144102e9400401441101982241100208081c50000c0303081000400844041450364842c2c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 492689649 1250 492688399 492688421
    0x1090b0a090b03090c0d1a01090b0d12031104030606150903030504091a18041406010f0e0a150605030702071e0605030601030e0d0207060210061a0f0409110d0f0c1b0309030204 77
    0x62100071051f11007400c000001a005281c6c041e0a2494500c00b544503250403500140d4000140c180811541c4d81c120001c142e40150510343c40d400003000000e001c02604130509450340712440d4028004400010b942003907061000802282003400b0402c924500c0d0340c46108900b0340010030500c0364075402c00084210110032409405a003100080c0828840756085207c862002400106040d50524901c0c085509807481590a2110a800003600c03040030354100e8078001105c8817002c40520b807602d0b4080c1c660f403c100c40d200010700c03901da400104408645c48a0b0404508201a00c15150405004403801d500081c866814962100901c01e50745008000c041e00340c2c18264045d0101c1c0d810048001d0030706e422a05c06020081c20400180300004082c0c6d845822950240c020550300c40e4000500c0c3c5440c0141c2e4814580f85160441c1d20800355518001820311011100c8100303c110000002030382200c21048051002445103c0201d0310554102c1c405481f0034000e0502c481003a40e20350014080e01c1e0f12640f2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 492690899 1250 492689649 492689663
    0x2060d050114010c0203061f080604120f0e1809031204080a0905030319110f0312100605070b06211c020d0912030503040218070e01090b0a090b03090c0d 67
    0x410011296200c001020b01c02480c1c050004096034000030394801002c0c0031900e0b4180801000e16860303000303405a02c0100703038110a64019103000d0410104011707802100d04041000c1000d007007411889001e855034443c0008000d00c2401101040c00781801c4030040031141140b00800c504030313541e00107000c418412403007600026600d044200c0018202d07009036121030300a40c814000c0741405208041d044440c00424988141c41d98240005145080a036400021290000146003c0070510b040540b41c401c060302681001c60a91700e440446a07442555400b070316803020400032498516125845000c16140e92101e1294507075040c45050802d20b85400100c94850116010304040d030b014030003e110003407923080100c0d07000d00c0c0c01c0026000445a003002010007100000141c00c5586040c0308401c00000d1811b10151440c100c14082c0c80ca9801064050104001c04030014080c0022000c48404904941e2800c02c7c4910705a0300107441d400280800c8000e02440700105c51a48812686065007401030301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 492692149 1250 492690899 492690901
    0x3a0903030c080d150807050f0109090c0e09070e09010e070f110c03031602100302210403031401081f051b0d09050102030412090f031205031e010b070312020a0903080a030902060d05 79
    0x415a85000d81c2d66001c98010764230a820071040d6030300100c0c184115030b2a1200810641400030302121103626a9051075405444ca50521a1460344280c0e645030740d0109481980903640c8514200390341000407500d03240002e0409084800082c0b0a100450b0410003040840d05c1007003442c40080c1c11a00080807091581038400c0481042d4a004500d9180d088420300741103141600060140c04040100d002c522400d4030148007007001c15103e0b90041d103100805400340142940c59840c2c1076202c4030900e03103020700e002041420061001892250134003908105a60030505081104140d1094111030b529040d469072b11459100494028002035104510403018202c6503485080d02070a1402c45400280f40b00001d9101800010004c0c00d400c507065006040040d01d0340d0315000640e40b045c0d070148120013072491034400060440303c581e014080c100d10030386510035a107a1100c803040480c0990b8100c5400038000840030000b08150800814581d4607d18000c00c40c1e102c540c0205246a01030b5a0f03640b0220381d944 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 492693399 1250 492692149 492692159
    0x1060309110a05010e060a0e0a1203020120030105010e190611070611151816090b2b020613060c03031a03120f0c3a0903030c080d15 58
    0x100d808803044101e8100100c2c41c2882c00080c4018402441d96005460005840c0d0415004000580020700b004040c142c4403521026070410b24117500d00300b240550f0030300f491038411401c2c650003583c20b42907510400341142c0c600401190788804601005030051900101190200b0f134101461028181e1920b502e120a100200401d140c003d10303501090800800590365855001e01048118075440742005000d656150388030890120301201040c65983e2041e17030800390b0726402c521401411a907007214104543c068941c1403100e0f02c00c1442c20b104205107240ca04000c4403500c0136081008031700250007281400801c02c1940c05010182e048039000c200d0361280c120400d503060040204103450002d62680840022010a5444050042d543c8440c2c00105840f032a0bd60300106541c200c011500032540101c0d40d0494004c0200700c034160b408007610341c03d0920302d16030081da4203900c0584000d40d41d40e25150301d1614102c4080c20218011103180f40304000d00b4244032284d000301d0000180044000f180c0300e280c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 492694649 1250 492693399 492693413
    0xc03130f12090f0305100c03110a270302030601090908070b100807050a0b0a030e031e1c0509100902031614011722020307030804060903060b03010908191701060309 72
    0x65116083d4009186824000a800401c0052982d008a0400700f600c02001105802400800c800c000d103401d00828400c410720707400003e0307202902c0da40242241c8407082c100860520040e501003e905640507800401000c000ea0340044481d6001c1c0c3e0281e4181f00c11a6600001c101040d20300035500d035030841040c4a00c0405010003402014101c0d0819001450050b02c1c60351800b940725200f003810b98884e0302e600000c5d014022501700e11505540f00301c0600305000011750740c1d00500c0202c18500700c9003419002c1d4203101d2080c0d5020f110100018003010300794a4000c00500003800c402c90300350258072045102c001e200b68540014006141800703203502c140302e00041c04d0340c143c00440e002c2c03d0189028000c600341d0301082100c1d00440b0341421800182c1d1400481d103400c1142d4401015214001800511030341e0007a00d00e81580e01c80c90b018400301c031440b030800d4240c500c074000c0130300072a1040280b4540c14014080840c0340d48040d04020600d1401c11050301e030044070076840307039020a8983c00510108002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 492695899 1250 492694649 492694667
    0x30d0e03040e0604090b06010e0a05030f0f2a0d110333011512091502130807080c061c050106030c030e01091a04030215011202010f030b090c03130f12 66
    0x10613034040003000c0168507481c12441e00034100e0b505201c0c401600440c5501c8403419131025200180880d0944041c80254907a50405441a401d450044c1c0b080307401c101c401c219503c03061410508030210b602040700104081b1411084003200c07018290789079804a902d050101c0b450008058142c802540034421b10010208040c0e10324140c0c0b40702a100501c01c00c6001900c400c0d90641d540313030120072040c042c040780c0000e2440f01c46c00b0303140308414444602c060519030001c15120091403542c0403000c1e901c101069441c3d80c1d5000d001e07956040f60070000154201500509000c2860346115030250701180c1104089076001e81150000030303210b40e003103a070498041c081c451a0246000081003a01d0140e00c0350100c1942030344230940c04100d150041004d241c030800a183c80807090400c9248256500c414070300c050000e1709000c902144c0c0f91448003004a0092181c0300c05050042d04402c0782d0b584521400c80d00c4d9000400d26036424450225080c0415601c2ca05220101d2142d0700c01303080c284040801400d0088 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 492697149 1250 492695899 492695911
    0x180221240a270602030721050412020f062202090702060708062409010315080304030210030203010605090d151d0606030307020d0f020312070f03030e0102040b040b0c030d0e03040e 79
    0x2044032041c00305803108080d108045400c580010b80703035150010215030f81401e551000c00819100340041c46809081d2303000070300070fa10404012192a28080c3e081e0380f90105642d605503903070007400000317010001200700c90714980b2480d0801c02da80c40c03e582c0014841002581c0384001607002001300250650010300745a040070040703070aa5565200c900320130321004028404002d4810b000b0915003203a034029041940090030202c40d5141498450071500d94a0b00a0300c0180e228500c4000f505840c58080d1080f6030598026030b031081e10301031032175091128030100c1200480f1192000f029603581c070305d901c2c41550340310302140004940030005107405916040d0054841803190b00100a88001640c49965541c02150300c06582449140030740002400c0c166641a114609800000c1000401c07154201c1c203040103200f038404002a614a00c0210b00300d0250703007d43e6103400010003041c08443e03c0308010303000d42344194007182e2402d00380c4100c6100342d542c030391260500303940041030610110034440b00240c1e10817 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 492698399 1250 492697149 492697181
    0x3010e16020708030a03021e1207260403110a05070803070c08010b0f091515030703051f051315060207080f0d05042102030f06010504180221240a 64
    0xf81092012070312442100080414142d001490000090880b80c2c02030404c500f0310011074403462900301883d01e1a4080f1070400019029107481443d245840c40c800d18107400000c041c40d5a50303641d590030b0303038a824100c00704103062207190071920000d6000c02c5500301034001ea0300910f884901e9454403c644140c0c0703400164559040c02540011a107405241884610b0100d030006907030745810008070b20700c00c4c03100440e9400440010649165000b408000c5002d003030305540802041d030362407604407060207032422421003880709003008021a29001006d17070004400303100e00007520b541403141c003008001c00e03070300240245e0004c420030481c0c02000e00c449407540c2c0005020701403059038144018464402d40c081e1840c080c8210041951800740410704032561a8043d088810545240d40ca2507030321802441024403032410240c1c045d070700c50420022054010307400b07046841c48607071561001c4060b800b40111794030341e44103031aa1007014200d0111400140d18002e0042c03825400d050300711100f90740d8400c07010580c403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 492699649 1250 492698399 492698413
    0x150905030a05061605070501050a0603030908060402100807090e0f0a0615081b04030b040318080a020108240303040b12060406050d0b0c1b100b01080f0106111203010e1602 75
    0x2ca00c0105983e540241c071380046a0b41c0680000c01134500c1d005c0c2d044007600790361900040180001141c0c1c45803098900035101e440029944960081d80c5640407a002034006c10260000428603001e03901594212810381850710010342c49545440c0b8840c0110395908050b06120140a0341188622030788020b04540342d80040030010880d03020380b11000141807041e4508048005e035214440c1001510040c41e40026040901c1c02c041c10010404410191941003410400c000041e00800000769001441c4d810707100c000d0a0741c0c0704005041404ca2204d112120451011411500e90f5024401070018198810600da201c0745851242c240180000b00202e0103245000010b20203a961004030801c603d030b0120340d40727447e6030b03815142042d00e008001400501400040c10514107010100c1c03203080c428502c2c4402c00c09a08540011108002d040c3d85841c06c6040d4040180407a5118046890070138192004940c8800e0760240c48015030f07442603101c40300c400302001c20711480d04003020200c0207190303140c130060450f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 492700899 1250 492699649 492699653
    0x90302040e0609061302010903170306010e09010810020d02040b0313060506100c12111b041104030308040b04080919030201110a0308070f020a1a2a0301140303090406150905030a 78
    0x1a410303024050009150282031145c045a1080c542d00018507440480c200d13040b03250070f501200700e8109641d040e011030940d101400f220f0601c03440d000e04840340310004000190a0021800c000d50180c5813110702a5001c02c0f0208006207864019809060068903241200d80203050400496401030805440350030500306a03c8019030048000141680007513080c0c07541021000152000c800010340610b8030700800402d00c1c00e0704540001380054080c00e96007400480c1c00c80880381c01c01d10580c080140131038214004203022624001a151340035204000862414903000e002400c11400c04900e6a122410140c052085590240d446051000400e004010b10a1f0355034028140a10041c13001e0304110042680d400220700c200003942c071851f00b01c1400440c00c55407003103400491318100c9110010700074000040690070240400302541c06810f00d201429039003040b19040c0700981015956a0501c0184807180e019503e81c0f29100043c9014198418402004070300540b02e40c5103076110303911a8014541c0000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 492702149 1250 492700899 492700903
    0x706120501050a170c03010c050405010210111602061c051504020304201503090708070b04030c0905070302040b030a06090b040e281b080106140627030d090302040e0609 74
    0xc241d41590004104c0c04c0b030130040030b502c0d0150758031032613515600340302114100e0b58100c4002e0007910b0b0700f0380c2070b0307604c0228142440040d00c03030420076010600300c04c2010f41482c801c04100c80f6400c901c020003851600344da194200740180c0803602281701065482083c03180843c0408c00114403100240c80c1503095250986071090842040c107150843d03a80310b4611842c0302d51340d8a05000d00e10a4044555489042c01044030341e490b07803107004184003881001c5e000308d50401d6641c2500c040b281e01440f2001c0c003070304004445000d8480500314609064007404040b81803800c80d805144140380c410f200240b5189841045016603100f00850303400f0741c1c84c0819081c00e40380c01085540488600342d007107181021b0001c55100045018220240910012101040c01c100d0102880000c44910500038495181c40d44100d43c062010b040701c540c4c0c001c50420842581c8041103c0c12400410503064000041542402080c10710048540400014030500030034401c40c501481242416650400182002c2c17403d1000380d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 492703399 1250 492702149 492702169
    0x190e0315070e09100f1e050f10141209010c0f030618020309030408011d0c0603130b09010e0106090f0609060b2505010c030b0f030109080306060a0309080c070612050105 74
    0x90f004850307110014012032502c03a518002081c01100b44e201543c4c2e034184c0c600e0804840e1031031080200e100b450005140c81d00c072440550b8001c00801d040f010485000043e12258101217030320200c5078040c0b100648441131001d03102e10851001001050503040d140e4020110b086d031456a8060503c0c0080900100200303800310404050590001682c0b070701d4242459145001d03607881001d00f90b00b0030344280d25076080c0d001003041c961001c0d001c640c001a041d40c00c00400e8041181c5840140c00c0e00e03d15940460340e40b95496800c0700d41000001403034001001a50b0940d09942c101c2040d030768844402d004001518030a00004140d03010042003074038180303541d0720540c3c810b040080e03054140442c012040d611461f400d1a91080d8044000c04c1501054140a0050301400c04201e10075580000920360030f040601605050a03807050b00307185555181000c00540f03030003070610b1401f0166548107007000a6200d4000b401400301301c400600549150000081032162518403010031030f418100100b00c10b8449540301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 492704649 1250 492703399 492703427
    0x31a010e0703020702190311100806010507060222060503090f0604020f01180e0a270b0a1d0a0605090c180112140102180906040212010506070206190e031507 69
    0x560786103214000121b0864805001880180c102c12000007003200ea082d0a01d020101070750009800c1c0902c8909845462045032070501180f01013000c200042c1c3c0702d42c0288415807040ea9288180030b40000703004807001c2d1a40003600412000414402c103400204403014104490100400b41031410f580030401e082c00c04480c0606001803c1728424801135030ba62280040c0039401c00701c140318a1304140710000f40100c10391420700380c502d40782c46a41d1034048409410344240c1050000c01603844000d0000000e01c0402008240319403000c40002080d02d0520992070303164055400071903075040c0010290700342801c90844510584407100000203040e00200c40e14110b91001e0b40c190038265260801e000940200522203070107510000b088001c1c40300a44410100c1c003010744408015a03158410f0004038401d0700000303141d41d0b4240f4010004e81c038181000303001440c03000d4606800c0c041107a4000380c2051001207032001192448040740075609081001005020fa03a00241449081c602400f0741051854049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 492705899 1250 492704649 492704651
    0x2040615140325031505012a0305041a07020405130201020a03030b03030405060c25081e03250b09030a0e0d020d0816030306090b03030f0309070806040c031a010e0703 73
    0x50104405601c40f5100c031202c00340303034901e40c1c180c44000400828549440d044907019604001c241e55201e01c0409903c40d5481c01d501c00055460500303c1d031b00c0e1003000300460801c14200000309042141c0e0410400203014405a242c540070b00748104001c2d140d0081031081a81c1504840002603030340000c03c8403130550142000105085400301207030440c40740390405504903400007003280c1244030006d800c5602d00f644d602c0c0100301515003080c006411320f0034030810590364401c0074900052403290f40f114442c4448402124a01856180c41031084100750744201c02d6442040200d405201e101c03500564880c841502071071921040c000090400b05541401d180111418041d400464460006a03200c06801110403501c0ea81c001d01503010740c10840008a0000e410010000780c1d145030f90140b1440c0c01802000365041058444500341145c1000b0903446803445072860004400006000541c003990298003420480d034214242103c2d0200d5140302050306803402d00c010841c0240e04000c060b0480050701d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 492707149 1250 492705899 492705901
    0x2a090e0d0f0c21030e01060f06030b030304030b0a0213080c1003051909060606020705040b090f0415020c06060f0d03020607140f030a020301080f12040b032809020406151403 76
    0x54100e41400782010018148409000c59100e907403800c503080e046543c29a0380500074041300d02140d5080c0d446034803400040d070303210380030500440b4025001030001c03a00203001c50742170035607036150350f2001c00043d00c0164104e60b0014007410324482d44020350024104080c01890721082c03542c00328400076000c1442c2d00415503601c020551342c00501c1c5050004900320b0fa02400301031624103001c0300401581c402d0300c0c01741c0308060002941c0e04041c0100001450000c0005007169242006103080c4c400c001c204403200b48041d0f501c0d0380480c0c414070142c4a403684d060000d110501c0d01c0828071050000c0900c00500c00c8181e0604040080d5000407202e03031140d41c0b03142103182c2540c0500516030a014103940d28081c0c0801204125031600c4a80c09107040b26000070803100d541c200c40a28a49030250800b401c000403008000c240040390307101c0b00658011070340901c055515002c1c0e00c51019100a004400b846d9030742c031000d0020661030030380200c8010748540248800740300707580000541091581c00b0100d80c1954084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 492708399 1250 492707149 492707177
    0x14071113020c0106080d1809020f040f09060906060309050a1101050c30030103200102100504050a060e03180112150609171603031101092a090e0d 64
    0x511501a2018550300540d10380000b410a980a008603026454051140c50300c3c0c5281d00b0b10941c0820030685640b00194200d604191401e00a90300986503030074880000c020010f003074140000804001e009100002030300900304804441500c032681d01c241d0070036081859a202040300851514403540d8408910030b4441c88040c01681c10340035641c0d98404034000e02100d103001d0500b02d45986c0c1e4807602c52100381900c441c401900c182d140030a0002074400f545401980c03d80741d00f180010346030030070140111070145902080b0f61040e074604840440c1c1c0c94014848138000c0000c98041c05480b40c9600f00650b0420040c11191035140c5003003180306040240d1030768840c0c0c0c0f0221581c4207421180740c0d2200074450b00d84900010304100307203c4c0308014401e6840e10344401402408115803140c04003405419010a207581c4040b25070340000d643c0b00c03419560300c014010000300b50b4103035070004884012824001105101540510100940c0030001150500b5003d078506100420300201034a020305080212200d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 492709649 1250 492708399 492708409
    0x10e150d06090221060108030a09150c080a090501030c0e0102030d0f020405040c02070806100501080601080603030c070e100501020304050d06151d160c0c0306054201140711 76
    0x42d020194112038132038180383c0b5141c3c940342500b030351032480b800721007003a42d98410b03241d581e00c0750030785002c0041c0c40c142040c032426682c1c140821580005141c02c440d840c070300da160000b40b5442810080d0200e0b083c003d04008958050048500d4034403503013818028060f624001039124415000444285543e51280541601c55039050300d01804020707000b0084418883d0010359115907034040c4200354407850000840d030280040d071b00c209442040e902d0303d08030748a903001502d4050317001c0c004c154940001d0004150039603042100d0300007031190145581407810114000c864654480c1c21081c1150810401405243c480110b90b440b09a0f03c4070740003400721003442041003218440d4010203921440c0c2e1000c482480e14001c502800707400151440300001c41c1480d000e680d46c440f182c4000b000ca107100c0c20100041800307940690391010303803000151031169000824028100c184821142d80302c004030f141143c5510095140b001c112401e0901d60b08107044104042c00d14041d04200602841d00d040d5010916120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 492710899 1250 492709649 492709661
    0x30a0605180a0c110a050309010e0a0b09090613181704030c18110301031b23040e010e122a032704140a0b150a0305100e0f0f010e150d06 60
    0x62411303102d0004107032416586030348c0440d41145c009800b11606211601c3c0c058064411203030941c0c00c15103000009004e10100440c0101034550005e001d018041400d91940a0b4200d1a4000c0981d805000040d2810643c01100190f046200000a01061000540b84c07008a000c3d50590782001c508840104c880c50054825440f0788104608040700000800046500800d91130b08200040c15009440c0c0c00001c0494a400455140692271500f842443e414a503125156020300c543c004605005240c0c035051801c11074074640940c080c000512181c1c00e41d503001500e042c1000b0f200c070b0822000713002c40070107561b070003801e5005610f03030700001e060107400988800710030600710090428800034505042d030300c29410040700c404191605107103d40c0729929180968241c0f08000d0700100e03051136981c450032402030000070006c5030b5506110402044007102c16a201d0300c910441c61108110346041441004030100683c0000071703c1c0c2d42e040901440045990700342c4940501650200b140b44081c0c01c07d4006441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 492712149 1250 492710899 492710927
    0x30308090a06021210050409080a050310050a06020d0305100f1a2206170c040b0708070506010b090a080c010509011101020d060906050a080321131205030a0605180a0c 73
    0x110006050150900c0c01a00e6403040c44105d80e03155034650307a0001c0c4400d4983d81c440051003400c0400c83e00c0341141c0039901540d04024034001f03400580e41c0701e0001c0342240041d0381003500960711550064907521f43c54004d8680c801c01784041191254607110950f13100103158040e540c00000100050f800300d50803038085e40d0621107001080000a0018400074004500364000c00300022408001c1a482642c4901003a0140d18020710482c90b2514104170140310b6008100e00b00c9903400d04202020124008202c034501900d03030081a903564140c05c10410801250a40c0300c11300641100c3e9044059a03040f40541d00002e10030b00b005080072040052080c02031054a80c2060b00c00e00c0c003031002c01c2c0b1040715401403043d141c0a60300506440c1d181e140d10341c0d4902030740806409a0302000005c004c00c88030391001c03a4000c40c069440708a81e14841d0b540d2403c01c0900c11065001410202c1000540e00150261301c1c028101905c83d100381600d101d000f100405001001c0010103030325038417a550040d10440c41255130030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 492713399 1250 492712149 492712151
    0xc16080703110303130906061101020339030a0f06050d03050909040c030203011a0102010c050c060121170705010506060319090302160b040e07020606031b040605180711010b0307030308090a06 84
    0x1606e6040c4c41d00100098024031b0000341c01c100400f10019014400c407802a0601144403512a514170b032030440c40c51745d6541095144898400d203000d01d000c044003442c0030310107809012402d010203188250856445a00261107840105903039404a6003000440e0304e601c4013078a56a04940e1241440120002c0d1940000d4040d0301c1d0111040d42d2300344807042e00d032204209034001d0019040011049606000d60904112940c00581c01084282e150313165600c3c15070f4095080b01c035041c80946070441180d80395200701e601c0c904002011000c00400307100f0640e11072001c45d022415414865111500010f010180c1c80e04181c0e10000001403500801000441803080c40210b1030541d15840250b0380c2c0d8000b841074070115140d040106000c0c1d800825010300c00d07607001e0000c14520120301140210101c4c42c0880b942c10643d81c0d00d020440780ca46d0003040c048900707598880c010078103084c140108041c990000220590b4940701e12100166400309880c001c481d00340c030300104075454040000b030901e111480020585 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 492714649 1250 492713399 492713437
    0x50c0f0d140c0301050a14041d07170d0503070c0c180c121a01080a02040504060605040501020c030c13022107020d0801080f0a1e0609080c16080703110303 68
    0x114055000194070000810107101d040c1c48050004249000c00c0c0170381c0341d12a0008009216084800e0240d40b0704100081000c50450542c1412680b0a00034600c9210700d50000b1340180840451400170010318894400202259010030740300418500000c1c200380d00f0440701c02034050500860307483c4e54010b02204000c4030450883c0c014140001e0100450383c0c00442c1c0560101d56100c5400e104244540c00742030300301010148840011201c501c2d0042c80b0081e000c7c0d0078000841d90f80c681d803040c20058403258840781d64881c03c0200188c0f401000c540014803d1f8400512842c2a4494000a0400c07004041d00561595100140c00c4040000885400b48045400f4204411154001180c114580085e1204a402d980f111200340e215030101c1c1c28500d0300d0b0b1000f0041c10005403400001100c0683ca080040c02001d0a0703a122800da41c90b090060300c41002c08100c4110050090001c041880782551441c081b0914000d030701030700c0d00b0040c440079204e145200701a1780c254500b40100d03000c8440190b000704d49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 492715899 1250 492714649 492714667
    0x61b07050d120e0a050a061508010c12140907090f0204091a09070807021b0f09180f010905100f0603020d080a030b0402091c080d0c1106131203050c0f 66
    0x1d403003580802d41060030559414a01003001c544440d005800c1006800ca1070710548030f94001c3d101c01480c01e0850200003a001440850030f01c500401c0c0540c2c4d0f40c91035106600e079040700d17050f80c01c1103000e81c0341c041d110410f222701d20b0000503045081310320721200482c110150b044414003d01450340000c2c02d0303909224540000c039904030382c3c01c0f000b4401100c0080041c0c440d907604031490001224508007580c80403d0300f00a00c00780b03a101c001e06c0c8000411002c400c1610b10b0200d54002c200303981c0800d00500c2e0201800c40100180301d0b01e01040b000d44001c101d9940d9503210310703549500440b45540704607607981c02c8580c503120715005000a5a000340203440410300320328020305990300996181000034901441880c0740d01d00380c000c40d02c607a80001d2081c64030210302003881c0d580103440761040301c03000010402250012064010030385660303d46d40b50352016200101c000b070b0410900414102c0841d00104407500000d4204400141154031881e001906503580c644804841c03140e0700d1895040500454404a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 492717149 1250 492715899 492715907
    0x906240e151908040c0623090d080703020607120506030703030c0c0801021902060a020a120f1407020a29010e0a0207050a2009090607050903030d060e01051809061b07050d 75
    0x1000b00d00c070f154054412591100708032580713520369118041e5040011010303045220901c0243c295880d000780f0089078140270703a490b400300f80e00c0441e04a0258005504010035640c00024100491458040922452503c40000394030346c1e444d03010040500885c060041e041c400c12070760510207020484002c540e40c101610424060b0159007000000502c500c00005102450b5030003550031401d49501e91645c50b8664a03414400f800310088013140480d41e56810005e10041c07503d005026050b26000750102c4841030502001200300c0325000d16059405034a00ea4210b500c442c0510304451041c03003444595191305e11003034040c0c0718040c03002d00244580007a00c41404000700f201100d004813082614005074107841440854103044502103030541002e8000b51400340207a000300305071034004059a10348000d404d420002c960854000e030b08501c6c6850018042420304000f50a03554501c54000322051402c40f03136403566484014018045039a180c0d40c11082a01d0000a0787c00c4140d000d029100a03424ad418020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 492718399 1250 492717149 492717151
    0xc05010f110405152505031606151220030a150606030501080f0a0204050702031b0d02010b010c050a030e0619020609010c09050a0911070c0906240e151908 68
    0x1601c50380c1c0d000b000b5440700507444102d450078444280c07600e410351980310400883c900c1e115429601ca0001f0007003116480702c1d2112059408d84504030004078850592001c044044581d049048140000d0803118042084100b913030554200c00c1d002d20003c000d00034080303030501408002c0101000d0800d100040b841d04150444410b403503041e03504100603aaa01c00c480e03555841c8480c0703805650090340c0c0030300150400c0d40040703501080340d004507481c217034280c40040020038000c103011a907900100c01c001d840a50a001d42a00d44d082440d1076a10150b461b141c1a0700e03100003240003010700c400c04003400e0a50b1503450555000c192003115111003c506010301a484000c2180d007070300d03030b9441c058100c0109406110350390141c507800f0b4445e0017a01d003403803080c01c01070100c0003450b8510041804140001885590031302d000e402c02180c0410681e01c0c20300094914121520714590304003004d0004040507520910038518400c1c00c9681d010000290040a0024460b41b80002c44110b4a064600e080e150808100f07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492719649 1250 492718399 492718409
    0x40219050904210f0c15060f1d0a060f090906090b0c0d0b122d19030f080f04060f09020306070e0109050301090c0b03100e15120d020d0c05010f1104 65
    0x210b403100306100350848201e13502509a50100740c0c0c680640010a0781c44040e480604680b42002407010b0b1100ca6490003148164440900708000c1180e4101030804121942d401c1144508284041c0f070800e0078010200078580140322000d507880ac0302074203000860304014540364115640ca619030401c05008030095004101c402d400c1400c002e00100c450031b0581d4844044501e2501406c51103600d401c03d901e0390403031001448180e00d0040e020540d0b882007801140811140000f1665200c00a0700d405041d940000fa04881070240d40ca0401c14548002880725078400d90001000501c061100c0d9400c0040040724000303034140c8034890410041c1504905a4901c4020989810021655450401d4241c0340c2d60031000f000c1c5202c4070310412214041002854020300c11200d80e045540d20b40700d00302aa00822150741000c680350380c048640301e0401c480311401541100004e014000c45007400a9a14074000c3e104400f009440400d0380c05006082d8400000c9a0f0309443c00e1290940c10030351001e007500b1502803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492720899 1250 492719649 492719693
    0x110a030912020f030a0c0f050f070f090b1309050a0c290f0702101103070b0a0507181526060315070212070f080310030507050612040219050904 63
    0x82031600c5800043c01d4200b43c0d500c900158a068845c00040b01c0303101000c032040b07858030525406800090710a0211949030341301c00c0004d08903180303403210000c0107040f20341c0075038280ca1801a05540640395111800101d500004000c24011010700d00f4074945482c01101615940c0d6181010582d1424241c4460000d18200700784070910310f9078840c0e0061807141d402c2c088013025041210500508190405255407070990614041202450481c2801d42c1d0180108032001e13204003080041082d014495030b9003180c41443d00280205800500c08194002c0c0c0c0501c4800c041d90580030301c1c10b103115407010007c5149c1c02694aa903811100e40c60050100d05686030740c440d01515103800510f856240c822071041416030300411000080001c001055404458265030310001c41c4240404102090300850250b81186900c20000c1d1541c140103080038042c1d040a4400c4074200324003001820030b0881d46400c40e804407403125a862895071070044010496010035041100101008184802c490240050810b5202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492722149 1250 492720899 492720923
    0x415120c09051c021f0512180a152d05060402070f170706020406020f0d050a120203090f06010f1701061203030f0f0e032208060c0a03110a0309 63
    0x8400d640414036402020b421001e0000d100f488040c1442e18510828000390210303e812032500070410903c18541c2d005e1000c41c40028220641c0c065501c5e00035407105809002607c111003528215489075912800601480c007178203245400585c55038882d040e0340205000c0708140303c14445142d80300349500c55040c0041464400020042e040a0088030840b561191b80700030f00d940e141d510070b01d0081e80c1c0001e12484002c00d20410000500c01e00c000c0025240d00e03001402500b884004440c034001442aa000405c101030082e42d2189401100c218191301c3c140d040941c8030758031100c42601e402910002a503680c82032900001750222079088142c1070314009000c00d150b0041d00001c443c26204244240c8201e1403501c518600032901c40d0b804002298040000401c0c41d2406001150650320705200c04401c60b003000410300c90304601783c024529032190400d55441100d01d0b00c0704250301c98070000e049001c4914001960745245100c0c1c1d1240806103840c600060b240d5524640c02001080703480320859003018510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492723399 1250 492722149 492722171
    0xd0c03021203092505150306120d0801091e1d06070512040b0c09030a0c230a05120708030307030207030e0102010506030d031107020307140906010f020c15041512 71
    0x6800c40c0d01c191804002455034040c2003404c3d15800c14032480d19107a045100c80c011903181d641150218031196490b0890f034407404d1000802440d0140f0002c42d00c81648400d520003601078001c0400c2d0304442203d00e0011b034400c01440340c280ea1a035840c4400486602d0600e54101c4400304071501d039400396000040300c0d00c0d43c0e51984280c1d2184215031500c1d16482d034060024001644501c01264020785030b80600742481c00c00c1e0040b81c94070015032021130703d0290000e0103002c100250307004a850745280092030f014045401d400f094242ea110300444c0d015503c0b03c1182642100c08026213001000c401084a81e240b8050500a000f03401c620001c47c00205501c0a014036584140940c80c05440014060a81c01100703490540c01080c140420710802d4105000520140c2e50074004040105141c02c0b0420003034000c0d10410038030301002490f050610503030903005801680e0000b00d00b003507490b05032201f030104060401c1c0d2040a004a40c4244206088100c0321001d00d0f0380b15070a00710404c2801814422101c400d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492724649 1250 492723399 492723433
    0x201050112150b0111011802030c0d0f0f03050c030c0c031207030e0112060504060905101a03070507030903020409140709020a140915070807050d0c02010e061b0d0c0302 74
    0x1100000e0541c50355802e0a081c5500d095206424080050400002800300b48800c1401d5403105202c48020f001c40500703e01c15030506000c06603203004210f50800b5110361982e60b00d150701820728006030205195040707a40805004a08850600c5100011252034840c641c1e119030359071045061183c000c0c041c170301e404911504c1d49401d4400c0356070b040c0c0b500e60b50701c20813800444601d00d120007500e440300d803034100000d030310348031841a040608854003000c14289082d5000e4a904110b0303601600c0e2206404045403030301c0641c402503a400500782d15206655014504040381c207078555400180d031080c0303010130007400c00c0314001444456800d12000e8414050fa0381c00100300306c0c007544e140f04022505070041864902030341801032006a84c0148004080100400f400b0700c16000508105c41070300000035000140714040203003100040c02850011140401580001c000c900700c110050700070800032416a6040741514644198106058102c0f220301d25045c2c1d009091014181d0700380c1c054019584141044000703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492725899 1250 492724649 492724679
    0xc0201080601030e07030213021b07030807170c011509050f01150e060c1c1b120c0203010219051b190b07110d0509011e0c080d0b041103010602010501 66
    0x16103442005507038440c0154081c04244412091a0085050120040e500c01c0c405118028407184016198944a030401404041c49103914407940c6c88030008000003040a4201c40050381c1c01074454842900c9088541654090b0480c050165420100710115030707035480090500700c5401038428025500d580311190040b180070b025490304902d44046602d02c860144140c0036008601504a61809201da094541803111311541103402654803240102030711b5100007000e4903246004945080704d04655181c80c85404034046010038000e2402500c025982c2c2075041d20745e44014140251007450955000400b280d002c4803441c001c61382480003110f000000043e1b5140007032841e480e03808801103151906a100303c07000700b07082d00b0002c503882041041c000500c80024494031507201c10380c44120300c50016001d2100780410701c842c1c2038280000101654413844c500344258001c441c0b00e5a4000c0c20344079201400c6d0703900150703401c103040048802e100d410b02c0e00110f040f919a58002c201d40e0740c031008d4080301244 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492727149 1250 492725899 492725903
    0x209130f090606140f010f050c0712050d02030a05190c0b0f100b0901050f07061d0307050601140f010c081603170106050309060c0c16030f0311030c07090e011113030606060c 76
    0x22884007950141d40203060000341038846003807a5080145000e027a601c0c211854011170203085c0107514400c01c004081100703c840c6d01c1e46d80091806c1c2050008010302c140030b00d140d80205000a44110b1103a0340c040c0c20141c00440c0c000e95429001d00e403216010443d0703c0155140482e501003a4000070300040c2000950f541080160749440c40c01c40da00c0412502c0d9000f1010548031196175590a591001c20010501c0c100c40c183e5000e15101c07861410301c02d003003030016480031502c2c905051460b40300340e40b9080d0b941c0078a00c003402c01d00780849980c10520210701030704a1455224030744492610038103400c91108980c503e5010a5600755a03250b400440340b502003504c41c0c900940c08880480d84d5454402d000d014101c40c0241200c05030780b084642d0601403e4554025103002d200045c4070003d05920502e050703101e200b002c0083d480c102025800e0382d924041032143c00f10883d40d490740559214402c1d08181500d210750b0035001e4444460032131010704404680300c1150fa162508000241413030203000910310b925 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492728399 1250 492727149 492727159
    0x405010509040902062818051012140c07020307080109080a050714010603060509150702060105061c1109130c050403080702010c0204050a050a18020d060209130f09060614 75
    0x3071490074800908018903089900180a01030542c068940c4c1c940140e00c0301c0201e4114510304564400a4840e0b000c0b5582c6280f40c80c0e06020a101d01e8171003030b07140c40b82d1032071500c1e200941c41d02c0c241c41c15000388900302c00058001c00e60001d11100745120b40c0600540e0b1b0007241550f044541c0c1e030700c03d50700300c40015000810b550710904c403010116000340003174140d4600817112814100c001c03122050844589410031070704107136508103100c0c130200100856405485031600700200341c00d0144002e50b94002c144610fa02c59000080c903004480ba112001d50a040c3c09158140030044000143e00110b0b01300c407080c2c0340030b480164404450101140a0034241042644503e0301d0141103840b8a0015030110305c5c10383c18044481c0c041130040c2c64a1091920943d070f42e00d0005510b060659401c003e03100800001254610840c0300e200260f5144100e0105681d802140160b5410181c0082040c102d13403480c04c85042d43ca0401200c5520721241c00640c40345201d01c1081144135154007000690285050040d5001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492729649 1250 492728399 492728407
    0xd12060806150a170115080d020c1509040501031203291306271d19140d02070801200d05060f060c030409050f07051e12070206060906040204050105 65
    0x501c180360620803292030050f244040b01c6803903441c0350161442c1c2c00704003030450f907442c0134800d5030103054040b07680604000005495855003c902c001d50303d40009103840d00c102c40c040c4000328003071a882c2c2100e00c0600050014400c039a56400c02c6010d0301e242c1d210b200701281c00c11407124075465521600c0000d81d040c1c5100a4680d04440003031150503043c01d03281044983d52020085400900c031865200c002112516101a046800c41002c041d6046c5600400c100c80600c02e400d150400040352800140fa02500d10111070070040c10512909050390100043ca4040c5000e441882da41c0815003100f40e0720303c0c40090200e0b0300e403520040034200c82d01a00b040340000c2404074808065283d004160042ca00802c6541c0d014000d4002448070361114031500d4096100040c100604013850081540c00750700b52441e100b0794035110f40080c1c01c51003036410401781c0030f000103c00300780c129820064a03800c42000d81c0b01074592502c4030001e50788250503903085100c0c00e68070001511a2501c1d0013100c0680d481a907802d418 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492730899 1250 492729649 492729661
    0x30b010e040206040e0c0c0705060309100513080a02030d0b0f1309031709010603110f01050403020d17030f0702060609040c06110c10020601050108070c080304140109020409050d12060806 82
    0x6500c014204030381c407001c200300000d900002010b00c03034007030313048070b4240e65a9021000e82c01c0e1074032105c0d60109001f9a070600401180d503102040100c0d00089542e0f01160590b548031201c44140c0d4080b600510465011031500c082503800400b03804101107950013001107041000402410f030380c1c0101c0d4968864842c00e01100d141c1050742041082c9440381c00d15000440d0f1424006014020450b04010309039580d81d010414082d882c60b0318500720006907891412440c82c43d00003452445540000380c003c85481d2801410808403261005400d80c00c4403640392030f42003440070884490015595200180314000211300a8039045071542c0c0206c1d0310503262410744d0718014068480725a02100300c038140c011040d440985413508034090000229540c06400d1139030402c0c00140c0a210085d0881c000c1040c1d5884c04000142c800301207030740094006202c09100d48000748131502400e80098001c3d0801e0405c180c0b4000c01c68005401405100684c5986001c1001c3c4405602124024840e01040c1c0c2c0c0142d002c00c1d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492732149 1250 492730899 492730919
    0xe0a090507050d050a060507120c0504050d031b15090b01090c0c110102150a02130e1e0c07061e1b05030a110403020306010f06020d090501080619050a090f050f01030b01 74
    0x80e11074494016603008410507185c05044031812115680850000c4031100002712281c850005071680c0d5007031080c00c1c1810072020403000c11400c030004041c0b0010040080c5140c0c41680240c0c48a42d11646d06103544200102a001819401d54101c901c100c4840010920550034040c07200c08207020380e90740a4201d1039440b004000c42c1c140048038154001c1c40403071150b8410515403984151841000560b0725001008812803200700c0e9400300c5450121103040c8090b0001e01901d6455070b810460b02d04103552101a0b140165208100b801480540b8062855401059094501d50380c00083e800400c90402e80c40c3c0075909841003215281e00180d400c000040919090f41e000d07250711031010001d9030a042d26a40402c0c900242a080303199904890b070b1003042020b5040040411201d4940340c84500e903403601740043c0c40414042e00003071240d20820f03e00e503090700031401d0305002028000e0500d000345a40f100311100078420103a00e201c01500341000a51900c2000c07801c60b0490b584241c0d281e115a1134000001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492733399 1250 492732149 492732169
    0x3060b0a0b070b100503010c0e0f040509060703090507050901081c021204120f050a030503090f030a09060509040e01020f120c090901290304030e12011a22060605040e0a09050705 78
    0x1007a124036403010417152800d21441a000501391103d0400c03100020400c00561800060203109a05000400003055000704403d0780000b00790802056500e007a141076402d04410350402500229488000a0030703076000201c0144410381d1400320002d14074406002ca85401003c0c0941d101560308000030008100c17424403004e901c82c0605e000c88071068031036850508051094070150001540032060100803d4288004100b210050005514000400f9000b4001d656107108200601c80c010903603603555103903500880148403011000b10358070404070521003e69003040c03064a103030044020000300b0000b8240111400702400030800041d6a1820300341401420440b020305030448421141c0d5044500e03c00040c41c000e0f407003515146500c0c0030240a01c00030351000c0304119426070400300e00f0f02001c1c40340c029030b1044000a443e40c1c44080d8400480721501c4544607031907001140703070500000e03a6582c07005c094000c0e20700d00503012103191644581c96040d40d02001d03020780a40c1021070100b02d41d140c40c45400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492734649 1250 492733399 492733411
    0x10e040902060d0b1003050613090204090c150e010509030709110f04031a090c24070804090c0e0a06021b0109150f020d09080a0b07110d02030403060b0a0b070b 70
    0xc5503000d010780c08540d0310f030443c04008800c1ca4407078030410364915001010b0030700f0207038600c3c040085251000020b2a140c0d08050350f00040d50340d50301484103648450b0007124145030400b8110b00200e41e18400c6c40004950050400001a04e05007058001e6114000b29001048000c0060049a0600075907000030b0984188c4012082c03070412400984040d0240035000940c024003098000a017001d81c10a00240002c00030080d58108003860a03403070b51260700c1900c2e203102c05502d40d000d4a80c8003007001d00070f00c280c25016200d9072006c034000400101540152031034a0302c4c0d90721400380c588a5404d12600400034001c100168218044035410b85284001c0070044440514103d540c540d5984049400c030b0080c6401c02000603103403070fa1003030541d0301041050007150082c50900038091405080315196020818000c00c2a6009800b28141c140300d181c080114056003003c0d601d45111b09880070750340c1d0b88180b10490b9590b003800c0a2030854501a1040380031101c0e240f180f50f20f410741c19038451803d80001001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492735899 1250 492734649 492734651
    0x709061802030c04080a050a05010f02040e1f17031905030702030409200703051201062c040f150810060b031602070906060e18070903031d030a21030509030306010e04 73
    0x20000390325600f04010446c00b4040d0001c0c0801500c1c60400a0070b40740204c1d4281c101a00422081090450400c1c1095000000950a40c00c02e100d6014080c44801e150344909058401410041d50b580740c01300042c2b440b82c2103001c2c4002c0d0f0055601c0180d580b80412580c1d640560802d010401188685c0d1b0403c005c1015071001189100402755a802800e80203640c05400185011424041120261141901518641c200000484a0018020075101e00001c0540c924a0403150180007611540c0021488801840c414803506550b10000c0c41c4000403445003080e00d104c0d280e081001d081c424407984040ea58045412480c0d40d947c0f1101103908000b03c02d40004500c204007000070080d515100d01c60151038682c6d01c00800750540c504001c298808030001c58001c3c4141b0061104468001c1508001c8075418207003082c5083c10103c4a0142c03001100c03c150300740c00b68095150401a099901420346810103410251200030007400314100c4800b2038104800381e000b0030225401d580502824011b04500400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492737149 1250 492735899 492735907
    0x702010c0c18090302010518031909090203183c190c050a05120a0308070c0812010504110a021e01020d1104050307060815040f0b0418050709061802030c 67
    0x184002c102c1c0c02c044001d200300d070703034840101c2050740c2030082ca50441c10610f290000c2d4005200031507120310484c0406280030700d0400c40022005e01a101c00001042c640c64210340b00d01d08031202c204411030010400d061800b5102c0d41c204034005010080200401c0c0007140c000d0703e500d2008601d1005000d52080030386210b2503040c40314100044000360141482103400c0d2a45914150912002c1001c0340c0100f40b04402c1004000c888100020303c1c0f8000342d0701480c02e000546c80320b86007500e0510707100c01c000e0416000010300f510402c0304a010b580c100c48c000d480c00c120002c000750b502e00345030150702030250050300308269101913181104c0350a000c003600140010301d00896070300721804450140c0400d0000c103501060801031450107010780700c014201410115800d141c92802c98500807040e0a04900ca1a40c5199002c0032050580c042c03000c070300c4003070410407500541585841c2005140c54040b40c1c44d206149000c595448140101011540c02e80c5200c00b400d844c001c0c560300a0f420050511002c800284 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492738399 1250 492737149 492737159
    0x1a06030705271917030403020d0b0a0e071e050111060f040201050c030a030603050d080912030405031201060507020405010504060b070f0f020301110706050a0606090302040e0c1926030702010c0c 85
    0x400784282da8a2800f0f85030b000e80d1a08072861148007203845a0f01031034105002c01c20158840748027254001e584a01c40e17107c9503544a540e400103180800440d01588560800402c15554800d46501601e0290310250f060a0b6034200440c1c19644150b82c8000b41d4002c0030205400b207000000b0150480e105045c410705003100c0b400a00c3c503540101c0584800a40c44040c10000e01c2414050444820480d2410080e01d2400750003040d6110356441c200b4500c140e0000026040c00000d005035180401601c0d0000d9195070340b540000e00c0350300220303c01d074400c500d06400050207152034803e5400300d0301480d4000e07040131802c0e01d42003e540d1000030b095803281401805100180c0d000e21440d03070040440c00001da21590075003411021150003c1010401c245000c03014006150015130705001c4036411100800d0140c03e031544281041c400c20000c0c0c0e089411502d8424403c6010f15a110030740329002150418200b01900d00c005034800000300005a40042081c1e40255125a00b02100d0501640b04100c80e2076a42c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492739649 1250 492738399 492738409
    0x60c081c02031e010b09010804020907050408030d0204080d0f1e171008120703080f0406091401020c0c061201050103020313050604080a110c0a0e09010b0904061a0603070527 76
    0x48600361030109409540340040500c40c3c100c140540050f0568074104202c1c80e001804c0601c0c003400181c41800075100091401d4801c604860142901700d0a0703e0321124080a990081c3d0860f018010b650300428810003007041c8981c0c030600341039002d55182c03a9031031105514208070105020f1132031308002c0c01c64984800c1201c2902c209005680f80e81103890b1043c6081401d40c2001c407000103000307562504001080219611042c650f4200a40d600c03401900c5e00c0c0e130b01c5c04600500c40104010300d1602034500034000d03424194040d0012507000c40980b04202e000ca004c010f600d100d590a040d10a0702120014000c1d548240e020303643c0300004030720310215034040c1d840b024580f020458040b2060000002e072602c400754040510b0649081d100020043c0a1402d4009106036001c0d006c4c007860140804d0018290400941004040c1e240c003408981403800c2609001e00a0566270780c030245003070810300001c14103040000449100d254107580e041d080548a50903600b00303010240120b004e150038959040025510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492740899 1250 492739649 492739651
    0x4090516140a2303011401080c030601030b0d0209040c0e0709030510020304061401140a0b0408030d050702010b0d050606091f03120e0a09092021070e010b040f0e01060c081c0203 78
    0x350303c00580380e61400717020302c41a600e829510343c108021003060140115440c000d89030000700900340070915000303000c0850100101100c001c0e6002d044e4100b80400c5c0405414a5411b40d0354880304030b0340039a120b5200746e81140c1c0d10b100c010040c2d4080074401d03140324020350280da0018880c50010072141c0c4540210346205400781c01510101c900c0c05040d0400d880c105085d000240308014030b20382401c1c88d0141d62a140d010f0350080c10510382e10b0300000362541d0300c00c1d480000001c05c000c0010503942101e0811030382c2e0b148102d40c046d00428480c0c0200c0c15130000082080303c200340c0f880c1036012090450707a4800f0000d59130307145201802800c090207801565082140005080340243c002400c0d000c0b801e0540d1003480e0f0704004c143c40c01e805607039490341d84c4501c5c0c1c0440c00d22110084610302c0d44688146a80b4004042d8403940c24660103000104a106400c801401180d101c407411407900c946a091262030030700701384521700119491100b460001a1461302815400c1d989081d920800c004840a103070503a84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492742149 1250 492740899 492740957
    0x3200a0c1e060e061e0f0c10051b040b0d06090203360a1506090c0806010e15180a03050109060b03070e0601020304090c120c09052d0f032104090516140a 67
    0x4404012400d88e4400c660380b00d206410110b420f00c420740e0580d14180b14500a07010003000c001400010f81116070001e000030b000c524001c5683c2d2800320b40080c0c481d11200c00038200300740c0c88911041140f19410690a00e403180350082d01078140c1c2c4da5103450340b9401e000034018005881d0100001e1203042ca1040f940c90640c940c40312440d40c076001000524481104900e030f407140c2c4c102500428030354004000c2e500032144c01011102c0c6114020005520707880903500c02401c07503003408800b0b400c000c0140c2000c290301d4000c0d001c40715115150310305550140c0c8111825401070303100740410009020641c02801e400280ca007441200c002c6000302d0032003510803010414012545090301040141050401e03007040d032500c4a0700303100e000d5a50f03005101400c0d2a50301c0900c10540c030a50340126583c2840641b16524881184001c1c8441e83c900c41d1006030020300c5070440052401001500703081c810360211a039412240c1e075040240c5803c5107002142c0d00840d42c15002c004c021580c3c1404050005050b0084030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492743399 1250 492742149 492742153
    0x60703060f120c060f0309060e0102070212070b180409060905150a1104030609022b0510020301080c04050a06170f010b0a0303200a0c1e060e061e0f0c 66
    0x28107200c2424514000c5500041e000c1c10780b580302c80080b071004100803058910354500321040c490fa0000403009420191406440145481c01c0c04a00000540c02040658425103c0d8107005401040c0152200da0f50712505416200030008007151450076182001510001480014201c1094540c42c1c11038440c48003c0380c00e41e0140f950607118940701102281d00600240b000d0000005022244030309001d940f00c01007456460365031000440d514200600d48402c1e48286043c200181c40703150700149001b00c501600c0794022141003440301c11060003140e0503101d58800030060134082806200081c00c0c02000e0248955403281c0c04220901101c5810b030032000200007d121070201d0800031401c40300300c0d0040d5031040000035030400000b904000c20340d041d1711440c02550070b903411781e42401e030401861078070081840c43d6040d1b010a1129541d100724003d40107907840c40c144240c561030305981440f1103806066028505200344c0001040303114180030021800d41e6402d0a0481000c442250303030308100c644002c40c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492744649 1250 492743399 492743411
    0xa030c0204140c07021e1005070212010c0203030103060c08071b05011118010801120b0708040302030c06040f0501050a0507090902090303120f04050f0a02060307030f0b19080c04020c0c04021b060703 87
    0xd0319065011040c46ea142000b01e00b0301800c101c00044420794401c680d01300b40840864117030199681c3c00c40745941520158000c0c05481c0c004038001751242e000340011241c2d00e1030400624013640c81109030502c11155a112109001203507648606c1c046c3d00c40380c080b51a5034a40b9031132985064404054000b00c940c6000001c100d40c00c01c4000b50007400140c01c21503480e8004448040420708400c1056048111410b10007410b4886043c220f09510480341e24101c94450b41c010b000800401070b0f603980440303005030020419611003910070030030780c0d00944c3c0040000740d01c40d43c2884040100c1e4014034640030b0040881c1e190644000e10410303a07000c1111441c00107040d8008000910200340010903864844201600c81c0c62038542c00500a80400b0f442c103800c0540d83d40c0a1601c0c0082540300200d1144000e00314003084480100c400256212409505050b000e40320101d40542403d000b40c80030700e40440c01800101c107824051000a4210030f408541e00b91048040c907049010a110607030181c0c10035a404106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492745899 1250 492744649 492744653
    0x41b02030a1b020f0108040305040314060118020a0f1103040305010908030109060b030103170d060b0c010c18031109070302122a07021008042f130e0a030c0204140c07 73
    0x140c0c1412540b0071580d100d4445400580d5482d02c01080c48809080484c1191941d0a08031071a0080d600003c082a00190000030f44c4000081d555048079090505002440c074101c03129003d070700404070700002242d2055400c01003107008802c440c2407182d031041103070304169607911068250b07494403406035403440340040140b0100c82c040c0500800742c00b02e20f4903d840d65241d40c0e036510702155582c1030141144004240113155000750b4200034010100140815201c900d074104549c000c08001c040c44c00465010005007192040d55034903001142e8014801005000808042c00070010004109408141d805c008101040f002104564014440b050b9072140f010701d00080120809048021120b1004052203220f0050703680480383c00043e10607150079481a10703189012402d880d0080c002582912002c000d08107950444840c07030745249800c03101c08643c0710b007407150a4100c44e03400719007907c150003031500d2802003409070740150b006e0b5102400c00204801c00101d2140d2004041d03a1000002c0760005079030302 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492747149 1250 492745899 492745907
    0x7111203090d03060315020c01150308030a06061803020d060e0f07032f0609031f0c020c06040602031e13030c06030f0509030306010309050c0d050a0b01060309120e041b02030a 77
    0x12000c140f403d00700029402e549400c809000e444000e903048503000a0006c00844081d00440c0307119103400621242c8503101e160414007a04102c4201076060f24200f000540c080c070031003020800b0804a0704103100d11741180c003403001c500213465080d41c900e034981e10800c5a03c2c0d8100005c0f0941c0c6e200034090b0a406045190043c1881d03400420f00e800303a030307440149065005800008802034841180c00316910003c2801107070500c0d1104409180342c2202000504648580d50041078071030b16070364241c4481002d00c0782005054045c85c002c01c00141c0c03003448040345110005c0b05000410f000684031504107128201c0d4090010350580084800816031602000034603018040c5900d81c0400001c240300130320f400369030f090b0b50b4080101243d041540729a1000c3c148001400ba0720400e41e000b9000040004c80703400c080d0742c1c0303241c2c98508580040c0b9260000465030305ca84103148104e43d000c0c17408061010341c2d4030101c038116504a0903560140d074803001d0314080f40c00b60402000e200f8090f00075545880c146100a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492748399 1250 492747149 492747163
    0x1b120c1b0f050a0e1909050c04090804150336150f050105010323070903081201030b0f1012020a05090403120c030b03030d090807051005090d0518090711120309 70
    0x10b200402010500803840c1810072040c0d148186030b0b50001b51242c00e0b06001e0b10302208070a00680062400542c10203201e0340000400c19540b8400c40d10301c0c42d15540d0812004c50f481c0075404c41505203d0780c02202d0300a00e258042a03040fa00c59101c90811100c1e4488150803c03c000c00808040d40d1072441c0c01c000c8940e406010f0040209003010020006003904464203051141d0444140035000d03c00582d459014445101c0615005042d00d03031030760f400d9804102da441e000e00040d980c84000500041040150301c69032803040b00500c0f84000078514141e40301d403201d80000012684100d486030041400c3e1600140a44030364002d9079415001004003a04004440c0700104800c10182800383c000c5181c0c4000007128001d480e500000035159410f410000b449000d1000006d21500848860a070800c900340c000303e000e0280b0070195594804d4009090314940b040e07611016644585512a0310a0301e40103101c141d10000b9400c1850360102c041d0841810018092900d12220401000340001d4100400140b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492749649 1250 492748399 492748409
    0xc060509011b080307110106180e1b01120b0a05060c01050f0c03070f080901020f070b010e0f16051602031903091e0e070c02040f09031b120c1b0f050a 66
    0x460182d16054588105901c8010046424000c00915103000300c2c0c0f0941c4450300030701c2c0c0f00c02a010003240081190300a881c40f501400c2491150100200403282110b140742070040c41610790040c0104482a064042c00c001030b012a0711918204000401d80c4a81004203107030325a02d00000340318901110211540c61000d000354031107810500400c03100c0c80d0024010703d0403ca8a00386200c1b95541d02c3e0401340079100e201d1426000d150b011a003a0100042203c546068901040e40414140c0d03914140b6070040800300c90b0380d11041d1600c01c1400c54036004100600500d8101000703807401c44c031103030046031828403c030f040001d12031010790b440818980c0c0989040007030a045120340b02d10188100644000c081e0500402050b18100c4000c200b240e0301591044c003c140e07000c1c206000d0201740d0f0070a0001054181415000300341d2400c6601c04200f00c40d900010000d038400c3c9401320705400034174200c0b801c2268920803035010241220004c0c06200c1f454420004080d0808004505810720080c8200c000541e40b02c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492750899 1250 492749649 492749687
    0x50105190c0c300b24060406030603050d0c03050406050c0c041a0111060f0402040509100c05040501030b030d0c0803100803040807051009121205071505010801201206030a0c06050901 80
    0xd4580015105858136800509010f001c108000b2250603076003045d940125000e5014600050000b003030340d01a0400400c49000d0000e4172003a1300c3c01e40d030684403541c0d2820005c00240003080180501c500410140c6249400d190440b07512461101c00b08040b900510b5070101c008020040701c01e4150f1703002456a414130230200c00b5080e0341c100780e0b411034101040608000d20a40d140c0c0c00007448010100f26042c3e9052050801344070500c101a005402ca134060b000d885d00203424a030038038983d42000140480300c1c886517901c200c0810440d4407aa00141c001424070511244040000503001c82c0810180c03021f4007106c0c1c0030304041490001005072009440c1d010800784140c0d61000c00c200070403d0f409076841600519651076000d003102c01120a8802c5200c0200164403051000e803400320294000c6050740c0d4104020424443e0560807000d10f0358a030300510310010b408107c0c040303841740c11408a54024401078112454024950b995100c0b42c82c00303402440c00100e0204100100d907070b202200c10341005c010742c0d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492752149 1250 492750899 492750989
    0xc050312120a02031e0c040306060e040503190905030f16090509060c0a0e181503120d090c1d1e06181302091e0a06050105190c0c 57
    0x203020101d5070000c000404455001c00001c0107041a60183d4408480e040401e0445252818000c41035030410b0006503505885d1920106a524003000355034000c6810400071070030000c80d071805070002078031861200d08000410f00000f8158504010000e1840d040d100540706800c0160386500586040b0380c001030303546041200713004d285400410010303000704007180800c0d40c854904005030f82c105644048550407902800e5400003081c0d040c125a40120b90152000c800480d01504040c1c0d1800540c0503200c2d124800c109c0f00c4030510050740102e1149124250768038503e1366800c2c440e422194150070800740080d280041040c41881184031040b148031081c40343ca01411303c500414560120a0500c0c0d0651888802083c002c40784049141c60171076000749120414170b0041002c4a04440f4203280c00d000440100c00314804100902400080c2c0e4010fa54083c01c020b1007000f4416021407400c540400e1000801e40403010401c2d030111080070f0600c03078101c0c00c403080e1070043d2000250b05400018030181c894072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492753399 1250 492752149 492752167
    0x7090e0c010504050613030b010e0a050a110a180801020a030525050a030b0d051f0b0a2d0b030a05071704050d0503060a0e010e070206060315040f06060504090c050312 73
    0x1d050383c0035a42d098841c5500c0d901d443c810381444013410740003d0304a82d0b00751b00000380d081c0f079440c420f40310305520350382807001e500e480b0032010582d41040d01140026400340551140e0610030380461140024a04604621994a464a034220303070290a0781c0c0d0001c1e80340c904100000c100101442218810142010b51800301614020824081d4118150030552111559485a600c100c0c00e20300c80341e080800e035451402124043e035640030b80c1c10000f5003500d04001c0c0f403003d245003824030130040302c1002000100c0c035000101d21490324841d03c15100310109403802c0c04680001c1010241d0300c1850400000030300c5007000c400c0504030010145241e07000050380740c20072001a501161021100703c5ca810701e07585a4884000040c80b04080350001c900780341510000080040200030aa0301801d40c07602a40c00707688812082c10f856000000c03550503d002507502003070004042200d010081801400300080203912040018240c50341d40c01c00341ca11606400040c0110300d000d10920004148844d01145012201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492754649 1250 492753399 492753407
    0x6060806160206070e0a17070f062105070c0b0709290a0309060b10050909150315090109060c0c031107050d02011b1713060804030509090601180807090e0c01 69
    0x8184208004444680c00b403151039407902100a400087c44070700c0e500c68414081c0e65a0710282c0b082c04601845410001403241c00b072020140d60725a403c030009074500e404000078000d00005818507081000043c2c6020102d444c580e0300741c0c0241036580d030f00080e952600c62105040c59030060315411a1080711040300c46d05140004403561500c49050100e4401d03002c1c2030038001452060440383c0c000c1c1e540d0b010190070942c000003e2881c440111002c00e66034070341151768009a021000000d4040e40280c0640c40c1403980b80910319801003620b400811004002c2d0707108000d813041030f542040421a400790780410190001490390400826000800d8118070340b03000038002d02d407041000790502c01c03100b68060492320030202030722403241c20a034072440520020201400650042032520000031004401142c50343c0304004050065416595090a181841c0e0810540810240c00913041c8078641301606280070003800ba210050101002070250546009202c809a803400d01c0c110102d030300042300009440e130308 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492755899 1250 492754649 492754651
    0x506040b0901091802040e030915040302010806010c0c1d0405010b09040b070e0d05010e07050a12030503011a07060e030d15080613140f1e190b0901021606060806160206 74
    0x10503030000c00c07841d000c4030808040081c82c1300060741140c1040e21202c0090000001046021002d498480501c21110200c07a0070380070f240030084c00030700318901282ea00d41c894452210010301480e9176001e0306555292014110020203a040b103102e8590b0100700a0101c20711079034140710015903030b4039140d02d460398520402e090014a280140008440c030060035071140070802e0620356201000308441e40512012075a120102d205461240740091408030740a070000205620740c90f4151103990440e42405650a00740f40c1001c40160002400c1c0710300400300c0c40c02e000300c488078011103000c1c55580b03100220f83c90546115010110100c001e00004011000000030400c0c2e1040f516030110651800d5468a40c3c0c002c1c0f00b40045114a06c2030b130b03049031002c00010500c244240015015500502c0c8046001500ca0520b00ea013a49200c00c042240300100c0c0410005a03444406c00000528007014444102c001c1d0a10040940d910b03030762a042802070300001c02c040e503003206420280316942d018a45000f0f5680e0f0b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492757149 1250 492755899 492755909
    0x206070e090423030903191217010e040215071104060906060815010309050a121214040320071e0e0105130b1906170a02041d1e0f04060506040b0901 65
    0x184600d480d0291000c240190380c54000001c0513a2040104207c1242e8840c0c500c007010340741c003014021030b000300324000e40a002d90f009103110801c000b07078a01002d52601780e1005009a81040c0e900a0110302d1110100081a5251244000300d81c4c030b41c00032061000701c0360170b40c10920039149803090a020f1280c110710125030202c04126800503030802440100c002c1c0c1040000100b15100c1e541800d01084540c81e2000044545665007042c4040c4146050040c0caa00444012250300079002181c0428480d4110844011a410800c441031514840041c50a0407a501403403800b0401c1c1d03c25800400070f0780900c1c00401e08a034000c00f02d17506003000540b1041a5212010f00d25036030b03412203c1c4544880b00c600301002283c00c1d030f480b580c50b41c41c2c0019000210310b0f011b0388407841c100c0c1c00049030949644240c0c1d064540690422542440300c00411a00e60700103001d008803600212038048144401c0d0b00858400c82c90350100c075109080500d0440107a4401500c0a485141800c80e190800d494071800c080c1110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492758399 1250 492757149 492757193
    0x20c0121180f03020a110621090111180f060f12040c03050616080f1504020f12010b070203060108060717042a140a05100305070912030206070e0904 65
    0x5500410200070281100c000102010000c056007000e0607004100d801419000d4807200908051440401502c0c0c0319614864450342c4040021210b2030525981455008007110000190341c10032244039600c0360800a400000c050600b011441c0d02e04000c5046000602e0688926061032030305041c03000d80b4065801e000140704045000501403141000060006642107000d441090030300342c1d140e2081200d180e051401251484001c601614104d4255500c52a002c41104201c4920541040040d40c440344801400c0362040c89241d440320411003a0a0003070040d4031030301d03a0342d40151040c90700303180050f40100301c41c0e04808100400c56030000514800005150f410031200c0e9124900229503803100f1300c80d4030000c5072000b00d0092540019011030705076598440d4481c250140344007007080b008402d00646402201e0f04518090701030181e0851600099542030920000b5202c10b000c0046011100041d00180d00c60414044c0b12074000b030750b0010415080d500c0b51118545900c4405c42c414110751421425 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492759649 1250 492758399 492758411
    0x2205070212073c060b15030609010b0f07020406080c014806090c030c12021c02040603050f0610150c021e061b0c04020901021005100302090702030a020c0121 69
    0x41c210103031841c1000c090000f941c203a621a4107021000b03142c401034541c059003444103641c2d00070702036a080d42e114810040841500d68203000f1a8541504201c08455034401c0c20722049005a42d1030040030040c0c41079400a01ca41c411003c00100f080390b000c0400c40b10f00000e242c091740e4540c4100c0290b104502c010380821544040c1c844000b0480380c2c40078024041070314242940080150304405a002c8a008000c0940740341c4e03c07818210141000000025400382c4881d10709034041d400d065a40d516540010310000344030ba5a61201d41c18400c0c490500b031159040034042204c04e060300c030303002c0010f42068040003540c1c04400380040c0ca5481d500b0300191042801c1011204600d82079610000e04010103070089403a0f07540d9104800d1104a400584a2a4003031820b20310007904244c42941c00191051740109016481c00d0910b4000301000b43c01c1c106000848180880582c9800082600030349003a401966140341c00c8a0090a1241054801c0d04002055400b48158620078050290030684a280002e0b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492760899 1250 492759649 492759713
    0x507030c12021f020309070608150907080405010c090308161716062306120a0501090809030d0e031b010504150503060a06030e0607050702220507021207 67
    0x20000d411008020550400681010340c2e0701103200f008070380400700b5400319076000041c807409901044609100c503911520040200354403500c000c0c0d07007000041c075181e00e0411005000c50941314044401c2c40200e0030301d4050108000302449411400003003482d0244140f400d654070741d5070303502c6010707644655082c54038604c000380b081e24205a6000b5606c403010903600c84000d020390105140b00311040d0f5036030b03140c0400c4211441c0f8510040800030b40010306e045155031044100b01072440790301251880ca119102318500024424896004805c0c01409400c0e01c2d0460042050310f48001506940c0c20084c0e170802642c482d44000500350400c4e65011001c0c4c4100080000480f41400b4680c0401c400b1800002e00001441d0800015402584290760b803c0345140c44030f006405580c143d03181015035501070000138120511a20113030810510042c10b502242040d045581c1a2820103500e10240d01c4e924014030200c10707010009a1003041c13841101500302071103501c0318481101c510300034039001342a101800c0c10f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492762149 1250 492760899 492760907
    0x10906030812040503121f060206090705061608030c070c060f02060411030c0d0c03050d0c0807150605220e0a0302030409050c0c06070801260606040b061902280c06050703 75
    0x4000356138811b80850783c0307404035156604080c03079110150100071000000c40c0c9144041007140c85075040f1001490001d00d06410700c0780301d90121000444101c05030400b0750015140000450054200ba11000d880e80c401e03040003144240c640d0311050038403129500d80007001d5000b241c142d50107074106510100800400e03010a00340759902c01c106a01c40810b116680800c40c0703100114096a0090041300c0c3d40006900d8269000c121020000d0050740e0701b800300800041120340c401783c15031419007002c00c1c9a655000410164460107524900c0c0040c014882d20510000d40b10706503500344804001c00700c07002c0c80c0d180070f03449110314025a03c486440f4070014600080798803c5840e04640c880c2240d080345099070008010582c21b000d100b215960b078400001c003001000c504c8485203a48103025080c00e440d60010000103041d0300c108240c202100b4400402962030b0031f4a8045260055006041510b134046c62140400011080401c1d400900300c00c1500400c1086d000581500d40340d0410310741d80c00709410155 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492763399 1250 492762149 492762157
    0x1020606090c0d020a26010608040803040c0509010308090108150604050f0f0306090607020f12040e090c12071e030f080c0a0605040c030308062b0204090203010f14010906030812040503 81
    0x720050001610040300c13035105c0762003500c11407000f44070308606c1d0900980d2518140c0078403602d400100c1c031001103004038002c0d50046401c80e102d825024107039603807100820a080026401a41d2007100420000c1d50795801c110301c240d0101c039020380d5941c0e1202410025015008900605010361128044c41805407600721031810603030401011100c6a1916100c69540c44504545010050003110100e901035040050004190824683c1140c1041e0a24820b61400e5030003c2c100c400301e00c1007400346289900d818000a0700d511008010b00b0156043c4500802c4401d1089154000e40c00655010000b06410b02e606001d5154005401c1342e44046003d0300030324080d4072890281c107141ca4582030100304a500710303255048034440d440e81c824582e0380c075040090f00021620b00f00005e00d101e400c0480b84c00100160301c6002440144001000c4c070468011a0858100404a500c000d640e0214004c021954509041c0103001c0304109006950440d591400315000703c0c4101c4207010012000b050801c00144161 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492764649 1250 492763399 492763417
    0x102010b0303030f09151302011116030305040807050109080a060b0d0611090f04050f0103140a080d0204141215100815040b060307050918070b0a02010501030c060e01020606090c 78
    0x1c98483c10301c018110703065003007074407800c0152041140c0386d002a9424003403c1d104449101c525114a2503a40042d07880ca006c1940c0d06509014482c403140c1c040c44200e044001031402039495580b620300f051001840c0c4549600294140042443e0400281d00d0000c2c40c950041ea104001056049612010801d48a0115401050141091381640007500030341e02900030200c0488070f84042405010910040741e109950140c280e4441e580140046508030380b50802c440a4041100c1c01c000c0642c4403900070f034000c410002421070b000201003199400c0025401c804c90790490b21003003900d869407081d540c1c464660403d060710112000000e0300e10b03846012488010030103101a281d00070b0000b0b10070b00034083c0880d0101e40601c034800c00f20b11300e410009040420b441c405411241c03103840740c00c807107013004081c44440c2c5602d200300c10000c0b9440030024050300d0041d8031a000450a07504601e0900c2c81d1181540001c010481d04240905075a80e001483d00c0c0c000000b69280441d548400c0000801441a02d0070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492765899 1250 492764649 492764653
    0x6070c05090106030f0c030506061605100905010504020f010809070314031905070b07030605030a140102090316150c0305030a0e160609090605190b0d02040f030f030215061302090102010b03 83
    0x7801c260560045c0740070b410008002c200e0007103c6107080e01180e0003580c0c1c00da0000f506008106018002c500058079036405a4200c0340e494bc0741e011602c2c182c1e2544101210640d4586041c001142800c00700c2002c542c600b400c0042c10703881d115a185607140841c1c80003034041144e140d8501d16000d002d108450103400c1040e40d18101488046024210745c0c042c00003100d2003110080080c100785d220b485000d050760401001340c203c16907551070b85507020584007155440c03550b0070021181e0031740d02004102a0380d420071102e054514030f000b94004101380c82c44d400e9420f110711149500000303540042102d40c80450100c00160102d00c1608485c82d28010a0484401c1d4504510100b080e541081c200000c44105060600415403140244001e0704a100400c4002c000001d10038403040c0c2044022307013144100040010304169a8250300719203618030b540180c0da2035025030b02d820107066041c8030301c181c0701c61250000310b0b103400c11a0228200c8011440301c0c0703000036400b00c0c03103401d076a2003034004c1010201c004007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492767149 1250 492765899 492765901
    0x225050d080c1b060f18040f050910050c090907020a0c140a0f050a05061612051903140f070201090c0e160f080a09060e15041b120206070c0509 63
    0x3500d403825038070100c030081291181070011080c040d080044009043d1010f85442d00748518a5070301400c83d0004403800d4a08448500000015111032150007a80c1e844030038041650b041070600c4138146000000c4288580b030502c030030070040300c04840c01c4030720584040d01c100440303a50701681281040c00e0740788002e01d981e1840c00005000340e9140c050040742d10303007200d985100a507194030b1034a03140501e104403600618100b2003040310b813600d04050290906201d154000f11a82c07030751200e41c0003c684041301d010990100d07102c1004000340170818010b014038102009040b8581041c003c0600300101100c0312001c0c9200040c08040c400e40144090a51041c40c2110f00d5031a02111503c41a003100e04200500040d984541c181e44140380c545020b41c840d807a00f48060f103410300c0c040d0242c8810302c0250b6403140c0780c01441c000080200b05809500d1a10742900c803150030b0500d408605226121443c00650412610a1021414441c401c4084507030440342d00390399512501e8803074101c014a502195101000700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492768399 1250 492767149 492767153
    0x605070f08030a1b08010509011d0f0a0e070603150504062601020c030414131b0c020a0e07020102070b0604020c030d0902041b0504030b010b13030615081e06090c010225050d 76
    0x41145c9040c2c68089400e4001a80c80ea010000401240607140141c401c0304070205101c0d100d41101070760010390301400410321407407a61080d0301d4002d040c0e12440000c2c0d0749810208c01006030340c1142e80580400c540c00d01c0158038120301071400001004580303060241c5402d901032651025411103613480641410b41e51100d54a41600d4200102d0002c0c0354020111000000d05024852064005041c9200300c00c091007420480e04039614190ba00d0101d030030041c8110042899410f02012600c141890b50026039180503904d024842c01c02c002d001e480c02280144000c51186001009580d500c0c6051a00040c0d04080c0f400040c000c0e240001c0e40a01e17292020025004265022006000ba43c0c0a00d105480300d998603d60b40300c282c401da003807002c20766010400c10700004400b5040a042d80220a0700c0c03d600d15120981207060040d0b103041d19411190303a101400e44201c040c40501c0d072114006024044400035440043c0d1035500b03010040e030445180c082054181c0500c0e1940ea0082c24014001c250150140c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492769649 1250 492768399 492768407
    0x3020a0f0302040501090513031107090510170c0a05040c0302040b07060903140c0607050307020f06100f05091006030b03070b070b041a13140f250605070f08030a1b 72
    0x2800141e000300d0400c80041070a5065003e094011801011039808c000b8003a20200e0b0340c181b042514070394902510388009054110b5004460040381070450000245141c840103201c50340d114023003c219034000030001c840036988c1c4d1040000322442654045030340320810000b14024403c030f402c10b040002001c250071062145561006c0307800381c440d441d0b10300403440c51010701c03003903008007041c6080c541c0c402d4001482c0c0c184a60b02440d00714095004540c20040c20300c81450034a082210104030701034030558104900803100c424500245425500008a820071002c3d6860810720360181006240d1144030040700794404002a0005121000d403081d00d80520346010303181c0350802d0318103440c007203010090b68001702c505101c8a4055000d400d43d81c03000c0007043d40c81104148001465480700c0c001c840c0701080020003442200251540c40d40e0aa440d251211003101c102882a0492000c00c10140120000901c0110300441d1058204108948a688136540e0f82c01a01e5030803003030280701c00f04a001640d030b9500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492770899 1250 492769649 492769679
    0x120f0403230c010c0b0a09031b03020a02030624040e0703080427140f040311190209010b09060d0213122f060a080a060815040618030c020402031003020a 67
    0xc100300341c60607082c50340c004641c40101400040c01352844080840d07521011580600c0f501d07031003400c0c40b00c1d09055140d000040e40f84601c405802503002103522004500e414081b007030303116581000340c1e020441e0340111030313a06002e640760950083d0fa54807a94044000c080101000441d4071040c1c09649a032240b50720f002005c0314103024030b85040c404080c2012220940038425802c4440e82c155400c51b0740d88a030141d4110000381090b424082c0108140010410601c22010160707441e45581c00c0107e0148144215448140d118030005141070226a0040d03448204503000345180380c50240e11546140100180415168007039241d920003e8144020003003201300c0300fa000c48055019075400071590240380040760721260707401e602000c2007007041c2c2c00b54003690b42240c00c000c2030100000c019859010040c64135811034020301113040d040c0100420812603001d89062b40142c01644440f112880d0703400780c07401088000007440b80f900800001e106241905000000759002440305d1801c1d0340c0d60144860400e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492772149 1250 492770899 492770963
    0xf0d0507020307021020060a0b0f0d0224130f090b030c010f050c010230310305090d080406110c1305060a1d071e02120f0403 55
    0x420800012685800402034441c9690082c01144816039500400c83d102055140944801c1d903524409800c002000c12009214414540f0700060084880c41002564607000d9a05031061300c08000b0000141c549200c010800b0b0350405181c0004443d607001c040c0c0c0c0b409152004110091016000110706844081c0c02c411180841e00070003820b14000185920354114044980c0032540840f100044c091040c002054800fa11200040c1400c40800c901d8450b4201d8010041645640c1181444c000c10b500c401c00760004100b031070907400c0c640f01f0340c03c804c0391801404504401d141c10099090034540070b0f4003210310100b030003094090310105610300444281c0145c0142000900044007282d0b0b241ca0000f200c5001240c020a41ea03c0b0050341c40340203000d8803005002c0c40d007000c01100700240300708a0005020340000a6409056a480c180b0002004c19042842607043e1000c844d1540c00450b0700420b581c203003401c000c02007903900c00040c140c0554038804c6600c001c080d5801280c208500b80e2a61062040c080e03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492773399 1250 492772149 492772151
    0x1110f0a200a050c09060916050a030605060c0a03031d06010b0a0c1a01061d010c0f03030219090302030120031314030d02071a070504120c030c031b0801180b0c0d020f0d 74
    0x515130101f8040c490f04212604041c030b04c11502c10314009409200034080c684000d20340445c03c10f40343c80220301c041c1c1003084840307615030100c01e9440030540c041c09444c41c044a8080d0382148449407c0403969280b42c1840b0301e064828000481d040241d11410810700450340090b001241500d40109540c0141030910031100003030500c01e4811303400d000070b00c1d0b0810354860580d00d000c40001e00e41c03a0744028917141c1c04224285542003051041c0b043c025070110403180615110808094910300605003580e642c020b40c000c68002481030b4107001c400340415240c000904001c8030a544495203031000201800e128080b2281c480450f050b60410b900390020600c1911034412075502c81440c114041c4440b4050350803002281c414801444407801c0311180e0354030346014803402c1903810354a0703c5000c4001083e81090740c0c1d800710100d07440d281c20b08440c240c600a20340c0c14005c0041800c00b0b0540410790035480c0c402807103c50b42c00701240310b49404006441c0218824401103503101010144041e0a900ca08090b40e041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492774649 1250 492773399 492773401
    0x30415021803120412230f07081c0503040308060f06032d0108030307050d15182f13081b031605010c0b07120609050901110f0a200a050c09 61
    0x43c0421009460407900e600544c40f8100c041e66680300c00300103000b030354a0141010010310322010103040204c1240c1d501c0c1000500500b5092090490400c103944601240003d003c41e0100302c5264400f0890b03610581615040c03d043d1134034000200b0220005400e0303a84208007005114407003094000b00445805484a40c2d800c084000070b10f982c07003080074824500b298100b4000256124022001049880c0450b080080d90340b650640b08000060903800c6010032902401411828060520940c0020303220888082a0840401400c8002e004003d41c8203800030400701d0b03040480d0070b1902031880030b000c7e000159101710500c1c0d40d02000103120221898481d00c41d903003030f024031403e40424800076610103079600030759501d154980380440c8101800f46020061100070714000000c03107203c1c100c05808180801300d0a03062814141d400d6540d81c0107103107d4110200a0030500c614000215040b410041c00c08000c0131140c0c82290f04145201e0440840341d001e0340d14841c080041c007042a98428504860b03000c41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492775899 1250 492774649 492774673
    0x90501181e0b030316080406090e060a03021e0303040e16080f070c0f230f01110706090203070506070501020409050c25020a05030a080d0c030207030503010308030415021803 76
    0x20745030a1420302184a0150030866050000d070b40000960b004050201c03840c0c0000c0d0080316143c4079035820180c070700351001b0500f07016036640817102100801d126490701106051400015404e8030f9144002441224001110648014800c01c0310548800040c02e807a00e840d9100700410b06903408468032010700c0d042d031410380f07075880c09403107403d004da1905040c1c80450781c3e4031030050760b0001c40d00906550600d280c0c0040e6002641000540840300101d076074800d0010381c100a420310303110002c50030400c180d05144500c400c03001032005451609400c1440801e4200742d40c000701c1e042c034020350482500080000348010500c4015001041104ca95180c10400ba0f5500c48001c00540203603021000c614541208040810081190300f80003030780002c02c21004580d8840005c0d03d80f40d034071035043368504008a404602507a0600c1022410300c1103040541c58442d15980041051205020050201c0004008a003d001c01e0b00b20000a600900c1d40c11956100c0c804000300300070000e00e840318401d101d40c5404201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492777149 1250 492775899 492775901
    0x80d02010914241302060f0705011401060f1d0d0c031101020105060a140a090f06060e0d02010926031305130621050f07060f020f0102040f0b030901021309050118 71
    0x1040e6100403803489104001950b035080e10307034006000607640d07490414404c00903035a40700080103a0800d1094143c0e17100402d18145094a5080f074207100c5a00040c401042210342002500c42c940803140b80040c551a007645e2120900b008058101d1f82204080c001e0b082044890000c14054038010603200c0181798084004a080c0d070004c131205900003800403420090807001d8100021000c03402041100000d84800c03a010403519940503003070205840c1d10f4204030781030300429014500c10042d41d030880c8042964002801e980294400c4104200e40f85c00c1754100a100c191500842c3c90841c0c0c25242d441c8101f80e100b01e42e0f0502030217503034801d40541c281d0841484180c031600c812a2403540039981c0e000c0c8030700000d9040c0c01854500ba1a14014007080c000303045014840f12020303114644031030510b82e80c0715000078078201c01030104003202da104010520040350b884107500115440e1500c01d580c0d0391b481d61052800381c014000c00c000107680e0074a0211f0000d0b61a000b2505890821030303201c60708007021a03048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492778399 1250 492777149 492777163
    0xb0906010806011e0305070b1c0b030a110f040f1e060e041b150c0b01171b190e04111c020d02130f0b030d260a090c06050903191a060109080d02010914 66
    0x2c1d90580c8000c20007800937444039240121480010a801c144c103502e00007140560300c0c0a10480481c40e070302c20030004140c0d16100603800604114000f080300d2400c00f4411070880201620180c1003100490000082c01c1c008070542018100400410b1088000c2c0c401c090403217100da0104803a44035014002151224155048107a07148816005002c0285c0c0062020606461a610a03401038101e080d1808070301103000c0350500500e00e668800300d40c1e2515041c00c541031002d90f2903480c4140801d020f0303060303003550302031140941da60100d400781007100076880082c40340c00d015403502d4451070800c02c0e400c05240040e48510049581982a59840c050404084032000d800c85034020401c0c01c10b42141d525164100c407681d51059030300c80002000c8169896070030103100d09500c820001000002c2944642c102409400c034200000e400c482d00203c03c907034410740601290703d64890207118030000035509a200704a010002c00b07159080c7ea000810001009000c2c0808110907100c1041002c0d5a550048001901e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492779649 1250 492778399 492778421
    0x2060f07080a0c020c061305100c030903080d09020d1202070e01080304090e07090608252303010f051f080604080a140702060f070b0906010806011e0305070b1c 70
    0x100c0c0c2d5940d418042c0041c01c05103401411441140300d4209280c40c2d00d00189000501143c07880d0394940b0704070800410b151144c0e001000c020868807080e0000b900008141c094030b03408000c0c50b07111003002480400030050910080c4d8044d0007840c02070244106000428003040d403d41c02e4559403a00c030031341c4520f404028401c8541c65401044104070807840c0f1380c001e032620f950031001e44044030f580d2868201030721240c6c1c1101c07000c2e40240140284000d009181401400840c2c0603041c1d1561814000111310340080b00f4550080b031000e00004102c1e0b60a600081444040c25030030001c50900c0c04005160006000c0320b450071400c2c0700320226014000040c25845603502645076440c0c0b5400d000200d954042c0f2654888252505010100040c3d8844025091104a03c59100d440f200c0c0790503c1c0b18a620094014402074102c00c1c014000070a000c2000d42c1540d8501601c0e40080d1820035151010404030f52014000780540b5402140e01e042a100030009043c0180700b91940501c4200c02004031000d003048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492780899 1250 492779649 492779657
    0x712050105130b060d06060510030534052104080409060501031e0914010509030306041128050f040b12090d020705090a09061b020d090302030604080f070f1202060f07 73
    0x11345585804144a03190078414940825426030f81c00218048400d20071004010a81b15801c01014a40140d0300701d500c004030104440810844080d2000740708802c0c14010f08004000540c400d80752414160041d04404034950144e01d8645424108041e0b08640140000d81d410020009243d40c4a03020b0302c0000321003004110300d0140100500c070300512044100f2101a01281d001c1c03403806c0303c01c3c46410710561001014555900c0c2c0035040004941e4803000a800e4204140440002c04407021520109075a4140800c2c01c0c01e0131683c000d031018001e5108100ba921b00006000c140c011440000d080c2c50340541c1d100300081c3c1c131344400c03080c3c44016140c1000d0060340083e108110919010900c15081300024074000740200064841e80c06a4101590038200c441d01e51380c03444c00443e810400040011500c0c9011100d007030075035001a880704000740028021240105000c00392961101c110b501080d440314642ca0116074500d824000101030142e02000b50061000050345030f054110300c42e12481e42030b51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492782149 1250 492780899 492780901
    0x60806030106030c090c170411090711060703111903021c06081005190606020f0c0301200903030417071d010510050a021e0c12010204050d02010f020f0712050105130b 73
    0x40e0f1700a0544811200421480200d904403107030451401e58081c500480501c02c00708035910031b2080e42000580803000700000050020700008011440715040441c13481c0c00f00305520780c01e000700d10038000c0c2c41c1200e001c503141c00401c144c807981607402407222884084100140c842050003100c100c7e14a445000000d40080040078000200c0d0740c00194000341d0385002c1410654650011400c07910386030004809a803180601030500d940422440c00158070440090101c2030700b95000f41000710700150061410311010075803620030742e0240300b40c4000e00803211010080d001740c550f1150380c031402d911a40403805070030301c402c0ba00800300818140c161400500b42c0303034076a40e241008a07a694800e003005411030080c400d00d01c1034031800410111080c400c1d40e0041034100d0070541000b460800301800c85060b42c0c8104020495500c034010341c82c0c02d00780c090a200795804001c50003a0304040c0710000780174590061000100b0058034040301ea900060284000300301c41d1390365000d01040b400b074201000e020005404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492783399 1250 492782149 492782159
    0x31c0609181b120807021e010f0c0c08030d051611031603170403050c010b1e0f01092112050903070e0a0905030c030a23070209072106060806030106030c 67
    0x1081d9080569003402002036115907902540d03e9410ba00e1400302c6210100160000540c90030080314915400b8101c48100e50150302c3d0000b03400030518007202c5007070008a502c8a0244168010240c00034081c241c2641d640f14407901f059401404120b55090b222401303102c0d540d0843d4402c18510074803004110003549001842b105003038440720041411001c009048690480c05081c410b4002d000783d11030f0320381c2901c034907003024840d00b52290109540e02402c001000900364100d0105c4102c01c0610503154904144080801283c60000716044041400b0000c0120310b000d05880364448055409a80d020346a030342c00140c03c4849100b02041140d1681c050380040c0881220420f8050700516000c0740001e00c42401d54506055401503405100160008240c0d04403560700503030b4400d491030345824100034178080c843c0d0300a2540901c8038040d000794080e42c0050442400344841c482d107142603d00e055614401d004010026014602130740000560345c10110341c003810140035550580b80d1041000480c90300f42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492784649 1250 492783399 492783413
    0x6050303070b1b040e01060e120a0b09121809041704030b01060e010c0b060909100908040f0e22020105160f12030605240421060506100c1101030e031c060918 69
    0x1601407554010918008014025010807084ae043d61080303000d48610318000d04440d007481c49000c82c3e025001010000f0030b4644400004040204400310b0344000c0342d841e242850684c150300b0124069406400241c08001d106990b00070a040350302c59551220591901c40045440656080006150706030b02404101140f0380340102aa00003400011511481c00c140d69020989110003c10382e10804006030621036846c5900c2000041c1ca941504841e4a0510401c62140405020310151440d0080c1c4546411688141c1c00c407800d030b64000700d03460600400390a00c100c2100100300300300c641c02c0c010300605080038081c0c02500304842004040300c00050300c0c510150f04030020125540d0300c0080c10803000c20710a50103c3c0018840503400b010382d80701480b0303141880c100d40c00600b400d88501400000c0181071580011800d00082e03010a035900300b0b00012005030f024050000e41c42419000200e402141c42e0014409415a0160000148415640d40c16500226046103030f8403003103001c6038000080401c00d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492785899 1250 492784649 492784667
    0x417011401060c14010c030b0102190b0408030c090a06050a030c0309050606132301080d050403050721050105011427070809120a0c0605150d021306050303070b1b040e0106 75
    0x1251420f450094a805117800c5800310180400813039039510020740c00d541e040000018007422240c0707510030b18405458421441500500091080d0300000c001070031b00c203100e8144c038407180c00a0541111070b5101c6002078555000b00c20036100092031b0050000a040c803d0144104031900100038025985481d01070007404005000e04082c100d86031601c1d0103114440f000c0310340c03902480c00e9000d482035051400c56814010702100a40401506110500c041070300411003034102c030a0b0b10a59150000980440510f81c1a010f001500310f529040001074914000d90060412020849a04c03800c1c4906c801e040d00c5c59520006004034a500c51070000301c90600501c005504480000111105000340c2c10301261036a001d0031030f50b00010b140e45d100e641008014060180c01a5000008000440111020801c00c1c40741c0040030b4485c04a06d201c0400c04402540310401401c2d0183c11369a5508141c00c001180d601d00340c1d4841d0b82400c1451400e643c01c86032078155001daa41010008116034a0007404a440c00c007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492787149 1250 492785899 492785903
    0x7081003330501140d05030a0e0117130623130f021009050307061b030c0206131215090f06200d0c1706010210020f0714030417011401060c 61
    0x8903904101640300c80051031446031100301440800d4641c18000400d0400c5060840d442c0148108040d440014031b001c007d43d00300c48111300d00b1134026820100100c13058180341d010104070301120020301410b41240c1d40700c8442c0d5806a0000e01c1019807000020805110a895101c0d801c045c03040410b000c2261110b0038800e4900071020400d410f04a9000503041c450080c2445001c580d04140400031420300788001e00050004e07040548400c203114070100d1b80d900c01050000d04100f000b83e2204210340d00c10007a208907042e90402c9001c2c00340c855800c2c6c00c1043c0c3c602c10948141501707425107208100c2e280610620786500c148003549101c0203649100140043ca5040801d405c003001078070b00c040c80000c0240242c82640100851500760700c00001d0540345400c10345501540b2910304204180c3d800141501e0010007850700103035a02020081e03402e031806407040082c04c001e072030040400340010000281c42030360000c1c1c0b200c03146000c2010345d0500303d40480550720481c0f00c20100401c0f245016003480100b140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492788399 1250 492787149 492787193
    0x6020c01020a0818010506010e131104170f010c1b0809030d030504030f030c022a030d0e120106060e0f03030d050a021905090604090c140409020a0807081003 69
    0x44580c2a40c10610003400010540004c1090301101900910100000b400003003041e400c1c203100082030ba03101700c074506001c0e5500240a241a500c15840b880d10340d4174a500c2c05441d617858107020b0020224031140320060748030300c2806604504043c49100c00404d62a03e80b102010040402c0148041c007840c01503d503050300384540006520b05000707076142c40603140d0740040c0b10b140c03d00d00035000741120700e41c031340070940b4050609107650317000140c426561108503410f81c22406441c03404452048604022a05402400f017142e8134680c03c03140741c18200a003140c2e1401105c1280759828200c2d25288520000907200c0e51103c00a428041c001c000180c0c0090283c0749045601c0c0c040700145d03031060711709482040d4000350080c1c80c00341c41c41d0f881c000d800c040d2404600d00710792900010306501843c041d02d090302c0d549411a07003c036409100000202030031140c0d41500c40d0356a1504d030000350000d11070800460144000110329a04c60181c541c4a01c03500801c4081c13480c00e42d00c1303100d508a99920700010301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492789649 1250 492788399 492788407
    0x10f092102031e1005090d08060f040651050906040305061e06030d081f18140c0901021c0318080315040c0906080402150c0c0f010e0f0105070602 64
    0x145000764030402c95200503000b032007841e584e000c000c801c40e003006140e41c880e6040b085001180c039503c10b480d40e41141048404003014200000018018607450740124091400030000100010006807168000c02c0c02d039103118401506003a16060410794103c01a100b1001d2104000d4250f0141003e09200d10014040600300303601c0ba80c0315407400405907440c11140040750b81c40000300c0040a141070344480c05401038803503600308910142c44040040d0040e40c40e000143c800084407105d440002c00107100c241c0180c01a001d0346d0245000034a580a006209243d2503000a003078280303120101c611145041c0e00415001041100c0c00b00f4181d02d810085d010146c6562a01e8a01a141c40d0b079111844d008000076596801d0244d541d00407410200b01c418000d6003003501d10310345660002102d81c100c4155040002003070340c9031f2000941e40084000e5100908038040b502a001100000d00c102d0344c04800d903100314030315803400019115100481c401c10380c00010400500800d5116401410750107226078005418 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492790899 1250 492789649 492789673
    0x9091516050403170c010b0406180504060e031b16030f06021305130e010509070f0e07110d260f01090c0201150e09060c0f12071e0905010f09210203 65
    0x1030f49420344e00100c00110040381e608413114084c40740d440e040900301c1d02002034034a0030880002011000340d00c81280d40e070300d20014040c40402c0e0040254142c0040580e943d504032a0070025400100304d40559003842803041800b51040030032242c070140ca420200c400707000c424540c0c2c0d070006580819940c4051000c20080020075498448550884071140c03500401d06130700320140d060840301c0c010f2500b46180c0c0141020000b501020481030305488070001c0301d9540b0703500d01302e0680700000d820712180382c0c500c59030a0600c0026406442d15401c0541e12259501c0d072089814003078031220099800301e0540d2002001000700000c0c076804168803030914000411345108620f041c1c0d40e201c2c80340c6d110142a80303900c0c0c02c1040e07041c01401890b030b000c0c00f201030031401e0940d0f080710210070b8010840035403809803108000c548103500800c0c640703441146111b808a01040d40500080c41d04a10744981c40c00301c1c11152810b2043e83c010a942d0040c2d4003000588a42c808803040d4a0704801004141a03806009510003140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492792149 1250 492790899 492790913
    0x8070c060509040c08060d0305070f05070902090a15080c1803030301150311040609050d1707050f0706050a022d06040b07020706050a020a020904030e0402071109091516050403 77
    0x1032119854894980c03010506101c142c1342c942e40d50100700728550080210a640d02441c0280c02505890721a440c0c0c6903600d4021404250810b01514622605400081030302a0350014008403200340c0368a016a541c0340e520a02c1203489858810102e2000400900d0b242c40d10070152000c42c02c0300d034509120002010120341150302c03c3c0c1102441880c190b0401d85596018080c01c80c1d8005240302c850301c2c06107001f50044c00600709009507807103403082d102c8110911003820020341484040000c10b81c1e846807645403a5a4540c08100032500a00030880f0004105001c0c0007990b200340001c0c0c003e0100828007503100c0b61980441410240005050000b402285004201c1d940c490f51080d010111107052001d00a40303841d030340d41e00030400c01c5000c0100609065001c0b8601c1d00403075054665190b01d403038915080e00c0ca00c804500c0c0d141c1141c4042082402c0c880c03201407031504500290740e01c41243e161030381c0203600d0b400c0440540c07400001180219280c010a600d00705041149850411b0805407680c3e0382076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492793399 1250 492792149 492792173
    0xc01140d060605030919260f0406020a020102060c03010b040909140a0305030a0b03190b07020a02100201091a100b030424140a090c180f0501030c030c09060506160807 73
    0xa80003d5002c000c220001ca82000b0400b0001c0170002e20322880c00301079441c180540302d0350303190910b00301380080181c0c811200b038402c0d0340c000c0d60650a41038039282c60340002036860450703544c00d900600c0741101042c04125580f048034162940017110901d0181814580320241902c05002c403442030021060003140c00c0240500384e407280c0300303a891075070344c0c00e00182d19020384501c11b00c1c2a02c40c1e0007884c602000756840b6500b01d081c180e40546e000920341d465000036824000da102001e50440c2c0f0b0b481c441020103506500c800501407290001c0c0900000110440c0c0410030110b8a0308045d02c007a89050080d03680b01c0014640c403510071780c0747c80080710007888881d51032a0107846a024554542d14000da503403e4482001d54020400181000240502d0301c0d50140c0c408944076038103520240030031814000e50250030103a808140c0c1d450512031941e40c0e103070020041d100c0d072206460565514501040b800b03100d00960080f640010226814141100e118007030099501d9011204490200f06940014041c41a03034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492794649 1250 492793399 492793409
    0xf010212011509060807030e0f060901020c010c0306231302120105090106050304050c0922120e011407030807090e090c090601260402030102120a06030c090203090c01140d06 76
    0x380105515082c00d01d511226940c10103803c1c0035080000b4030240d41d0140286601ca9001d00e0049034502a056140b4184505110350040340d004000030401d019078150000c05181025030002c10071101e211000301c5c1100ea0318091980e0b0003500c09001c05010b0076918503c0059000246015420300514102a0480c0d10400c034180bc0c1e01e445400401c407900d02148041c1c01031503103090140c41d41c43e041c3d450315120650f0301c0c0c00c0c83c815010b05000c102140c01c1c003043c444034a5080f03c08600040d03a503041280341c80c62070701d80060006020152885880d4401c04c0d400e003440d8400707030000307081400da030398113444034140281040200149441d00183c2680e05504141c02403c4000103086100900c01c00e00400b50401000a03050000b07000002152030f43d21042d01040c44081da070b011681d520345100190192142e01111042406501d003400140d80150b4030810450303208005451001e07995811810603800308a41141e01a00030a0f1405825400f13250402e99132007000ba1034030710300100860b400c001c80d412034100d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492795899 1250 492794649 492794677
    0xa090807032904021f020c10080420011d010e10080601140306060405010e13020307020d021006060e0409030e040203090307020f03120a1103090d0b040302012307050901020f0102 78
    0x2c41c201c01c2000895454000409405007221840c090f004141d4006040c040700070340210203909980c480784240803030210504018414050302080b4100100100070a031026640402c1060780f00c100c0c7c6c800d81c01404100401030310b42840440c0d034192058000722038021883d050280c003880c400d0555494142c5070724100951b40300c0c42514105100010608110110310012140080090081907a229030913907048030003d28000344240e50507004100c803010042c000c00f1542d800030003807107541038002c6900303040704920754200c40d0b80d414220908020349007070b031150318041180307041450545d0405401140709a4084d00348010b00400c0600840d040b640100c46040c40d68001060380002c500d0866089954510100d00520400c19008600b54141c8a0319041394144091905040921502481514031012000b0014500c0c0030071420038214419080314203c00652030985080c10404401c000d8031b41030400c0343c99000c40e6076a41c110940d1300e80d1043c0e2030b0f1415485010014840c2120900083c9050344200c09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492797149 1250 492795899 492795923
    0x1050c090f360405010e0703020a05060a12050901050702120304150902190603050a0605030705090c030712020a03050406110c0714010c061b1103070b0c1e07060b0a091406060a09080703 81
    0x70aa1708648804150803136a8204507000c2025079510b007450f209403842100c2035541c600f074101058500707003089810304011a091400300a40c0d00c0701940700900c00d00f159000d43e40a8a81c0c0355100415100440d00103000fa0001c0c3c03548952460641c0c04901c0841c8098040d950460b0210940028402903610203000a5202c0b01000041e084a010740401814154002c2c40301d903003404c0000d00c0c0480000c0030a01108804030000311725a1081d150381d40300c542c0b125411942c07020904801400362108139400d44400e41003e5140c43d66500441c1102c0d04262a070014022140c01c2001000e21000d03203400035410070040481ea2404100207115000c0c030301c000e480005010460300d0130090010245c091040555030000d002c1eaa01080e82e08031010303880004c080ca072a070f40d050403580a94014040701c0000300805408907842040021550000343d14140466443d100182d6031184042030745c0c261120340ea007882c0345c007010130707134504024001d003802d090141040c000440d00c617400da614000c00c581c0240c60f680141d034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492798399 1250 492797149 492797153
    0x130602010b010504030201020604150b1c030e010c0f020d0602091305040c0806040c06030504050a0602030702010c031d150c04090c1e020303071b020f09010f030501050c090f3604 78
    0x4070400c207028900b0308183d8146499074002030f4450380700030006407103004a007840201d4003081d640101e40703201c0000e11074a103542d4044600c400013a401c410440208101c5068150b03151301400d69040c1c001e6110341d03624803c1086900340080040700100c2120565001e03c1382900c2541c0d041000300504a07820000290b40c45c1c1424004803011441d80078903c40c3d0030000912000c24010808071003501c40341d090205460303c0340c3c90720625045034000090079891000c410300014680c190420400a04d20781d40600c62103002c0e14240e00180e03c800c0d643c540a07884284208050015080c5050b40807290150860600e6520000c900507a64120000c200040400314019002101c80e4000c010304501840218110302d4a2003001e001c02c20100c12030040c20030210f080c101155108602000d031420040e040041c40d50b5502c84070100520a8007080f034040d424000000c0c0e004120f041555072451008051b031001c400314009012007201001900b07400a45044103616400c0001c2c00201c0009460710860152403810b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492799649 1250 492798399 492798401
    0x20a090f1e09050a021002120712020c030d080a0f1805030301050907050301030b0c0d090c09150b180126040f060b030a030903060c091a0403120206010b0301090515040213060201 78
    0x18444500098544510400481d83c0000c59840d1254103540050ba01000050103910b00034410342a02509140012045c04001040039035480c01c10f455001c448640045a08060f244d01c11100410001920140002c0da1460241c009500300104200001034200c41c034140202c80551442040d1010f91000004200c10306054440517405042454220700315410740e5605110108c0c080c052900311000401e100f400c0440e1a807040c030450794803031150724505a0b1103583c00c2c0a4080b2802d82030715040d85080c0001c44600740f10895446480600c05c1201e80c6142800540307201c9078012485c0058204100034443e503c294900c154000d0340556911050307828940342600a50307100b82e813401d0103500490711000c0040d42004884090725441480850301d069a00012201240a80c1c4885010a262005a55502064002001a03900420005481441c0d111003669290002c1c07280d400ca00c682007004010320403840e8040e6070044d0207800c0e00750750b140c40500040e0aa8108a85086900200c00b00802c60b950302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492800899 1250 492799649 492799691
    0x408030d061a070b010e060f030a0c0609091a04021e03040302031201051c0b06030f01090c03060509010204050d141f021206030105150f0d021807020d2a020a090f 71
    0x1d8001102d20f0300740d459a51070700880044c85075059501da03000118209640c0c01019000589000d000c55100340214100b0321030040300d41c0f0805000c1004043d01046100150095210703040388001d80d0071050590000344402540408460040501c58110481140228000650083d4080e41c0110b8a403001810081c12628069014a1080303009001204031360040c2828410125000141040309584250100741000380700000c02509500e0801d01400b00510048404245e038002d2200b000a507442412040c200d12940c0541d540c05001032144e03500042c19900e95184004040069680b0390f11940f1444603170700802c109560340a0b03004184090701302c44081c02d603a4440c0d8102d0081c891406c4c405008102e1004052030203018102ca0b208280442d2500100791500a0380a030030020180700d00c071300080c000801a1034913001801050400c84400748200c01342c1d007080c40300540f03454504d4241d249800c8594901d1400301e80200d1800800101c098a601c140c1581444201020032558102e10410b092055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492802149 1250 492800899 492800939
    0xf1b090605010914060307030e03030c12060901080c06070c0317031503070302090703020c0a0b0c07120807050313060f0c020f0106080102031e31120206070f03110408030d06 76
    0x400e01c00810134601101d00980c4503d41c1680c4403036507038a40c07010881c080e011180e403000355448000103104c0d81c10068002090000504e0140b0300258541e41d04004c0100028445c0040a1b030060031008401d190000040c01d081e1304c2420307500e8146a607aa42d100c035500c0140c1c101c21000d070700032080260400d028060041c0c404000c401034803031142964006150000041c001c50304059000c14211350211042040380411a04071070848036524080c1c804000990101400300d450b9005410400c06607401907d003a0702079130260310b8003820340d80c4400c0c00d490109060701d4107650154903180c200d080210342c0e02c21080c0c86102070b4041c00c5000140c0c400e403400c1d240580c2c41000103a10400c20007032183d4103001000190b4040109078402900c4524843d100080e03c00d10440c189194495031140d0002e807029203c0d011845840c4000340e068410b842aa110501100c079140800c0d41c205514140c00e210381e000070018030b0b48011503410203494400d107a19581181c0c21000c0b455035a9102800f039078200a07000f1051030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492803399 1250 492802149 492802157
    0x60609010246030207060e04020403020d08070c08070e0a0c05040915030b0108070614070204090b0109090213060501270f0303030e15060114030912030a021803030a1b0f1b09060501 79
    0x10001e0f80c0007581d07074a01c1e00c6080c0402c090414502c00d00c0e692a0120390003143c00034107040d83d0b24200c0c1006042648003820869038041010300c000740340c1c10041403080c00c45a80c0750b005006a40d40c1c481d4800603201e07810041d0200201003101083c4801d0500c40d03010744098600500c1030003401d42c9046007610106030045071841e884010100001b0744c3c490503c11000701032071070f01a1211102d20202e0301070440c00c4e0700107117107603940310002c1013600460344070520580c02241d80c00a40030f0501d03206001c90788103024417400520f0040c3ca180329007060907104422882800c0410b2807003a80d840240c151202c89070411000242c846440700c4115008100600d04002114140c48207810900700203881c20942040c194a0400c020001400904003405055200104100802e9591038540d0101000703611144c481c20040700c0003042240203050001c26070700c8006c0030f92900c1c4c059403000c0401c4d00c076489002d60112184404a2131900000348403203411001e06102d074238000746e1035041c0a03000003541e95a8116034104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492804649 1250 492803399 492803533
    0x204050c0c010b030102090a061b12110c09100e040507080105130212011815020f0409021b0a021e031c03050108071a0706020306030c030111130b120606090102 70
    0x16641b07180742c01040310f6480c284ac01c000b40f1000c80b21071031011164400390008020200d040c25850300b0520a02443c007942054507200d40b450310402410503001e0300c1c028070900403000c0c1840f40046501c0c11682050041c421900f500d40d48079109401e407101120440041075801c0040d41c11810617040c014118082080284240342041c004149600a914005003041d50070181c0300b03c3c3c4a503203904a40a58900c064400d0f07849840b9050f2001a5010320301038503081c0e807555051040c812001c070b800c012869008200da0149000b201510304480500d1142540c18014010098044070a181044a00d0085c2e030310040b03080c0d803404001e07900702543d0b540010118034900c1c00d0040320311220740031035078060352004005840c1d40b2241d001c24600401d5100e0660158038100c00f030410340f0210b002a003e0a5621000003d401e40c450340100c800f0f000324590100d000c1e1040010404500c0d080002c0e01c240740b01803044406039498400064a441000f16001400c41404001420a01024641080680402100c40c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492805755 1106 492804649 492804667
    0x31305060f100e190c1710090c050a020a1506083703021b01030b060409050702011b020316020102031b030c16030803070c0606030204050c0c010b030102 67
    0x40040c03402e070001424280040080d12840011501814281e02d00d2803d1003e4490203a6030b40500c205c84401300b0002c184000d020b84500040750f4002e40140c5042400d01c210fa504080f1402003000400c5042c0312690005401100756502000c0b054054400844c800000d2680383c12526080c003440d0f942c044010a4102040c68031307800456410301d546051441250f4100649000602503082040c0300802d45e1084200206003c1060601054100a030000610554025080f81c10b20302e0b60342c1c0c2449141070382403285803410100340d11130241601004401a649005001107824280c40f98101c2008592080c0180c990381c0701c40c4008601134100c1e5411468a0350003010036103180388192682c80c2d2055a0520540080f030784c0003000589940c507040d40499a951501c101604c1c0551520760001c01601e0f940300e024456041c5445a6489004002c8911700352007070900030034442d80c014000078034 = true := by decide +kernel

theorem cover : BRFrame.Cov 492625899 492805755 := by
  have h0 := BRFrame.cov_init 492625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492625899 ≤ n) (h2 : n < 492805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
