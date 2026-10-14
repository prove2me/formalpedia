-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2858
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:57:38.429121+00:00
-- url     : https://prove2.me/submissions/08c49cc3-ad4b-4da0-8fdf-d7e73bda975f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 513848920 ≤ n < 514028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 513850170 1250 513848920 513848927
    0x5130311011b210f05061002070e0c0702060c0f2b020604260301030c1a0f070204050613092d05030403141e01020d0b0a05030a0605070e04020d05010e09010615 70
    0x83c03985000c040031403200080c000c4034461030540c880d44041c00a09410040304200e00c18942c5031b41c4408552080d0340510250742801021fa801180c400c1480348c80d18540e1001441500641954001600c1604c1412582e103a0004440c07a036600c0c00910445c0c207101c03140c482c042c00320b07c00c8843c034050f03400f00b80407800096540b00c04080d1503c190f0384c0c1819080c4014a4404c3c00e900a030b10950760304d608182c1c2800089601e00002d2018840c107018035203000090031911080703014615019104580d681d0003c2d00d1a242c1c04405050381e54580010024510303149020b00080c41007055040c49007034202400b5615180c00064050115000070080d4100740c0707142e859040d000b0060683d00c07001d0080940c0000824200248505440745000c000758894881158601c100c60b032000b1000d104114010042010352408200c032055250000710201c1d03240c0d0b522006450b00001e12421540042c80041c1000c0112643d601c0503040e50754032140810b0540300c0706685400d03220b40340594035402c881c1c50b4400c43c40500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 513851420 1250 513850170 513850187
    0x60f0608180102041203180602010e071e09020406050d0501170a06180b070f030b06090609040f11160302070509060f09130b250216120305040905130311011b 69
    0x709002618007a1100007913400e0240b40d01044010070243d50a6040000d954010710000d003040b4802000048010b100d0141e40307640d58071411041e0300550302c5944042e090344040b4009400780e40c00955a4540d621030040c82907020309000d002e0700d4940400441c80855034081c400c15519414000c14900300b0381c8d1184401483d208180410080340019410002004550a24403504076034072000c42e10001e806000e025517941c00501c0d44102410030000c10240c2c0e070282940c0300300809650002d80d4200079100b41c0002c1c180e0006884100d000401d0143c0321505050500f504c10b4803c0d0709440c5d01540c1d0305c1c01d01c09800c1c0c1c1600c2d555440a000c0340700c4040c505000150740c1d44582c0541c100300740c14207680c4900402090541d00d2401c1100010903500d21803004544407050341c1d4443c070080100c101200250001c1078050b02400d90705100305d4442c0c0c824140710700d090783c02070002c50700100090306214607402c00e54000d200c01200402d031480d80d0400e201c0300612481c00c810102d002511150300c4401d404546601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 513852670 1250 513851420 513851461
    0x90102190c17242203050403060e01240612090803060f181006030e031303060b240915180108060103091b0e160210090609050307050709060f0608 64
    0x100d01c0d100780f0b07241e500c0c0c0700b1103103c40d0700107103e809140d041801c840c18015070701201c0b84242110001c2d4001c0000e60100440b022aa00401e000807c240c181a5080c05018010305640c803400903e07000c0f200c40010456200121080b50721a1002d200400c010002601e400700300144c05108113200141140c24100384029145c0302c000e201c003807803842c007004081440b80c05860700ca80c112030215081c001d00b9014498110303d44103002c010350601c010342d0048600801140402030507652181044c141b0f40c2c0b40c9174144091480181c084202c510300c06640d80003240c000c02c60152040090002c85200d0100a2048a0200d00740e5082002e109800c0001500c4518010300200c3c10142e8660003400401c034001c2c50304002c0c2000310182e410540c0b030248050800381d409044184401c15440c030303403d41c0c01c2d0001100c41d14a10b280001007250000350604100900c1d420308090400e0100003a428200000070070400d0950701a40c008001c010740340c0d00008282901ca0090310040307805c03c00801c14004110441240c40c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 513853920 1250 513852670 513852673
    0x62e03080901032403170f09010e03011d01290607030305060117040f0b010b031e1003020604060908060a020f091306080d030603020f09070e091b0f090102190c17 71
    0x219a8104100303516044e0742404614618441401003010b40d1091410080c3c401ca5a00c5c00d0280c2c1c4101c001e818401c00e0b9480e41484041d1000e80080d840030b4003c50070311664550300142c404040c9201c50702802c85000c0103010300c5120589110515031a1003085140e001c042c1c8003074200486540e00707074000d01e400707003101f4140052558081c0c111803960718880d104a210300e9019080100519202003a424103170030088800c0401d208111010880a103040c0b600c04418001e400241c56101c6c0c10b01100080381c01c060b41041c0c1c0003801040054100c07a039402116904000c440741542c0b0f9101140c22800f03641310b003010001081110103224a4491214510034076035a800140e8203075501030070b926119806240e58042030f1503290400951401c5064000626021f46044515103002c180c0100800149486140300300720a030b000c1030f20035103180f04140d0075455800d02a5650000d211a0500d80c1c2c005003115401803041054800042c6251200411402da028035250400b030b081a1070003007440c90101800c40139 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 513855170 1250 513853920 513853931
    0x307090506032e0612021b0615011107050307032d03030b130e070e1806091f021207050d0e01110702010813030203030c0d0b12062e0308090103 63
    0x80d5035400c010b50148201c4854098100015640800307000c40d4403142240141d074280041020540015102080b040310480050b980c8029104801041d90b0300c512070a0306214031750400c031100703840c680c00d00c41c1040240c84031503101d040d081c0881d9988565016042c1c15812042d001c000251002d103440382545200f201200c13250307820545a180d6401141c409a001a403614551842401d058020900a481216081c01555606644255a29890b02c22501e03050b100f140000d140c904407503842a0801c01d00d40907225641402d40701140e981a2010031500c6d501c01012140c423003804203100f100e118880170201c03621281d946581c03d6800382c100030040c0080b281c0311708030394030503103400c0c0310700c01c003a1042803130705901c41c07042e070000400504000b004083d04012491005010139000400e507544000c0032041681d54820015510000e00302d149851038001c24142c0c48509160740100b42c0710322078070031a058440540d04405030980d8607440520300d40b950040c92207040c804103403074030028440040b060401145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 513856420 1250 513855170 513855179
    0x1401080f12090a15020d0311040f0b0a0201090206030c13050616061508030c030d0608070b0f13183801140f0301060c05070b0901120e0a050d020c01020609010e070308030709 76
    0xa212403900ca5640050700003001c036180700e9415218800000d036810002508081c107040d0080d4091003240176a60418001033114400c041c802d401160f10540d000e08a19204d09080d844911145c120b00702c1840400c40428010406090403401c1d500f03001040e58441103c1510f5440f01c000a1901e074845182407801d1981c0881d130304600708014a414440306c0000c650310306442403003604507081c80d007000b005500208000c00921000d50103554610510040380c966506103d69607420b4032079503900001c240125210455548211603201260010005141034455045941d1350740329603120303107151404030510007103000c12035201c4c10550100c8400c2c1c2251910b000d031640a110142d4209901450005050090310003c001082c04600020410604a14189103480c9e0029120100c410501040f899523a031a030108100c007009a061421703009000e40708180f42d0000000c0d21804203030803444c0035215040105043d00c1c0140301d01628000d081e4007400340181503503030307d00e00c1d43c1c405410b4208020303c1000208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 513857670 1250 513856420 513856439
    0x1120f09021509120703030c12120c0306061214070309030302070f0606031401090b13020103201314030a140a120c020109061718030c010504061401080f12090a 70
    0x307a01c5921801030b1140c0b005020040c00d03101c1813540044039040010b042000036040032600384150b500030300c200504200b505048420203503110784084210706044011050941603071145068400341d40d50b00d1030801502c0401010348240440f00c058070403c0c000001c949622961212140c640304c0e15000d403509000d0348401403246203014051307400a60f900020410410705440388000f408500340240700c00d4105850711211840b000b08022801030b560960002160701c0395100d40ca0303500c0041c00040022005111100f4240c01c04800018841d9a4000110311040200180b41944030000c005004140c0943c0d107143c40040c480c0078130082441601600000030f01c4401c0b26410017033046d070341c6448010f01070000400c10a00780c0c0c4130314140b05080104010f0300c3c000414190f445445508980e000802e40030045255124410802c0e800394078000070301c420800c240d08003100d8440001e02c424116600c6d038400c9500d800c0c98004100b8158007403413141503400b134404080e01103201d000341000d0100c2d0b614003424 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 513858920 1250 513857670 513857689
    0x106020a0c091e1b0917101d010905370f0204060302030a05010b0112050618060a0b0d02090316062a0b0a02071a150105030c09030f15090c01120f0902 66
    0x4104000004440c500c0704e540b001000c0014549441540c40301c410104101e9212400340c00c15404190f194020541201d4210244602800d4440001c01089407541070164031042c0000702c1014003c4c030300701e107125141c500752103010703400c0b41113410742459404960320000120f140742400c07a0469101e40c40000945e07818400890310314021000450301710034030b00004207510174824461240c50300d030006114564070754207003241802501d202156015103405c4001090510981c0c012a02c0000004001e08100c2340f9402404007a00d0650880701e4900c00c000095480118030302640b000105201c0c407501000c0302e03203003c9250800722080d850f11020001d80f22024110000c44880f40d03000e40005041007001229150180e040d800745031080c0060400c0c02c03910507040d0585038158104800440840c5a04011070211062004c0c010200d034142010300c0714094403a121590102600d8504600140034050007140414071602c059407502c544000b12700810005000400c103400e0051f68802c3c0900c0183c0300c89020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 513860170 1250 513858920 513858941
    0x92d03040b070b2208090103110301060e0a0e0708060d0312020a05040e06100e010e010216030b0403021501060219080720040b010306080a0323040b03040b0106020a0c091e 75
    0x407070755658107504050b60303802c001509166003030610748500301044200f00c00034607000b5409070b1131035074940c50707400104e0180604250745000394030000000107005410400c0c7e1045d000307050b5000e40c4c085649054900c40d015045071070b107002c100204009078640c038108411802c0d03d8401e040140c01c40281040010032030700101c00e900c0114000040134410f4010200145510075400c8600b20f80c1c0194000700140b404540c02d00300d505004150701d100f51140c1c005e000302152000c00240100c600c40e501d05104104000c00d55059003d4014111800c91613484102a01e0607104c0a4009040c035843e011482c2c4400b440c40a002e54030500203000b06000500c98401c0449104803440d4640307883c40c03045081000b03c4003090f007003d051610b082c900300000f14000c82c80502458250829100d070002a00406403070402c414006010f0600008009c115510031102039801140520460000c0d682c07074200690f070b5000d00c04030180012090400401111810307030401584c003040c1240c1d1043c8845418040d00580701d180d02e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 513861420 1250 513860170 513860189
    0x6030b06010e041a1009030503131719080904020f1201090c0f081302031e0a031209050a14250503010b01020304050a090e0307020607121403092d0304 66
    0x3440215a840341d80c003074400d0340c2258100b064100300030180f203100c900ea0b16414041c0500c2441c0200b42801112114011a000f400352661081507050717203000741000d8003c5604d10402da5901c02000303000060b54800d10355115800400c0c40c60580c85074003007908140c9181303a10940800034084101e80d088050314a05440742503c01d919414103c00381c0594082c030041d0010821000071a21400f035002e074071250442008030380592522007900109050218142400c007080700383c0d10003004444c00004140c88030b580031380e032428407540440e2030300015100c00d000050026403010160340701040034001041d044540130401c41301c40d0016440d072980b03c42e54800d0350381c007403103182c2604112a080a00480c03a11310001d10245140608150000b84c03c207140c4c0c02210b043c0ca680307480c2c480b8003040801c1202c2400b50014425910382c101441c0c0b010306001c1ca13100b002c00186040c8a64100c0030903000c02c1d24041c40d10306d0054084860914500d14020101006280c034090342e0802e800800c100a10003040680055030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 513862670 1250 513861420 513861443
    0x203101404020907031a01080c0424170609071d04150503011508030a050d02120f0619230d02060c03070b0c07020a0e04020d02190501090509060609040c120603 70
    0x10007903030343c1c001003111307043c582000d411020030503200b1245a8003081c00d0a04820f02e440d00444000f090081d0b4010701f9421900e0381070f004124281000b041c44442e915681d2000c44104440e006000c0c41c0d066501a8000c040f40000c10303138081c040c01030300d481500204282915140d002d40028103503020b00e04c0701d2040750010031b802d0115007000e00814a814208800f509002440c0c14a44e035524443ca0420804200002c070312900c0012564040301c058000900400417103042148801000c0720003a83c4161054180d14601030b00c2022291026084803d8440301501c0030313000280301490961b5581c035080e44545e03582d01100042e03941c00042c00102030740e080103503212520752a0007082c000c406050301c50368a405001040c016a0344203c44010303100c12024070100d503122803000c1252842e4842d0025400280908000101940b10000c174048510980e00d007914266144140180301c03c09480054000b80104244002c1d410590442c0c9072400d000d03c0d0000390a03900030803078030072520340e604110f6002d4101c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 513863920 1250 513862670 513862673
    0x90b0f0d0b130c022b080402122a01081003080904020d090b09010c020a0519061d0d020c040209010c080307052a010b0a121709191d04020d030c0203101404 68
    0x4100c0403885080104045c0501d21150380c601c3c8001d0340d03222004040003030b42e000140441d00d40c7c10000c1f61902031a802c032460038080200d031101c81e4074000181284c45007601a8103140c1e61050309858051030802100600030341c1140c42c0c08482c6c0e0712001003103820580800c00d0546d0700b04d241c407070340111a0003101d007240a420040380c0d050940c0c25002148045521664948000c18400704000f1401e030103595802207550484d26002024001d60701601c8039012407e038903420486000304041441c0a0142d081e1040e4486441c00c0108a0003000040c031f00240c280f041540004001d040156004015400c00a0520b064000400000b1540c0081c0c40b00f44400c4100c045a518002d01130049140d808079100d40010b030400d00c6c00c81212080c0d0002a03c100704481d0060201d4800608442101d140580f03440301010610003218100c944612840110b14148951070105248640c3c803507008540c000e04225204615882c21110101103940582c1d01d4001e00c2c4000c0d00300744446c403d090812411003c8590113242a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 513865170 1250 513863920 513863923
    0xe07030c1d0402060a050307200307020103050a1b03020903100504150f06030803060d0309050a1e08121207020c0d0b040201030507020a051c090b0705010219090b0f0d0b130c02 77
    0x58407030750010070004a0501c0016078030101a521003000e90b140682e22941c46100c215201c404980c0300c0b0050708520a04210313400f001000a0200074000c0e241840562268201103044840c6818002010741e280c3d0301141c2101c3c032a400409107448010121240810442d42403011620155000c8805d1a0220356581422132940280f507255034542404000651840d2500b50702c43c80b00501d207920400e92100f9a0003098000c0c003c03400039100c0588640c055540300c00c10184807515100304050705018000300003034411000138040b01c0003110f40c4a680d08014404010380e014610140c509000c1d801a498402c0540e1120104c8107405800303001f9150290030a400054115032000d01030b04215003200c0d8000010980006d1a481051080c0c8240c081d03030354100404840c0c0e40b03010f40104981e030b1400200c81081c010305401800c8607401c42544920b92200040090303c80c00001d11818403a220140101030000982e02c000d0074494208400220b8000117490018010449000b110049a0f9442d1b2120b40d54030b90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 513866420 1250 513865170 513865199
    0x303090f0a02060906070602070b040b06040f0b0a0611070e0c13050405040317060607060e06010e0105060304030906030216050d030e01050a0b060909040203010912030b400e07030c 79
    0x140500900344203415034000c110f0a1040d01c12040c0940d00c0065040301f0403a0660480d070f800b580202c070201c11070a0a29250541300010f071102c40c49107007091034860914210303100d20400040001d103401320f03180c42c158098a04150a407480c01003400f03031110001c2c0c0070712030360078240c41900b100c4551b80c0d4441c074514000c5903030b240303d4000c0c60086161004000003c0c0d0005104001c600042c0e40b080c1c8195500400183ca43c420f44600820319410030400c180e0001000031b2050503038400210403400f6a880d2070900c60503000455001d1b00050b9802010070000e40268010125603210101034200400151503061801c01400c1e02e0000080d40d910320402c1c240b00a00c210754001015400070f000c00034681000030218060301c060148500f4800001c0703000c5540950181a245074006528001c0c815114006070007481484569401400d00348031540c2404041810300b81c50141c2650356180c69880c2d81f00c1800c0c58185030303050300300140d90390701408807554041040200a5200b41c42180c00cad24180707008540c8050703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 513867670 1250 513866420 513866443
    0xb0915120a0807120806090406090c0f120b070219080904090807031115090d0e0307050a0b04030515040308011517152805010c150f0b0f0d0507060e0a03050f030309 72
    0x401e10301440703071b40ea60b0080459005500700e0404100d041c0309080006520f00e5075404800d40340307a0f882c4001303801e032544120141014040d07400012140c2d940389080e030315040100c0038590740740062418040001c0151005d424040000f400c0041c0c000c4c0700380d8031310140e030f44200340a502048007248249400c10042211201402014040c0d00d00ca042c114022956200410407250501600c0c10b2514250340f8204510710090500515a914003a1365a13480e40b141c0d800303400143c41602444414070090310720130188601803513050340c4c3e82c50701380e00e481202c80458588918040800c081c4c0d4114a46408991030014003031442400c03600348800c1e8002c100400700c00034441e0104031009110502a4251090f6251011201c081c01e019030180c00314a40703500b040090300144c3d5401480d019140091034200e92100070031900a0b0341c0742030806441c108011860742200700040440c2d00541e03040c051584150300070040200c016003d01d11064595651030b0401800b54680d0115500100808c80404401c0195040c0603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 513868920 1250 513867670 513867677
    0x51308030a1d0307050609040c0318060912051e07050a06140a06080718050702030409020705061b0c06010b0a020a080301092f030f07170702070f090b0915120a080712 73
    0x11071404010030101c0c0a07c0c8085841280d40300444240940203800c5403100c00c049141c403034000d401070715040700140b021a400b66811144104040c03e654000c00c101d6460340b0008901190700c3e20560032050040d44600c0c011621030003141012400262103001c1d000c01c56601060b80c0c0190f1402502d1042100e00d0350340004a41e50007082c1c100044041080800300321480b20351b0214590b03032101d6061385903100716448003c0c0e07103100181503024030801150740c60085004840d000034120841c01c0340b6500340100e41812103d6002140100910f021443c0201104a110b0041c0c07000b814954481c1e060680007640003221250300c503c022108221481d4400841c1144415109030845102901501340d000040080c1c2c41046203601041240d4050520b20143c2c00b40d5460103e070710303d004400251034000510a021140005850209880040e4020100c6404e000380c6112200d64440121800b402c000301c02c1207811940300301c2c0c8108610f40a10030340b502c49001c1c81d52641d8400c0030386400303819615904000b8042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 513870170 1250 513868920 513868933
    0x31a0a050a02250218011503050c070812060f0d1b0801021603030b1f02010c0206090714011b0203030c240609041506080708160b0403080703051308030a1d03 69
    0x4807202503000159504064100b080428498404601181d02085c12a030000c05a000001607a82c4c400112040e5602c0d00c0e0341c00c0c030141c0c8030010074402c24040c0450082000c0000d0040300008001401b200f6031010300280982441a100001f0442c0620226003e50300d00600140098104655519450041c41c18800841c40c2020085d81420441c516200040400d9100c50070003031280c1e41c0c41e151607550700700340721000100582048040d00a004203000200513000304400034100502c007143d480119000c802c1200f11707421500c00112102e2240402c0e800b4030003c441e0040300581c03420009040150b0f14080100011041c4440c00012804e02d58590310048491000f0000340d5158441601c0c2c1082e07106074007105010103507807090003411190b080000e592050100000d0244d4001440d015400741d840c0d9800d4a581e201c08482149110758040070302100d4042050f080000c0c0324030003c0420105107902400c0716610380600d10b0442d1303c00c030390902c0011340c01502d0310721449200d181c50320018000c60041c400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 513871420 1250 513870170 513870187
    0x80402012f07062c0d03030f1a010206070e1315080a0c030c1a1e0c0610051306150e061909090b030a112710030b010b0f030109090804031a0a050a02 65
    0x4044d44010050b0250780100c1c900000c1500a4000503200c100d80d98003448540340c445210703006080d02c6a6014010700c140404101c2050090344002400003014042100580408070000003600801030702c1d886840c50b03a9400110300c00d05000d080801d5200700e50b244607451940c00c1c101e1aa520b00d401c54460600610a401400f594107005c0b2000e1390180a5070301010703034801e0420f5680c1c2c0a420040301c001d008a40410840111011005c03060320303422120702541d01c50310f007610070803900b4030300074800c0400d143c080d1901d134180501001d241d801d000801c9103141c5138055492103001104c0440c11004aa009003046c0920b080794083d4403c0d14006130002e02c00c030031550b141e01d40d0540e0f61051941c01011104c2e01c0a0f443c01410080302800c4629192039025400c003c000c8041c8801684015102d06215000104012486000321025680090009415030b424038a021004000e00345c803c8034294400c2000000082640201d10140783c0805050318007031920304c013002c094507001050091a284104242070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 513872670 1250 513871420 513871487
    0x503010b041401090302040e100606050f0d0b06090634030f0807090b040e01150804051b031006081b04020f07030e030a0515090d030c080402012f0706 66
    0x1001c4074140d144414101102d0340c01030392006469040690402d0030660005214200000c48a561050041c4204030040e6110000c581da4000d04038440492002000404511503150b00504881c24004110500d05080300c0700080e0150b11900c0341d503080c2440703040e03486055000003030748000341d20880c490544440e03001e5034000e01c03400078103001c5014013006402185075503100d071400c1005868008541d598a540320307407a035880a44248607490611119503101101030340324201281c082c3d54040e004001d440342031702c001c100c24200604440c0e0503200d04d0b6191105903609000e00001001d1440c09407a049ca01c0103441c03402580080d070041e00440c0100085140d00044c0f004655480350907103050100701428000207401e00c0100700000d0868030541d030007281204030001c0d0a074055400328040720009580ca40c016400d44000a03050000b043c61240000d02550299148450248074002d4410140040084404100d070042407295030690020310705009458220040d151a142075a00540050b01c240d840301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 513873920 1250 513872670 513872677
    0x41a041203050606070f030320040f181103040209090a060f0e0606040c020303010611030d09081b0a050c0103020c0102070c030804292a030d050f0106030b0102060609100302090907150503010b 84
    0x1402c00d50784e00d5089d0b58807600070f0800c4511802c0d00380c002d070340c0315903c00c400a0b810700c46010f000f1031445059201ca42003120b038882d88500054bc074130468159513482d0200041e4003801030108015004a8480500058283c49000001502c5900021392903449500c04d5240010041100e0300461038403c1c100100e94000060f20304445091a05a220400540819045004407122100c0650a2480b03200400011002910b080c000e910000741c00100f40340c0d04030341d0f51100c2080140c000d80101c001c1c000103511a400402074080c010340090701e001c40554589880c000d0903030040d1003140001c02c0510002d0680e00c80c5900ca0300001685074201c0000104140840c465076120070004480788a078924107120b45c45190408403074000036281c54001c10070803d00902003c990303840a4820f000c001141e03482c0a403264414246c01a40207020740c3d510b40060001c89a07000d0220006040a80d0000005a543c164010722600b0240c0207406914130304030200304643c2d08982d004041c0442480180700842040c000d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 513875170 1250 513873920 513873923
    0x3041716052d0d0b24010212040603090206070b09010b033d060b030a0504050c0d0b061e04020d0207020a090b010f0f03021e090a14011403041a041203050606070f 71
    0x4180b4410a20030004100f0500c012004050705003600810902c0750340c40303031060144d40b5803003000150b0300030750001241c841000d4020703240041ca05000600155220750302108003244050b2620345044005d403242d0b4041d0030112144900c60703441e08401c3c206c604090118601f20343c0000710300519980b011218065050725500d00100d1425009200e80c4040d400340c0040c0001c08001581e56030b40c1c144282210080c040031502940c0500c260080000281004c41e0039840d101e810002c030640c2c1da210001080240c1c80110119201050505601800c690392407000b04540c00b180500148c0c2c8950510501c01c4290300380d404034126902d005180e800690b004104504902c1c4a46060350341e080100400360000d000c1c403d10f0588018025000851100c83e00001f0700d001c4504031010a00c180e521049c0050040f22005510b00040032001304043d4180101c3c09035810902c039030030f20f21912a4140712698185401c072070503118641415a460314960301031052640120080e0b4205103001c0c640e03100e03400c0300e0112000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 513876420 1250 513875170 513875239
    0x803040302090a0b0d230a030807050a020705040509160803090102030f0a050d4d1605010504030c0c06080f06010e21070f0807050a090b01020304171605 67
    0x64528106903101e030030b501200034006240c91700030b41849140d2010380e1410b2403014801d49204400e040d0009140032406a040d511301c031041e43c42d040d0444507908901114410741c0704100300031a2694035405814032804c8024000c05444c0000c417101003010b501903000140a40041000c1c6e00f099134080100d4804c01654030b055541c2d00c010050496483c0f042c0d85200c8203c52400c4400354040c906c0005e8010544404034101300da44440048105407401d2800468480220a404e841c6501000c0c03030280519641d01c01c2101e40781000c9403a400e094400c2141c0840015001800071000c102c217003091032002d80107e00e01065140b802c044407051300400903002505201c18031040819941d03404076903441e52104403007051450b9280592065075185980584041c0961440c0007140000c80082c24004a41004100399045440d01e64000000c00b0410b10407030450108100101d114081035032120744100414008001e14400e4100d407120304040c03038024500c1100d04500740051403540b01d074841070141c040c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 513877670 1250 513876420 513876439
    0x20d2a09023004170c01020d0c08091c0f050f0c0307021203030708010e0423010f0e0c0312030a02040f150305070c020609041e0e0a0506010e101403120d0203100608010803040302 78
    0x20150340c13460050403614103d940c00041c0c000d00e250301e160496210030546890319011a11848219610303001540864540c40b129103003200304462060014100320000b41c02c00300d01d00844d8003818080d560100088030041d40c80000e01604609114a003802c01c0020280910b041d42810100240041c5040c8a5038810007000da01107400d101400881c0811810301147d242ca601081d02d43e1036018040d540d5030801c03110315200c0c040c40d1203800031401c02001d50000300a800d000c10460405043c3c1e40010300300d0b4214507424000402d1000071048000c02030b1102c0d5080c1e8040d40c249007002419070700000c00d50020080007113000302c0140c0300c030829a6132050040b50041000c900100c5165001e68400899801c4141480107290b6902c1c004902c0c0740c070481c00b981c15140d941e0b81707407092641c0c182d40c02d981540d0400c05840080100311421200802a880014103a402d060162918503020b900038003100e00000d5400020f01412440814041d2700402e04c0e400c090b403103503140200080d02c034012807101078011015031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 513878920 1250 513877670 513877703
    0xf0108070210091506080d09171e071203020a060c050f0d0c0c021005130e06091801060302031501060e12031e04030c270504020d2a09023004 62
    0x3408050301e40e1202c0304c800c00034180d0310b481155940744811310141c00300c0d03a21117011954000940b0f4105c4412802402000c144031001d0a11160f271203c1da40001070350146100c0410070303441d055032a0300402d0183d070003058005581e0074545d007114903041c4404248070702000080500d62084040e5a00403911140010b0b47e07801e01c5070143c4110b04181c0c40290f01c402980558a4641d4001003e80b43d100e20f01c0300c41103102603d80c0800300383c05109889056100691400182e40c0201c0c0404c0001c00c040c441c8008114141d403580800d2804001d0240040500400ea00608c403196201c0c0101440d0b410480d0247c0d100503800080903120b00c14547c500308403101c41d80f200740810032a107088500841c1d2082d039000c40c0355900c900c455440c40401010080c0da106803030a0080802050052034040d5400920726a80708980f966900344a5508550f00384c0e84c0c05a032440b84000f040d00b86020340007850703154400742e032b29680208180390f40050102544000c8060407540400c20740728541d459072250707002c450000c0302c0e03040307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 513880170 1250 513878920 513878933
    0x503060d050d0302030a0c0e0303090d0c03050106180e0c011403090f100f05010f140906040f020307090317040303140f070503070804050301050a060e040b150a0e04020f010807021009 80
    0x10360001508521803001d4228106502da40118800c202c2d15504014210512408843c1c4d183c54850055059209000e1440c4926103038002014061144d140c040000703560f03984007401e413175090740000c40c8040020307001810302d00035006d5203402c5404080540007036000400064a4001101561010f000000c0006200c00390104820303107525101c0710484a501e0445482c0c140908031b10b084e0360120b00c0c100341c00002c1e055002480d0006035004400200482c10a0009015004800031f01842c4c0c402e8807025842d0101c489480118010201595040280c90860030264001089081c00c0550314104110406c00300e940091b0010701c40c40340d0000c582d0390b070403001451680d9010704032001e84a0f0000084640400190b40c00400464005900078001641c0b4020400c4c200c03126849490715401600c03000400081503a200c1a5002c0f01e040034807000d80c030080d00401c951144030380001610521550034000bc4d4500031621914801c0246012100c2d072500c06802502e0342040c3c0303020307100c994540401e201041074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 513881420 1250 513880170 513880189
    0x5160c080d11030a0e0c0108340e030c03060c180301110412050c01020a080a05070317130302060901150e04080405060a0504260d05091504080a0b10030201080601050306 74
    0xc1e014288030700304900c1c09444541d40191041c2007030518007203071588481008102001e2400f0305031900c4946a880210b14094141c0b14181090500c60020700c40201214184100d8602035241d510b00c1000302040c01810701e4607400c40d03c618820340c011410000034031001c40845090314005110140d00040c1c010110380545040e141001c4844000318010130000c0e41d05403a607020300d000f4004c41d10a10114801a038482c0d19000d80901122020400f644c0c0041c010070051000a100340380110403011548150208a04242c03002505081085208024140d04000190304954024002c10181005034681441410148214110846040d00081c144401c100c292801032502602c03070359032790181280042455020340546254014800318a0105070040e100c1c1c0c501d010030b1500140031424003042c09456039008000010f501c10600c030480800c0c50004405880100100740007050b1110f460302d0300c00341c1c41400404203108079280300d00400150703074412403058102e0b03000e0138501e44d80d80740c03180071410014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 513882670 1250 513881420 513881437
    0x50d210204031a011401090902070321021c060e0f060114030f010f0803090a060302180a0b090a0e0f0c0a0302071a16020d0206190e060109090209010905160c08 70
    0x5101080001c20700103201c44040b6a80c01c071030105603d41e0380394502d48840e245854070050004900d221b00b44004802d5a006085050103824411601881680d41d00c1a1a030000e5082054540201d9200100906a4888455450161014442e060801c0c1454841d044c00500c10007c0001c244045180c590280c1144c1c03a541c550108400d6a0b483c111603070708203190702885007415103641c401001071525404401d0720300c1501e0040c44510210b1405e901100690446d244581c0091143c0a0803107159643c105841c005005a030340329a2518110b80401202451990101c419000c094007013001d107400d5000c103241c0c03055000d070b50030341c6807111410308800a00407480020702c6000300c041e02155040c2c00d02d069a00c51050340d00c5440000e5002c440032a12004511076030303409a845000401c003003007031182040313130120f00070000000c0000c2071010040c580b8400383c0c000419690780d80c2c4850294104041c40c1405404003040900041c100801080000c0c00c80c945001c04028503115605c08125003a02214541c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 513883920 1250 513882670 513882737
    0x204030506070801150f1b14030a0201050f0a060302220f060305161509050f0d170c100b0f06071a01170c0904030906080705070507060e040b090103050d 67
    0x2d02d8840406801c0600070b020f07007166082c20074012400c5034840c002c6030410009030f689400c0640024a004d41215100302030868a84046007048403012004001826202981e0350011803141070800f06d052001e030002d030900c550142070000600c0545c58290003080c004440c84000c40310040b0b40a034501c0149422240c40d17802c1c509000c0004103100001500481003c0320300140900c10365611b4041c450840705d4190310012841340c01080005181840c2d9054040102401210310104183e0743c01c0501540c10340108204071001c00c81c0900e04904000101004a422004000303005180c0300041604178040078461160300000380e200c1c204640c0581d41c503040e044003950f080305541c4031441c03010001c8100e6410380c014400c0e00c400207102d1500041071743c01140c061701c886041da0709001e03040310781a400603e0346050000170007440c40001e07001c0102c00c0003480caa076502d01c008009202040151040d4105e810b2103010307900014404104046003003011204541444c402c49030501d03c5095050458954201c1380c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 513885170 1250 513883920 513883933
    0x10504050c0a050a1b06091e17131a071a0108060a11070f030906020c060f030106050c03130306060e0619090506010210091a060a0f0303140904230c040b09040b0402040305 75
    0x108540c42e0051408144501c081404004490b0102c20413603240c000c8c050600c018001145a5081a000062400c0b69808171418000303500c0f28460304042d8005081a00468000a665400d20503200141d03176010f500d40380700300019490a00b05030790760880900742c07040956407502c00180c1ca400c003004541381d0030b901c0200216020f50908000d03042c1c18840c030402026018046000d80240350000458030303104040825203082d1303400c1900c201c50b5500b122038104441c0c407080100c40d00030000c51b89054001d6219400114229080600d0100503e03c080d1101c1c1c016145270440198844c81e0005400586c1d20f6034100042ca56640303070040b450840f001141034441c6141c040107000380091702e1184841c004114840b94441d884a805002e00e0604d10320a440305107400801c00d200203071081001180311001d44501504003c0b0a1000600329030700171f4411080307401345101d0a00004003c4480c07075400301b46901c002e4241450700c000c40c1500d118540c11144665034628440705160780da9030540740a19040000c0301c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 513886420 1250 513885170 513885173
    0x3161106040f030f02011107140717030403030e0f0f150d1e06051005030a0510090212041104060503070e180d050a11010c0504030f240c08010504050c0a050a1b 70
    0x40341407580b10154002406451400c03801d0f801401040400004002d203180381c405d00e038079002c0321502d140c0407001c03035400703000400100140c0d8803800040c01021003020b5640d840ca1443d01034070303010041c40041d004c1c180340444041d0b59501c50103076240081c000c3d5521204880c40f5510202a440740c445101000740c82d15000d8181e18028010308502840070a008102264480741007048107044007000d00e000440410014100b8102500580d07040702010f0200d2508540f00c01ca01e50070b90b08102603040800404508000130b22810718044d0180100230740c0d040011b1800c1c54042a10741200c0d0080182ca40480c1011490815260303441421046180c1e05581c03540c61250070040407039104500800000d00d50040c01e8503500350600c602d6651411075216a40f4103851540c0d804110a02c0d06019a003084c0061344110601003000b00c01c0c20a52485100015490311141d40a0817803441a04400e024a01e03003405c2143c4882601c041755003c0015090560311400c0200040311441003605510b4103c003010542c0e01c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 513887670 1250 513886420 513886433
    0x3071a28020106030201090b0435070b0901020c090f0604020a0e120105011a0c060a110c07060305010501140304050a240c0e041103100536061c05030316110604 70
    0x200b070b00e10036600c00303500542d1059036449031b001e14052b1140040d82c402001c0f08072500c80840018100c2c5080036618403203605003081c2d00308401584100c9404000180a00e569a8180302d40c41501c18111a100799505041c90355042c4403000400c0580221360015004440d42c0c00340210f000250402001040000e45144d01d8901809080c030941504190400440030300d08500407d9440d90000e2030002c080d10795800390710b54040c0c501d0b0001000418010081e243c9a03140c02c0c040c000240049440114403545428001000c3c011011040790041605005020010b178000c1024000c50340c00044800000130103164074941d02c4400e080c103c0c42c41c0e241181c156071054008294145041e40fc45041019100e40d1070f00d4203007441f0071a0814285164110140240e1800400c41e070000c903550048030400c00100b10704941034032194104c04058003026403c1154501e0101c00311070903101c01c04035038451140c203030b6942a030328000580401d003a9408400903054040c480c8d00500103075040103003154200d06080c10803c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 513888920 1250 513887670 513887681
    0x5160806030705210f2a0a05092707030f11061201090501090b010807020a12020f010f1a03011407050708090a060f030b030706050403030815040504050304080c03071a280201 76
    0x3074140d40200d5000701071005d004204a01004032041c20f41c24601c0c0701c900d40c240381000300d40189a204107089000316081d141d48100c5845940b5020300c0c902d0127400c280d121010300c1d1080248074010351245d4070510000d40010b4055507555030015002c600b452074400015220300500f080d16094046035000054110b00070b4015604940c1180c10422108217200300450740041c017100c420780942e20840d24600007468440041301d1180c0a44140c61021110051180c01d44a0a958902c283ca40b140e50b42c4803510b114800e58100071808500801410082c04441d00498000410310400d004004c11403000380300400040720340d985c0c07000300780c8001c01b1380315880584162040346040700000d00e0300141e6034507820001307074050580d603c52319020b042c43e00e1507904848201c07004200001d08103107a5aa21183d0321640505405184290041c544540c00c20172024941116810102d1103079010354000c21812290f20500c081241c100c441040d83c6007021103900981200e09a401c81a446500ea010001c1541c1940b04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 513890170 1250 513888920 513888979
    0x1e0a1a0403050322060915080915090d0e040c1b060612120e030109020604180f0527030a0f0c050a050604080409061211040509070e0112140105160806030705 69
    0xd407404c860b00c0700b0017121200414050360741c0310005c42c0c143c5030500e4028172100d507100522000301c0c0c6002c8004004c5034080c04042e9800e070765644c00884004201c9411100e2100b00050586080004050a40340100000443d1411138284c6070580c100009108040e0040340c06800c0d0b04516484060b101d1800c81016240700124800040381d02120085506c1c0602464111640060490b400c190521034407010300d21a1942c14001c0c0d5a41c0ca18440c4045641c3c040d85100e1140c4070030b40388003003025880001004050329240c80d041d400410160302c803140c002507003201c4d4140c0d0340741580f00010b4500c2c205140484000001c0c15a200c1c0004210030800301c1d07801403040d10844601805610b581d803140c0c40000e2030141d0001c1140e61840c42c0000740b0704045d40030b40e5000c410070302202c400684e18100d560061034284c00030b100360041400c40c0014004a050b15140d9000900020090351405d450b4124450680d0602d040c100071400b030105546550420041014000080c400d082d50510940d02210000c43c1495 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 513891420 1250 513890170 513890227
    0x2030307061406130b0114030c070c141207080a15091b08160503061f0f060809192310060b0c070603020703091503110a0507021e0a1a04030503 63
    0x2c144c003000455000c4d040d107078101078417860003103480550115003031341008185c15640b010074454100803440066a900017045100c903a50140318649040c080e80380c03080e624000041d8000103003004240e00026600c041d07940c01c00101140c0c0e114490504c0c010300180000502085507000082686c040e40000d14002c881420086402480e0080d2064075628414810507601d600214002404500f00e280741100d8800d040700d4101169032252107507400c40302207030041000111070408001903600104003040b4008401840e0f450003854a80d81d024644154482c8420f0301c20403154000054002002030542402006501b03012041e11441d130081c0030741109103412442e100d0ba04000800c14044d108441d03035141c1681d951010030b4207180301400c60003004601203080540c0c80d98001564004000070b450b1a0b05c00369070346665068140100a004020844881c8280c1c403076040c1c880341039850400000c21100c03c00d440ca111045560f000341e031240942d40c8041c160340400100c000070b5211540340c10004403103070359 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 513892670 1250 513891420 513891439
    0x70c0303020115050907020d05090406030c12060b030316030e0a260105100f031202070e04061b090501120f090b0a050723090108190e010b041d03090d02030307061406 73
    0x10400c032665170141c0358031026070001e54125441600c2600200380e9000b002c0d001003005a0350b6600c0e160700c00c0340c6a0118002007404801501000702034011041540780c00c400442c00c110320f6201200b084122550000c0600c5903603281300744251a841c43d030100424030355001014000c41d103400c05606110402c1e090030503500e4040080e46030886204400c0c182d0f41000517120145013103a40b1509007016555030070742584615500080c0c1ca48480d0f038010f10451196002103652a4146001c052a91003070825000340405008107100c1668070180b0700d40e41c1c40102c08042080c20f541d2412800800310f45d43e029001c00000010489080e056130082d9001d1a16655505550700c20200c111520f0301e08102251421202000703107961542c0b0030b070540354002644802052442d8050010310003150700c0c1c2403046e6102d9465059443e0b80349130501c600340031625050340801480e0011a101d0351244984854940301c2e8003007542e25001d64808200f51f4018592011041100340d8640c007559003003171802c03103260f0700c07644105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 513893920 1250 513892670 513892679
    0x905060711070e01051011030c030405130504151e050c1308060403080415140a06060905040908040b0c010e06090a051e03071101030209210c15160305070c0303020115 73
    0x144401c100d94046031032014903400c0c42c1c100038550a801e924041000341f00d680c0210000740c10b0000340300280000c401181d41c0c910308070600c9400c6440107070b2408060b242c1410040401e800c211004003090f81c43e48002881000031071030010341b403002c0c403440186502d03200402c5402d007505001071000074003244d949500550358401140c1d8801c41118001c0008034190040781c0050003512a01c80304400c0a500410302803610709a0212281c01181d10201e00c6440702d1003000384d41d812080d1000600003d030340500c2040f699469440041c46113103d4504541c000288171022044294429030542860100755007182c10101041607942581b02c2003951140500c030030181140c1119200d0030344509141e805181402d11513124000b007140950f1666040c56002c0050b49240c1d501c031260492194503071f4018203070242100410038034140c0300750b18050254069280100324490b0b0035080e02c800052000703503180140f00b14a4200c54501880030002d0501c1c2020001108154040d00300784205804901780801c2660355 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 513895170 1250 513893920 513893923
    0x13180510061b030507061a0909010b06070f0507030b34080402190803040603061d251202120a0f050f180a020901030c060207120201050a05090d02040905060711 70
    0x86206410100d100c029000b414500781041c02040d49000703090443c14112543c50b0101981c2031122401052405198103101c2403401800782c0350000001c500030085001c180c2c011640314828040083c103e01d80c1902c80e42d00300002080518003440c0d0100f00c11176241020042c24540d01149880e90062004601503c0c1c105079a07003a800384c040000d81d079018002c1d107590702440443d14a801c001c410f4001c03543d20100d0300d808100010310040507165400541e443c9807401a440c0c07600c0c003a141c000038103548401c0c081110800d046400700b01c01692038401032418446003d0ba0304203805811034560328000319401220340507044590388030f8405030a00780a02c0c1c84180002e0100c5104849480d4450300a0f804075942c1500480502c40c468560412101c140045400041c802e4000b64011035283c2c051100501806605020b0f040082c0302255040242203000c1c1e0000e8124014000b09904000021854400c82e94551440c211102e401030010030400c0e640741843e54490a048070001d020a4040c1c1031a110300c1c50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 513896420 1250 513895170 513895201
    0x51c0206100b071109060303090a03030f0e01170703110c07030f110f1509041806020c0c010809151b0a030b0a0506072003010908031008100621020402131805 69
    0x144034907500044d80280c0204100340760050121707609440144a1403020341c45036600301000e50301a0305d5400fa64264250014090184c0c400c40c241000101c2c046190145c80d564251074020300c1c81c8c03c000c41e40b0400c4008104050041c81011405403003a0b00c0000140f08034003400c07481c414082c8030325103646228041841011810201440d80108216881001704034118010b091550303002000803d5406d20300d402e8a51701130341c03158141c400940c0000e61042024040150741107086080c200000d0b00c1c0b90031144d0980f10f0950048900c1903e16000c0015160300403281030351220300c0080d511540301c10b02044010020565220100d00034040c600c00030410345002020385004d5540521101480c12500c0c1d4018004512004100e03059034a5200510000b004000038612680c43c2c43c0010f101d00303287c1044d044c074286540c0b881442d001c0c80c0c0003050110048050000100d41030072101c9011000961012034000c1c400e2400e8011400318815000c11034580301144120405001c100c10b004c0da8440d012040c60102d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 513897670 1250 513896420 513896423
    0x609050910150c0212070303050d0f0b010813020f0a060513080106080c010302070503160b0a0b0402030402090a1503150b01030506041404030f0903120801091b080112051c0206100b07 80
    0xc0002c202d1004240c030941e00c00000910190481c00b4403110b0070302c118540b40603a00120302040000c9211520030407e84581503145807524024002c0404c0c0c040007a2503514040d2812000900c1c3c00000d038103548440900b0380702c4a030050f001480c030a0351800000d00941249540b0090380240c204006a102d02c14015001520b40b06405000102c00d4200154000d52041c01c040390640814440f04e10103020030302c2e20b00007144c017401e10181145802403105084949003480ea40c800c82c4103006010140e04e50400c070300e0b440901c40e000001c5000c5038102050804109900041040f001240c03202202a026002140034880a0704d0501c2907446d10002c00081c3c8042582d000d0080d03076000001404244a00271410050300942006141940c8036268009c0000c1c3d01c1c5846004074985c00010800d405551240b0043c20004815070b441d04400c4040050180307406104902e9040d5140e00c0610512500303010307080d4030f000d00b509503114a545058002e925004202c40d16807c202c1c50030000a40c1000360303412500e40c503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 513898920 1250 513897670 513897689
    0x60306041205130503010e0a0201080c030f0a0b0102030d0905010e120f0d1e020c01050105130207020d060c02121206010f2610030b040b0f1005010507060c0c0c0609050910 75
    0x3800300341207030303290081c0340341c2030724a03c0000340020662420700c51890340101c010050300310a0207a00001d40f0140d005031000c081c0d00c1d820010401c120409141c8150003850040c00821880d0354040101d1840c003965200269052500e1010b00070450158892200d149121703081e6000915a062044900d0103181c804400c000000c00c5184044041076011184203250114072840c03084801e95200c0c12a0030403a2000381c1c130f070754410041c8140c1c40e00d141c2c292101c42d2200303402e40c600704059000c5031011761400300041415480340381c00a1014000d00c03090801c8045250201e443e600c00aa00348200e100030340b0580d02203414158035502d80c5100b0300980c0002c00c943d0290f90020100b1406816100000900c2a54003c0914002000080350441803900031809072005c3c584a0918038442e50f139003031010304150180c01d600389040102d40d8200b0141e8101c650032450001e2000f01da010103075a12a1039020042050540c070074089141034001091070261401642c0e9001555240c18540440401501407110031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513900170 1250 513898920 513898943
    0x5071106150f0f0414070f03060b04120f15090f02041b0207030f020d12020c01090501030b010c020906061e0d0c2303040302120a0e0411071101230d0f0506030604 71
    0x908103050050880140648002100990001c5c1701200c414142d500000162041141055a03a45030240a016000101e950341c6001e180010120b460070028400500c0591603c11500034005094900069000028010720600f2b14501c2c090508100c1902d040344a18a0400d00303c2a0130800c607018412008181c005010705800c60b1644856003230380302822030384841c100703019500049800c1140c08003030071590010001081c00c41c0014062038415007081e410546040d04003861030707902410001840c0e40541e1a080380713444803804221144908040814150300c03211406100324640002480603a103064401c200062507200101c456003440201da080803c0d1982d1030728164050f10780103541140c824011288000e070400d0818a80c0c0e0071251964011030280181d001d40741c05c00f400f81c43e107c4a030b540b242c0e5140402075a20030340d2400390310440c60f040003684605240c3c0112846210508546281c031000c0d2102c4010442e60064041060003402c024284400f066250400080d00c902643c0d0006001c44e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513901420 1250 513900170 513900199
    0x5060313150605300a06020d180206190201090206041d0718050f0d1a01051804150e030403080c0601170105040f320a02120318060d020903010507110615 67
    0x203042c403602110131015a0703260340041d40850104081000340c3d108000241c0c60b0350059021500b21200c20b4a2461782480713004035000142d1720002141c8003449000d0b018058009428012401460341c15070080d0031003400540805d42d03103505140700d08196010b0080d01c015640d4030508440700140885400c00f4a141c030036041c015490040c100303901103030340586008200d08050325018a01c0da0400b000d801610310b00300052100b030a110b581d600100c1210604617445007400d9540d99804400c515104c00d90581c0d600740d0202c0054148121401150070000c007680b1a9150310b09180c9900c42072150410b40b00107000001020003040c0106071250360400c01100d45580319031980840400c4079101c0d00000c04800c0300144840400f008041c0146810800a044083c03692040c408000880080600980c0c010f100e8070601b1180c04040c4520400103031851500d07a0b410704641030203801511101c903459400c0c4030402c1030301c82d8030104e01003036200070201b1140036865080c50142e105400e800443c0e084000c43c40c03040d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513902670 1250 513901420 513901459
    0x120a060f080a081e070f050106120f06050c0403051c0f110a03140c01110306030c0d120c0602040e01060201091b12110307030602160c0503010b0603130c05060313150605 74
    0x1e90015203030007514150912141307116580c0041c4044641c5d10701540e194041c49000d00c81e1101074400405540340010780b91b1034071014841d040d0f070000c01158a0300c00140d10b1361082c4040d1001107070300c07404131601c29400045000d001c00c0070200b1040000c00c1d503070210340b40511625440e004801d2080c0545401c8900d07440480b80c03007804040e1441c0c60241000302c949001070900c0360109440809004540b030b070a0240c20182849a0020b032184144210b1b81220701154258500a601d50040d0501101745101031400102070300490340f102d5056508640002506501900020000d500c5107212400c05003841c2c8103644460654007951080c214a449440d0014600342400d01030840000d0494400503501d660320700c103aa020041d104002c240c043c0c1c4c50390402042c5451800603041c114002e00a079803c0501191040c000180f0303142407001080344100c07e1003203d42c1c00714058100904040e5507490f008000600d00c10041f00110b130110601900342d85500701601c10b50301510f1005104d003d08904801002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513903920 1250 513902670 513902677
    0x90c0801110409050f0606043c060210060b04061b020402030a0507020d030603120c05010e030f09010809155211060714120403030506090114011e0212120a060f080a08 73
    0x807255270061a450b1300d140c0390440715440c044c4040d401d16003161800c14200038101801e0007101101d0b541482c006025904260040e141600c1c80c5280c403141c1b01812148405020764410f034080c0d0054800001c1c001d0310221504641c0c807420341902121001000c0d00c00407001ca84079480050132085c0c001e40c048580601c51800c034070009000f01c00118001990b10740c46d50a650041490001145001450b2841c55800802040e40101c40782d01808a0320b40001e804205c040c00242030103524004220294548000010210071041c07484052210f50700c00100402ca80000000c08591400b5200440200c0c552241401055041d8540c0c0501103a450701d000695042d030007807440c040c6402e4180031110612840b20013031840303207000741d4000c105400c0c1031003400300072101078000c08180c407102c8a420030543d8000d50383d0b55024814103802901340d91503400490500150103241e0380034000020780f48210360f5040b640d0ba401761521040c02c010700d030741d0746040c03040c64030440c820201c050f00109065004918624080d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513905170 1250 513903920 513903959
    0xd06030c03200141091918050a140f060301050a061d06030a12020c0406210f020406050307060503060f09190e0316150507020d12090c0801110409050f060604 69
    0x1408814110313078004815100a504490001100403403044070a00d8050001c21140c1d4654645503001802d0603602c04031100780c2d4500e01d003000c1e213410100d280d400c55540451200e14400b2054800c909010340541a140803c2c1c813160b01c01c2d03007401c0100329040660b21414040f6030f800911003030424234100f003820080e5401010654540180300f001000710300c054142c5162400c859005c0c100000300b102c1000102e8079a5040200d031407050021400425400302c001788440743c1c10050400c40721300d040c400074010b8019a00400e425002e15203001a0b6560404055405140e0403510340846c0c00d0480d00303201c22400229040c03004c1418a20841c060304820341e01c03000d1042d003d50103403454421141000e407422081440d0480740a00c1c0c0c032140c203010f807041d441801e803c4012407004c1c00b0000d410035801481038a07500303000e070803140d81c624801d810024400d103c84020445100240000101c0703010b00d80194025100781003ca506060001c0c510000c0310f01111700c0b4500080040e8185410003509501d1048640036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513906420 1250 513905170 513905237
    0x1031a010c11030a03090303090e01030b0106050705010f0e150603011b0f03270204230c0f070b07032003090a06181515050a0302031b060d06030c032001 67
    0xb541a5101442034540060081d00c2d40310a542c40c500d00207111040a520061031950a0001840002d0000c002c1c07a04540e49444c0060321598036044c00d43c0140b01c140d5103000c000340b400a0000070420017084c0340301203140c1c44460301c40e9a03480e4030516003610344220040e00c80e0030840494005103400744902450b15034844c42c000644200301c05944061061400b5480d40c801c0c500c400282c11031820740140201220105640c1104140c3c003135455003612005464100390b0301000c910b9044c5005210103445080342c01981140b078504140700e02030014418034140340780b140540620007820f000c226080b00d02a0f21a00d0081000c0c0c0b1a54549900420310603e113040c1e840300107402c1a0104154007008d44030713038400c6000020014030840308540740c03089550110317000c1c01d80315504001503034002c285000c950f02401309103c402070641000480d03602c80c0c003684e9850746160035804810700401c40000c500341e91051550342d203000320032a01040b011048020190010718102c425101050103000d5403005800f1054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513907670 1250 513906420 513906443
    0x1a0a050103023a0203090106031709010905060c01020c1c03060b270d12020d020d020c09060d110d14010c2a0302070512011505091006030b0604260c01031a010c 70
    0x180c0c003a0a90340152203555007070303448020910a020085824ac4a84e00f201c078012803074048154006480c4140603c80c1600c10710012520141500c0c0a40446035110110f400707507071320260100d040421002c0e8400e50023001915100012582c01c07000811601441000c5c6070407d031325280320503c2010a810000c01d55045010403900600045960a55811126880d006005981e240d100020f181960301409007013190b0141c4c0d0405c003141c5800d08003030307080300090b296000002500d09001c61601400c1c00a0303034004e01c50006101c203000240d104500300740230313080017809032440070181251180b003800f00d0b100c2400380c0031403440300c3c1a0007007541854030381c841e00640c3c240c10b94404c0015203c0d141c00800d410305035129010b551600e41201c031944083c1c1000c0390441c0843c05c02c02d15030000400c15010b600181541c507021200965143c50688008003149940483c036001d018015400e602c924031346111041c4540d444100b6658064000c000d00641401d44484c00705031554011501040d940314251422100340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513908920 1250 513907670 513907777
    0x50f03073809011d071401030e0312090a05100c0e0105070302010f0507090801050c030c0703081f090c020c040501060e060f0d11040312020a03020601170c041a0a05010302 75
    0x1901d00d440760200d507000103405070000c401003401c1d410040303650740f0079085000300303100302c512070036500c3d07405002844c0014200c6000c0c21001d16502c0f8003e00561212409020050821070000b030405c0d966204209075459100303110038a4082d110003646440116131107503040140d0394840e10292800d10700910000c21000c030980c44d040b04640702a03401000081901c1020f004205090181513002000002c00504d549080ca02c1c101550282c2d00000302041541000704440104691010018000b1320b20308082c40343e035403140000146020000074004d402801c04454051074a4031611f4125002503d640c84001412000c0101a600c5010103416600051000c1c800d40381292051a0b51486420309003969541542401c0c4072442c40c0201d030104542c0542120000280e020640c1811103c15a9101002030409003442e81418514404030f03230000d14040704255404084103c554940c0015150080c1c5151100e004400343c1c400d040010340d008418403525498a10101482d00303000e061a510605c656041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513910170 1250 513908920 513909023
    0x31e070e0718090b01090602160b0f0c071404050708060a0b0f16060603020f03070b0403150902030a0309030c0f03081e07020312180103050937030c050f0307 69
    0x454103d441541d81d1800c1440c09943c02000c464003808060008048890840c0c40103940100e050007000100303640418848000a540c005899400c855501030750701c55510740d020301056a0f104130181740710b10306260108001c00e0251001502441c00a0204490f00381440600040c0341d026045400b0021810052014650400c2000b202503620400c80811503038514010070031b24901d100110381c4640c21141041180701c6040e02268101d80d480740c403616070948404940700040030000e40c080d4140c01044480000c15900034501c80540e441204c0e46610039880b01c2c40c0314440d07102c5020007000e0145c200081c0d0080029001c0e05c040cce5a100754200781c9401d54a502203400c1c01d1244000440d210004100d01c00c10090184030124a0344080c0f17000c0025207000c080c0346954801c16541040e1040e82c009041100c000d0400f2030489a14205032600c002034290b02d07004100d1440fa039016215401ba080c3c3d408074220010023121281074020898800801c44110000710100201c0302c0d031000d0503003c04064050155 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513911420 1250 513910170 513910217
    0xf060d0509100e1501061103033108190203031504021815070b0f04081914160b010b090906120309130f0c1106070c0804030203070f05031e070e07 64
    0x183d080904940c2203070b00d00d51489500c06810540510115186d102805c0000100b6268002d104591741d42c940900840c4007a80e02ca42034900d0107804801c1803401007802002070041144444c008038411412518400c200c2e00c0340000c0e6140c483c0c5035001c0c400d402880ca4207801812081943c0c0040c4400740c00601e00181440592014602c0b403100041120006c0c40301000341194058041e0760030303071481d24141e82c078904e161140628019500c99081904500203200f440804103030410061043c2d81c4103000036003043c0c0380182450071550f0699400011414900704000c0d2041c03240013401044440e00c9500401007030203028202c2c1402c0d80700601040c5240c0d55103010000c00d5030140100001c5c01d0052440b2a4182c0b100e8500300b00a02401c0c2c05600f82c0200c0c00500f0380d0313201085180603040c014842c90920000d11566101a6051240c1d200100300d002c000c140c1c800c2111411001c4480c03840501c0c08440000459030040c007030b190400202040301003840b01c121644182c0c9803030005200701d074030b03004c000c1001c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513912670 1250 513911420 513911441
    0x4050108060f09150103032d02010213060c20010c2009060607020a090b0a08030f031f0e04150e0105070e010f1119030e0d050d030b0f060d050910 64
    0x1071122050105140c1841140341e00555240007604129004613500009040180300040030081b0341e080641c450b0b40c0c81100c85404004202d003101e040340071408028040c0d08618402400c0c095003000015025028041c3c00b4055584a102a10b440d4802c40641400049801c0b413a411300900201510010725045920060311055551091030714000405000700c48800400c4180503040030016140540e54404000080381c10791080403401078500c070301094030040540c0c04071415120100342006001843c0f4080e40c81400d0344003000c000000114101c0458603114440e814109031807101003000f1a0000700c0c05842000701040110b2444c0e45100c4050868030b0446940000800b611040721242da408092003449000300c0c40c100c0407511307004515039101c00c0c0a4055081071074a0550718820075025503501c244661005000c90b81c1d0807010b08041d500ca050701c0c101c6070006841d0400080582c68a80218000648003074403070350034115000d20302c0001345005011101640301c2c41c6044200b0a8444c003c0b401b400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513913920 1250 513912670 513912673
    0x60309150203060d020d02040b06040f0e0705071e0501060b0712021b010e010c23100f020f03010b0d0b10020703050609030301031214041d06030d03060605090111070504050108 77
    0x2001400c094105a42400c10103850034010414401e580c0d0303d0501144c455074049070b40b41210300c1c682c800034009100d20704483e5004000440e000640144c2141240200c4000d00d003d20308a6569040c02c4500b44180580203119510f50f03000500311220521481c02e10a1042c1c0000400c2e07602c030240845e580c1c011307141c01c03078418180b0641da4207159418070100315450b04900051003c4002827002030000c0318803038080c03410070205003400d4081c0004060036a01405645103010042150448490345030b04080840040c4c5504003080403240b82d1551088900c0306c6141c45485043da42040703801c1d06250300400c1c02d202101d440c0d00d2418425520005044011b4465400401c01e80f4658904282050802404910590824801080810180c07071080700b027904103141c07150101c2042c41400d01a40a29007022504141d040202c04403020560020342c0950f004a00302c41d80300182013000c0702505d0030b900449002403028040e40d10755500400f1000100c031841002d846945403103001003402c6070801d81c1301e141503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513915170 1250 513913920 513913931
    0x303060f180b01030903080604020a030207021e0a080c01200c1203030a0f02070f080a1107091e0c2109050115051206040b060906010c0506130c080325020612010603 72
    0x292120310070048403010a0805101700a01901d01412140d0000c1c00d160045400040c00340d800d5100e58110b030070b41c0b1760007001c1c90300c240b807045540d84151050200300c5004503444400481c1d400c80024800752254416510b24140400c00c2c0000c1c0080c0d814000b000c0340030b10a41e010b4008940d15a840c803501300460710010341e103d103005a00c880954101c21940c0381c009204006440106145000d00d010003900840c07409d655104603c41140d4100501e1031074042d0707003e0981c001c82c00d0049500540030421560f15a401c1280c03c00800c0c400712021040614080f40c14980000e82e8050314412466121000340400a040b58003600ca0f142511401d440304110488410014000351500e0300565038690715400c010000d40c80d00da0345e83c020031078000c1c01d0300c0d20680ba40c000140702680f00f147e51900e02a480720944542342403085144d01082458402141c0c40300c91400049001b11b4000141d800200d12044080b60190f4041514824012080e130b080e0303001003080000d00f04034202801814020005907400145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513916420 1250 513915170 513915209
    0x100b1204032a03171602120903070b030103060501080d0e06030601030c050d111b280204090212030304060b012a06140f100f05060a0806030f0601060c02010210091e0303060f 76
    0x500780402801002ca080e600708040107175503400220050450914040030b0340e18a0000c001910301112a401042da9510000c008010422560807850481300090704940d80311038188010b407050340200f801310750042c400b0f2000685940c400d4001c2d0000c4001400c019160581c441c01d0780c0d090351046c4641e8810400001480076138114456148400640d141c00a03003c20303014100c10940813042d581c58031a1100388255100103560340c552005c0c80450340101942c980d00c0308400c10580740d400440c2c054420724540703680d6418550103042c0030403000c0c4074114070708046185207100400400d2588000e68540307503034a604200c96114185034038020000384903040d04600e00044131400d54074131500300c21226002e201c0208074a803102420782e00da05605042900c0503a4880d0082403601840708002805481040c0000503800c1c0c1012180c0d041c0c178004e03403d0303a1190300b0000141c000d075201c44400a20703c80500c2040040e1044210340070b605075100c4d15002c6451a0344800980301e811080d00a4280412580d01074034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513917670 1250 513916420 513916457
    0x30f01020a1d030a08031f0306090605070806090106120221041704180c020f150a0b062812231e06040f0f060e100b1204032a03 56
    0x1480c0b60301c2244400481030804011949800201400600c110804000310381c1211841410305c40f02c05000b4241e8500301d6036030400b50050b04000300c0aa400d14136103004140001d104540c02445840e02900d070200c541d10b4001c0c11594101401400d6000c03660a001803080d1203c65040b4000d801100c040c0c03451241002d050820050545d41c2000c020110104410040c590075400c00c1d81c42604911030012300d0003007018069090504070600308855001e408040303004041c000001c02d0069003400402c200e40b801c03000a0001070b10031540010078002c2c1d1180682d9004008800e1f001e00722801d443c100c0030547d00440319201b551b130080d0344107404005c1060100e0010500344d04c01c1c1d031320072907002c0040756400b42c0450274091424041c0c00d8500843e02d428194880c141e05421414001104080c00c00c40303543d03607480700c0d0b000074016504002c0b9014171001c0094860071420646420428500704984903480c1c0c3c0d5015a01402c1b16004840c521711030340000104140450301000c40d10b80079446645e01d00300c41803120f1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513918920 1250 513917670 513917687
    0x131415041403011d060112020f0603100f08010209010203090607060e0d11010f0b0d02190f0803030117070503101505090910050604230a0216080c07060503040f06020a0e030f01020a 79
    0x13400c4030501000d5401c00c0001c0c0c1d14111110851408201c1880e400440c0d41c9004414200f90421000005d0261090300000890202c03080c1401e10040b141e166050340b800d07445100c64031070041c0c1c004e02100209190040052142902c10100040c03469105001786007400b041d200c03c14040b0b42c0d40e003d900c1e0000c801b801280000c1c88500e504124401c0e900d00041c0c40c003103c0f40d0019018104101c003000040cac82c5500b444c1c01800c6902084a1400d81d1804200c0c1d50341e009010b260010802041e89440d514230000e030300350548000a0280580c0c0001a14100060046080b00712000398910070028941d25000105070081d0720000151204006000460058450140106d4048e80c94000f4030010031542c45146062000c840084c1d0305191111402e0401034014903040201201d40a81904100701e007a0004205000501c000d880c04281d4500c01921140011100548100164502d0a0026a981d80100400c0881d8180f00300302c0b80d90300020900c1e00310028010a00e03a0350010710030070b500350400d905 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513920170 1250 513918920 513918941
    0x31415070503011d06130513050c031c141c3305040b031c0c150c0507060905030705010c050d1802030a0803090f0307050303010f060513141504140301 66
    0x240c2c5107524001801c02c50320040382c00501358a09400105945689a0785692041d9105d05424402030a008100403d448034090007141d6600c1044980c0616040c00f28a1140d10707079614940807983d0504202c10755103400072400e044060303402006180341c0b0158000b02c1a81140e00e840d000120041d420159100078686416102c0000361055241c90500c8011250b010035100c0c00d90300820000103080110340b41028161a02004e026030500c403414155200e460f10480078058800d0074440d40760446038004661781000d41c1c800180c001c201300710215045400014a1714410400c90f85080d105449280c211038840880d540018400100b02014241c14007801a101c03245032881c46a81505600082c1e03901b190350b400510685002c000542400000c1c895244040c2d80002034030f42d500c10510342aa12903201740108070090200700400303e9840c0c45030b002d0b1030b0102450220429418202140d44407080c000b10a440d0f4000c50025508440200000190000380306c800ba0590039940100101800e640800e00b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513921420 1250 513920170 513920177
    0x9040e1c18060215150d06060b07032d180806090601030302010e0c130b030109020a0e0703061215050a020405060c150717041509060c05031506160303020c030403141507 74
    0x8000c907132164074107801a00800c540307100c404540c402d0004502985035000000d000c40f0300d0820005641240d910040507254441e80d24a00b561070b06c00071000c9d107802805010444003d8003240300c0c074114004c00891007402080e02020340080d035600b943c94a4804110748a503500d400020041007059024011000002c4283c4050080c40c2040340101d00f84640704039001c0c800646410007018680c50a5008841841c2c004c2e12064030720307854507547c4606410941d040c40c0000e00e0242e0003c1d400c1c55030281c03546505d510a460101002d1307001200005802c1c05000501c03916400c0000081d5943c4a40061484c441c42001034040404100d81c002207650300245068203021400f209072003405081c207003469200d50301503058103d488041d804c03d00202034481c402082d035032030942d580c102590400065480351340c07049a0168081103041c00d11855005010489a12207129403080300003a000e9006400d611000d0030440e4101581d0351150903504204a400b190075070030000c000d445000d0b110706400e80c04002c604 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513922670 1250 513921420 513921433
    0x406020a05070b091f0218190b030403230901090905040c0e010f03051e06010501050a0c0816060e07081b22020310090504030507030309020315010b18090c09040e1c180602 75
    0x140710030b04081c0f2130000c11300c643c00303c4841440321044501032360060b04a0313044840d1030b0b2400e403601806000c0f00004c3e161000c4117402000c00c0383c1600c142207884018040c0d5a4003810307132401c0030182c058803014008459003002c83c040400c1505402c0a170038000d042144988400900c1c0d4205103007041c038081c04501000405850360b038082c8030b00055846c111402868142c0d65150a80d80894541500101c020030280d0700182c48210300d08001e20615a184c02190708102400116aa031039032038010340b003000603079003110602c02d01a4006010b20612040c001d0030400c1f458191142030b8484175441e18a000311981c1c04030500965091480e40000900180d0b1403c0106040c01d840c0503003103000300d800c000d00301900c922903030007103440901400850904400c0d40c0151561115002e10582e0407811901c40003e00c048d54a030f40c1403500300c0c041400b844407104864904844841840003400103040c89050a11920100c03003e00845400d00300d0140380f050b075502c3e42c03003015840041d00324207a0744e000004640c03040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513923920 1250 513922670 513922687
    0x6010302090103021212120a110a02073006050f163903021c021203040b071407121b1a06030c0a060816170406020a05070b091f02 57
    0x1c0710002c1c1503e404603030020342e00007114000f5141224940c0804503426020840300c04008443c0340a600800509506018100c0300104500103030043d03182420040e80104c804103c1c82c003514060000a0400d280c4c241104019013446009500102100310340090386c5a0800089140c0c1c3c0316802d0300010780060001110624003001091541194400800314400f001c03840145c4480347c84400036411040c2d04840803041f103007000780d2149103012501c08200407014209003d41c1c804552087e071020700c0d680c07140c25500d96031105141205c0041950b0140101c50031350404644c2c01c1c4010340740c8640f0500d031540042e922154020000355001c1100c000102072007500d800018207040c074444011030296042c04035981e81d203000900d45405000640d07040710403404003041155100300c1d01840f03100c015460420500500d5000c0381c11000d0303259405c0285205a010500140d240e8000301003444261404a00300440c036107030440080302c2665420981d6218103065041c42d8000c4c100d25891414581d011400e10114 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513925170 1250 513923920 513923929
    0xa060b0a05060301090e190503070209090105090d0e12060c1803070b0a230309010c020f19020d11180f0906091015080307050105070212070302100c1b050105011706010302 75
    0x6010350000651120341c0e240b0304a1040107068126281580c1f0b200300a03100c0e007842916588150300503400b46c0b2110340014002481405414051403e102c01040341000c4480101c07007090040c1131540c0c0c0904960b01940044004002207801448001c0140b03545007402c00400f1403c403440f9500d1400794015000401005c15002f05688400c0c1541c10020305000390300c004080f0a5000341c445004001e008402c1c0042036005510917a5201200d40031a05641d4080d48500d60b1482146680c1194071406241e010041c14500c9007481c40d18030410003500348102c40340c00541c0307014481103410400c0b41d0703203010003210040300b5403c0394010502e20098500c5027010710a16445601480d40303c4c141a8482e85c010040c101180308050042c5401000d490700c0b20450b00d003160284c68103aa0310f40c014411800d4000e1180440412038406550540080191000340e000085c050070710101c0300b405101c2228060b241a1300c0e0000208101e51040c0000a250742c180486c00780b8845e0107004941c0c0130780c0924014401601c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513926420 1250 513925170 513925177
    0x7020309010c0809030a1401140c0301060f12020d0b090109091106131a03070207060906050a1404050402070b0601090b07020306040f050f03040306090b0c070b0703090203120a020a060b0a0506 84
    0x5080c82c0c0035600410905002409100e45401103825206007540746003400001c841d03a020804040c0024800c42180300c0c0642c008580a80390006441c004200401409000b0203e2031464070300c1e402c0c183d00190302d0710080300882e00105c00000c6890384900b5440e14900c1c1200b210750240401400070820366030a40c44001000360400750042c01024006003080039007520b0001980240680760f100180b0447c040340039102030700150f40711030142c404c141d40071a6641c0030310138100555170140c2e2101d04008002c80225070800301803111400341c500401002ca050303100c1c1d00040c904203015001034401400c01e03200040002e15280d01084d44c500e0f00303101c3d080040e680800c070b15801036000404811460060b051060810f0f880e411081c40c80d120001d00001000761680212143e24003410120903980da03002d458081502c10541e00a2030701d01c00c1c000041c400c900aa00481030240080c04640b036004e40c00d02c0480e400d5012809000140c3e000404d4401000001c0c095002920016516203048519000c049401ca00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513927670 1250 513926420 513926437
    0x120207030216140429120f0a0606290f0d09120507050d080925050d050d030b010206130323031014060705030f0a12051003050606040b0916030e0304080c18070203 71
    0x14195030640c0b1405101300700481c0c0d104000d40035122300d9005444c1040042c440d5214000301c0e810ba0084260031504003121440300602980c1240d441c00e0300c2e03800300b903c4982c010a001c0c407415590f11500804030b100b52051160011541d10b400d540e81e40740c0d081c51441c00a004400da01003240c00400c20111510100702c50305256142c4280c0c400b1680e074001e501d520611150401900942140300d19014400c1c006030011180021fa2010060464220012600d403142240e62081c4100703484a03000c0040d04c5000003003020107911001038440050010266403d80c8140c80c9481c0c0c0c0444011700b031060003030b031640d4204d9000341107400d02d00d040180d56404d0340b2801100400d030903451011495059980c01a004a016108888810440f514054210490b02d03225400160307083d1103a00c0001e007a9040c42d102c1e09501c2d01d401082180326941e480c00244000068540031010152242600c49102508001502c0a45841e40140050070b40c0001030211065029801e2425003c01c0002d204410b500801220443e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513928920 1250 513927670 513927679
    0x916060c15020f071401110909090a0210050901020d02160b1c0c021506040b0a180e07090912081506070201090b0a032a120207030216140429 62
    0x1403030300782030440910001c0c81c46221010b000240f01091030b54104001d0001511880309205010301401549080300d140103640c65168100708080b08881c5000c40d00582c1c00081c51003200c2401e4900da022030301d42c10411002d13101091000c20426241d61b01400000742280041c801000c103101e000c603c81c060f03031141c0c1c41a25640d1200207400389605007482c000d42518010603400b8484507a500d0b00c020b58642001003c210411a1030b00816103e10b45405024120703107004081c40c04c691b04000060303825010904c10410404c1e5207a4035070003000010b000c840005c10550000052052460900c0710341405850210010010150100060010545d905c00f502d1201902c00d40c0e2603440e5840140c40c08259a0081c20815101160040c1c0480d41342c1c01003600708070100c0d086c600341c40d030002029414203e554035940c04100103018075800d4403603036409001098082d104030765400420140000030300216800c001199049020b0420080c2001d000e10400030341e0822258800302d051003000c1511070008030255106 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513930170 1250 513928920 513928937
    0x6061b0307320622140714100f080a0b0d060209031002030601050301030f05070302181803090a0315140108250f0e09010e010501080a03030e070506070308040c030f0b040209091606 79
    0x55284c1103611604043d403080311100400c101d18005580c40520b8401c0d440e842e00d0f290b03100e046608100b8520001010161142c1c0d054840c1c400d0252800300c8018501d400445d0b0755010003070b2661728002c04d101c446000b80c400590740c5c1d8402e0b0905041c103984400d04140c09004000380300443c0da20400700d904682d0809110600040245070050810340d0540c0080c0d884140c07400b410801e900741d08030050103046c412135144020000030000c0754580c000d024a00307902507980700c07081001c1030091910051484441400041a24280c040e12013213900c2a0401d40c11680583e1240026001914004c040441800080406107180014001807807005015520385000c003580460b03030003c402d4010341d11303169022000384019a1140b201540e107205500094000909002d1280c1c1d000c480860f842d070648102a05462414119490903260120050300445440f5006000000400c0c507070312245050700d00c14101c844180c1410300410452140140c013112a940100c00600202c13421101044101c03106030030300000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513931420 1250 513930170 513930211
    0x90302060a09080d0504060305062e02011107050114010e100303030b010509210c0414010905061201050405030a030f0506090406111e0405040c051206061b03073206 72
    0x24080c103694081d0070b041c41404070200c13a02da00900a402034845a0350204500e5036041e081051201c040414600078915a81c610705088103a480c1e6046c1d844070b58000859100c18014070000a87d1044a05542c17596550500c0c2408240c00403105004125a41d108003080c2856200414619401d110003014165034518001846e4050406c0c1d40c1d4030b020060000711207080b010110f40040c90110300000540c0184100101131346024810ba10302d40b2480f0703200303a4030760707013403813420300043c070006d40b105a0042400300c1d6a002c8806c01d0080340d2040e40704a0103540c81d4014048041c054031990b19014941e113081000300101600d50440340c44d802794212070b010850072030044820b2481e20500f100c1126000c1c9212070550f407003e80e40007d200b12181038800304480c0c0d4a0090440d1035000b510596181e02d80e2550228110385010400740c860000a01000311820f03034550741c21071031988211011a10000da1091444240d4505108404a0303040100d007800040301e8454225101c070f00c01040d14000240b01d040051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513932670 1250 513931420 513931427
    0x60103170a030b0405040c0906050105070302061f0314070e0a0c021f0b031b091e150303040b032a0901090603111b100e01140708092a0a05060901090302060a 69
    0x104010f0014100304941d00b000d04085116400c40e010714400e03035043c8440011a03510075000ca418407601a03000c0e000d1520ba90084001118181da0700030b8001c0003603039011002c246015807101140d1900d10042045518080c5000001c00c130040611880d2450000400b00190f00820140e10041d030400030410b0301c03010b5414800080410000346030b00740c4a0b03401c2820340d241c600500104e4441707044404c95a035580761004044000c01040760310f8034030102c01001c92544402106802190400102900e003055121040014a508100e400502402108101e03072500d10a15003500c4400c3c9a40350424030345204000003074440700351480350340d0030140e031400e0f00100a03a440c41a549041c2c5000140100700d01c80030a46542c841c071000c643c02c1c602e49010b00030508207005100d0aa80500132801a90540d50381c56020b4902440007000c0c061140201191125949403074ad120340004c180b41b130015006120300105103d80030b5030a40000b40901020461074030542c0e00100d5078001c4a6044400d995100340c2c81c402103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513933920 1250 513932670 513932681
    0xb010f0f1b051902011803020d170f12011e060504180b0301020d39121503050d110114010504020a17071d0108040b22080309070f0503060103170a03 65
    0x34040e4001c201c10f0004220301401080100d5000f60703180c621824144500c42d00500a074071000790310609012030b2100050719681085200d00001e0291070801450a11040c09640405c2441c2003664449c801803003a01c40f2401d02c0307901caa42030350440201c9030610102078601d11590007100c1c01250f0502c074071012440c40b030b00408035061000d0029510f030062540301e030024120040d000345110f1017054001e011030030246c2c0c400e284181d00c00c40c5500b11800c880303802c0e41e401c05659400b404058441c01c0403002d440590007201d00561041000b0801200c0e9102c004000403420020001c0341e03414408804040007510340750302e065680c01c413001030341d501401900395117080042e09400500c00305e0200708070b0500e400042c00f6000384102ca403110030f10103d213401151001412900242a00b10301b401007041c400d40540c0070302e0903941c2c01d40d1b040d02e030782055152401c203904201c4030070505d58004442480030000d111050d50040c041a8020f0529504540c0c0300c0c80700c034034424207540ca80b42000c9058500c007442078000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513935170 1250 513933920 513933923
    0xb090705031002090a12030f0e1206070c140304081209031c030903090902040501080a110409020409020711010327081c0c0807020601050f090c0706020309060108010b010f0f1b 77
    0x8031100200d24042550207900304c500040d10403018400b000400ca041c00300c580312102c0e490780d40c520b40100c08440580e6100c0816049540185001040030700390320003084054014a882d8407000d900d0b104510b07240d01601c03140c1440d11a60303001400100104200011240d06090820031803e4680c4608030200e0b2500b40a000c1c101c02060143c11888c0020741c05030b00031915140203a5400414680b43c05119043e84030350f01c10140010844800101b1900c401d501414040c03116540c03880c0340507070325511281682c200307400944460368001540300c02c00c074004030841a00d145c2800c060221020280d5000721644911076805141010040d600301005807440458035010b0151031029803c100a20381c03500108122900b10000c5964280801c0e100c50000880303904071240109078201718001072003030140c8050302600d030076524a0241b002c180041c8687c0080c612074907040008180d10342c5801c22141c00d49214070146414000341c0756141c40c61641c040104854075800b8104075204d41a08501800c2803d1a07100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513936420 1250 513935170 513935173
    0x4141309020603041b08030331050f0114151020120301090e060906010510021518100b03030a0e03150c0d0b040209061e0f0c100c020610030b09070503 66
    0x402042001205515039000c2500c04032039440340e01c8406c640c2d41c0348410342c2e07a172111151b10303182c910640c460050040b40c0201650480d003d40c04040c4d560750300e4122005d9030510165124030b5411518018448843d501c45c180c04440740c1d10070040000304105000420041d4204070b00644440c1284040d0101c010903140070b9000c4039031410b20800c5840390364000703018000881c1d080c43d124020190000440d503000d90302c1c2c200a480c40341d291504002c1d0502e111034580e4254061002a0b8810590070085244100c21811103404025400301c1c589050080841403803a00324501113405a0585000003954951103040c200300d141080d080b070020f45496205030300580d0008510040040740400d503070290a04001c031940c00c0c00141e00460820050340240c0400340d801600500041c860300180c0c0406001079040ca1006616043e04400d005940c0d40c000c4940c3c60b81c0d5400500c40080c8401544030b5011650050b2001d0301e002e0401400c0901100d91a02c40580344011340000b007500001e0074004440100340040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513937670 1250 513936420 513936427
    0xd05061528020f070b091206090c010e03060106051e07050a05100f0603050c0907110708010606080f013204020a0e1c0f0b0a02130605091005041413090206 68
    0x84601d41c031407601c481450400030400304a00529070000a02d1440c03450381d071015101107810142540340c2c3e500030b07440040c0e0200c4800c1c0c5c115105401401114000d40f804e40103005104100d00025050006810405020341e003c04010803541d030b031000903545c0889800301120030001c0c400c046010303140107440c00940755025803000038040002c001104c3d2801c01e4000028000842c042281204541603844094030a0304225442101464410003480c0d008a5500700092040c000081d1a0310b0b211050b044000581e5440600b03101e020381000c03901c1c2d4003004484003030f40158181052001408100016500442e200a025604084042c00002800400a8011174072280c403000010120b0b11000c2800b40682e81005e01941c0fa000701040f50303030150750407118540c012046a40c0300c20201c0801072022203043e50910816880865161460008107500e03501c1d50744032010300003040084014440c2034018000200002c01045001ca2655218410100c48501d0718180e80c030207900103400501c1009511a4002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513938920 1250 513937670 513937687
    0x170f071b0e071d03010b28090e1b060705070303050403060e0c13150803030c04031a06030c1c020603010308030702100b0a050607080d09050102031605210c0d05070503090d02120d050615 81
    0x1d004841840e80c0804d44031200d41d21a08d00048520550300c01e031181d04100309038058400003c81910200034090100ba1034507905883d86400c00c2c005420031000540c000804000313101c2c4034004c0d94884002c200c00740c40950f080b13800181d200858280c900e103c194640013601944546584c0c2c0038000c5c10b0781c9007501c0e070b41c1c50030440540069206000445503014041e05080000d2401c6032028820840a40284480c41045081000d075202003242c00d12224980c00b01c0800503183e890180d0300851080070303a5038490a0090002c2c0c10410311600c18003e10340b525071180310035070760030030070600b114001d07074130207642c1c01c900d08002040d88a045103071061541040310420800805500843c441c0c81d039415204034602040c81e08540340d1040221545144800c44180300350700940110300c46c0c00c00b402400e01031400240810100c240d450072584840441d2010041001484060240c480c1c0d0640a20281501140c60911284140a01d4610742e03c8076039074000044807903e42d4007008001024031400d058450369403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513940170 1250 513938920 513938959
    0x90b19050d170d3b03030105121204150305180a0b0c040504090813080615042a0f030b060a0c060f060b070804030c0b09030a170f071b0e071d03010b 65
    0x500320300644e0070700403209060310b0306410800021501461640e441c2500300001081b000000183c107024600014680c2d4459000510040c41140407070011010344d07140c05412100020940040440060101c0000321400310f0504040d80c0e019204001c50f440b100340502480c00b80d074002603001484c1094500034481e28001912110040c4403900003003544407204251160780a862000c50010340f148030501070303e048d40150300380040c04405035800344185a6050100c144048500e030200340290b5146420681c07500031216091416030f00c0525290080e9401000102c6188015083e00e903985800c14068826401100040042e00e98036034542491b410020503540c050302c012591219254800200c688440c0b0645841c3c500080103007060580949500c1d2180303100c541600300a4100704180c10081841c0005031410074040e0410750852032030340034a200000c0213600101d80e2a4020000c10411540c4992400400540101c06808045244002c00e014112051042d94450012144004810b19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513941420 1250 513940170 513940211
    0x8180a1b051e10090605030109090203011b080a0b0102011e020c070b0c061501090b1204030e1e0a12021f051603050306030d0f080105010c1506090b19050d170d 70
    0x400310303a01e249a125050f000d40d08075802e4440c030b4022450030f01c0108104000d6500c241d069500281c00400e8941001d1031985006d00500700b20000705811109208000740c0602c54820201c00070f00003048540f5180384c0c030340c140010b011401c0a90380d0f0001816409888140a420700a088410025803034952100c00c06e9110b00c4226000e01d401c070790007001860309600c601c050340f080340c41c001890791802d1800bc40003100350318024415000e01c0500d00c2c01001d2611040181c04401802141d141042c0141c4800c0010340c4030b01d6413011859600c6d50b14407201590751045030110a45100d000281d10b40c0f0b40550590721405804000000c6c05030000e421801d1541090003148910802c40030781d40e115490354070580340310b400600b0304800140218018041940540110858140150b90b08401030804421842c280c500036001066107903207883c1240f0f101d04280c0c20544003e083c0d0444080c003d401d00c0702143d000791500c0170151040d600030a81c100590b8904040f40c4800140d04000d10450807098841c100240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513942670 1250 513941420 513941479
    0x280606031101021b060a14091003200717090d06020d06051f090b03070e03011107120c0b0705070602071e03120603080f030a062408180a1b05 62
    0x4110040f191540c54184c10428801c3c004c03e500d01704001d4400071a03c002c1c0705814a0001c0004004c08080c40e5a0880c1460580c00b00707540114081c500740c0d4008102c5180108803004508041c014500080d02c0a9461940309560041c0140c50761204000103d0080d9000000780840d840011107602e800701756003206065400940e24078000700e0501d1543c0d4480891943c07000c001030341c3c42c502402101c030084002d40d0005051b03d8003000d105060000203085484080354013007540da001070124108809190344c002c4c8800e040c00c0103200440c1d603884501d5480c400030140401c2140000c0d04170304001d0705070305a812240c0c00400c401c05e1201400c0c005a140c015190080c0c1c0420169455944594042d0060fa8141c0360f120084506100400b8041c400036080a04013108040c1c542e000826107400084202c8158800d080540c0d505011100c005803226101030401403400d044c0300714400c5da54800190404540e5440716880142e0b03100c1a41d004182c100f2070304690350204000c02a81c90500c01c8540b510ba003603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513943920 1250 513942670 513942673
    0x13020706050601080601120b04060b0f1b03030c040b070512031f0506030601020309092e09060801060b04210c0602010609050906040b040f030215070f02010f050928060603110102 78
    0xe4842c00015180100f040340c0207030000300020181c0400d031005400c404e07400c440c080e00200341389459400a140e11b8000242c804030103080869900c0d01c0e5144041420941c0d01760f81701440c91820318244420317071441180144151100005a8001000001c00028600b00c00c0c106259444e81010a00d001c19086a0701c20b18083c00f80c030703040204d10307807410f00b0489000d03510507002140f40c0081072091004407100108904554000441210740c094400650700d00b03403460b08414100c04034101041d0a04490a581100ba103030b80c0340150500c4405030304404c40c0c007914191030041c0040208070414490162802d880240700740b60199000070850380540101040d211040814000c0d82d590100c4141c2c0c40c80c0441340540040d00c0c41010401082c000022880018000d10507600785080c61100200c3c54141621000d000030b2000082c036640340d60a2244030b4040840c0241171040b4207100c5021944e0303d83c2000ca803240041c207910421400e8081047e1112000d501c20f100780400c590320304100415803401022140075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513945170 1250 513943920 513943931
    0x2616120e010810090c0507050a0302010e1905101107061d010b040e1b1804050a1505070206070f03060305070e1515040303030b1809060604270f020f13020706 69
    0xd6028001c0302e4803545001001520141c9010303030030310107040b50600113803c3c0301d0300700504400314070244a0003152a000750008101c07005450702c0d882c42c00d002003a05c440c41c1006c1c044164009000454030048480e00048041006441c508008a4a00c14840000e100c1d07803410705581e04000d4032006a04118000700d0081054102010030310081c2c41e334141c444030094000c082240c0240010121410000001804101002c408a01000751480003a01c098401c0d40c0125680d904100301820040211076419005005500306044040d560765001b81095050003c1d03e124017550b0b6109074041c100441c1c004003160b00541e0780b484132118001007910007412507641d50b101c2d00c1c80780c00c0c0f122041c1c03c1c80c84101d0085d0b03d400c1c6152811802452030200c41035004c500728040c0c9188401c070040071805081000c000d0b2103942000420001140c100a0003070030b01d154140c00d10380340e01003180f00e07410003580c02501d0030b512900103100182e1008603510440e5400b052090f6480604030039a40a001403903c80d120400c04c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513946420 1250 513945170 513945197
    0xf0c08061801050a0e0c0d060b1207051e030307030c0302251a090102060a0f0612060c030e0706090605030c0f0408060907061d01030f0e0303130302100603261612 71
    0x117844022a2403070b00c80d0300609500004e400c100ca401801940116800200070303101d42e000880011412503030314155400301070103001070f03e41285064407e2031741a40321541000341401103501c034090550060240501c4044074070a01d4000d01c100d003002c101c0c00000c20810504a181c200907040039000d074490351822030183c400007a07940e0742182d2004005800600b07182d80d0b0760700c590000c0e14810101514040c1c4884002581e81d001e0048070040300d10a10000c41c0440c600d40c4001c080310540c281e1841c0f264064002080f90541081c0c01d901a1102480e041e60780303548201e294010392041d226a05d00340c18000400044000303000c24003500400f41b5006070f850315a5620400c4034090074006a41c050356218524010b4298040e61101001c00c00080c0041812000111134030b0540d001180c10701c000010f80d000d40010103905020040d032481c003041040103441c0c191744401001404014104502d0003041c000b440c2d904404600340c40654030031111842d036180541c90b040004280740c0282c2004030b11030114100c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513947670 1250 513946420 513946441
    0x20c0120030f0703090503160510050105060d0b04110703021f02040e22020a030803060f120c0405060303040305120a031406130c050705010609090c050315040f0c0806180105 76
    0x380d1044003480c054110303100c1c154840901c07000030b808a41032590380c00400001070000d001403c107504480d90f08126007420380c200b02d420480f141c0c001c09a014948001400250740765000e03510600205c01f00003440030100004035004000440b25000d880c540400d81004155000801002c0400040e1034a4551850462103005030f00030380c01980c003080d10841c00104c1d94210380d40340c0d02c4811b01d12038030006455601d80206140074016041034070814070010400c0b01d582403604c40070510030400d0700c0d0301c4c0003d00b002d07009030344401b990142c8911503501c03031000c508695000c0003a02e020310323000400d0f03c00d01e41b03d00d00c036441c007940074003401c07000319080c5038041000700c1c00745001c0340c8550702c0034042c20450300c0c441407018000d0084008010a00c40144150303c082502485240c01401101e200040c8802c01401d1004c003180e10750784110302c00d40c082c8250b100802c8150341d1304da4100b60721401a41c4000035a2410205050240d0440c118500c112010021400340304410a1101141e500003040a51940444103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513948920 1250 513947670 513947711
    0xf06140315010c02130c080708010501140f0306061210030b060a0303200717060123030a03260f040218090a030507050f0703050703110105070c05060c0106150201020c01 74
    0x601c0540c08100000040354001c40100701510b00c020724041400d20002d42c1c01e021203d00d206404000f0324500108000780d40c100703000c40e014000900b4409101c1d031001c1010205446408940b280d40c003c0031010441c04e465000c10340c0c500e000ca07021402014039080d40440d2904c400c1c4d10064614509a0012400e00d003050443c0304152600b40c1d4845081c0304250300c03001c0002180220520441c4034103280003c1041c4400015600b080d101c1000e0100d5516205151002e032219541d81d1580010081031050b807a64002045d0081651508084c50300740030400405015126030345001d84e41d080d5407402c00081081515007544114801c880100a4600040701c3c608403000071220810603900c04840c0e0804280208041c01100e4070490458160012405949040ca42d1580c4111041d42c490034040c420855006403800c1e85e59800e2801c4c03400d0683c5902d034091382c0312031032044c2c0d402000005512401c054007900315030054610540a49096007860030003d000398401241c02c43c1c0b07035180902034000980c41352a00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513950170 1250 513948920 513948931
    0x30712020702060304110111010f060e241e1f170709120501091b06080705030c0d02070f0b01030c0f0f031524080307060624080c090a0f061403 63
    0x1060940e82d41780d880d0b0059040360020203042c04160300202c1c508c04801d0142c000080355001001c51010718194104c0c001302000f0700300203e400c1400200e50502c0304071603407200710048112490f0090034450741c0c050790300344488070540d50840c00500e0350f200b4403d4845005181d100c115034421500c2882074019180442054508030b000400000c03040012071008134800c4100c0d8020000090602e44940e40c0c03141040455640418091940c0401c00c103558103c1026980165541060f502d10320384200558107510460104c401c000ea80030452209001d420320140c80343c5075210244803200d50b103070304080c5a0740010b0300c60007a0a01d000f0b800800c1d1b90f0000744900d070440c0c0d84050964089812400c8910143c440700e80d8007a203154140b2010344400c0c03c0c501d210002072606201031079076070342c2a040075410b548141c1c1005a10001e01000c002007013407102d019509007100d529000484c0d803101d1a042d0399501c41c030680f65a10615520000c0350285518500d4411126140c444c01190309035145103c1250004460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513951420 1250 513950170 513950179
    0x151a040513020c06070302090103112809060207030206070f150509010b04140c09041b05092e030507020c1905030c030c24160f030906080c0d0f06050a0b030712020702 73
    0x221710158021b4001c4c0c26104070504020406021040084900744c00c0340c11040e24091018100036004041d120440783d40e41400c0c50721031070301c81c1401d00196a0341100d21000340122000900307003040c400f03480303044072074140c2c8a2203201c1c803000040120350107444255003910030365180c02207140e981e240030303c29101005507410030f030402599400300102040e00700402c2550059150640368040c0e402802403a81d254039940c46154451300d442c0e0901a94030f40501d41d90102c1c8880441c03041c661503078413990b015104041e180c04281c6540d881c2d412804d110ba1000c2403a0400328481450070300d041071900c030800780e83c0c0a07022a0300030086902015a10500c045015030001a800300d00c02013081c042038005c0280c249840101d1030507501c4244041c001c0d4800c40192507880300105c1d20801c05030300000c0386c0c0c010000c6242ca401c25091003e00e42d14240300342c4850b00d04450380d8000b00403015000f03400100c02032a0041c8140d410030b940b14140b0360035500c22a201c00001c2d44807080758681c4007407403080d545070540280 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513952670 1250 513951420 513951433
    0x2190305040c051e1c0218040311071a09010c0203010c2105070c03110721020405090d02030f070c0302120319140f030a1409030c070503011e151a040513020c 69
    0xb401102805640f90f0302c6440150f006410240c1c0381c85c1c89072081f03220b9120130031a1a140c6824010b0220700050039080c2650880c040c10043c80580a490703210288817a04210394502a01c1c0041c1c60004021070001c3d0507508281380d04812541110140c18103044140380300140440484440084404c03c69411011880703841045022a00c00d00792054080c0c083e40464044a07100c140d20002703100918203002052007401203120031420300d40202c43d0002c6401004103c0b2030030748000652a4024090703000e141c078a01207080b2044c084140603039002590007034000c204103951180c0300c540700d034400c610078813003089000101440c01d0f209008142a100c44003030302a0038101a0050030481c0e0f0320243c0303864031007511111038015221444000c0360281e003c550055950340703210f00005c0c3c14500194090b510070b9242a0103001c0b40c250b510001703001131000c28400075601c0306210f500c59104209800480d0b100003c0401551100c0a00005100b995001c503411403020980b4021807050317108920a049203900140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513953920 1250 513952670 513952729
    0x601240e100c0510110703140313060e031c0203040210021506211c11070b180301020f030a05071d010c12021c080a05010b04051507050102190305040c05 67
    0x481c1031000051151044c0c0e5108094500c050003034030301d0452003000d840f1700001d180080641020562101c8005140201d04601e410740f07152040800740c0d04054015501c0b500000e861440134401c691528a0350301881049000d400e580c60002d41040b58101c1c05804c0d080d42424410380000340403004652130445807001942d640090008001900040a882c01d2180e1840c1620301014401c0c048001504c0491011610203450002c207141c030070180702e840c1d64103c1d5000b440400580780c2110400c0345200341c560030034941c001c08070307009120703404054907200c00100521168044c1030300803c1c098800c070342e10043d60a4034207111f40041c82041514501040b002c00c0343d940002d0103280c41060655982c010342d00c40325103580002c1d1201c2210452140010064010440300440d280300c0c0c00c0c09800706c0d014490030a400c1c840030904903885a22070410041006ca001001c0201c250102ea2603041e1403000031402481058000d0f01030142641d00300d9615100c0c2002080900b844541202c0a801003ea465421b00c0720 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513955170 1250 513953920 513953927
    0xb090c09040602071e030e03011401180b0303130611071a030403180503071d010803090307230d210816180503120a1e0804030f0e030601240e10 63
    0x1400303086170150348076500c107050106a01000300b01c45020303480300c000c005140c004160840d40b0802d148050010034600600c9100c54000400081d60100c100c0090034101740000240b840c0074400203000950b030720010100c0d055600c10048035401e04a9000c5505942d100c130240d14890143c0303143d84048402c10f00004002c203118100c001b00c60803204001c0300010b0780319804642403094941016107050082c0e40115446048140b03103074010610300001c2e5082c040341d5030000c1d455242e42c3c455590118003500c0d4168400c001c00c0c19040c03440f1801810198900160b04d00351400c0300d40042d15503403000c803e92560024500800c3c45a10134004400380a007648a140020b07100c0c100c40440c0991045100740c1d0200d0592810040003003880b080c404103e440e00c0c5e10041c001c01d0701c01c3c941440c0b044555510f01229019411a0341c958009502d800c4c48540240859000c403210704031030032001d525205082c000941300604407a2551000e0040001440c00d541465040e11503800b001e40c250381003106254401e000501c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513956420 1250 513955170 513955177
    0x30403030f05211f060c0c092d0b010305060306042102030904020705010f050c071205300109110903030301030209040501091401050651040f030b090c09040602 70
    0x2940d0b0030f441c12500e03424440ca103c00704102c440d0a0303101c9001d0400340b001c0c0e001c04d000384000e03d501d2901e4078004032242e0b54101e0290540c800d01c4415500c80c0d01d80c1c86141c440c00007241c041080c1c08490415110188440006841c40800342400b207890031000c03441074100820050b10898020b8610380940d000c2c004408400c20011021070f0840c001400783c2c0040750364a0008007070b1107000d10000300b12004101c0d094021900c0141036040016010050003000480c01c400c19031204542d4240390ba16103c02c080401d484545403c0101a10000c40420403000707021002554187c03000088100650402400d6503540352242c85001a8140e20500040006250294070325030b10a114030000f1a5140b81650b540e021801c02040d054081d0f5101c0c01049010300f00301034503d0742c0403c0c02c0100201c00400c0083c05c01d00880200d4150a941070b0001203031903001e42459528a065070b80c100c400d50725655400200d2942c08140801c075020b1a021022409912001660010301d61005011410603101e5a8a04000b9403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513957670 1250 513956420 513956437
    0x306010e010909020d05041b0302012c0907020f0c15041a0906030405030a030b0301380310060501090503150f0a090c1401261501170a0204050a08030403030f05 70
    0x2c002c0078040342c850030070b00150109134102c45001c59641458076040c646680915518514002515000c00250380d00044401d19200342496a242007090407815072802070450403900e4100d145107040c442096800101c410b1544100c00030b40d1a1000030b1001c1042590086494106d045803c0c4024002000d080130740c0c90444d050a5909440c05d40700b00041303405c07900300b10380c2a81d460300007149980b200c07509402044150441200200100341040c5920b9080c4020195130010a03d035043c10742034219040e2800e4440703d10020120f44002c11401e40c1c0f103001d0000c0e401200c0c00555510400111414005003400121041404580c0d070780c3d440c880320819002006240e10f09a686900144d0041206c1c00825405496500706415601003403100241c00d8030050501402e800c0182881041440303000f903429078001154503c50040005040c0040b10741d032580e100b03102e184000801c240214102a42d0007401191400d8413140c0b8225a031307075821a01c03400340d0320000d0040b50341c9000c524905480ba200529440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513958920 1250 513957670 513957677
    0x30b10140c01020d09030509190513050606161103010b0603010f03030509061c060f120b0105090721091211030322060524040c0512090102120705070201091a0306010e01 74
    0x2134004401a150148030660100e0300c0050303022030604000d14030921544e09a0a10380d0801e1400c030201c0d50020044114138403040d0785030f01040607980d40900f2115903070740700c25199221811604000007503001000225100750b1030415000f42034100401643e04840c00100c01c1c2c1c40a0340b46480c1564254004404607a001a04000b240d602c00d2503c003180704c1e9001e01c418005995030406028941d44d1286801c0900d0360100d8a1140e00094205420300e0b040d20070a50700000151229001600d0328202c414582c082d0700002c800190050784c01d40d102e1260a80541c072000c0b141500440240d80a83c9007111000644e00100001010051111221303017481f8007030b5095440780d407090340701d0204998050b03894560b011882205076079802a05507074005040f00c1100c0c100210100d162016080344207860414a105596200040c5020001c0d41510442810304040c0c8003a450701d000d0084c00e035401203000301d01044030044007040c1c0502d443c1c43d141041081410103882c54031480015100401c0c00703040103042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513960170 1250 513958920 513958927
    0x5010e0607080c1207150b31020f040e0a11160b040312020307050a0905030c0f042a021005130b010b070507030611090f030f06010b031024030b10140c0102 68
    0x3107040600040070710034060058004646d840c110010142c4051141d5284144296007050100d03004841091050442401120505640c5010400003a000f032141d194402000410001404400c04110600c550f030b02070820440c0480581c61000c46014101400b41180402503403c000512481c185a41180c0207080ca0407902c200210004242e900894103000041d001090360780708a904501030101400c805c4010340491003a6102282035403c61040941c480ca84440701075500b48440c0c00503011001400600fa80d150124140280d034902c40c880e9008280c1c2e140500040800c8450820824495032081c0d0041c0c250f481c0603411f021903080a141601e06010f605c200100141d107a108981c01d0101900f12581c82c2c007000c1040040b02101800218002e80080c441c120380050040707203203170540d082816402d072261114a948004502d5a401c00450300e010807400c0d400380341e202d45540004410b542d0717080c8000222481071003066000071902d200401d40ca400d0030021100104040c280c03010003007000608 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513961420 1250 513960170 513960193
    0x9140f180616180b0a0e0105091306050a06090305070306021b07090507020c010503010b040e071106070305060901052e051e0a08011a040605070c1509080705010e0607080c 75
    0x50280030341d07151812410700b0303864880150304124140700743c00d85140300b03401c070600d40b4004040720b201d1040840c04011700025a034105030b018038140c03946010050720541140f811161101300401190003458030600c251940000c00340d1180218000781d941c032001406d8001c1c90b65136898080e4000c1006101d0b0104c442d003514420110808c40d000081240d404085540e09220401a041140c1d4101450402c101040103201c407142e6042160201c2e1030401e40f4100360341e01c000d800c542c05c1102c661441028000c0c04103200b42e691381504510302030ba07000c80380503405982e61800c210300d21640150664a2140c000041403038500011018204021355003025440c0500101802d068458586507507a00c0e000049048003006078030041c002d01400c00065581c1d0f080c40b0762550415140928490075040203400214001041a440e002c10700400a42e02c0d181215070b5010802b9240300a1405035045500c23980c840003c407507100700e201040010020b48994500707207454441300c01950040508603074501c40c2040c13145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513962670 1250 513961420 513961423
    0x110f2212050105152e02120301030b06090a090b07031d012a05031003080702030a140d0212180d290411030c090610090801050114030709140f18 63
    0x101648200e0000686240c44d0360000c20a592600403d80140111501c440044e0800c0f4100a02d810301101c0b010390030031600500300d02e40080550305c9a01114044000810443e41f01d02d0390b805500308a4540d1b01c00c0d603403043c90800f11146103a01a100b60b00310b10101c1c001600036031004c0c04030407902c191000c031300b50041009800d42e1040449410807002c0d01108500300000000d02c40ca41002500d0030381e25504202c0c002009001850101501f400c03000503e0794115134081124912523a440b40d0700090a030001c21200780c4030b05090000c0750141c0a900d1440351510001003c46040c50b00e01e4589940d0303040104240700b102006101c0c12200000c04040404c0c512011540014541c0400345000301c0c646058909501903110021140b80254070951501e17500b41c1d0f440704225400700c401d440c072a007004a0118122218991540300300115482c2c01d00200d4640c10444102980c02c0003641128101c5584404c10400c545c04105038848032070b0000046054014207503a60343d040409201182c0001e89880f0056 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513963920 1250 513962670 513962699
    0x6090f18030a021023042003010516020f012c0f1c17070e040203060d06140106110304050a0b0f04030507060e0a0b070b0c03072f01110f22 61
    0x740540d11072202d0944d05142c40c040c4c6015501c181e201c88000380a159008a0900390281c402001031561010b0b030b60318080c050f01c91104109004009004d24148080510401d10304446964018041c0420082c5003904c14001e00452a4503540036050305035403030450814492100210351518004d00e030008105190400209c1c4081d039072020865402c08150102030f1164a007072180340750556083e410402c12541001242080358401e071030269813683c4160005030f1050040800405817490040701e102a05485802541682c42e2070300c1e00941000d004085a40d80d00441c030940754400700c00181440510018005850071140710580e46040a8907603495506121440c0c001c40000391071074260300e4061600e001d5900081c42022841807800c011a1629820008001d004184404001020036400392048006407284080d161000e032442c2d54045500380807465001001e082c40d820040002c0d640d05036a001c4032003803202180c500d0720708a01c4100b0240c0302e0f050741101042e1464003440c0000c4c202e881da02003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513965170 1250 513963920 513963937
    0x703080105030f060f190609020d1514041805030c060a0b01032903150112030e0d030e040b210f060f090a030c08090d0f0209010e10050906040e0307030909050c0306090f1803 76
    0x158580040721105011071305410501d60046989132002c00c80300b408804640410cc3c000c0d40c000c201350440c4910304141704500320b0002c29038440091460760200000c903080e8010340a010301402034580b0b9400440540f0035010103070341c0401c100c21004010b104c9690481250100c09800d40b10840c18045441006840c242c0c40440400500b030401020103602010281046030221526480b200990300c0081010a603015400d019566a9506074480d6a4441c0c6402458901310301000494812900c120344070807030f8101d010380d24801d08011401c03c91241e086244100c46070300041043c010552012243c221819a060303881d4202000240d0082d01c402c582d00c0c003094050a5018800b00c05031050010032b42050b40308141d400404402d006500c01d80c200800c0807500c04a80c0d00341c05071107800014004064a148020300c91000043c803500305500400b14900b00e420882c001c1000d60303034540f025145840308840d684d500c41858030004031301d61070440d911a080305940d0040721030314003107510b5949540c3c0020741 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513966420 1250 513965170 513965189
    0x20c0a1a07230a0302150415051308030106170c0901020c060a03060e01030f2f010302250317010603110d0522030201150f21020d0b04080703080105030f060f1906 71
    0xa0071028140c040046141b0211074018400b40c40c6010b49074644841e1002203100070507900d07880403d4450f075000c407280700110342000003260789507507401e07000c3e0400104a400c10503000031a40041c0c40101c036003080e501e0360001a000f03030a48609034820002554003801c00c00301456640ca00206640d08441c44443c0038501c9640120000301240c01e101d5000c20300b0109000c0140b01600c16500b1030308007007448094000c4207090250300e401c1e00c040c0042003d00c81d0038420312018455440c5174241540a017aa43d0720a281c0c58172010301d83d0701c07260100c00751503a1080c0c80260203805c1229401ca0b01040c0d22050b40180700185160400f8170140100c00a6646154240d006039103d21004206103510f03d030800060038000190f4200c0c600d008001d0766aa0701d0019080d40150b400c0300780e042952954190300041c00d910410b28801490a440d106540e1340243e9403c1e00040c0e02d5600104840c100000c0822000941d007004048940d0307a401c0f603c00f8824000c11030701d02206e104d40301103c02c078030341e0180b140a02403e14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513967670 1250 513966420 513966433
    0x3030f0c04081609240e070201061e03061404030e090c07120e0307080c01090308030a06170f0c0f0d23100603170a080f0720030307020c0a1a0723 64
    0x2a09019510f050f280c0c00100c9244019100000c0080c40c00c2d0021103807250b000d1b062541e1072410a03401416907601155418011301070101c9440720104030030701524862102000300c21804a4481c4011104990040220320041c000210624200200c107502c0754840d0380e014684200d96035150500c0d501c4c41030a0700440e405551072800d034502401888090314066000740b420415644c00244500c0c098030024001d40740010200b816040107030452809070a034050000d5600072001d82140e614010444048031710300a8200807080d42c0703040101d000c1000001072110100d1040c58031590300c90102d030305902c2c1c3c950010301c200c00c0c9110014400b18039116114040022014550b0401c040100c10000807214400320822a2680c01c5400400443c3c20400ea0b403d501c140760745182054443c2e4281e00d01034400c0c00d00200103e03840c4640000258490b1100f5800e8600b00e100c00c8081c400702d010217004440701507034000325054144c641c0d20f000c1e20b81540201c1c8030544110b0000c641c0d20303101d9800007207000f9035042071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513968920 1250 513967670 513967679
    0x60b0403080a0815130f02090301140106020d02070510050a230d050a0624020114010b0403060b0d11040e0703020402040f2102060406030525050a09080c0303030f0c040816 75
    0x14039041c0d404040075a4107210341c022080000c0505c42c012041a480b20760301c58828180aa42d5415901c82110240080012000068002074090402d106000c01442849003207107801e032000c14130310304561000c0c111001000c2c503110156180c0d04400d0800c07007000107101490a100d015495040b1000c034036805216584c0071101101410303180000d22280246003001d008220380303200145134480421281502410303c810707510049002d8045c2c980154412400900049205001b14004004691152108012024110060100175007410704060180d22021503e046581401d800580105031164281c0b030f24640c6a9000038102c1c0c003ea04000c2034140e6000040c002f02900580720200002d1031206a003041c0603d5002641c0c52085028040c209900e51010862b174018249100c03020201400c808150141c0d0744000910541184c6101000245858400280c050b070100e00d0682100780500514599501c020f941c414400010b13043d0400520100000503000c501030042c3c0382031031a000c4c010803030649807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513970170 1250 513968920 513968927
    0x90106080c0c072c0108070b03041505090c010e03010e061807170a061518020d090503071218030515091204120507090209060316030e010f060e162001060b0403080a 72
    0x50744c1452504200310042c8128040043c10600300c1e550084015600d503901d280440b0300c0c913000590701c0e81240c00d000905c5044000800e042190a20a031b0b43c1c03415180f0120105030a80c5c440c44807406860b000308001c01c0c120500c3e800c00540b4020404102e84036507a542c0c0d100b81034040e402d10300d412030360401000c4004114040c040d405084403423085a01e0028141a14151700b503040003040385805a00040c00e078200c2e0381d25041128115003203801c1d2515003d80e800d1081e501c40325004c40d5800a6076401d0514510302150b001c0a090720f400000800d494036500086040d051009044c4131024810400450b0a4650000081016002506508080d081640b404a2420b02541c0284201034014007004085407940344c10b881e030000c81011164a00002002d058004120400070ba6503279500380306c0c1170002c1054075005071040351003842d90081590340701400311552054044180c2d000407410491079007640104e012078240d902d044c50000845e240da9000040072507000340e104681e804400700b4101d5041b40c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513971420 1250 513970170 513970229
    0xc270a0608190510020a050904050105060f0732100506100e0f040b040f021803010b01021903050d02040e060f0a081207030323010e09010b090106080c0c07 68
    0x4109800d0001904142800e03072195984880058010540c4030712400f031103c00c005001c0e6100d10a00c0866403400c801000502e20b0307001040e131074011303805d01c800021141040b0003115805660b03000c82a040c2034441d55101010300007842d2101018140e1039140ca1060300c3d0800744001062107400030400c000122156509480d40102040c0c8100129802446d015412440c42c5025001c21101880c1080f81b1600041c01030100c00c0f1040d80040c6002100e41d041070a990007880500c13580c0e1003543d0058600750405007a100c071854007600507000781e101894000c61807440f4410082c4a07003083c40c245441c660009080b40c000782e00400060311000140202402c0072103060b0440c030001e40d040e4240c1c0b820f00a03a280c0d9013031a0398000c0104040040d0ba44c05262003a03104070b2100c0f039894907111203c04078010011060800b80190040c4240c0c24000c125031032014854901c0c40c440180030620302ea0700c1e02c1025145250000c0820080f030304100000b581c84036052002c10003426406000b44011114100c0301d911026 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513972670 1250 513971420 513971431
    0xe060111010c020c010822060e0111030c180a030b13021005070201021f063c0e0c18031501030b1e01090c050c1207170f0901110c27 58
    0x2d24000c48402000e9001c9a09040d50300700b820144402d465040f041183d072a01c1c02001800c9402c98400e03142000b020f07401080200341110003e01500000d0a8244a988402d8400900100c01082001246032076801c0c011020030300241412052a900d84410b400780004841d284503400170f6000381411031801106101d0702000e14a001803d01c909540017075514008a4000b101d458419150010380e40380940140e0044d1098169490a03079264109000001c01c40b102d0412082002d038510644682c41c00311070204039441c203040030000c1d444941e421420f40d44401c500c505145554034180003541ca0070410801405210b2020401c3c80d0b14505002c518420060100d84c44c1040303081c902142e03d40790380c1095041d6108485e0000346000c1c0d0b0001520319100740c045100c664001c0100d0628051890406045002e0003a2540400710701481f0703900049103d002448410755405210540c50340d4441e01c42142120402021141c00184d0b00300040d080d08940b00c0ca14002a0300c3e403076101c000116030f500c403a400c003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513973920 1250 513972670 513972673
    0xb011a0a05030a09021c031713080403030c0201020a0c0e04140102160b1317040f0801021c1e0f0c180806041b151d0a150302160c0e060111 61
    0x118562100801d54403014251041c4a91580c600340d065641d610031840d81c0302e200050100300c520f15032074054104001c240c1040c0320500c501001400061085001441503503202a0342450036045036019501d00c03141ca0001e03411071007001261800296064803407006007000c00f8607a02c86180c24503000e81204860000c0701c00760303401400038049002c2c5074032140c0748065108a40e00301540d540641c1c400222030226000c0d0000c408022001140340d0300f5070081082d141e84070002090705071035891140c240e1059422000c541d049180000b959034409a210301029488001c48500109502c4045000c2d1401708907520310407991440b007202c0c5140c0103e0703810003080202d0302214901e40340000c1542c642d01e0013800508088444a00e5401d407200c3d105040303001c1c01c0100003181e040d07044840f00034803c004403104d070482c0503490048414680303000c05900e003c440040c0b03100400c08080c110220040d40000703074002c0340804482c40210010356090790100181018060302840e0745481000107010505215081145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513975170 1250 513973920 513973927
    0x801110711030c130903030e030f030702070602062a1309150501030b0d030f020a0b01080607080f09060c0c0705130c090b180411160c090509030a1e03090506040b011a 73
    0x1940c1315803041d040c0010f12103d002416034214101030b00a80104d01c10301203207000000e4400001600350001d54041e0712152300721030b9203541700c0d442a42c1e12003090310000003049101d02c4000d140511042951000b024101030181410100c501c40e14a0b8840d54000c0d00c900b0340c03648152008205c002c45048000d1000b40b80c18070a00010b43c0c041560800007200103020000030410300e14213140200000c2221036442280700c0c140b503a5910b60540c4a0784242d5401d400284804003045245011811550051000c28060001c580300d03005c040711160f104c0004c1808074040c40c0c200080c00c1ea5400c420b000c803074117105404140401005402406000346030041800745106000c505883d00c0720310b084981c03641080c0c47c0051500680c0141c8643c1e4000e503010740c2d20b2081424030101c00c1007800c4480030100d44c0380007414440b50b119800003a85038003408114100081003201e43c440b05e0340310075203003108080403802e000901c8206030300d4260038081c0407034040e9415250000108000c070320103c2e142030080300303c2c00201e06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513976420 1250 513975170 513975193
    0xb0a051303090b1602150415030209010527060703030f0507050a09230405130302010e06061818030f190302030c0a0305090106051f120501050d03050a02010204080111071103 76
    0x308282034056222000f0000c40d40501500c10241c1c200201a002040003c10700e40b00003510170310f41d01070701500d480741e00d03400c41c2c03154414080d0013a100d05088c161a42d908248011450340300d14a507468820b80e189080300c030042540e844040040400728041d0b507010039a1041005400b0a407140502140b0800000b003114024140e40b0151400598014068480741d05108111740602c400340190060351041c03501003403040d0200d080c0d09401c152303840f9400038400d20f240668002e803a150115081500081c400703d9031001016207403090340c1e0041104c00844407142803582403918503041903032070780000c000008009101c40c1031015100c1005103145019451132400803046071035809119024000d16480b500460381442c020b400150107040084c00c50403c50035216940a0401070248808010030150002d2645804442c0200c5040e103201038070142c80d5aa2310f64080703450350303c241c840c201155400c3c040451000e600717018500742458901d100079220110390410000800f48000800d2081d07005110101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513977670 1250 513976420 513976427
    0x606120106050a111902031009020913020d0c03030c020a0e010b0d0c051204030306051203030907211a16030b03070303030c0302040914090708060118270b0a051303 72
    0x50540740c0901e0000d032252289481a100c0141c3d4180b0b004150055190040540303800f0900f0200050084046030b071004480d003000c07400c507a80103101070342105100e8000748400d55038102c114a03191000e88903030b0300404642c072003481060403900100c0014003190840700035480c096445e05d000d001040307841c00d01d44d45404c0c503690091080e100754090a648545c5c002c0c0030345e4024001c4e50440341000d41f11401e03c0c506407400800429550007500d01c51980300e80c030b1326001800017060b20f1081d803202d00200195428601002d40e1111010b8a80c40200801d107801d2001444c40e4003088102d45200248580c48d061000c022001d0b440f034840c0150402d45410f02400c0156400174407601100d4140c240051601c0300035400320041e12031908140020347c1050002c0301e00c600304100040c800c41c0b11038242c1d50129110001d00380c0f600310a2040915442c40c0300100080d05816074054880074619812618840500c0d40c00e540c60f1982c6080309440304980c1e0360030403d103c0d0460280b1a4000884001e0172038041040e84c024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513978920 1250 513977670 513977707
    0x11030a0f0e0f1801150302040303090905060a0b0706050601201c02030f0c0a11040e03040b0d18110405091606050304140703080c0106091512050c090a0c03050606 71
    0x10010442881c103a900161266a0115802800a4003209030091540c00700303494a002032040b0140030704400100d5460600c01c0c82502c05032503140d510441c603240390010f4440540005050264011614000045c0c0c1c84101d80041500ca80300e261f000c986440c1c03410024000d41d5141482c2c41a00041308280c83d42c0101c0400c42041e8006a541d140b002222001402c07461401070030f2458444e0b050018000340d0741d99000881d14080b070311031850f001641600c48244425a44c03d441c0ba101f1070f86c020b001c24840d036140700c03000e40119542d0080000f00d05c124200328401c00c490494040d51a00c11150040c551030603d0300489a01c031070304034001d0542c42000d115103400e40607544220010020080080350400c002d50f20303190030410540044820150f00c9040801d40d5600401c0ca40d01190f1a01d000024180018003030003105c1580b040003900304924000d0700201c0310706e50340b500b1101400b0b0324080f4095607403403101483c0174070402500091540d40441e030107002c40707002401c03c0d8892602405202003c00700b80301039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513980170 1250 513978920 513978947
    0x8031209151005121203072a031707050d020301060531061b0203060c130906060206040809240408010b09013c180b01030b0d06051005041a0111030a 65
    0x115403080d00081600b40301c0d07102015003400300b002051124030b40d03101602c0700c2040503080e48008c0400700c83c00341c0c0e8002c44003402e009000c55580b180d500703108400424016441442401c24a1030300d050440c004080741e000341c000601144011070f0b81914a903491603168030682e000805e074028140c0c0b8919004205c0c1c118411030301005045007491002d81304006440c0d8030366a01030103e501a0070f1000307402e1102d0300406046641d010101500040750035450243c1e4007100d01540140c00c980d115602e91031071640c494400c0f1070b0409004440b00d420b90014000c070526100c0400034590326981031208403420f444442c0d0580e803180c040c1000601480304094080e0012445a046184103481c8103e4105c01581512080c0654580c0300013001605203610031304400110b414000420910188100540403104209140c5403c210402c0c441c00003c3d0181e400181c12039001a10520b03495511400135081d9013010034002c89503c02003442003402d580000c0d1454001c0d0100000d541400c5c000040104000500c0c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513981420 1250 513980170 513980179
    0x2030709020f040b0c010c08070504030f1e080c1e031c0510080a03020318010c0b18421308280201050f2a0c010608031209151005 57
    0x44602c00c0e80c8215003202c00400309000c100b41c54440440c0c0341c0d4024100b2075071000114071070000050502d4800e41c03c64085e00e6102c4604462101c41d80c4448085c0f810f0b614074124041d10703070102000414000c030050022008814014003180034402884201200d031807588500300c1c0c0c414001200301c800c001e03046041d00351a509002480e81ea070300003480f1010390540e00c801e40324020880588280340e404001480c16450b030b02840d155524443e4011502e00c1c4000303001521280054000c1011491f603007900d04c40381c0305003400f102c0d002125441040015500e0300c03030054540c500c00c08034141941d01100104086014400c03605d00c90b14124440c00170880c01250010b002034000501640c40b040d0554051411030030140500350a10340c603040281c020007051b00c05084640500e0005446440310307a030340c0c45010b465500200c01c554080c0200490a40283e8038a00c555500c5140215005000b00003500005010941074007140c20103003c0c0a0801e044509081c0e80d082c002c01c2007052000614220740200d441c141d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513982670 1250 513981420 513981427
    0x313021002012f04030f050303040c0503030f07080d1410030b0a0209030303011503060305150f0f04120302090a080307050d091415070516140109091401060311070803070f1101090203070902 83
    0x310204818844c68000800d0840895000e0003031101c000f003d507100e6031181602c3d000641c3c0b640c007090303980d0040c011599000241040140e00080049000c4c1451446600c0c006c0b6044070b40640221a0000413580301c40e925080c07190800070700c1581c8511b181c008034003040451500c035000d4086030302e0f884140210354140000c0c3e81024603841c03182c1e10017402141c01c203041d00c0c0d1008a0148100da5078005540c41c90842103018041000d1240350807890303002e1503000c440c1ca52070340082e071002d40103501721891a9070b20003582240010b4410050005105c200e2081d0b02904030700107502c7c40500440087d8201131000c0c11303c900da0404648540c040d0784c6007403140c80d00c040d44401e021316000e0b240903a07610f00c00b41e070410104000104006000d0842d14200310988540c108142ca0304643e200301c5902403080240e0601c000010084076019500c5501810b82d0600014501140c5031912081c2d0b9000f40c03202c0000a0104c0c841c001181e6200300c841081d02c940030005d0180809030340020350b4501950082d600282d5000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513983920 1250 513982670 513982751
    0x90d030b0117010605160512031006020c10080603031201030506061009120b10051e100e011d010c051504050715021c05090301090305180f030709020a050f031302100201 74
    0x51103104c0d0080e030f0041c11238110782a6401d0f02c0e1695002a50700c1c0000601d565004a507070350001c03031011540d200103408000501d694030317000c40d9440f070040d11003901804100003038484c0c5280b42c01d4582c065805240200104d003410010301c403400880d1040e03401041851390052100c00c21030412020041c1c0c0041d03001195440f815100002d1807082d610081d8048003003844180720020b50046203000e00d04c22200c4017520341c4040c500f40c401c2d0b480351170328900040380040c1100c001d0300744404601596030306161010381d903c01035640d1458091002c59a502c0c1c0a000410041002010040b50024102e011040c05403551050310280d69032190078081c0301900b5201141d454014031a00607140240c0c001402406852502d043c0035240b5480f62040108800c0c08984001c52800c00e40036451640034082c00410301c031440c0c21a024001d400c41090a000c11804000140050944002a60055440c42d45030115039036288100070001c40803504910039179050014918240b66041016400300d004c4501404c03401108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513985170 1250 513983920 513983947
    0x140303070203070b042d02090f060d060f0608150109060f14060c010b150714010c05070b091609050105010e04050f061009150519090f03060221090d030b0117010605 72
    0xa899440b520344c806c0c2008962032240355011203030362500940707002e41e41c4c1d11800c208403410345003154106c1d0441d02c9507990b0400108241d021081d2030002340000140c082d1502d0017142041c82001c1010301d4030401c500103219030466803284400500c03441803911119441c00c6800d01e1076254030441d00f1721500c00403803506180c14081d00000000a0000d1110750a00c400c03000b90070190308030602c155400840c07400300e02d2420b0341c144100301d4400c00c5c0f62285401c103404c0d5030f1070140c0c119005040c0c0200b80910310350b40c100910031501c80009800c5d1100041215030600000425118140c3c0700180301d103081071301b0310400d03802c0c404200e60440d4080d10704c050412294981596092119803001c0c0258070199a1840141d5100c4058880064540c4009102c4481003804071408100d90245a10304e01e0b03007080800003d0a20360003425682941181d184401004005070788600c001266084cc0c0da4000a003183c0c001d66061184c0905d007a8242071a46501c01e5412000381e51440c1409801d080c058000741c03968400c0c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513986420 1250 513985170 513985193
    0x120209040c0818010b090604020307120501080a03030e0a0f081e0d050405010b2d0d1a090606061303060c020102190309030905060c1b0a050a080703140303070203070b04 74
    0x40140c414062002610750081c400b200494812016031a20100503050b0f800c18051405000402081c40d2895121368042000940c800381585007440034600130046d6801d10740c01550f000307002d074001038241316aa82c10060160317130002c1c402d440f458112a50540c0010b0325101140070b0b154025103099110b01280d44203041040c50b00e000043e080307a001c901c4c40c00303050450308140d1149100724003d2180300c90000602040d01d085051034246e41000070386210040e045030b03018680c03c0c44c0052003554081000c1d100e00e0f05c150100803464400052100401294031401c2040c2c07030f0000340a0f00c4041c50103006004c000c1640c8160701004110b41c3d01c0c1c901302100c591007501a954076003401e0320a0000c080c20240302500500e203412046003c40d651440c0058249001402e85401d026444080e0000c84001c0341d031250300700c041d07112050748040740040c0410340781c079407103003050141c00c01000070103c50b400c41c245840084036000c0b14681d90340c0204200024a42d020007a40c125a9000040308015100c0389400da4082a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513987670 1250 513986420 513986437
    0x180e03090d060207060e0c03030f030a06030803090102070b180309010305131b09050609040f02041d100e0f0703020d151107080307030f0c09270c090611010504121202 73
    0x72845810712050003003d6000b44404c91084034100b0030a5190780040f0740381c5440c400d1469041c2c01c10310904500d084250000d6500500070b984c005603c84e200d5460358001d400603a0003111980d400700e18842003284100c000c03074008076031a51000c0940380c8a9180c503900c0c0300b0740c044603041680303540c08202c0101c01005281445030340101d10283c0712102040380d0035a1011441195101401e02e0081003440c2840e004190269801c010040703a03106a5409010260010310300c08030043d00c2d072141c410310030a0144035100882c110108041111158502c2191904642800b0001a0b400c1140d0810060380d50030040d001d25584904244110948481444010308442ea10222103171400142102044401c40c000c600c104259101009100074012054046442c07030000000403800c101c00500c14591959487d000300d1104aa8825203c4444001d08050b5100140d03100042440000248115608126002c1141045070b00811107845c0c15125440041c640c8001c0c10705104005141804000c4181c04982c200c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513988920 1250 513987670 513987679
    0x271f021501060c05061f0504050c09152d0a08220302010204090518280f110a05031c03021605160306230402060901020313030803041209180e0309 64
    0x1076941d62806441d642da10301044800d0b015410005078040c070080c090289100c1c00364244035a4a0402c010303c0010a809000306251100512402c00a03940c1e001d030018002040900c090381319800f1340e84a103821144800546841c142e000d507000701503409071080e180b080e1414038140c0d900391210f000d00d1015402e03800100d0181a1900e043c4014190150014011121030010800c02565580d00b4605075040c046035011083d08009100c15910042c0e856941c00c4261402c96407170041a00d645100d400f042107a000c94a280207800c0321562403809010b100028001035010380401c2c41110b0600b1440c0c0c0c5101c40c45001e050340070400ac03140001c2540400300096101e002c5802d650b159078200036003640a8070040345c8050070101c607000500034411140b480d26240b45014003c585460b800c1040036004804440c1c110300c02030006651441200742e9010017903000749906e603640d0a0608200d10041c41701c800307460601a054000b04040410614445225030703c48800080103103402c0300700790844c410083e149920 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513990170 1250 513988920 513988963
    0x1c0e030c030301030c09020301140d031803140f150f070504090603050c0f06191b06020406080906090a0b0612120a0504090608070e190906020a05271f02 67
    0x245040000214144ca00810205150f1551a42000268402401400302c2d050603505c0081141c14107001d8030f1521446403d04148603604111613941492443e403056500c511510120040070b1814003810215000e04809001c5a0f001070182d100c06010144c040d101144208001880d217612171015039001d4054039006120190756818410f640d0305a198500c3c0c403690b4250007502e030f0780c03800c0000c68000c0e480c681c070840400c00741c803c6d060320700c022040381c0c040d08034206000050000310030b40b000f48041c0145442d00e0045041ca02403861a0070001000703400c090340207804407804103c0409003140d009404588a44e06000301040d5641443e03040c00b86494201d4020030001c1c103c40d04400644252071081d034040280564940b2915540d002500c15607000d10314410201d030722542e000100a21420441502054003045a614076080b42d202900707081c009640450386100801500b1390483c11f01c08040721484071042118006158001e4030306498002400003080009000d00922000b810418141038aa80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513991420 1250 513990170 513990187
    0x8060709030f0f0516050102010b2d0406090e0f061b1e0706060609062705010509010c05161a030f0106050901090302090103051e0319120f0911040605151c0e03 70
    0x44040d05d80c0100303070155080041d415600e090541c80c41c80180c00750100c09a400304607511000700c0841000b403058019481c2c40c0c0205400c0307058018601200c0500000741134801c080483c890510300c010b014204400702210b04004502e415009a4031001410100e00801900c121030248547c451250014221818998001109a0462840c001301c60f142d44900b00b103640c07030100c10740700c4410301c0c8051802c000344108144041e500c284041d102d500d2060509140b80d070000d1319918070f4207490400e400d00c07a881507417003480034106d0940190b1240c4200e00241e401c41c202038100000c141c41c14000c10080044c00301b00c2008580c441d420f040000c40e00640402c2c21540c40342000340e15803484100b510300c00600c0300c1e42c1c07a440c064000202e070f51802c0758440001121014400882c1d200580c030420843d03031500c80d008500c0b8200e141c45903c2c2a18800c03aa10400c1e002c40f80140301c02d80d81d03607501031031050210140101481c0740120132125103000a50700b4070555184400c9410003014100800402d52102054054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513992670 1250 513991420 513991453
    0x90806130b10180603020a151b0c0b12060a2c0a0b0409030522081b060d062c011d0c070b0916080d05040510030b12010209010908060709030f0f05 64
    0x19031b80242c1d918a0015210520f0000950a0031401c6000034540f455403180061481e07070b1081c1c0c41e44501c00b04503002e6501d0340c40100316001852958580003048040c0140340c6400b20300a402440000d810000040c001202c1f00c0314415065110601040c41782c00080d035000e4960300c560204c1e80001c008003c2203865080040c03a0350041c0da4014a20508164502541401c41e4102002c450440c00100240c00201a80e06502c110300c0703021030b030403102c107101f08140410f407402410050840030071019040100840b0441078400c0c00603903010400c848800600c0410480902c000d04c8500c0004000b0342c0752911000b01516104101001d004801410181f00c0d00e03000106404001c034111196219001d51608074213074940c024114000e010410422080101e420800c041003520705e0f1500f0000761040721800401d4613400502214074080c0d500081c0c124080d0380110b051000b83c5441c0b0002d110615040d81c01400420301400040c0503032141c4400981044001c81904203941d81c03042c261618803c00c0b81c80031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513993920 1250 513992670 513992681
    0x21005090301111b010f020c03042105010c0f1806080a0213030209010b04060801090e0607080a0b041a040f050123060c01150f060f081614070f03090806130b1018 71
    0x74001e6508008003843e1b20041d50007030b030b0000b4a00742c000d103103814075090810038a82c0029000000080344001e102022400138444c8405814590b101c844507840b905800602d03c2070507102d441412081c8030401d2003815808943c1300d91002e8a40300c0140c3c0c80003009040d18042e5050350000358440d440c04008a10ba036603c00c0500200e6481391200c00c1c42d030362a82421410f40740c000342e50707612580c0044009941d4910640c0029044500c03d1000240f05945d003000c14180c1e030004030300028581c9020102181b030f00340740c41442c0c03d01c0c841c0441004954148401c0640034044010050072519070082285076543e20031084405019200008020400518400001d0320032148560500ca42540b075000448038001c452154440c201d55445516564030724103208651001d0103500000c0251440d0204000641c0c86c0040149a0042d03c0e50046a01507240046c9000070799007100100da00324405000503107003a060345003042e590000d602251a0b50344408100c00038056440501c03c544a522030900c010101d0740305 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513995170 1250 513993920 513993967
    0x506011b0c092d09080c010c17060d0b01054605150d0509030f0a03090209130507060507031719050601180b0d0b100203040e011202100509030111 64
    0xd10032481001c40c0561000070442060740060718440c0c10414083e0280d105552040c401c42c0014200700140c00024212040d0345503800215162804041815502045056101d01c007140d510075420200d5880012031714040c8225030060403c1005440050b25010754602c001e03100320320900202e180d00c4050300d401410009a100500305d01e40c0081a5802d1480070340000300400620145480e02e00d802500080000808216850009000107000701510800402c940140703a540440d030424140100168000090808021620703805440b01c0012030104403101241c10303e06009889059508099030b011180c1030062007503511080070040e058003180003220f408141c400c4104241c2d50360800664240d5112a0100c400c03582c540b408114181c0c40c00004d09544903180720100d900a10721010070b5140b45036402030300140c5c1010a09000d0308140c1c1a0f00c60040c03e05081c2403000045a401107032860541340820000c004000540a4054800b5000f0515440301e84c0b02280e80e0780310b40c05d0441035160020300c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513996420 1250 513995170 513995189
    0x5100c0204020f071a090102070c051002010b030706020106030218070c031409030a0b16020c010801091505040203070302120708041e02120a06290307090203061c050c011e0e040506011b0c 82
    0x12991b224414400d035140150700422480d001e500309420041240341105403041150340360000150191001c0c000c00b0000c01e125000881c5050075803040191200c1c10102d50b00400031030204002400c1d51081000120303540500300351181f0740300107010010b98411014855058072036401c1c0401002840d0180718403c50303095980d80c0541d08000401c0342c86402030301030140001c44100052180200950100028a003031687c2a44a180e80b0404175050340c00444950011903404a00401c041e1818182c8550000d00ca1400d0340540c40c0030741e07821041030003d1892155000c0c0c480c4060f002c64441c5840c5410702c0741c2c032030200d13034005a030780c9464009882c01c00c100c0400308040640e0030160509205c0703c0c80744610002d02a2094500303100801d4005d400080a05030f0202000c034a1401145c0c2a1400c01451740c05038014000d40140103001420203030500c24020b4500843c0c440d545402030f4020f68a50030403100321008100b607250200101c680010f403a040b0384070000e07074414040410600000c1001155440341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513997670 1250 513996420 513996473
    0x8180106260a11060306030109060f09020102150903030c030402120a0f05010605040b0603190b060a02030904060b09180403140f030a0b010516030e030a06020d05090105010f05100c0204020f07 84
    0x4181e15212a001c40c0e00920042090030f200f259407400d075028560100000e400011030104035199803099400e04c05500c8001559020518155641800640c11201d011100002d650402004042d52880001e18100b4448800320108045513641401903c0c1100200d040340e1800c44503040070408800801030480d21580327021000195804d060203000c102c103030010f03e04c90840c0c0c0c07034103680c2592000046440c01c540e40e0f2100d000010b07590741b001400e1241229401940c440007400305200460318150070090b800301c0c09119008855895443c030500900c075600da03142407500c4500c0c0603540b80c0307510070b03210f0b0f02c89238041030082ca034101c02c101540c840c82b99620b00340800c6007040015150351140030f00c600c140e82c1d0546000b001080c002c8003200d2100001508a9200c61099200c0a089030806010200300603102c00c02d108041000340600c60240048071480b95565103044006003a030648940b0714014031102c06a2107040d03660381e905485004461401841d0b940185140c41034002120118014400c00b190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513998920 1250 513997670 513997739
    0x1104020d0c090905061003050405101b080124110a0c0b1e0304030c02061809010b0307081506041512060902030405240a0e0307060f0608210a08180106 66
    0x50050500810010b45640c0e4800c91020f070403406090000d00944051007a01514074052f201846060900c0c2c1a00760f0407884250340702001440800103a204040e07004a80e041d003101e2021205880c0a020000c2c10312040a00014064a0905000700e40103010210520f40c001055038071103005001c003078000d0340608030f0048925210100da00060310003500140000701d2510050a1841c028107031034202024540100b18032800050b08903409030000c45c4507040100901000a410496154000c084200491f030480c0b00f100c08204203005074891610300888920040c03030000d01400d5000e81940e071400081c4076403a2a40b005601039441902c0840e03403071003900012803818500c4100d50784204c0b000300c1c0210182e10384c0305009025180c0c400d0902c029000c10040c0e000003402c00e03c22189401503018000c90510700d00302c121403c21506417070582d0041100e001151165181404460030085181040b1700303540c44003000e4000d995000007100c1c00662130312001017050100c1003480c01085101e00003600240501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514000170 1250 513998920 513998939
    0x1e16051002042d031704080a050d030b010309020f090a0609110a11030406050712051903090501060803090d0602160503070303060e250c14010c0801050f091e041104020d0c09 76
    0x1400821400620f900001d00001c0e40003d16074010301e04200001d400d041c0c8801c0018182001d07000e0895980d0b211079050600c15405000e1342004100034281046070081d540c0108075a11a0810814030800803030000500c6041c082d40984042c2410341810045d8461141c45816981e000145a501181011040078103200002080b175060703030b41990314076041c151560303241c1d0b0f450300040c80a2018800c0c01d000d0072907070b5080c20350000191a081e950101c0d1400c018180745003100c04507040320159410404c102c8804e0b498103903d990451350f00c104016580d0034211410406004803400043c983d0100041e8030051541c19081242501e1009040394900d07200c803040b00c1201c0501c182940600d2644130100e11840340074040306200f4034007600291100c180d41d000310f1400c66900300400000b01d4035580040c49a81005007510082c288290745268682c01d02011340210b00e0104c406c4292906856400181000f583c0043d194100c54054410b648480d40400440c01a145101c81035001400810001505049 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514001420 1250 514000170 514000229
    0x106030803060a0905070c0305070804050d061b0504080a030e04090b0916080c130f0902060c07090e030711150d14070305060102070b0a0302160f0b040312021e1605100204 75
    0x1021f44a0031048812a40e0644030b41d0000745083d5515142400000b5081e245d2400051099201b16400138602862041548600500c3c031143c4c420014203100078401d2242c00038050100030b80504080105204010004000d00048000104410704080c14408240e00016086402e80000910000d401e6121044640d8a1500a8511354050203100d49401070089a5100003400000c1010100303040304c4070340225666070300038804e00d400703039100c15020410032103184141841e081101000c1d610f05103e546825541b020803044c42840303040752144a41c0381c860b0820494210414400084c4481407407841104403107c000c9440c1d4011034102400150035601c00b0130024151241704210504101c0c16603001c5000350046103000c41809c3c644a071a0011900d26812525050711501ca06c80b5503140c2172600401c03601c0949480c00e00907005000d0548101e9610303c0f5180e0b44200d9504680e00e0303892042c0ca0180070350314000050312501800a904903500c0d1a1340050098509005884001031903000c0058613188 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514002670 1250 514001420 514001431
    0x1504030f0216122a05031218040e0f010e03030f090d0c061a0315070f09030f0201080a09200901060906080a020a021c08041104050712050405030c0106030803060a0905 73
    0x401c4240911040d141070f5200d505141c02541c08003c0c004101d0300190310300e1052410300f821521044000c0125140c2041300004000c494417005003002d504207445082030400e4903865204648540c0310580c00031040140c444959600e10007400004a0501120f0310b90b40f040d114070440410200004100c00c800003500b0350041c210703075503d000d092116111800140783c58102d03810078845180d040306041d6405c04c03200f001071704a0741c80203c443c2030a0030042c045088841c00c02060002d210001c102050310221b1039103000380c081c2407400980da0341070580401000d502a00614003000e181c589041e07103580800d060291681680d0410050344c031640161503400c1030307200e50b60004110100180b01c0d01501d801501c25140207004031542845004804030031985a440d01c80c00046182042000340301c519002d1000c006e41c140c508103c00c0c00e1001006000301e1142000700409070b142d10100341002030410451350f2100950008204003500ca00e8900880d03402681d85074442d01d42010003140c60341c003074400d1038000c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514003920 1250 514002670 514002703
    0x14010303050711041104061d0d0507140a12150b030318040b1206040503131509090c140a0e030c0f0306130602071209180c0219050c031504030f02 64
    0x7140c1c2c68800f0480c10020054000e512580c0381502000c4840141018002d19203c801105018803400c21140c140d400084e0b1050940c40c10180120b0b1010901d501035130350703550744400c20815060100b01d4215590b404440c0318070461b005001849503110722410001c1c5000d805111618050041590700d000d51800d420003030032030410481c0c4900e4103505c410003120015004110010041d604c1ca42030a104071026140e0780c01c00160b640c2c15429000c00304026041820042d0070701c0030740040040c800b007001e00a0a191950f66243d443c3c819000358500410645411041540c9454901000700070358903183d0401e0003032140c94401481860013a107030080101c00500100f0841d500c2d142c07480c1d090001d02200fa80c0c00750b0b08008203808a490008207611742600b548642e80e805140c5043c400c64920003100d400b0005180135040840c5c81c0d0b01041d0b090f20310160301e042e0114156103041a5040a03a8007825503414841d0014484201401e1300c0c405126902a4450303a0103421038103401ea031100749003503440490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514005170 1250 514003920 514003927
    0x308040311091005040e0111030f04172b150602160b0c0c0d0213061d060102010e1209131e0e0321070e18060405010906060e0609041e06091401030305 66
    0x150130705d5400128142c090b00008075411400c82c0c1044903c1d4016580c5905603120242000240000c00b80c0481d40840d02704200d030b10340401118052a80c1c1965056058181d40c07409210004071050303000840703455588039003412282d50744ca4011355503925003039012003880507030000081e00e42180000d45000740d00210150903140c411b242044802e013807180c0200d80c80380c0c5c201a0961818114480c18001e0000c0580d20f9a00c01103c0194017070440005003035604580c142110001d54000110380f0700304d4101008402034491040d02c0002e92900704c0700c3d8105a41d1860f2805d24844103404100c10020564801000c10140c040007158a46900c00c040840740c0c031482004009128000320001da543c040e59a26281004507000000181400b010a180b2084083c1140c1803101c149007611900f401000005030030064540b0b0080060a02e0701414681807007628040380300c51040c0ca0302d030010340404202c0c403080000803410b0b403c03110040426002d00c032461890b2010840716490100803182c10380e60107031900c80c203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514006420 1250 514005170 514005179
    0x20315010609090b0d060b01050f030f0f0f04021c261314010c110607060204030b04210906050c0304030c0b03041e2003010b090109020a0e0a030b040201081f03080403110910 76
    0xa000c4c904842c7e41084001c0016604008203100910b0003441e12060002031030500d810b1117145c0c0e0b100071307140d410444969000c0c4001683c3d0020400043d8094800401c071201c0d5500b006845030691003010041c8440c402c00c0c04080002810007401640300c6031010811050300c901186000706100040305003c51118180f02e0041541c0c00241c9565101c001c1c609071400e03142d07540d001c061f030f002507000f01d500884d142c0c20f000170000098101c014242e84406400c100c61000c50b401055041c00d8480e804c18803500154110601d4010700446000e580c0100d0341c001090355a00d2903140c0c41c0e00440381505c3c540d45030509546052401c0d4816007049030455001c084500e02c1d210b0300303000c400400e10075540c03565840b8041588d0f03490310040070340202001d45005845d40a482c10240a0106191800740304444100c8240700045055a2940c0c01039020702c0c115209a44a1003000d00c0ca0164000761f08a07003003032020000410192400a02c1aa0700c03803840c000800c9000004e01401d003c05071007030350036000c45240510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514007670 1250 514006420 514006433
    0x130305030f0907030f060b0f0909060c090f09180d090b0d0f09140607120603150527070f0801021e0d180605011401020a210c020315010609090b0d 64
    0x16004040e000680b10559641c5c0c0d07904401d2510180b044074460307203c001c0e0210514103022424003002003a2198490b52410100c1c00b501e40200601c42074108402082d000e4850300c4100003014582c0f405410300c001c60030040210000700a85085c005080e1043c254410802417050f04910100c070055000786007020b0312311a0020140001260081030169a03c0b041c10102e555600d001c40d0b80c4010318040e000d142091600140900006d918210315a4100300003040003e1301e44007140c10800041d103000803580c5418522410401c072140c8540f800b00030105104d141414049418000c0f5090045451070240da180010390a0b40a84200510000901d02000c103417041004010284c0c0c410303101000604c284c07030240d83e000d00c110040080d1400e50b07840c0010320141071070000823203103094240000c000c000a1503079550090144528082c1c2e13900d016520b000c05840c0a40d0003001e8080c2d0050958911003114581c000401c1c034240304003800621000400503480047d8400e002010b400030704207804124841d00c1e00d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514008920 1250 514007670 514007701
    0x7240605190501031d2514030705100c150b040c0306032a1d06040c020102040305060c0d061203020102070203010f060f03230303090708010c020c090f090a08130305010513030503 78
    0x4030000402d00003613a417852010b0200c103507040c400b1070380300d00403219503030783e200481000c4d4025041c81000000b01d641d09607800907464048030003c481003211480c1d000c0d421507900d69000700003041f4101c060206020213420350051400c082c02581d04101d8180d505408905942c000c2c40094072004090058011031188d09402d0028038001080c12101c0564070b81007810340490b000002e03a90102c0366010701c54940b426028000d514801e5100a41c14181075440c2c00d511640081e008001074000050200d20460b00741c0c201030004c103a2003a601140700c0310307410044c2c01303580801000c9110354605041100d000c0854030454040c0c40c4041c1380b200c081421556200040482c001515500782d80f138118045c1c0000c010002540b20791180c0000d0b1580714900351185d030941e44110245e0065400040c00c00744551940c01689034801c0724809003809984610505034241560f400014065480c0000c1d4207c090704131903030b017800b160b11450003013185507510030440038085d000e240010b00242080003c141a00900e036041c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514010170 1250 514008920 514008941
    0x6071104020a112508030a050906030a0b0301020304060218031b040c030f0c0c020307140904110f0433030b150a080d030c08060913020103050c0724060519050103 71
    0xc00c200034141c0d02001e14050407034903c1007200f09208005980b0844d0806442e000b00b1808008508000e4030280151050040c1017100d0b02562000c400240c55600540090017641e101400865982c20310f424000007950255121078660410004542c280d4100091081c25861408824a1180610004000140100c000780c901019107602d140c4240804034859001100c00031341700c0800e0105940b06040c00c24803141c0c03005802c002e2010b80b80840d601d40c903580a52040d4400000c074006409100015911007107480c005401a1414440940c40a9a002d83c01000f4941c03070611100c0030151000d0185e42030039800024071103520034000c06c016843d007440800071480010711060126840d06180d9140c480d0f08241400000d03140c800380049283c1005000c2d421070010340f05501203190141c2d0354121117005000c028100b50356100011a131090200c1904c0d0090b500c02c4011842019861a801403540a8644101324514000f4009210b14060005480c80609040007070340c42454403006400a0808196 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514011420 1250 514010170 514010177
    0x204230307061209080c0703030e0a060c080304230604061503050703061d120a08150d030f1e05070209010906120b061305041a010f05031e011d0a0b0606071104020a 72
    0x10001c0064a0000601030006c02100207200051840c140108a609094082c0d400b80000d0750040c0303c0543e0205a00b0707074480e0491402503481e140c070714021003040942007411212003000790602c890202c001c11000e0095000d16000d215081c0c90081707014000f0010310000b483c950003840200009a01d076048100b0403800544140a41c00d5100d003172380d013411103541c041014448009041d0440540090310a6003048038122011b19868904010403820031082d54060203000d09641c04810052107200c00000100c042e0704040e4495000c00380c0074145402c0408101e1181c500c500c004a00703801644503070011281050102d00d1031215540f82c0f03c3c42e14101030b01844d0000000017103442e00c0e04403401002d010318411148280070300350511044810720010780010a400d01c01020030441a07900086000c6800032505060340816a49055180100352414800340c03455420288440181008125480c0090044001d25079594070501040b0140c03203401001005400030071540801ca04182d409419103201d00d08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514012670 1250 514011420 514011431
    0x41202150c0d05043809010b100e0301200c07081504020613080105010e0405010b1e04020d060f170d0203030103050d080601030f052a03090628090602042303070612 72
    0x84900b10100c298170b400c40c8158400540d685031801c2110003d0340016400c4c002c04c00f46480d080041c02d0740111184117070402c040b200c1d240c03180f99429485002840c0c040144410380018098007401c8a8000010356202c40c022070a0002e00b9240208448a0801308880d10f00607554031942000340030b41041204841c5100a180040740d03140c000d00c16030740a8208031012481614180c0b03005400e40300940300c0c0c03501900003a481c40750000182c0809924990b4111405a1109400c030b000c0001000b03036a0041080038121480041e01075603903080c007030000c416001514820703000200305995a00c03003880000d00c5644a1620701307640074480c03421660001030524010580d084101c582c00e042d20700c10748140400c02201c0c08104088441041038605441d56402c1113400c1d4035202d000c0d16121700c4000c0042041d00a40d132078500317030640c02250402d034002c070580d020007800c007480c00c0000c0250058000c542164188000350260068000e0b0300d49039084000f401810040d0900004480d85102e858041c9030f060740300c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514013920 1250 514012670 514012703
    0x7110304140a060203070b0117010f09060203090106081c12020c010906060e062b020d051227060316020f0d020102090405070507050a1e0b041202150c0d0504 69
    0x92004000078505103102a051226101c00c2103030120072684000255030082041c6400500406142c5044034a0071540c625942c17040444103000d022900c0f440780800e858a4001c0041100c15405140654443c9008108181c1c940f0056a920080c52410308141c440701100c070f0360000d10480f5088203480f00601c0140c28013210410031829900403044c00c0f10100e4a8110034440c0c04006c180c0c00e03900180c100e03a1018080218100e00049030000e40c410051034010075a9007081d0b4489841e04280b242d03104040750040c40d01010355903410f82008181803c13180e10250300b50306002920348070170b9007144d00500306451074a5036100b00c05150386000c03060301580100071003264007107070511120072800607940016a503010f5150400c8206c0c4e000800e81018804240001390100700c0004440082c035510100829510301180a02101c0300540c83c4010844098a000c10080024042d03148040301c17080c0d001c0b12108100000010503040081720f4440002c081441003000350082d80d00805e0708240210390352180c00940303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514015170 1250 514013920 514013923
    0x50603070e190c08071101020a1407080f04170601060206071b030e0a0b1b1603120203070b0a0c0305090c010e0d0c08011109030d0302270105130324020c0d05030711 72
    0x84074002c00896501400c02805c41d40100030b003070480a401c0f000310300e0304025201c081d14a0359184911b51440b04040ba1402c2003107030350421641e50821000c9000d4445542e0b840c0e010f50511036010f5182c190095100004038540001203050068105440e040da0b14260014a0b2210800c0110203408004041440d42207948445a4240c0903016180c66a560303541d8a800703181030310320070680146c220380c04070b0340a56010140384030b0717201940e5011040d81420807282c00e00f00c1c40c0d4011544054424010101444645040b030303482134091001c542c030203000301d69900040c0790721100c12100103404182e800d041c0002c0c1d86803080c4480720700b910519940400070348415200382183d1a0300c80405500d40005104481403804203d42074010600786801e52074030307508080041581144002e84108251606044e2000b6800344094580700310405401150b099528106149111030801b10071482120310480c404904401c3c2c000c81d000c1d258202d0061034000d0045008680e03651000b4900b5003049600d0104071a0b4072070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514016420 1250 514015170 514015181
    0x6091909051c0f1d0603090c10080a0e07032a0b040b07021e0d0204020d180c080c090903070b0c160303140c0f0f031e01060908070906150f0e0301230a050603070e19 72
    0x1e5130342e101605131401220305000c4cc0da59550020055010890070000a0003480c081c000c0c07106021242c0d0042040f042e002d0100b80441d410183d006c1c540414041184c41d40c84001c0d05419000b211070f0011014600d40440000740b40a4840381c10030040f418a001505181e0020700084d03100d10000298a038100804c0d071103503100d083d01160700c0380c0c100704c0030040300800b0000e2107185038085800c402d450070710b190566941c0c030806600800000c82040040d10780c1240009407032142000044d00f8241030710500c2d004008112660714805044070346004500840ca0110580c6d172900b0003006501d1810040681c114040d400092050505d1410026141446081813219900a05050300c541d490a4101680a420540c041d0040c04501e4a400c0c0c1c20007442901540d2001392183c242002c90f14402d010728121120300c01c1108103034156090802da0400b04440400300661080081082c840c1620b490400328103460059484581c940c0c0804810300660302c1003880c59400c404400d8404407040c4042c00b4a006030760 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514017670 1250 514016420 514016449
    0xf030b060a0e2d0f0a0b0a030c020703080a02010c12020a0906030902060d110c0111030705070204050402030c031b0418050a02092505040311040506091909051c0f1d0603090c 76
    0x4210240c80c3e22810800c00c0c00c1c48131a000c03521402020b003004c03071000d65030050510303d408141e1190b85070103815009028120186400051403951190348800103400b0b010007a00074000a44c00b100c0001210301e051003901c2d08240c0c41d942c1d100b0854904002203000d4849102d080c0d9000004000010315541c040c450542034001010b85940c84640e0035203554219500386440402070f090800400c0700300341d4854101c2e44040e9040301d001480e6226400801c0c40c1400703d282c0d0f25010300c00c2680c42074084481010308d19018a0840b400c0c420380c2c1e56414080203203403034080300802d507902c803504040c01803030324490540d40513200304401e0076014411031015801024106118000c0f482c00201401404504442d480002030b080d1002e04c083d00700342000c901402d80007000181c0d001298044c0c0003e8000c2e98012010194000089a801c112121f50600e1100355600711040859005800500e20b40e0083c9003100c0d41d0002034582d0804001c640c001e0080d56800208001400d0150300d54220003940d07810582c1035950b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514018920 1250 514017670 514017739
    0x33103020c0102070801090c15050909040b01080c030c090a020f0705160504060506030609061512040b010e1807060507020a0801020c0d0809010908091005070b0c0a0f030b060a0e 78
    0x401e030006410070b8802d4110440c0c03a4140107910003c00d400c84184412510b05001c600c85600b1411001c49582c0503404130a41e10100d48402e0200740084161000d05941d8081d05844a14005000f0180d1700d00d400b15140d5000704036840055800d0300b1550140000c0ca05640b071151a1124036620315041680760400300001d1a03201006010354105031103010050310040e140d2900d1420030900150300c0306001880745200d654098910707403088880600361661642001441c4186003054500f80700c0b039110074058010110b45440010b0f43d1750401c11a140d2045c020f080140480700d051200072607482c0d00c022400c0c3c3c1c02003080300d40010101d80c08d100070302c0d03114090406400010320b02c482c01842d0a40c041c00d40c50260307040072101808509244212050440200c0b4811001140d019050f2514080c0d2070b005000d5911034020000d0b1404250002e1512401b0b90f6108812005200c50a50446412031000794100e00c00744055902c0310700900380442503410041401c0943c943d0b450440030031110003500c80413007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514020170 1250 514018920 514018933
    0x2030a050d090312050301081510180501030501050a090b01090b0d0f140606010203040605090603220803090c190308071406070e0a050d11060d1b050a17070503310302 73
    0x503c2031341c3d6084081c1090a241040c40c551400107415601d5800461680d5440010008a40e4501200328150000c20b421748814151924580e404801040e003440241e515509100001c0c001090343d1203100c401c0c0f64800449070351031742411141d00050040100068101c10070752444008200280c00c0a21701c1d9100785140c0f82c0c0d4489550f002420000003401e400d0541d0b20074081804040e81100c182d03490300c002640c00d10f440b0740e5056400000305804009003882075040800c0e4406010500005501c56440c04080711043c481c3c4100b404560980440403925180760440f00340f00244801c4002c003400c500610b0050100e40600640d02d0500e641a48c201c00032605030244803c4d81d0401c40000c3e0010310044074030f42d9426690b07840d0360360901c00c040c1344584951700000e030805d0051450340c0900d00002000c10b030401031040344200030340590311106400e40440c030030400d400380f250031124590b8880c600710355443d401c2d500d0700d25032081d0a50341102d2840c10802c81078080030541e0003001d000394006000e42e004146 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514021420 1250 514020170 514020173
    0x2030105040c0816030b011e03060c051e09031011071421030c0307050c0304030f150b0609030a1202151302090115020a03050a0302070206180922080702030a050d0903 73
    0x90800f5404030480c40320450413003000402c007038104513811107076a44901031301c003010100801c0403020aa00300074009071901142c0d2040c1a8010003903c495030b200e0242411800b244640c0b1102c82c01450035459060380008080c0d1400300c62504052081144650b502d4180209517480301c1c50305000d40244c1e00366900a40c05025007090141710b07405100324030700d1098130b1410000f140c0c01c4584030040c40032040c080c001071245c00164080007124002c5800c080100390410f92850910b25242e122140c0e4140c040c00c215120752280b40140c11035034940301c02401010b540a440d554007044039041e40301d000541c040d100742010455403c0c04418882c0c240300d10401c200c400c0030b01c100550b040381a04030038019000c1c06280c501039900010941c4440da0181806c13512810085000c6000c0d100b100703002500001c2c08581c81d915403103842100c2a100004130750072282540c42a0704050b070302d13946401e2040c403c40c0c0c984001010442c000018450140013a06640580c5090380300ca51130714481031000e1b40048c004d84c0e002c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514022670 1250 514021420 514021423
    0x91505150102151e04030e0f040e03030a090303060b0a080a24181104060c0c090c0203070b10050d08070b0108010606090510110601120b0c13031b0302030105040c08 72
    0xa038004111440d11500c540c11000007075485540400c480c11460842000c00c4c1515449100040c10150644481c0c0c440d01e0f15150081c0308008403202c0b580115a020500101494180142200441400011401c41d40d500720018054650308409030280b55983c02c022803283c042d80011300e040c00d001c0c1c5981c0310b04d040000d00041100c0014070610320084141d0040b11004900759007180855106000119885404016020060064075004280b004001400196443e001612030121500568440d01099a01c41c600c005603645d040b00070380180c10810003070380010300703004419400c42c098409249100b178450780407032210800010305958824000c20424200410005002c0c050104080207012140c58598040c0c28203485004142c4104106441481031900c100760703641102503054202c0d034055030b6800c2134049160999609565202d024400108000c650030f0440300c0004e41d02403110310b898950b841d01c000510185500ea80a00c00f00100000965801d025850145014840701001e0904e8415185d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514023920 1250 514022670 514022681
    0x10020714040b06091203160c03120207080705150c060103081c0b0a0b09030a02090c091e0306160203040b0a05040e0a0506010e060307020c060706020c060f01030c270915 74
    0x294072030350424401c2d084607250030050741c0141c0402e6800d00074804405001e203003140104a06600d0b08072003003124000b07100d15101c40e04100c0c1c0c041c00b000c85228403445030880c0c4480c040d00a181c8183d000c540100f0440c02c0400380c3c0f46101d9218210542401280209241003a50a9106075103c80380410480401c96488098078915100f072582005000581804241e05841603c03032044952008501c00d8910340b81400701100f19a80140311014034a408000790000740c1100807180e0159100c40840412811304210119011400070010019940e8019220750b00c82d080e260740f20214002440001104403000d0080d1182e00c2c16038036529205d504102108902810061103200c10307031b0402040c001180d030400704908200005aa22070f83e6555600c00c180e02d000b10a020268020100180e0501404055405403442a00d01000d64080c1c3c0ca4210030146591000c2c0000303046482d121104020484d2905442c5401c40b54203410310240101c402c00b0041165000d0406071084810307c503106440080d00d1154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514025170 1250 514023920 514023959
    0x80601020a030e1309140105010314010b180405031306090503012007060b03070f0603090c050405040308180712260f0f030a110a020304080105010e1b0a0e100207 71
    0x50030314008984005008110103580b081c0100b0100c0312040040e01d0075008072003802e07008046c1c803400190004502c0d000300304c01d00c4103807000360904031042100031060007507900440005010401140c413407180345404103805401123466120812100b0461024038403400003d181075190750045a18203070a140c2540c0c1d400100320386d05e899a80c400c2d4080703200340c0b080d1600650050384c001020300e14640885d29066440d007080c1d03414142c00030001107541c1d00d03800441d003c0e8410701c0c1d900c01548d9a041031100361941501c004000c502540c0009400000e20101c071009054444201d8000a0313454800c1134000a4100003641c52300c0b09110441c0e004242e82454403002d050a9030307034a1820120b108100402c1c011080e01c00e25075400040400e40410464000b041041e00e0140c465a0301e007030380d181c00380d035039442071040da80701e5424400005584000c000c2020304c2502c00e08044400f422020085d030001d42c0c48180d000081c440c0105a0720500d81380c001e01c000e00404a038000b45440c40c02c0510350100b04441000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514026420 1250 514025170 514025173
    0x6040c0909170a110615040e0307170a1b1202011b051615050c09211c1701300f061512060203060907080f1f0e0a0c08060102 55
    0x150200041c0d0020703070b6403881140100c0015240d2a10070b03000c80c0c0f00030024803001040e115581c140f04000c4040250704055032003c44080002c00c091144958507401400c0700030700058041540c14007013590780802819160005d203814120100b118444007124803048070107465040040d40d0326103001e074092042000c0306501c481c13180c034110500280240188a50040b00d850904285160300030004a422040103082541005100034503110203084a1a041302c03800754071400000c134a21401480314170410465500c40320103010740c03151249101c2c10341407001c504503007041016501d07124007001c0203403030f1030103007000d02989403070790700b18100942c03403041c001101280c54400300e1201e030001400f5400e00107400e0383c048004114408038036100880e10740c1c01da00c20107003203116994050400419500a41c41a28100c0b21080d142d26403c60450b02c890084a5443e06400d011000c80c00700d50101c40d00142d40c2c5030385620350800c1c98882101d004403600664498481351740b1198007458898010001300d9000000b8070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514027670 1250 514026420 514026431
    0x1103100b0901030e01020c0d14030f06221404020102010c0918091b030515130b040f15020714070803070f0611040b0708070201080708102706060206040c09 68
    0x110148a1242284034494040c0c00016010145034026040190001030300c800071500d0398941c40d00c16455008403020400010019282c5942901a400c144ea01800080c2c4142e191075880000380708160407500800e07818004500d0740f0000701c588a0240d03103108010000c4845240c140740c800a07095402e03038100d4200b44400c0342400d00143c55040003070031700d0b280c0c01400402d02c802e103410030400c52a502c1c00d08902702e00400e0008014080d0020740500608145104c8883c01c0d940d4640c904099421600000c0803400004046004104000d540b10b402c1d44c051b51010003190101040c5070220392000383c040b41c00100d6000c07461211541844003400030700c103150117503203003c46071303601c5078050003503250300600c510f0340c0340001a0b0040c103000a80d80904240e0007403666400175400d040c55603820420080b40092800000103140d6486444403d02079910b09003003070004c0c0d091a049600510719201404c2e102410386144400f46a064000c0740c000b003c154000c0c05260401e0700f440400204144c000c80092820003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514028776 1106 514027670 514027681
    0x100b0703271203021501050a060c1104051f051e01080901091203020c010e0f120903010b06071a01140609040c02030d1e0b0f0d0605071803030201050a1103 68
    0x1d0b0219441d2500c04ca01d414206a1301f40106900087e9107031003000440e000c3c072040000144505000d4250130f160001040403606c00f1183d121400303507041c1d1100e05c115030002400300642029640302c4031500a00c1000b19102414071591410480c070200010300c250402e40c40b0603d40e03680301003040120081d9020040180d08000640d80c25540780c41d0081405580c00581128150100e90107485040c0800c0060001600050354168055403280d0300390b20690340d0701005142161007103100074601da0181d9003012541034141c000031501c1500c6511000c05039950b0f4117941c0c840b40119030200e0349250604040381540595400380f1800b905042060407840490f5214480b0310030b85540400913440e00030100003211030321189903504580d03032406d040041041030b00b24603805482c80c00d040c1814107510040c8402c101f22527100381d0050755910305120200c0c05501501100d50310b000105411800c09 = true := by decide +kernel

theorem cover : BRFrame.Cov 513848920 514028776 := by
  have h0 := BRFrame.cov_init 513848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 513848920 ≤ n) (h2 : n < 514028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
