-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2864
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:18.772661+00:00
-- url     : https://prove2.me/submissions/6c288c35-6597-491b-81ae-6b314d8cb4dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514928057 ≤ n < 515107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514929307 1250 514928057 514928059
    0x2405070f0c030803240303040909060603020402031807171c05072001090503010e15190f061a16080c030c060a06091116031d040903200106030b0a0903030605 69
    0x1075a400b105001a18010758407624140ca510000251402500c1c821300301c007500c0c1c0580c154000c00c002d102e0081c1e5a000400c1c2d01d8443d00010654903100d9001406036007040307510081c44c034400035400d04c03030b20300c1004000e0090108000d1002614006660985c0741c40c24400b080c555a40f250040135011446a802c87d54810f0f000700481018400010500c5120802c60410b50700094948130081070a1074188255081418030270001c1c40101000c0c5680000404c0091003815041c40c107a0548150030b00601030586080b541e0000068030354100901c5443c0283e06200d40e2410b0309040c411440030014001402066030b0b0816405600e64801c1030500d40795110311101d00001e4060303042072000d51401c541180042e6003c400e0706004050b18022035880c140a180d454a4420502c40c1e000008070380242500c00344190480d10b241c100342e4240c0c0c04201500c43e02001100007078107401c40e003030500d40310b25035188021219000a10801d072440d192800780283c01350810401554490f405810503000364840002410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514930557 1250 514929307 514929323
    0xa12031715060d050405010605010230070c061e090302090708090c04090c050f100801061404170a1a01060e01050d0905060112060507210e0a02090a152405070f 70
    0x951a1142400303080140ea044031a50b00304100827031290700200701c552146c0403400e00c2e5880c2002ea14004c40208840b0296005200d400b0070100b03004c1018841d10700e024141c1500c80480ca0010900d003202014404401744040004a24003800140d231250781d0740380c0103592403816000c5600c840140500b001200040180c0c02403408400c20200318081c0e01400c211001210300031020303800e14052100109001c4a00000600b07100010b103c01030155600358000710401d40d0383e90420f901d54903482d503034408212108400394400702c407600030444001400e084140d8440300c1c54180e0752401c5006401c00e07207060a128184540031031000c2100810303901603070895422070100c5209507500c003140300c0b002d020200b099480508050024020034003551716120100720403021a500f28150009020081003904011802e80c0200048040546d407107c10316801030300000b0300080c2c100400e00103099600c0c2243e11004521170780950300da90b5281025803029a60055091560b80d842d81c2d4a4075803406080d0860080c0328407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514931807 1250 514930557 514930567
    0x418060b0117100807090219111203041a0601031118040e0a0b070f08040b040b1810020a020d1805010c05030d0c1d030a0f06110c0307060207020a1203171506 69
    0x3096918101c1140e1120090b07178105601c8080c103405901c0b418490f580c40e16446041c0c0b034002442100010304100d049d10a803648000c02080e035105541c01510251003064000050a910120741d840c4c1c04c0d0001d40908081040400c0d030524130800380101607144240c1188682c2c2080e064580c0e400180306a00c0140a03207841050754030b0042d00d64134043d100c40d4000b510700c0c028491200c0c091444a401185c100e0700c41545d03a80c1c1e40e912096906001800364400b9003843c881038210714001c001c0306200c9103d00002503122200300b50000d240280748031601080200e40c000d150803510801540d0010f513942071074900405a1030341003251861040300000f141c01c914020381c2c04000c590083c0e4001223400e000801450968020701015501c6122503806810b0f6000b00b10303000001040382d80555441d603448503600d414a01020145800c5810400c401e46100341c0003c3c0c030108515240411001800c402ca00700340e6150402e480c01006103081c640c0c0e0010010f0440042000582e804c48042208140100003683e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514933057 1250 514931807 514931821
    0x110307020615040e030715141506070614090d0f09060e041a060a08062d0d050c0a0e0901060e0106050a050a02070b0d0917030c07023006150418060b0117 67
    0x5501f650f6020003c17986842c04130103500034080c4065004054090107000c01c08501002c2000ca0750001000300d40342c9580f801001b805901c0a0b40d07603845218010068030050860400151200202d4039445040107021a0140a45600510091200c6000390340000b40f4405802d820030841a2003a04a540a0310200d240e020069006001c2849014142c0f400d080c002002240c01d0b8018035408000c01100c844030041c14050309001c0345a03500305001c2c00451301c5012004020410799180c0e0380000b038000b850b010800407990801d00901004140c0601c0d40c1d40130350724200e4010541e016602c020405c101d000034040f1fa106108000c1480a0413512480360368402e1500b208500410521a0440b4500300c100745805140d004001900d20900c4c04070443c0b03151080c41da08000e1110000c0c004c07c40411102c841000180702554118162818103600030001d90810380c80721901c2e6509090310130702c03e0781401680452180704840e91010302c0c1d4409030203c3d100400d0b20059401aa403401502c505404100400c41c407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514934307 1250 514933057 514933073
    0x1124041a09070f08070b030a020a031b0e0306090d020a0210050c0106181d03040623030a0902130b0a05060307120903031506090e010b0a120e0102030406110307020615040e0307 77
    0x201c0b8102c0000c2d030140f66440b82860349a1030340d031007410660071041c000106400d1654004064507012807030700060000f8020401d900c3c2c00200a00100001d6041d0304049682c10100201600180504000c0050307031641140255216001c03040207010b0b0450f1081c012785280960190341e12044504001e120003a2203441e5500b0354500106100000c3c2d0130603110a500e80c9804188420098243c0080e611701810141c0c2035031761084080c0d88001425a000d03c01c02145031304e40155018520712400450f40032003900405c0800d1000143e00e11031945040d0780d00c1d8240d0354002072031f02150401d0340c3c2207860317039120f00d0151486000c11b55001980b9040481c41170825a06521140d070000300c1e840602086502e0b034008079107001640c040c1828034541c000c0140290341e80c03c009841030440ca442e1265506d82e1210155059035a503400352400360390088284010440d440c080d40740403d840c036042d9400e51a10840084d580c50b03016200c5240d420200090301c0c0c55464603003180741d001d068a01100c0e0345868924106403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514935557 1250 514934307 514934309
    0x1e0e0621032107110606300303040303060503031801080618070c0201110d0c140a0507030c0503010b0f030c011d0d080d110a021e1e010c1124041a0907 66
    0x8241c0b0038001548a030054115444d40f0400f180181001d54070a42401104c90002c0140d0503011001800011800000d0842d1034030315800380040c6480703003054039001d800d80f45d441e00600d02c01c2d001405445c051072a01454800700d0b001c2440e11100079111040410b01303000a605000c403170300b60540108450302d40c214107020503052007a40c480a1090260084c99250a0700c8942800050010364082c0003082a542c11171710032805681c20340b2403e10b0640d4485251821030381c401c50701c201280400300118a02032103001081d000031b5501120b19210100005d0711f56422002c00c0d030510829403903034410b443e61105010701307400014200b40f00c80d401e242421003030794200780e01c51190760b03052078071500e43c41d2200c40a075044ea4426800801c0b809100c40c110035100400446000810700c01e42031007000050b170328004a103481c1c0100c8000194445c2c07200e0010a84006c410301c14816030700460018054410820050410903403480390400305840300d1904038604508628080c2e01d40ca00141030041d04100800c0c50f0f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514936807 1250 514935557 514935607
    0x30903060603141002181908030406020601080d0c03090302220204090f0f20180a090902013e0106080a05030408060906090d030507050715061e0e062103 67
    0x2284d41a441d00c024042e4801c480b40c00c84814510341d2003500a0500d200880c1250318014040100140c40e40812442d40c0c016500000042e8420401001051000d004440e100000b91402e04c44d540d000d0348000d002c00b40c06100007800741d646c0522a16045045800d02100c82800c0c017001d540da550756100910192100c00d00140d0f00074a8801d691003942d80030312500c0401300c500107411a04101d540ea00e102c05801803103071100d00241000e20640e56030303908080c40700035055440300000c0d04802800014410080e0140c210403500d4040c500180013240790b80c640b001540b50318070301c00700107284085060250660b54030501e440c0c89001c021a082004c00700241040c1e95a0008580e02660380c5091380b50f650034103851850303540e006030710000f095500c69000340d54080243e0809600d403034465070300c007a01c4441100c1d440095907501c0e00c09210711201c098003900d0b40010750041c80c0c4100d06001c05c0d442c3c0c852010b40864440d03110360351611401e61503040c1d10807580303180c00300307803519042c280e80034244a000e841192 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514938057 1250 514936807 514936813
    0x25020a1a0912150f2205070b03061309080d060b09150c1212161403060613051f020f12090f03010b06030c090102071a030402010806150f1c060312050703090306060314 73
    0x5c00d0140f51425804400c0710f030400d00403c00c81d85804041c901560015101580240020791344082d088524083c40c14290701c503032122036445c003882c000070007120b1850b00140c54403081041941c40b140d54400249503903a440500b600d9892041c3c7c07000925200c4078441c070381e00d00400401c502c60b07103041c121701d03440c880d08240d40c1403040008860005c0f10007690204800000403130600200e01d03241440e5005d130204459007522000210b07100c0340001c00040a0000d0034000351410280303205519414402c820080c18044014850307a40c00680a002900031200700ba400b0703c00c6036448003c0341da002d400403100c0303910161085030349003000c9101d61075943c02010254054440c200c0005190140c40d101c82d4031603065408400e086480710341c01102e05020140041c3d0f400404003110b681008070798401010781c081c203420744071f0785d403070141c412220006036554400c00031600c0e04c1420400b2035140c460402d000d85251a10b2690342d4014a0161462005500064440c40c948200481080040d101161000f0248012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514939307 1250 514938057 514938091
    0x1140412090501050f07020406090204091a0301110901031109120f010c02060c0405090a0b030f07030201030e0303100315020c0d110c0910051525020a1a0912150f 71
    0x140c1d60004603100e0340b0300080040142030031101c440d801800800788024000304242e0317910802001030ba00140c0142c1c0703846544e127400100481e1030081030800003000707030001d1060030441200c41d60781d401800c20141c149912412503a004c101154119460180e0003005000c00040303002c03c4036503a05401a4a1035958a0b040310707803142900009900f441034007001904c610301420321050004540c1d010b8024807400341c44849000c4d199800788803d903020f850341c000030500b086c55400010183e48030303c105091607402c10818441203103c070b110114247c0390090001010310891226210080c07046010300b0358140240c041010009900c05141d14081420344111218040310b2410882803200a50b41c0340c0c00c000e4046810046414070b180300400c80c908401d061805c2c0302d110310000309042d52118a19049154000e0b1000461900401c07030307030280c00b0002e02c2c29692103100d02d041c16103100d40c0d03020f24030030005002031040704d000c03c0058003032403036070541d0715003090410520300350701c8282c281d460b0b0400350181c0d0a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514940557 1250 514939307 514939343
    0xe06030706180513141f0609080a0308040f0506070201150843120201020712050727090b0105100302120f07110a0b070e060a021b03030c011404 63
    0x704011020400b0000d91141440c0c2800c100302c10030901d16040880c0c0d1248950780785030141d000d000b44200c020350365208171002100d40c880780005183d0003131b4061004e00c203028044503200142045c0650345c03604080c2046c3d01e907420082e41c546240341004109201d86401c00070700d0f0f030b810741140d40d04002e0f122028051545910302991030f40c4804000c1000240300390f00c40303400c02132000c41394098030b08054a42d005c0030071078084503800050030360448124050210f010400b19681044180003e004c5040610006040780d9503841c0c68840d54401d20031990340c0c0d00c8413080d881ca243d00030800f144900c00c000b080000e04900c1e200032005005d00c21148200901d00040300e089010b4021a0b12a002c4048580c60303e0361902c0c102d81c40040003500315001c00140d040741d000c1c0400b080100c16049405216a0881482e25200c018a400030301100e15000e0354080c0110b1b444290005002100c002003814807101061060dc01301e032031401207982603249036080c400448030300b200d82c6408a026500881500c1c5c20012551 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514941807 1250 514940557 514940567
    0x90a0c0e0405150a03031124011202030102092106060a06091e05120f240403110a05100b0306060d08120a23180a0201140c0a0c0e06030706 61
    0x85110104800400c44001480c00341c1c4001d60103000c11404449000000020501011641c1c100318013081c0405c020903a83e40040240034499003e10081503101c203e812915141d118040c490003001030548120760381107503429019508030b000054a0008031441032002c1d82c00401c00201c1e4ac401c540200800f05515084c903030300d20b0003960076540304e00d400d40d80340542c000c24030400b0303400543d01d00c0d660b00804034440c1d44880840c40e04d9895600101414090fa6403900c1c140740b001ca1451001080100c101c1c654000c16810207540980c0506011401000d6800300508045003000001d256000e82c00c1134000012140c0e0114149820942c02c440760390343e40c5021300c80500110400038006420900241d021000d52105c41c3d039200003194400306064540298a08440c1102d111034860450901e0411807603240f00c8426a20300541030000b054480181c1d00040d061000340d0a00224800300010b54400c007a03420014481c146c1e50205030440a07568950f040310301408141c80e02807082c02580d00001d1882d201e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514943057 1250 514941807 514941821
    0xc0f08130e1506180406050d21052502180c03100603050c07020d03090308070503041815050405130b1008060f1b160b0f060f0d03020a02120327090a 65
    0x16040c6890704120b00960001441d4030301135640c1c01912650085404e0321045864480a4030401d07401d81460050b64812045030000c0000300b00308a8144101d820880480c4000407007541c4070308052100c0f030501c0c0041900503a0050701c1c240c5c4d9440400a0120119082d40194442e01444200c900f17001d132203005c02c400b560005d0750502c03414403040c040200035241c01030b01c1558240c03103401c241c8a50381e540d41c2d5420481d0000c203401c0e1140d4001040c100080c01400201c90220041120100007924841804900c0c00b4054060b00e070080b036407100040c0014840d24640d1210a811000c16030072071906040485042d201805400c5441c014003020982c09a02e0a103201e00428031281504032001c0020750b0800603030400702c18402c50300f44d16003a50002c5003500802d24028412a565150149050411302c18000315040145010310002c0244001203640030802281d0706030304441c440c84902d00c56400a01d1030140d80172905007040e00c4105e0402c03a0414282e07410751000144c0c0d20b158260340e0058140111510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514944307 1250 514943057 514943059
    0x313050d0329010504080604080c0c0a03020d030f0504091a0f040e12180d030216080601080d05090d06060b070c050409021509010908010e031c02040b0405010c0f08130e15 75
    0x1e26190402d4400c040c101c10107040c5051070900e6031750414a0300d411401c0d10252284ca01c0000c0340c0c0d20600003408520803213803007514111082031450380418003170030030303004045c0410040ba4000c07100144550103c0d4000d10000d0400c0c00503910780341b040000300480d080010320405244840205a09103030152024000e0381d24058520405032000c100e045910400f01c035100c42030100c074a07282c65074dc1c4440b1031380624001d500a080c4014013100a40c0200d80381c1c2c21a8008d5804040108419a40000c000c2d504c4280b500d400e03a100e00c101f1020030785002404e10000c0c9408e082080c0416417141010150a00c1e9005210032941595504280170480e0703914503000c0d4101e44400310b4600b00c80751505c000d00a00c2010b14000c0e00156640b1500750071107aa480020780b040d000064140d0709002c42d00486000a1107041c8210726140c5040100c40301e510603441f80c28144030b80b42000c00700f449511204202c4554101180542ea1280112500c2e10003940380030f00c2242d0fa00711000318182c5002c1e032040e181180f030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514945557 1250 514944307 514944341
    0x903020a180f200a090e0f0a20161401020d020901021b0310051512030903100b0d030c020a0f060801060311130302330306040b01080702060105240313050d03 69
    0xc1d0540407a510358011400d180601c21a90170014038410f50b10320300c1d48100403401c818091030a00a00e0340081e1060401d102122074500c0b004d00320740000c03081c00c840300100c2e43e400411140c02c00c3c0c600081d00c441c807482d44103500d501c0441c0c640500f807601c0e0000c0c126104243d01b03880110100050320a402c83e4584189909035120000710511400c1550140c0d4001140448180b0450440300c00038421001042c0c2040180d003003c5420b9407181002c022000c1c90b0030100388148a0902c0c0704000c98071208803004007800f084043e40d90381066445030400380c800b41c419002c10804c3c40d6101c490250000d0001e00c5604002441c02c00a00390203400141070b5460565401110180700b4515020411882c80c40c1020001403a442c080c0088010b081c10154507811108200a640300d140000c20881200d18120703440381441894000c12006170340c04144a81034540484102001c24080e80480d0611144010114040c2d0800414400d040701c1d01c40040e40c41f14424400c0300ca0512040504409460000e040d810b45c2d81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514946807 1250 514945557 514945601
    0x50301060f1103130609050a030f290f0411041428060905041505010302011211090d0302061906080718020705060415050105010201020f0d0c0903020a180f 68
    0x2910401050415007818a00a260041e01e030704001d045900869600c40c803c100900d00b04075070f0b5003042c18600101421a5003843d2149141c1760320742c442402010061000701883c50444060141142d07038400d10908011041ca145080c600070680c3c0f06007568103644460900748420380501d440d0040d031000c005445038820045e142d210700c003000c0c40c03113118034544400c00740b00003007000000e80e03c6a01c009007405000801c1500301400c00a0701507803280c100011090400e40180050703600032010513000303480118005502c401800c01c4c001319010b0808011307441000c0c0d80310308040c1940010490300a0301c102880344140005c198080e4110380c1c052250301c50a400100040082c03021400c1040d0341158800d10252404c4981c0c2d03107540c1422001c0320210380c00c203540281d00c1a031350094821507001d030200b03000071440c1642404110f000e9010308000862400d4840c9010201c1c903110b19a50300c000c56010706403d910a84428500c400c0c17900d940952000307149411800c1e50501040d00500500c119144034016000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514948057 1250 514946807 514946819
    0x30504090b130c02151806010b0a2f0d020105070f05090310050108011b0c0c09110c06070203091806060703050a090f06020c0a06030b01140d1d0f160303050301 70
    0x1d816005403555212080b040c06a003035a4442c010042101c050358003030300000d25071141e041c3e400310b8083c1c03681c45c100c1c8200c03800d184d158a0002c0d005064a0031050407a88441086204aa40d0b294035050004004a4124042c3c402200300508403e9070f030030306050315283d460701007089007240d0782111000001201c4500d00c0c0c030054082d03002410580d60190a50b0024068500c01d04280d9000307074400100c50b9540d14514800d101c440141a203005514a0007441840c1d1544078160a06c03400e005001520b9500c450f45d14028801908035010f0845a8056482905d4107100c06500ca801020040d40921400700004000f4142c81080611905c401070006060035000c1d2400c0321035810030301d5142c0600a2070003002c2025425490814002c0440ba8020440b0b12a00c0040c40445091584000107241c1071420301070948c0e812001001070300c000810625200d02110142501800d00d80c000e9281c80c100d071021000e1503010100d0300040c001cbc140b00c2122aa00d02020458040031502d01c0094009042840140a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514949307 1250 514948057 514948061
    0x13140a111c0320030c160815151c060b01080c0a1d0105130f030302070617060f0312180f03150a0c0309150509010e03040f0b03061c0f14060403050409 66
    0x41c00c65414600d0b07002c030380843da0580340d64072840d1002141d5200c002d400e2248614005138102400b0044080c1c2405000280641d801e088050f24000d10b14050b900408450384582d40ea4840d03082c4a4203d51044040c0340c00c0000040924100050016403618001a6160b03074180c21236800c046e0075510040b464a1112118140d1250a8a07240c108101080419481c1150340190301c0613000c0409030000d41e918520700a49005500c0c0d20040500c040043c11a50400c4014442940500300351121415002d9200010382030100300c0e08c0c6c001c00c10a01180141c00c0303011044400908c100c040d10a00300c0c1c103031100c08265a0345440704012043da4692000240d2403d5603410222410b20241030104502096a4846411f65a035400040c0c0e16642c0da000c100210340d00340540d80c200010728000e54a000d09103501c0c154010321601400220003000000302d4100d4403550004a40100c0341803820148100c0d508c0c1c401d0102c9596031060368000d41400022148100c0460030300e00072a810349541c0d00c0c2600d00182030300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514950557 1250 514949307 514949327
    0xa05040b071415150103051b0a030e0601060c1a0114010c0501090602030f060103180305040b1308060106020f0706030204050604030b2203121503051513140a111c03 72
    0x2154000d420b041020210100300810f6003c0000c01c0e00c008914182198403100141e903015541018140410b208d4628101f03a080320301d55458000d1581d40720030002040d40a8050240c040300c3d6445120000a11154014580407207144144819243c1140c803003503a480051080c054a0300024102c0300c05182580a1200340325494440c40c002f0036000c4046d02c07200201e800032a41886c403c001d10341040442d60f4541701e840c0b000005511200c0191950f030302c006003240210301840b140d040e0b0005031407038984c0c3da09004200800007501180e036950303150300d802501c1d00310300104c00c04144985880411098028020303034003078800141a40b814503186448291840700082d2a054404400b0512454880c80e17980010220f50300075281e503d0138182c0340912800f12504071980d20805540184184000781e000b1440900094282d031802182d0b1b16007030b414408280c126034009001c2d05644000801c1c0c0b200c0400c00d940c645010f986100d55258030704040c407400050700f01103840b5103945155038000184c01142040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514951807 1250 514950557 514950563
    0x30901081003061404170a080f090a0b0c070204110c060a0b01050403050d082517040203010605030604060515040605010e09041e150f0b0607030e1c061a01050a05040b07 74
    0x10742616580e840c0d0404031118800389200c0c03058460200024024a43d5881e05c001d8014001145001070001c002003030380d07002030540c071903420410300460ba00d202c0420600c40115001100c15000b0b040c6410703048801e922883c01203000b40c0c03c0070900365032540c07203006a6086a0358280a0415607440c00d084c54000e01ca051301e40d0f03050101c18007011000c2a010001c104c074142c0702d900c3d11843c45c00c100d40300030040b50404000960384645011301820065000030000100b40c516514951185c0b82c83c0300007809004250095605031103100e082000340185600042d00440426040c0c03640312840c00306000c00d031213941c0034040c0400c1828060301e207242810710450764010700901d050891628460618a0f081406500985031074010455102404445206204d0150034910040090840010204129005d03040c0090180450700c2010034068070344c600840044800f0042400d22a4600d181440050003200a52842160722100e890103d50048085139044a401d4a4081c2410700e040e10175002980010021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514953057 1250 514951807 514951831
    0xe03160807030c081c11030c070b090316050d091d0f04032d08010e060d02060d020f03040c06080603150a0b030c0a0b0304021c02061c0b0a080c030c011103090108 71
    0x19400b00d440000940903a0702070786041c81704010310503c1d05007503034845038000c40e01d04800c00034800181c911104881c0025032240300c20f0515507500d022075007035008040700b1810014a0034400301c04c01c2804110034040b00030980f520350645454412914010b11418044c0c80580e0901c400300d2040b0085481e8240d1003803191800c0d03609903250000580e1100117510b04540202c0000700e1055201c3d8105401d5805881d40f0440304040b85008800200c1d80b10810b40080d0260100003402c580c4951a501111b41513004400c4a40d035908140c50507010b1500e041c412039000440c00f0000c5503051801180807084036035455070104503034960340703503002c014035a0400181d070503c951030f410140303502c808826000900c42e0340c1465407203103054018401c100d40805032040d0f911200c0722900700103070f0700c4d48190380c030140700e180f5181e000380c0d81840351500400c004a6034560082040030000b0f80c9200000718a800e040059041d520440001401075a0f40c0d507042c0c180ea01950428448a86654031881e0690b601c55a40054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514954307 1250 514953057 514953077
    0xf0603010b0a0e181207020d030504030818040e0607080c03072304030b06012105060406030b0a06050f0102030903071406070b0705040602011b120504060b10030608010e0316080703 79
    0x4001c003601e640b00380600d941080800402c140016a200d80030340c04100645058021481700c0d0a4510030b541c1d00922400341c0c4a40101814421300603200030310381c041407150b0780d8405082d03181801c01a4590380341c0b10358280011822081d4003c0741d680d003e6150b5071908252621410f02c4004150401003202041142d42c0c2e038111019040c500703140105103000103031f0707a0b0b40d507007541003015000c00c0080899041c00000f4035001280f9220008144214008910020300d82d258100005c02a001ca0b5201408045d401e80a004a260301a400b800032180100d40920300c800f000c5d001a80c1381d0040d190010750617000701400708030318448101f0440c0d54050080115107003601c03541d1804030005082e140c2d01e00061010400340070050302441280101d207120b40d244a06159201001404205609403901c3d1003500e4201113001c202c50364104c8041c1d43d4005101904070401140020010485031090400a40c2440213800e00b0b420003000300c801c000c000b500c8000210751507446906c4070b9071140100300c3c02c000d11040c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514955557 1250 514954307 514954309
    0xc0102040b0309060a2703020313060e0102060f06060d0506130207050a0506010b0921010e1b031905030a0c050f031215040e0303010918080a181a030f0603010b 70
    0x802040602402284180c49090200c0c0e6a490604002c01e10202d061030199108440522541c040306003c01c12200443c6d85440e40c0f400700c1c11409080340d05a17508200c580040b070103980007070401600c2032007a4201d404aa441d00f07003810f98900162001c43e0058420088000504959080f080d4420006021131051283c0452643d003203901111043e00c042e00b0480084040000600c5003600410100c2c4d038190400142200145c04500e0004982076000407402e030381d05184800b9008007080941100a441d803e42d98055401d08030354080040504c0380c0690860b0740c0820341c28600f4038212940220055040014210003500e80050400c81a02c040c0b042e510701c51840e200420050401c1103200da81c0c49038508100031703d041e1f81308945040c140301c1d0b404c2035100f800f425000410b4904480c410040410303245600040c0f00318500802d400a45000b0b0b00140d50450190840316549080d11496150750b011551a082000220701000d204035640380e082000c12000d6078404007032500281c3c0203000083d4000488 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514956807 1250 514955557 514955561
    0x50301062a0b040b07020601180b0102010b03120c010f021c02130e040f021002010504020117130209010b04061e05041e120606062a2307080a05070f15030509030c01 72
    0x1000403540b10708460100000c2019011a107900403100d4001000c0b55414044500203a9643c0d40b50424030b10303910036004a5a030710075002000c5611004c0c06440420030722038084c50580e408010120f0640d0309007544c0304981e200710310031503140c010318480e910b103221030030b607814006540100c0000c04200310060000c0740d800e0540d13003054003552040402400c80201d51040c4080c522081c6000002d40e450701c001c12000d0307600302609c0d00072030b480e043e000021607031103628080c6000c610140c0a5000f060603000031409136251030041081d1041d40d1186020b0343d080801c00001410144003c600180060004003c403c2c2000e840e10f50b454102410144450344407110420080b11296098900da91101c03020032032180c019002a251549240c00074440303940884112103080300404008000c0c0d00078401d40794002072401c40d00021100c0c1d10013600c55155840541c69a00d040400c0c09562174003d00c10000742020f4101d818004451007540310143e0742d10032007001c0c1e0060000910030b0296010400106d0500b09080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514958057 1250 514956807 514956887
    0x1203091002070503070617041202191a010f03050703062007050a150e1e190524010317130902042606090c060a0309022214060105030106 60
    0x155008042c09460f1500300351400c009680200d00b8420700091302c40c1020348031028280c2c800d4000c03629019a446514040f403600511849403100101c1203807214041104044c40c3e0703422400401d081c03a40c00c2e40c84141911200015120003061648071150400005003990011005010401e01c80c000241e840c90244245500c883e00441c0d054003c42042c1007040410201c001840c00011003c100900c20b41e030301c40d6524440b049185204d851928200c00d83c0c01000c2107034030b032510128400c00026030380300c5c135043c0ea0b1501c6182909180c540502c001c1400450510841d604803030308503410030640c542d00d10350310405600000124500042d02d00c4042051070356400104010402e03c07200c40d000f100c018852500c29404044a8100e5400520600244403000103420035450001c5681507a1900d100c0781c260024015204025081b1511381c1114031003c203d05a200f00f031005402e0180200d14240200000d912800ca030264041030003400184001c51040410300c8480c41c03443c00b07544411400c000e5441d500211 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514959307 1250 514958057 514958089
    0xc050303040501170a1515031815090507090e07050a060206040308060d110406060e040e01060e0708130c030302010504060b0105070f030f20071e030519080403080c0609010501060914120309 83
    0x60380114515941d16101c0c004451006c4000850700501d07941cac1b01a01c845030b003600c84001c1c1e905c0d60813107018000b051118030010038400904020088050030340ca91980c04030f11400d8480d0b10000700000d031850001c105688996410f9481c01d2320303541d440c8100142e1651a5400780d55482c449102c50195848501c90580a8402d0f80c480d620800018800c00060700d9040100c40881d90518004001000c641317071076903130050240d0030491082d0391100d00071541e03140300c00e40141996034102390001c141601036120750f01a274040c40d828030201d0b14207401580d20741708200d030060407461040d03041400719208049a05504200d403902420300d03554010649001550b40d0301001c3d203904110410805c00c00d2002201d400069100c0c4018503403459610344907150411139050036500da000031100710402c020082100c1c05940d101460036110784884071314640e66481140d003851190310b030100103e6042e00508400c02107032910702d9858800a018000d01ca4410107065820744148800e2008419980c0c40d03007440098445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514960557 1250 514959307 514959329
    0xa0825050d020f010c0516110301020f0a03020304050607090e15220b191505090103021204110108061207060c0c050301050708070206010b162303160c050303040501170a15 75
    0x280c103d032443d00719441c1100301d2051040411590121038896100e81d810759400010000c1c4000c46040031a004e4840e800b641070b034034070001030300c04283d41c5c040c0d010b18041d43c0500304480300356540718404d0710340b1039090003104006148500014408400e00d0f604041060014200e501c480641b00c04490010030000240ea02d401e0f12483c03d1700d5a401c280d0042c4402964030b5041218081c03402c040040031030008010103040200018890705164000e804039480e002445185240030701c1c081c140600110210030b070450006182d007001c191a4644002c0c1e08211280e407001070035400d4900fa80c180c46ca1030b148001141d0403a201d180001c2d4645e42171158900c00e080548640711a4605400001e00701178050b00203407001401407142403000d0040ca1464408103500a040d044900d80d00c40c0600c141c1d2600d000403000905c000602c4950000c2030360500f0465601c01e2004450454880342010b40700c0c040c9001e11400501c817085081070410220b04400c0e0000d9024500156284801404034004d000d0744e0410780c2d00130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514961807 1250 514960557 514960573
    0x12061909090218060d030f0e0901180c03140115090e0403050309060717131a15150c190c08190b0121080c070803070f020406080a0825050d02 62
    0x2080c40c5003012a1600f0180f004022481d0000018081034102003010f001c0120706086480314902580d44410034000051820910303680d5034a1604130030381005100a001401c000c07000301030038028060545a1a40000d135000c05a00f040096181c841050008000300407020200240900355800f08502480c081c4d034840b582c80c074003590b849103040000f0f486502044482c100180721285020101030304544210402070418415082000841028240e1031481c0040a028042e05000d490800d4034100c0b016202e00c40c1c10102142081a14094100c1d0500d09410600e01c040007540c1c00d40030740c81d1051159207400c501c6600d52000d81c0c58868512110103256011240200600c00030980b03803401013100710705103030750301c0c01d10b0825041c2e4020300080102641301c08038a4060240d400d00940c03020789841000ca0b529100c071414000e080102444003680600e18007080450724400200d12403030455000705540d464001110051852409508480309501e0100f0b919200020001e20000b44030000a174000c0c2000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514963057 1250 514961807 514961809
    0x1b010b09010b030f070302030604140a06061101150e04080f0406020d03061208070f05071a031807080d0e06040e0c03191a090a1b02030307080901060605120619090902 73
    0x20300e06030810b8580180034810490082d00000845034411114500541c0301e840d05000300d0042d0602e9601f00203101c41c000c04220346c280280d40407400b01c038020713903441c0c3e40110845061404c85101008208220404840c103115042405814a4105104845541ca0302e8401d0080c0c8155400a801200040e04002c090003ca2035050142c08090429015411400c01155442c00000e1007400401000e010046180c10180b04040c4242c000410425020b4009c00403101140b12040e8000c54291802c4130b0b40e081c01000002d800185001076401da4002412080342c41c81086e42c440c10300c885244c0d4400810000403031410516038615004040e1155419224146030150394000707200b884500c28a5441d1174075500450030071680d1451820400e0700c003030686448000c101d10103801a610220520707252034080d012100e82c0000210312a445580ea07109550329a40111402e9510764402d820004206100007400400001141500008000c0c51032801401d03451281e030302d03941e1741c5e8000a00e0315520f502c20b50179 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514964307 1250 514963057 514963069
    0x10150905010312030e010b01090320040203010b0715051512030c010f050108010c0201050402060d021605030a0e01020f0607080115020f06090708010b030109200102030c011e0b0904030c0303020309031b010b 90
    0x41001707100007404008041c00000b042000c1921015103900c00303000d0411041c0d0f0b440603100f0000300002d042903603a903844288038400750b4480103084510b11000303513441e40c2000b0035100741e0b0b0094440850401404640d1402c11001c88115151460387e070000b0010314070643c038244602c4070b1002c20b5420214103903142c12071080c21030781c1c64040380c0c040d6410101007000607510708007103276450042d4010060710b46054007055070510904c6080180584000109c400301c43e6002845490066800d908490f51311a110300102d8503400103981940c045880c01d4018050303003015041c0810403580d540b04940c5601d00341c80445240000560718480c00b03400c054028080c0340401e008640100c030003600240700a0031107580e00390102c0c9281c48807000148810000551036842441140c0550141c0c0009001062081c03044c910804107900b88041c1541c509602c0f410a0b01b45404007502c02c9400d521382030000d22440d2004d902035440103100c41d002d8081080107011484c0c0d03005000c0a0701c2184400004c410703082c1018001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514965557 1250 514964307 514964321
    0x290405010b01080609070212160c0906140a06230d150512010c0504051c02060d0e0c0f0f132c010b0d05030f1e041403011d1015090501031203 62
    0x80502100c0040150140e000101d801400d141c00c2c200c155127280707054112000c640c5d02407004283c11384410000800740d005801000c02d035620301148003040e1014108118880b2224403509000c00d03001d2101e405500580d00041c90b0f80c17040f009005251412480e20007044070000815801c0361202d03100144464107010a8084500403204001c010342c016914000e0001e0296104040c49542404104141408648401424158090f0070315440b1804440c201010300b540ca10811628032810500d42c04529290888440c04c98014089207030b201224024009480515444404a0358940c4420321161b08900c1c500015450010b0701410300c80c030203942d054291812010080e01c162903412108001c0761001c000c40e0102882441303500d50303641c03003c0b17000c0c0300001500c00345222180001c81c0000381c450307451500398880503045008102990450b100e0150300c2480c1c2c280742066500c41211102c0040e026071100075294a00b9040940030f540d20081201620300903042203840401090500d02d1054041c016a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514966807 1250 514965557 514965559
    0x70611040f0512011103100311010503010f030b0a090c230306040b011205100c09031203050c0d02070218090703030f08090a0b150a03061b05090607290405010b010806 73
    0x146001d00d0064009260401d500a65103d462440925441100c1c00d52240c10024000d45078151249030103211150030140c1d602c0706a400c42805820295550311034002c4034181c40f013002c2c07030b401082c0c1140c07100591800000c000150190340c2d000342c000441d811a446d0401025061410101039000a005078a408040113200d8002e034000c105001c0080d1416204d03505459a401404030001d1003401c0c0b00d031400b03030b018030a8104580341501034220f050f4819030103001e81e4080d00d910313036110851900483c110b5504540040e070f80360b8184503001c81030039a07400a02d542c0b80020a181c046210304d5a0104e01d101096402c0350a84d485007108004140d00300100c0c914020481c103110b075403868044119901d9020703404006058103135090000c0c00d590f2640d901d4102248018011680050700c03803030008020158044251400c0c070103a0030401d19548140110b81c1280d50281c81541040e160360350305859400603203010088060005451142c0440390201c41e4443d6002d1710020652941e0000054903650b0090415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514968057 1250 514966807 514966841
    0x307230301060b030a0e032b05090c010807050a110709020c06010b0301210c08060f010e1b120a140a15060509100c0804152102070b0a02090409020607080706 69
    0x3c10000795400d0540350702c50f403003100200c0c40854624450342140305001c841e0f107502881e8203c400300340c0802a1020700c60b03030840a04014545844107510f65a0811008584c001111000024203151040c03010f0301d564460380c01d2484142a04512841c102611078009000d036540c0410240111182008603600400000c40024650350602e070301d0018214118403038000298032035146004000203e01600000c1c41c4203015109142088500380d50341c0c00080c802c140184d1038420126080b0301e002c0440c0181035039020311151030654041c1c4400501e0100501c41d11a1700ea40d08842d1a90908582e0b8141c0304080c02d030340c002162054080d036640000d54036080307038040200a1020084507222030a0b01310300349015007800e07510001c151506420314402d907001a000c1084e1010048069500031412807648001e41060310260b41000d64003c0c102d018044000d001160403030041240100650300500c0d03a0301d0041c1c400700b4182919008554a0360004500b00d43c600380002d40801032000c42d2041c0d0111502c02465 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514969307 1250 514968057 514968059
    0xd020d06050d0b01030b090a0803010806060a05010201050105031e0118030504030501060f061704060e030c0d08160228080a05030603010f0b1e01121b1b0510020711030723030106 78
    0x583ea411041400010004900c02000c030340030290410000845590044900d6501c0d070b11042101d44a102c161035060191000c1d01c070200b00fa40c0180200d506031503014000f421562280548035000140a0045100c25540c2d44030a9004900c04501405400e01030748445a40f1840d43ca041402c6480943c01422039400050081c00840d910800500c404a04180180801e0300c460804a004004120866207188800115004010310116a54540002c3c0d078552808030ba43d00380e401f0071608107041000f03005070801c0851601d503000b50500b040c245580022180c1d1150300b10341d0b408206612041d1074001069000c02044490300d000d004103890b901c1084d005204a0010303501082b003800c600c0d425640078680c0c2e84103040150b44150f03080c40c030b01e0b400e160003444041840a0103050614a0a0760507001a00303810300f080103112203509a091407903109004003294001407100d1402034210241c01c03240f0b494091080e207a40d503000c025044c042c0c02c0101000988995110b5070341c01001d0701c004414002e0f418200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514970557 1250 514969307 514969313
    0x3021212040504110c07030605090f03090607080705240f13020d12020c190302010e09070c020f060403081206090106090f050603060d0b0a090506060901150c06020f0d020d06050d 78
    0x41e01c1c111041600e0103c0c0c001d442001204c11806400400e00440c419468000180407158001031701139840103082d01c40d090060071502d900e03841902d0081d40c0100040102c1c400050032180203107912405441a41c240303002e00b00040c44400040c40380000d0100e4040140120041205200ca030030a001007582094903a8950128a8040b0340000142a40b03000c0390400f45564021301410308081801850750b81c0041c0c0c1e00120340150015400160f00061034911210b0203030400c551080e0080c2025211744100b02196401c0202041c01030310b640307070410030074000000086e40c9140580b200d40c44100904025103018401d004803680141d00001c20820b01d80b00c01c201e4016001100401d56801b0b076102581c0c1d6992102096417070246410040c003000c4440c0801503198056030003981d01c4c40c0308070305444140d1a01000c00001100c00c4c01201c4482560880020f071041c01b80c107140100c5846101c02504003141d5416581c00e5810403041c00e0151500012200040400340c420540030704400c5440a2000300b65031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514971807 1250 514970557 514970593
    0x21070905040902130f0609020c030417030307080f0403054f09020f071403030702010b01031a010f02012901110a0b0f0405030d0f0f0b040b060a2a0c030212 68
    0x1040314004e680e820305502c9035005034102c1c0003c0d1100c80001c1d036640590030020383d0b0b20740c030501c81c80c01044003c44d5514007415003c822030340205003a0f62480025190300000da110003c000c1d00844c140241044040100546150030b61101a81041d94081c00c040c83c03000108404011401b004503480d500207130280c102400f042c1d41050b80c4c2411401078882c818081400b0040c414418050304494952a5440341c0483c0000194071030355480e4020b01160b1040c0340150256010000b10a03041d40941000002d69403050f00107951080b044d01c00410569140306408100c03000b030b10314001558000c61990145560011401c2c401d040e207900052540c0e8046440300c0210002c080c28400780401c403200420217000080082e44e5002001d5001000343c00e00c401e03000e5004040b501181801c050074080c0e103d0980c80c0c2482078240e02d40000d810940791500e2810100c5141c0035640000e0400031810311002d4040c01d0ba420400f44d054820b000c0c2007051030660042214520005c4403d42c1e66034000e4203e040780034150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514973057 1250 514971807 514971829
    0x31005060102120706090f0f120f020a02090a0f060f14151801180810050c0a02120d241d1b03060d0618110a0302011d0621070905040902 60
    0x11038200c1e103c04d030910344038005c0d05154001400701c00135480c034603080c040e801e05550800c034403908240c2c01030400b001e0103894000d4249a00000350b001520040050f04001004940c003c2c51040d000891700341d50801075045640c50380100c8001c55600105115810104004070460710040f183c0210800d07904028080070702c140c800400507003800110400c3c40382d0203403116a6804643d226083c0c1c2c0305481c0c0c00455900d14001142c00e01840c21724001c204845103800031070300d00181982c080c4c045454100c03405419035120000b001301d415500c481101c2d40b0070200c05c00c0c00022440c01582d40340c051610810348030340c58070f5460b0301e0801c10b0880c1c02d202414a22023445050030403001c0307860b42c8954501002a50b4540400380c00b81480b030804a02603030707910380f036054444914841c90590010691040c1800300c1c0c4c0c0002d010090124800014440184440e840d05400d803450003007441d890951268103400201c1c1007452943c10035901c0a082c070075843e400c04c0746c0c08050481501c040202c40b40e940c0001c1c1d1102d941c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514974307 1250 514973057 514973083
    0x9010308070507170d030c0f0f0806033f19141605160b030106090e15041b121802041d070803041d0106050a050a050d050c09031005060102 61
    0x1000405804024050102c24000e0000078444e03119041140e8142d038440441c03216070300005e841c100c1c081ca43c042c02520058901b2943d5910f40080907414202030710034080250200b60303d0f2050000c0724140411000c4c41c0c1c6920303000d034001401901d4060720002c26001d802e00d440a400b4505120b02409894511010b41840403d4030744600900c20741d943d6400d10b4072654480040c0014072010b5801440030008480041a00a40c03010f0781e00d5030f0310158070712180820b024160016907000310800420f80c0040480b42c100d0540c5061100f8040c0c50f2001504441c0001c915000c910218641c3c200c80c0c0f60041c2d1001c4d1117144070349090165008059507020b4003502441d00a20455807140c11210b081c10710060f52107800c042000712400d0036110403001303070790703401034801c00300110760078400f440704050603c003014100c074240d84801c0d00b005c0180c002580d6a400ca00804010881c0c00d010110001c8801d006c3c544c001c680304610302d40e442440009040c06c001e80b840008112a0506003401100e0368000340502039039103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514975557 1250 514974307 514974323
    0xf0b280c0e0913020a0e190b010203090d0305041d1b16020d0f0606030b220b010605160819172404090b15040b180a020a031407020705041505090103 65
    0x1881c04003d0303842904501d4060f4000034204000705450041007442400b410741d0a0080c503072103500303100480c15203040d66032650040e08103000e0b0409501704240b103030003054400d0500504250301d80c006105001301d0301d6111580d21501000780801e440d9803c049031621840180c056240081c44031a0354400380b0000c0c07000340101510300220080c484010038900d403140d44074100703100855403030500d003000c0380781034628400b0b107250225094550202c2d04590392455034070488240301603290900c20340f202d030800ca5480000f10105522400000c0e00d400007801290001c240e162040d80031140300804c035003020a010003048001c0c3c400e100c081c0e0900c12140304007062800c4a2881044288081400740c0074006000740400000c03000e00003c0c0c0c1810070202c24824040e1810010606907008100c5100c2680380114071114078400400c080d1010b0350010b00d03199001f818085055200486070061250044600700d0040c0c02060301400249480d000b4021031070b995a290805036410540026207186040c80000c00e0b140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514976807 1250 514975557 514975561
    0x80a030506120706050f04081917040503060a05060303130305011a0d051507030f020f1804150b0304020a1512060902090303162a0f0b0313030c0f0b280c0e09 69
    0x40c0f4140c003150080c0446606a0380310000c0c1e009264503020389c801003103906161904941000c0f92071107098800712100140100380c02e86136910030000030b000140c043c90f0103000c20862807000340c0c0741180e50707001503101c2e100015642004000258000d000344440c2449242c1d01d14605001c9800000c074440014408200000940c5808100740e000b030420b840d1078044680040358080b1034000030000341c2883c40c0303001550409980c000c000c200481c4e803400300e0f00c00940e40c40c5905000c0b00084e031001c2e56000307201070408c2030190345581c0e0206130306207880c0c844000038202c4072080c1c2503102e060107907400400e5140d405505248003280000d440e80920740580111042800c00d42051049111a500100c00d40300081c61103c1c20007402144041d81c05d029820102c0300c500000102e020841c0300310703071140d4150b00c000c84a441c0316960888030000485c070140c988915540000012a20641c41140a0007a03802403405980924401035445041000c040880c07525004003200d1894002d4903002904e88100c03807034241c0d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514978057 1250 514976807 514976827
    0x90206030a0b03102c070803120403030908033103140c0124080f0303090c0f18071206060c020a0306020c1504050109060f0c0905121009080a03050612070605 69
    0x2c890340725960b9403141d040c1305e643c588102920404074103829103610180c200c03d0459891540e40c8809100e0120703960300070010403112a0a03810509d8000c2d100385000b01d2060386544407184a03800c240d901c09014160401009540c0c100da0b80c42441c640059840c0c2050a0fa00e510094402034140c1c50714040d02900041300c22007690b0a6100c42210502560030300c0316442070300800000030b080e60103486801e100b0103990001d40000082944c2c415aa214000c1400f501c141042c00002c1c1c421141060b0001280c0c0c11008000c2c1104048a1042d041c80e9248081201e10031401001d989030340d0b12503028442140c4105001d43c07501501c0740107403500501c0160340c50741c041c401d41c2d01d003a03955020174604529642c14081000010b40154042c2c5001d8a000c0c0700c042d180f0320650080b69030b50249100401d80c86c80c4c1c100440d0601c42e48500c1e41010580549400600f136556500c01d844541d0790840d103001000841d030083c16050312803140c000740141c40c0c5c8140d4840070307800c01e5074a40c6640900018004041014801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514979307 1250 514978057 514978063
    0x62411060f19090b06030607050301033507050a1b0506040519080f030c010c090b030a091103031606180312090f150e060a020306030a060905100219080a090206030a0b03 74
    0x1004041c1c450411101c580f6040c00d86840e2800da031003070303c01e0182101154802d44a1800c3d24103983c0c02100750054041c4100305541415400303101c45615070707100c49401c41c0420155000d0a0680c0c000d03005010004603501e8207d4040701d09030001c4902016402e420f10090303d030107086d181a680c003524491944021303c503082c60710311615800400e507441042c034001d13031600001c8042c0400798952070091010514618041d41c10300200e000d40d0a2440301031001518800e82c5404c90b0a415000b001080c2482d01c00c07501080c00c55100102c40792681401c0c6040004226441c800ca4003c14078504400301c088034250780090013018414003e480868035010301c00c0c1445500303515a030b913280d88840740b00d202500d5011204050105141d0070303040e60150000040c200a403d000303c1e031240300000d0181c08010441d9071078100419800704151000c2c480d000845c40100810720052000483c00043c1d154245040030005100050041c010b005842c103000e0f5074801600c036481565000300440c100800c0c000650b0000c249 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514980557 1250 514979307 514979341
    0x1406070204062601050f040f02091e0106110c0f010504060810050a14120c130e03160309050907030903080402041805010c0302040510090308030412050409062411060f 73
    0x3890f041d0240c0e0211540300c9610f03415140051100900540d07507800308596080100702c070084e1a004031005c03480010701e050100d1550000041081380c02001c0803130b04650700e003d82600303ca00422000321030048004001c10a581e650481219441c0d804cc80d8040024018000c41c8680e109000c0140f01140c0d100f050b0b070048502809029280100040d60380f551402d8003440c444a003402640e030703500c1c0e02c41d8900010031034031020039000c0c110301882401c042c01c5000414481508800340c4c001070044d04035110408800030840c81c0282c1d2800803250070441080801032014008505061608078803500003500107504a602c550105c41c00502002c04a25498892081c2e49000301300d5441d00907205c10450f010750280040d00c0007950340c261020004242541c080425000191410400703200240004080d00b40a5042c81010b1900e81e0505503207000c5002030f83c0c1c1d107070024490720701c412201c2642e082c0960f000111100f072500e050501c80c0400d108261300d603400540b0581d0060107110000d980c4410510700a9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514981807 1250 514980557 514980569
    0x11409090f0d02030714012f0c0106031203150e0a0207062301031e05060402040906060305030f041d0106200106050d0602070c0b0c0714031912021204140607020406 72
    0x250200b065008025226032001320101c81000141c075040b148508140b14004d0082400903030340b00085040030031608001d044040100380b940d410048451407540a0203840c0045104100c001050003800030054243c0380184800c0b05050018071040010101581c2c006412054210005a6981c203906245026040300900703404194400683c3c01c010b1405900b1042c1224000c07042c00514a9007415165130704884003101070500c0e41328038041005450715a2015940b14412600091140d58a994203400c2d5003000550314000d11000c60104602080d0039602141d5851524014405605000b00038240368140e403466864ac9002e0298030030100c3e001d501040141000411964000c455494a0b4000e54001c01c0126a1400c030004001070b001103820584042c59012800b92480f5801c0c150340c43e194660a0b00c0e0260b1511130748001c1004179043c5c1c0c400d00c81c603c0c050300075240c24a16946019141c03007030040710680666003c101c00c022004103080302c0010302c03000b03c80240d90340859000160142901da0002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514983057 1250 514981807 514981813
    0x9040215030703020d061e0b3f0c070b060301060308040e041a0903130801061a070c0b0a0c02090f010e071d13020901090f03150b03011e050106090b03011409090f 71
    0x400c8441803406506144086240c07800340305030302c0e9031300180540a0580c11f411850320070110340141d032205041c41d049c4880034104134040aa24015a121103110035961010700b5040041c0031424000e43c0c03051107612140030b81c000d00c0312924542d1079102038072840c41001d100e6004040032900304440f00280650081c20229503440c0f82c1014941e1030b46950000fa0059443c880ca688005510a4107001d24011200700b0b00c0001c51556501c401d1000941c00355404480c00f005940020400d905040050210307010541c5c2c800c0000c003070314414001084400b80a1140384200040100007003050602e20780d52020700c038507105045040c4d00c8601e00c0d071541d00d18081640080498586004846103a000d003110030802d981c0c3c0440155200007038003120342c103030001800160f2001e2140c40c120390150882c83d03141c82d015000203418080350340c0081050303113400102400e042d00d602c010400f01d90f01c40c1c035000180010401d0546554504039411300c82c80700c0781c0c134807a000d14414800103030105014420200155118815 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514984307 1250 514983057 514983059
    0xa02010b13142512020c390d0f020d122f0d030c09080609210c120304080f0d060e090102310e040605011e15080a06080d080402040b09040215030703020d06 68
    0x22040119482030400342c1d0102c0d002c4412a060040740c131404160140151502040304859201c032840035410450580e080704e000b04482f00086d00b6040a2407a800c5199a0325042d0984403034901c00740001c1e18421600c4035044400d01c042c882c80491540c13070710382042c1000604800302100a840c410825408040b45000365400c02c01c031804081884090414800091441641c00e001d040d000ca026a00016190f0b07846100000b00c0c0410790360045030014000e40c00d09003420540341540c17401d40c1c040d005c05400e051b100c00c01080840f12100d1095000042c84c1e00a50600d146030b00030794520b540000c4009002444004003007003c40c0c007040010301400c400342c03c42409150030f041c0540905000ccc4500506400d040d2400242003a0040840064904000341d0800c04100c13400c04488810010300b030b495003c0d907101e00c00509004c4c20450b0007451107541d101c0402e1440e1a004000c03c454040142e030340210181c0007080010303516a80030201c81040b0380c0040303407a5194030000320028052a000e4401103443c040d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514985557 1250 514984307 514984333
    0x121c09111e12011428050a0b06031305060108120f07060b03011b180501090303031521020306012408041e0c0311011110020a02010b13142512020c 64
    0x40220088000e00e44c055003520341554190805c0c0b03505520001003210400c1d501900081e581201d90040c20f06035000c82d4280543c00010381590050302c0041d44200c80c00c0740701c1c08011080c1318507801404641c02408400c40c070b170203011030581b1640e00034003440b10002500c241006016072009003184c0000d4000c01010b007035680000f40d41e200182031030001c00d950440c0101c02c941a80380c0349059a0040c2d4908981e18995541075003d0003120780609080d19888201181265400d0381c1448005504003a012610401d4014142440c0381a089141c1c00c00881c0b00000b510707032800341c6009110110789040b540d20b50303990400c90880d8180c0007803002160307070144400d81444070f030b00900e800350380c00303042000314001c404401900e80c48444100c0d00c20300d0704498800d060320b45044d4042c0901d41c556000114a94074540005540c0401c2e4070158200075a488403440c1d03410200b0718006900800b11981c610200d6500c0340320202c3c2048544072135041003140700840510303841c90b40599800070750300c001b1104170071300c039034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514986807 1250 514985557 514985561
    0x18060e040e0106030c180b010f0e0301090b0705040609140a0302010f1404030b0a0f05040c0e0601050d05010f0807051e13020706020c07060806010309031b0204020705121c09111e1201 80
    0x44549181b101c007911442108017010704c60302c1d81c1c41d90161101e0840303601040e0155807244041c86038076855581c8180c0040800c013a41e0100c2d1040d140d5580d411f554030b040c031202403c4540243c00c2600840501802c0c403500b0345504e01c05070252902402c004c184c4540300441280c20343c5042a4240411034003240c00010051182c0c000d600441d07030032000317001001284c8449d03002c5038000c5801602c0100d40030000c0110500b1603007866001381c010f01d0020b02d003024a01d280d40a851080c1e20130034424035000d1b4100708110080c0f006030301a16003201c0c140d84005064a500c400c241210001e50302c82c0300014865110485158111001d1310703440b1780e0079510b9941400c90144c4500c01ca110300030100380c0a41c002900c641c445c1c0314607403000350305491741e030f01010b00080001c40010450070101d8009034200807036800b040040040040c05074000a06039601d040d00d1445500c80c0038800300da1041d090a0050344400074031402c082485c40c5c3e50a903600d40d14500703503a108410b00d81c240080303260040410034014075000019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514988057 1250 514986807 514986809
    0x40807080c030114070804060c2f0c19090b040603060905151b3f1501050711060304020f090903130f06051b03041d04021018060e040e0106030c 63
    0x4500070030800e030841558a60500080311741030001801c01c00001d00150b0f040c8d000c40c21100c2c251800400c0500300612141802541340f20751a04a00c01442c140303034201042180300460f11096408840c020b525041402181405000b009a03581e103c0408074078039244d0760b025600640c3c0104d424030444103e414290f8441c0c180403102001c440c0380f940000d4204445400002070612400b030032030315180c4141c10401c0c1d9520380f600e250240808050030200b403d29002d0b40c05814400d410100c0000d4103080400d0784181e001c113503405050001c24492000420081c11000d44904003d568050b07481c9c0e1280b0000750b81e4001d090009074024042414048400000801307030191010014000b64450f403110084580510341e480360314002071041003080304012655128400c44064001140e041c240c4603400d00e10400c100060241082d02003200f00400d61410a5014140d400c95040138004601404c1e40c20311440120300503101131010b0316620080c11380360340c2e00038416641170034020003e150f20f0380b50070060f00810b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514989307 1250 514988057 514988059
    0xf111507030e0a050d050a0903080408010203180609060121050114060a09020702060301060311040b16031d03070b0903121209010b060313020405060f10110f070602150c040807080c 79
    0x2c0d01050500d002800034001c400260071100911081a0070541283c1030341c04900c1c00c000b04480803a001000680b8a80900064030003000056100d16100700e003860000c0030110b0081465000d4800e0283d84500440d601e81500ca41c94014104d40003a100e80d618091b0040800034100c2d8038204e0b00c0104520444030550007003174200c423140b8056684001000c02e078020f101c2c01039402113013000100010b46c081c2d4811080c44c2c3c0e01c00804c80c20190b41e100c1c0c400c0c0c5a0000c00f4030314150780c58160440d0400d41d000c0301b1603800080b18a80d07641c5640718400880d0703417404903005003000c048000440407040e40d003c11146844003840f03460301e50b450501c0380003191910010340342c000340f66003400700840c0e061415205880c400c200f0f50030440d100400c540c08200207841c003e40f040d90001041c50910314581c07140039003407007059120340b90307484e4800c440030340940b4000202c0088591900008014028036502003480240e0490840d20358005031244034040115210719032100c030766482000400184060041502040c0300c0c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514990557 1250 514989307 514989311
    0xe151b0601031e0b0f0a0902030d030902040f091101031109041a030f07030512251a0606030108070308090415030c09061a09010f020a0b070e040e0a020108070f11150703 74
    0x1524080c092100703d14944000e000d6518031001541c01360081c540030381c0c010845000444d0111194001c64200340b0080c0c0c10307000180d1508010010342c14140a10302c189590760b4401c101150b901d456189040c9503502145040688501800440e4840030060b1030341c4100050003003000c601800d0241e124020101002400b078010040100c10301080410303031004881d00000649110b46031040524042c4e070061200103600354509503a8011142e215034600a128071942c00d41a0300c00c4041c600d43d0750001c0092207103119240130801400721241c0030891200b160780c44811251194a15000203014100c4d40a800c1d4441408980c00024031180f806960211000c89204114903a228600300400e49840301c2c05140c000720801080020394807034400c03100d011441e031041c1c440e00a03c50751804050802031740c4400010300000042c00c50f900d0320b48100c511884210b801420a0303211a40003805e104002000e4134140315084d550021041d000e6007040340c0c00e0381404180c03103e901ea0101592041c03003041d03c92a0000c1c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514991807 1250 514990557 514990583
    0x9050a06050102060a0908041e0e04060b120a02030c1003020903030313150b1507031e0503061305010e1f080d0f08090604050a080d021204060204050415060e151b060103 74
    0x5a40d503c01c0c0741c91b1756041491240b0741820207101030b1001c2000048060381004424000840780b1a80c0141801a4490400803800184144c1006564503240411818076004070342020016a00001c546401440540e40c42c0d0020031a400158028055800c207582c1501000042003c0c1a895050340f0829030301c28444c408514241030506822682c1c0d96080751b801c810349441040d03420441c08050070313445110340343c885180344200808d000300006c0c0032404404030b6800300910506280000d0354540713181c5030074010400ca6141c0340803d951b802e0040c21203080c6074584d03803641d11110914140500604090021140c04001c1000b00a220000007808100090441404246900004142207015682000050220141940362011164091841495000da0807c00380c6101013a480c11580b0584c000e12005880e98602002e00041e601007100140042c0329043c01030080f103408c10303c0c0b00d041e400c0594034907a6800d403520004003140701d0b410700e0311408030074004425082d500c0080c0e014162480303614040c40c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514993057 1250 514991807 514991821
    0x606181103151e060d1406060c120f0c0d020714090702100c030e0a1b06082703160f05010b030d0507030e03120310090e0606100f020709050a0605010206 67
    0x6804103882401601000c04000c0106282c07a91040c42c00002940603c00004501000211581c0c402c01e6000905a1980d100c0c1e58880726441109a1010058030501d01d01484030741d00300d446541c1042041c03000e9001003012410864583d040d200c01e820107030f0481e081501003e4000c2d640d490107100d945612418520401c096042244080e03000b0400e035001402088604802c1d0005800031010313280400d40d5411805500b00c0041120640702d501070388a0302c1143c1c0d2805c4811800049580082090042d2102030048113a01344900290100b00c1d01410110340c1c812084282c00c510400000b892200d90350008801404808004020600d2141000b0081d03c0c4200080c107031106108601d10307001c40c1c0305015641c0824001d0703088070003200004095840308030000300b01c03410641068a612100c1040d2a0040c0800d403030a00c0350385c0f80a031303000004000e14602000001c0c50b00f441d40c404201002184a01402210300802450015000204003400f01d850305100103c0100030920803a4010710036580403580f2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514994307 1250 514993057 514993091
    0x30206031f140603010b0319050106090e0603010b1507051002180f19060513050a0801150f080703230706020c100c0c0e0c070b0a1b080f18010207060618 67
    0x800c00b40c0f446045a00e0b10780d0020300c3d900010800321491440c60038442e00c1c04014411079019201941b10441c0e00d40c10400300805c0c5030401000180030368900b41c03011409599040d601c0c428009c4040d22203946100518280d400c0402181c10300140b24000700300101080400c501040c1c0d808015901d03200605070704d0081004038030003003001342d030804d030088010310004d44550010140b00c0d0119400c408905d603200c01044900509610440045c1d41d680e14405041c980c142d1400000c0503101004144242402e1801e626005d582c4002030807409462100f009003581444461458000c0800780d0b031113666031307050181d00c501d040c030041c500c1a410280034068003405108035424094100340b403010307000d0504044d400c100c400546625071120007480341e080040c2e41c0741c81c10b9101d14110300c5c002c22107008100301709000c03944000c1d1003001d000c0c0100030020300060115203950320490346142030240300e00d0819698020720404502070a40c41c02c103600030421800401c0300c00c0400c54042d00070450440b1107847d0b505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514995557 1250 514994307 514994339
    0x81b06061f140c0102040b04032003070b0f130905070804020901061b020d050a0813180621020a080304030501020705060a060b1e121608090c0105040618030206031f 72
    0x45040b0307080c012a9000c401c80034040340e4088000042c9059110700c0960f11540081c1e104585103650745141e0100c91000d00c1d05100b030f8100540003415100d0800c148400d00f4014a0303003205503d1004103020f00c4070401e1005000c02403441010400c40760402c40d0380102200d100322010b03802a0040c00c0000b0b445442005d4179008128082403c680e07214050b402c005c1e1503038003103105503210700c80d056180f000300760b1050043c51403400c0e42c0002e01d8200d1408450920041051601d0000d207403404008102c0c0d20741415030750000501042550908108903c000b4aa8180da500407a2551001080c00704c1007110550040c0b60301c5020302d08a51180d43d5409244d07080d41c1d524018400404010300210411000c01070f1016044550350321b040381841403400d28810001d0301183d05505807655010340100782c0d5042461950000c00050243c049281c8000010308284110300c42c00c4104924101501c06403d40c10b407545020355402407034203030b4a0078208807295140100103907100b150703448440b0000d4482c1c40000901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514996807 1250 514995557 514995619
    0x3170a0e0d1805120a050d0504060f020c0906090405010e010f0218040b031f06090510030b060a210201091a03040c08060f0a1a0d030203180402120c0304081b0606 71
    0x2807026041505010090030800407100542c401d603140e01001810900c1800700548040c1c2d2952788480c5884401050400f646008100395040052003410704d0311030f604001d034014426134aa85a545652400d14010507a40c42010102e5103400c614000601c40703500209220390000801800c91202c4400b000100e134004000f9940c0b50740010340ca40860480303150104440741c02c203240051540e5036100d401c0240c0740701710350380c41c4081015403052003000446103900703410010075500600c0c1d15081403013010841360550505180d5110b2210312604580c8155001ca024000c0080780394003100d207401244203550001d40301150030320103a130804a60b030400042c0341482074030b032840196420744501c031010300100340b804a0212035040c1c0c80c000682729101c080564075050312a83c000d6984039046d01c61440c800d000c01c40100d210301d004001035141803900300c0001d0b421514a85040e65a0b846602e4441202c2c8181d9103051112244001ca010f00f100c40803442510441081e552000ca440d14605018010b50080b4400c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514998057 1250 514996807 514996847
    0x11802040b0a09060303020d090803132d12140a08120618040327030305090909011d1c08060303071202120c030309070b210403170a0e0d 60
    0x4025240a400c4441070200c0580600c1805072108148001e840d05904281c025920211001140e81c2e80140302d40300910000b405141001c02080d0704015555242c03040801d0144410418412145ca529104142c01b0503990010003195840701c3c900c00c01c050300320301075a01003030814405843c81e001080d00341c0c1c000d500c040007520703000c0b1000c0046080c110240461f034110024051940d20151715800a90003107000b51101c501c5062407c40040c0034045001c04820110310b080d20030000250031100391036814a08032042c00e403d90301d003540d1500415003042c0340c0710108103003070382a0b003842d0000c5007141c06071041148015040131481801e49201074282d46c4107406500070850480402d0258620683e401004d1054070750f41c100801205806411640d80b00303da60f080042800784c0d003081040710368000c0c02c450740e805007081d80d040c020140c1001240c0e01680924041400981014401c1c20340e105071004041151a040c1001100c0100034240621841980d00c200703001000168080c803880500d41d9903041007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514999307 1250 514998057 514998101
    0x30606050a050303030705160c06030912020c010c15020c0d0c030809030403021c060b03011e1506210e010c05040608130c062304090506090a02040b1e1306020102091201 74
    0x108407040d40c010b5030030340300403202c0c0c8e0900300000d10400004001000656400309a0385c5143c2401c000308148920700c0c900759448151441c0060f60080700300b03c42190008104160b040005030460301903c12001d000155000e44200b550041d500840142c000c140250707150000f507960382c80c2a44d924480c1d13010281d80074500340c156004c040302110a10102901c903400108420001c00c006c2425122811900340c80d04840921660b01403405205e80300d02d41c068010300556140c58032501a1020321741e101d040e000c1151a0441642c800415000916a001040001c01810603281d03001800b5070041e008074400240d2050202d0207907075050010000081d0411103034692036142c1041074601e003841c90702c1110203404680c120810006d0400c00342c0020b21050707201041a2410000b00408990000d10b00000184144030a0000c2081402a1080a040c1d0754400d0403100802c1f40412842c0140c82c8070504250091030081200d60303040d0060007410106451401c20001c0d4001c10a007622034800d004400056507000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515000557 1250 514999307 514999321
    0x6020c0f0d020d0308091207020f0424030b0403120c14181302030402040552030c090501020a03080f06010903051212221106040f0f030606050a05030303 67
    0x1102500c4001040016075072125400f00d0a1080d10b00029030101c0c20100030404151002e00c4900342454a09404921340303842030380024a034001081d6050b0050f40d0300c05241c07805080ca80101c2c091509803032a080c1207035550345419038111000b1502240060592208043d490b030742c601482400026a0b11021914252107000d0a40750308104003001c9034075660382c1524015103440714040915800580050b03501c1c51306005100035a0b5005d008440c0c81003202001d00c0a4041d8050412810030800010384c400301602c41026405015400e00e42514000008122000b81e4240d403001c0c00c2d5130580c1d120301d4401079070783e401661102d51070400070b404240b568000445100c40401555880041414100212034807a21030034509600284030741c41c0e481002a1003a880307140c40700341652080c00291000d01c0e844d0100068808000007000081680d500c03100c6c00340c407942e41c100695003e40210007001c421659119070506541825110542c0c0c4286440c0003c903142c10320040034001c0e54400b80017185192607110b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515001807 1250 515000557 515000569
    0x1b0d0305070e012f0a050d020705010c06050c0405060a0206040611040b070305030903041e082a010804231b060307020712050a1205030601181a0d06090c020f0708030406020c 76
    0x10079400411941078132900b1402d0365940b122400100080080040b038600307182c658035007502004101c05652101d6020003d980c0c1c004454000c43d40e105401050030348415079034280c0d0340615000306600c12404980b01ca0a603a0019403907124600804c0188200100b0340440700707580c41036029000881c0b808001e01d002182c0508021078210302500c08403881c4c95030360400006050010301b5070882c42c00c030301c100030052200c0c104900e0684002c0d08885d5943c006400f00d01c9000600f04044050600200c01c0c0040c0601989041044040710320703088840a07511018055522040413001118900030041c0310448541089000c0d24400c04881c4c0040154505113070342d003400c920071f4040482e00d910540282c030740020201140c44002d8442c1e070b04c41a4a9041000015041410429652080700035010741040f60320042008651400d81049081e59580302c9980c0c8030307001e82044d0300582201030902035009005035000131900c4000240c1e8040d115025203642d0a103072030b032241d4414040142d10410346404203207040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515003057 1250 515001807 515001827
    0xc090308180d02090907170712060b03010b09151c02030703060513050a0c0504180314030a14010e070f1b030f030e1c020f0c06180a0b1b0d0305070e01 66
    0x51210b4411002da80c0080c0100508440076416500446000c010682154810501020786600600700c0b240c24203001c1695081410380c041c0019888080c240c6040d1403e510404c110320000c0c000080781d1408885101140c90b0580300c03140110495180310000d40d241c81120840036900501400d0103500c2d60f10781c20702505010b419826000d4152802c140000d9040203004080da00c15040382c0211407a2108100c00c031081428240b60074030700c030300c2140002036000c44c40003000000c1c440b5a545a807280441000241541402c5110300b1289400100c3c2c0341115181e154451090b45e981c400340300c10540422242085482400c40542880303201c3d440001c0e0248101c0c19100c50586400124600040f900b03d107048083c1c98400400c5590744c1c09040711076414010501015041c40081c141c5d442d4100c00300304188102c3e8140e12280d507810001201c17a944410382a001002d45504980d04e4000d218120104c1524074100742072070f4441c10584030381c240c0c064065148a01a5900e402d420100a440103403451010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515004307 1250 515003057 515003059
    0xf0607020406050d030e0f010c1a15130203060f0a050a230604030b0708010b180f0612010305160815040807030c061b030f0209060316030b0904030e040c09030818 71
    0x703070748000c03520352101c22004d4506402a5101e5180494040a00140d810100b0805040141c40c0f00300701c021070b5041d40705680250224040c0c41c500ea441c00307902c01112641c4181e10343c1c031017644206500c142d00302f03802440c000e0341c00b1100c200b40c070320096081020171035407889003582000c920700e4204504801c50903418032901000c004100745500f4400001c07180d03803141e0821110f5040e0340080c00551a030100c1d109000d000358107445843d00b4058030300503d00d006200c00003840b5a034140880651903d501080d105082d980350020085542c6230320303015480b080079919264805280c00c1c0c00065080f0b0000d98070130030b43c146903403900840d03c4644550a003a40401010750034801a0756007003000030f02501c02e07809507510780740c07412031440ca02110050680b04a2080c4220190060000c861103075604822a600101c01c0c0e49071400582003100143d01034078003003d9041c0c0c8084840108002d050f001a01818074840445040080f01031801c0282c450031424040508411410300100000c41a00c043d2940c0d8114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515005557 1250 515004307 515004311
    0x309012a0906050d0f15060f0f05030a0b0609090103051507021b0616021002010b130204080717070b16020a060315030209090312131b060c0206031b1305030d0903020f06070204 77
    0x30035682d030307074140c81b000804807901c1000544104115a07102600c20304903401440c1510100e0300c1000010300e0360101030034a281d11130359101448142d5950500705ca41501c1d01900240040d80c6d68240b6580350b1880701003105414103c400001d12071407000c503041c0070401e0183c04050300303442240c1c24840940c02041c02c85003400f40c2069400c0142c0c3e00e80d010114083d42c40c0d4000704440304200184000300c02c2142500401350700500090181410201b18441130702c1260b0440e440b21020405d58a00d003100c140c1c040d922221000502000c036442001d052055a802550014003842da80c003011411150350090707008041002080c14401803901d03201c0141c011800c2070883e820f01c4a404001c0c03103001c1c41a14842d04d05030b007550805040205071a4841041000304040100161600c41c001e00598213007900207102e000000001100e40c00754004c0c0c0d014a002150a080e1642e1008132b01c40b038000c015010742c40c0f04e88a0012040d0f0828450a800c0c0c0c150b1341d0107841c004c6801b01c008180030998000c038200721382c005c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515006807 1250 515005557 515005571
    0x50f030c060702120319060512010906111c0e0a080a032003091c020313090504060b04050603060109180c060f0206180c0609030102040b070804030b0f1e04060905030309012a0906050d 80
    0x29489e40070b40070070303502c40d60000200000c603480e20380304945090a86801042c41071042e40750001218100d181503030350301680403410010b0351302210704190509034020040900443d003001000ea065111184124210070460103040843e000030409000c1101c080c1c04a500407110041c41100346502c4060024050044904080c4d10f4076110709000e00035006500b880d56160300704400e0003a18014008040d0342510200082d0070f2480c0801d80380c1c0c0c0e05010b00c6903550f484000e90b08505001e55a61005250440004032103d07440703880080c15206080400c4005108490220b552406205402d002c1d102041000b00a85004a02805050b401081240c3e5141d5428080007511002d0180100307012481040640d40d118103519203081e0002d0702174050a03080d0141810800c0c070541101003202c1c0c1909484900440d9960341c60220054550321070014018000031023801880401500324544040c101c50451988420100c4e880202d1094903030a6000110409420440140240001c10340c15405220100d006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515008057 1250 515006807 515006809
    0x32603011514032a0403020607030525031d0f1f0314182a010507050a021f110c0f010507050f0105010b0d05010e100b0f07050f030c0607021203190605 66
    0xd8004aa07400e00f0b08070710300c04e900f001000c0c0345040b0440e41d090004482c1030500f150040b40141c083e41000406104000a0384115001102011140100d00280794840929145401854100c0c6000c103801c550754140d86a4a0610f0640b200d91400c4802625070100600030003201c82104550861010a065030784580d024031000440700d151280c1e014881c48032203005060b00151401d8403000701042c40000442482494080160a02894603801d00e06161610a581885810525001c0d0002c2d801509440e1303185258000080500210910703480c0d02041c9a501c900040d159a66442c100354080c4461901200c00d60141c0003901d84a0700600481d250700c450441218211a420f0700b1900002ea0007080d44050050f00b03001c5d09001d411802694001f5090041c842800c030001405012000f407000301c1c40258010019003034625050300202280c01401e840d440c903e4a03584a00c003180040e006400c000f40002d03000052410350300801310300b080e14654402143c1100034001c45a0101029141c0400003a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515009307 1250 515008057 515008097
    0x60409020901030b0106180b0a0822060501140a2d08060702060604150819020310061403100e03031f0315020c0706031e09020f0402070b010326030115 66
    0x2852042c01135001d60750402001405070343c01d0300301850032042e10070310610440710010259103500d16141880074040c0c80700100d03200144c0403010302c1c040035400c2c00c2144051002e035400c0302e412104919415070301076038500c0900060404038010750300301840103460501c140c03409030076101e036861090705c2c02040c04e5114540541002e0041c0d4902005911150601026252078070841d07151310002c104440170303285415041c80d241c85410707075503042c0030305555442810364805005040b100e15400300200b04080d10b03003882c01c1c1d82e84010100d46000b40b0070300448504801c681e01c07070311760900c2904000710304554904101c0c203002003185141195001d0408800400503d04107440c0074000c030003800160b114440b4601c0540303440c620f58042070800d4201808039554030f542032200e0001441103400800d040c511400460400c404601110b5001403000410000380f21000712002e050700d114961030b41010342c404058170508110b02c1920041c00900700010012044e240e0140801e0392158100074142040200740454 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515010557 1250 515009307 515009309
    0x6020307150e0304180c172d1314011104050d050102190f0f0e011e020312130510090305090909100504060501050f01020a0c0b0a1e030603030e06070f0308060409020901 74
    0x1019203d00000c13085c01e00130f24040c90034608904e20300030f8411207800b500c0d00440130380034240da03054141ea007452003c8680c07107911444110b2070310750240d000c1d801e100c01c4000c03c4156403682034965000788890804c001c7c2060003070180654040100c0344c103180c200000c0007810155840d040b1107a42d030802000d44040c3c005014994140710b0394a401c1229091510080c2c0107018812803a420060302e1030a00c1003aa0308031101c0009070b10503902010071107008030780903441c52007080711101b403901d2103c0801146c0030391321031680f200520a10907100300166081d08002170780c881d800c3c02804140240414051030500c0702202e5440b500f03c00807a44481020b00235941280e005a800391101c98903100140140d0400c5429184800000c0c4003c1c008147e40d615098262407050041c1a03420300d0016510500300d1241d8040c510191015952403020401d4450182c01824644000c0b000709400c0c90041c51140f400e40b042d160070f260005141d0010301c60540e411a43c14400524032030340039541ea6091805601c841038014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515011807 1250 515010557 515010569
    0xf0102070f12170a0207090263241b0f030901120b01030e06070201091b141003020d021303050c0f060a0804020d06020c01021e0406020307150e0304 65
    0xa07103592034904000d100141400c9194003c0c24041064400003540003807a082266042c0d8001a1190b02c220b07000c080090b0f190741d110641400903040c11480c00c8241c610404101e40c08c865820301d048541c13000c3c000051401020b90181404400759000500700080c1c120320294003410318102100742418166501e4200007403040a48076180803400f155001000b500c549600780c40011800c08904c4400202060401003d1500c03441e00c0e0064051183d010390401046c6507100f405541240c80c107248000d000f003040d0307202503039641403105888540ba007440c5111030a5582d910300324640b082e454003e0102d14070060344100b041603400c001d0780c01c0da081c1c11b1003e4080e800c05103080b94102499410400c0c540310503140d08600c12000440c2020481d5120000c588880c40b403420104040d9696000041307501c0da0401c40540450300010b0302c1518200107500502901800200e90520740482030300d40b50041c09a80500c101503801000200041114101c0514401104c1c074008501d07a40315203000790458016603c25 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515013057 1250 515011807 515011829
    0xe041b0309030e0a05031905010b0405040f0b0a140a09032706031b051b071802030f0907050307061206030f0c0e0a11040e06010c0c060906020709050906060f0102070f 73
    0x1000301980100c00803a008411a03000306405d08200000b40c40d1010803010350440244040b103101040021b421020348510002c104104500c0c00382040500035044040880d001016180040c4015906104071484408130080c100c41130760f10321003800c3c020030301360b001501480341d855440a06880b2403000801c958054440c0e0b03080d00f40c94000c0250542c0c1c4120911180021020500d45010b039000007503400118041c552208244000c0c12104d0400703115801500036003151800001104400350001c500441083e070802d401c5a951499003526102140501da032b164008410400543d44159500ba8043c00e1b46440001c5039a0b0b02c2da10b0114207045040308607a0030040707074001c002d50f0f610781516943c000c00d451020720028500401c540e40612031400f550b041100e614001c5401c5901c9081303aa000c030380e8005a01001a62140c6002e071402a0500c00c8800511030101d0100c0c020041d4020180141d040d41d006085680350103042000a8105001417030440c880c0c01800650144000e50000c0100210740341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515014307 1250 515013057 515013071
    0x5030a02031522140c070314120c1206041803030b03071707060f091203051305040203040515061507110f0904030306090c0c0b070c030e0315090d0804120e041b03 71
    0xd8090b1089094408075400c0c204d41000441802e20088a000c1075040c507050242c0521405140101d0180c0103025405000787c4080094031407804004000c80b406078490000d15585900811040e9110070800118031020200782e500000d0198010300000e08000b0107850b2450b071980f14036603900b00501c0408040c4ea2144108100d01c42c1c02101c1010940c3d034620303082520318100080d00540b44070115000702040000994000c003401141115000381c440280b00b0340d0340e82041e0810783da8a000340413040e01e2001006c0007240d01031074035200d480c17040c0990315030707450620805031161009411300a1001c6d4120f0000140c510b003a40c0e0314040184524880d80f4005131040c00c06140000300d0704910302c0c2030b090081480703101001c500c1c80d450081c3d0001e103c0c07401e5120401c01c3e10302299031800b805003041e0148150100d80101d0840380042c20300c110481800c0304c030004903911044802c841c042c0d90181100a2140241001a2080300c28241903100680003145e082c40d407500000c1c800f1b15850310307200000d41d10ba407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515015557 1250 515014307 515014369
    0x515060a090c2a030c030f030f050a15320409020301050c190f0914030f010609090314030105060405060714061003050c0102010509030306100c0b010602030301050a120305030a020315 80
    0x40401451488030191495880b540d4083c5c201c40d8001d0b00034050100c140c070b580c0e44c02e5210303400801180510000500807401d015441c44003800e20b03e007920003c88490b4801007405440084000901d1030840400b5049002c5d00d4441d6400b40308610b0000c0e00b064645001381e005d61001d00904d03010b507504041180e0b035041000a800c4032500420003501c00c004d04409000b0840ea0321840d2801130311641180381840b1010300380082d10304034620072195000c0d42001400108001c003988010041d40c020f44440040950200c00f41c61544404d000d000d03842102440140010705040380070380f001d54840c0c8e2400030340c4415840340615145080b18000245840c902080c020400c0501c80121003407001c1c002406581400c0303403269205d001c010305031405910402d400b581941d00c01c92601d014030750041070985046d40c50b88402504c0754803d000d10b5000e101817400015180954003040502160075036501c506580310b0700c1c100b0700a0b44c40640b111903004078a103a00001d66032412124980400c0540c50301c000410201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515016807 1250 515015557 515015597
    0x1060305010504210306061e11071503060509011a071b080c0f06070f02100c0c090b0123040b031305011404060f060e01120c0f0605250515060a090c 65
    0x1071491380400d401c02d00c04211458100b0346048418a1420361440040d004074002c4a4901180c80c950356984a000350000300170290081c045040e00c0c9698041c082c0139203413410f100143e007080c8031b54804000414450003000b400700014004203442200240806540301d10804000304484d000820907410501c2c076280304e0718109074400c5402d40143c40e03c0e030428540e5120134065041c0c0c620701034024403140c140100950700c43d0303c2c1054450380c040e424884285d1a400781da0300501109400038089803080403501d2200300c0c030000140c043c0c040c40c003019140a080502c00c40b4560405402c2da01c0c80074144641000250080c0240100c4100640e0348000c50324140c1401e4041e10200c12160210900d0040700f03100d10415500c0c428151440c1d941c1c00e81015107180740c1100c01038120780c0050903002480308081400e42e80072004100700300300300348100d00c1e4016000c070b581d28484c2180030081113a44032258408503503008036051544890002c02042c52603549a14074820b4414402c10b070700000310720300c0c141585201c0b16 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515018057 1250 515016807 515016863
    0x203041a010b04180501030201050702101b110a0819080c102a030b030d1d10110f032b0b0406080a030809030a02070b0c010902031b1e03030a0f0201060305010504 71
    0x1c1c4c08184065491a00083c1c12445040d02c080d01070742d4445402c1e6865802820240d48005907503500d04004095810042c2020780b2000049104000418001420050007c3c2d140c0c180e6030061003560703010640d0360300d040040c0d0080e9000c241c18000d080400c1e0242c01c05100304070802100c1d01c0d001400d2031054507101c804503070400200f410b240c517104a104042e100081c0030ba41c2103545062071105450985200d030701100616031110b40c8043c1350402c4440007035020060804008802d800c542c1541992085184c4038060450303c0c0031543c4942e4554241c44601c07002d003501024001d40c0c0016602c490343e0104040d20129003015001c1d602c189e5203101003550281d08194805900c501441c1000e4804400030b403188900d1054034040000842d000c00202029400020015402030031681c0021341c081110000c8000313558168032540789000c204168262030844012108401006145001070152041d2202048400322804566881d040400054002d20506020b203014030b10607468803480a00d41d03480c590403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515019307 1250 515018057 515018099
    0x160c0b0304060e0d020c040c03020d1d0d02010b010c021c020907111006080604030503040c0f260307020102060432160602030a0c02130b0d0b070e0d02060d0203041a010b04 75
    0x4080095131041c1d0202e45d14980c2d0304120f9000c00d101c00b480380120040e00441420f851618030306030054030744141c078842d0700c4000101e14047e83d02405d00c51074142e003240c0121240c00d01080c80e5250701030052800c5039a454801001a1000b2500c48040c0c000c030382036040440c0c5100125541440c1c46902403010000c8071005042d00c20700b849842c0c00c08984984807403016000038248400803010400b040f003003044510140101e080e0100d005a070358910303d01c0700d929a08040190007501d82c148080c005000c001c07245100d806070003c020310341f40c071b59510000b00f070b010520000c1001c10140090345907038614522070106002600a09d10007061007004412078015078400b0056500802107a6649078202082001142d012074000d500450031813800d0000e040c4840f11a6880307508503000d04204150070103064001c804681e294040504020148002009100006940413405021861808680b0380055074040d110b251150202841c400652a0a071000e81140c60030310000b042c103104d202e000058603146464 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515020557 1250 515019307 515019313
    0x30b0907050f030c0303190c021306050109050a26010e030a0806270a02091807081009180f0206130303090e090d0c02010c0c030213020d0f0204050312160c0b0304060e 73
    0x24190700069070f0787c400c0e01e8824158201c5291905545401003100441c5560060402d1240b03600b603100410050065000f100d0204400b0310021a55041085040342900d1070b4580c9000108201500d44183c0e80c403420401a0641d241d104040c070a85040c030250040f040c158850800030305003002003082d41c01d02c0e20320702e00c2c0c10250b000070384030000a86051280c00000d25100141d451060802003141608501044041c0409043c284400242e000b1542c0348134000700000b40d452075449041e40c10699000741120340714000c01c2002c100100e0110203566514920052040740303844550507442040c0c2c501940141d02103036070002e041001b8042060038592004020000d40340b001c0030710b000503004420f0f0540280c100001250b03108100503488080402554009210411031001c08102201179406051808911401c0c61024580149140280c0c1c040d1031008014013150040e19480c5441e6412040a07054081010043c82d00802c1000c051400a0601f40400542d02c2c038050800e01c041d82c030754191b240d0480d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515021807 1250 515020557 515020573
    0x307031b051c05130b0405040515030d0e0d0506011212050310260f030c071215090804090c05092707050d2a020d050a14090406030b0907050f03 63
    0x5002054500116a0020161581200c041c2c401c680e1400756034100215080007400208420042201030310840d90104c07828030103a51081c0ca50217190744041c00303e40e0141e001c00c0b90485240d0007961715804c8544081c2404840c8000754865a1401300281e200e02c0c0c000c081c0d41040c0f07090021185e145c04061130305041442c51400c0c800d821900d0280c1c01e00c120f01c0043c48216404000ca05607060545e00c94004008403022905010040d85d1658450b00c03103094144034814000508990920350a0255074120306e90038444220840403802602c0c4020040310f03110740400001c03649000600c624072090b0101d0382e58035101c4100c4800e100146030301448800511003441800003000301000c0794190b02c00d8003450019100c603076102d0070ba000352034103034120b01c1c100e0002c03a02200c038007480700c41210715001241d00701c1c0d01031080d81d03909072160312603003c11a0008030300924007151440d81e41c0040002280c0604000340250752502d580707004101c01d813030303001850700074220400540c034048480b491102c0381200680521 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515023057 1250 515021807 515021813
    0x2d0102160f03080711090f09100908031914010b070201081b0315010203210a11040e160e0d03080915011409040203010e070b070515010302010c0b1504020c0307031b 72
    0x101e11280320041100340000781c01010084800c4036440c0201028000b03a00c01c4c00c024125035441d0740c045800d11070501c0f031041080d1410403180036070f420706500800100d14640f2000e5000b01c22074480800500a03e89031312010866002050000d8000c08606110381d403500c12510004200e0703980a030901c04c0101282000070303000d03c4c0000031240c2040c441c28a1700d84200102006074150300840440300c285248140480b003200501d00340240c441c4c0c07070b0075404001d0102c0700c0c0084001070099000c1c11501d10400d00004010b1401e0100c1080040441d00b0851a45604140014407076000e0240840000d400030051104d05003040082c8298034070f01080c081d14940c108440303103031901c1400059511400d540713400318056403403e500007241d0300b82c400d09580090b9194100000c0039070216030304655500c00c07100d580c042d1143c0380344071030b0589a0594881d41c01c0540e5032035050f82010301501c1c0000c1ca031030310303030020034140d03620b200420000d6030a101840e1030355440d04010740008040c0180c0580c20013400140c03800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515024307 1250 515023057 515023079
    0x1f05070906091e1e051f02060705030711030a0e040b03010b01052a0106080309120c03060703050c310e0606040314070305010e0106050a0501020d08070305062d010216 73
    0x2e40d5400042055040c60360150150580d4040c0e0003000c804c2e0401d00080c146483d182c18000a644080d81c084880341d60340c4d0f9034a50940340594126005070880f40118400c0380c0b00f4001160404034034981843d0201100d1019815980031250031000700b4003810882d03085040502171089960021402007200d0304900300040c000348690341c018503043c80b445c07000407803000000c80b440400394820802084901c1c1c841c44016542c1d404141c881d0700c1420380c40d5441010341c90001e5050103020011740503003c01c0d01c64039800c2c1d0140c80003500024101c2014030a80034050030607942118a46045454a202103414840000300038600d50405c200042c1c000003082456100c0c8022181142da110074049080000040c0e9281880c5041c0c000902c25420080c002c02c5402054001505640c1c0895081c1c2c0307001da0300e20043ea40d90502e03030000004500200c001560041c0241d0200350711010242541d14140c111001c010042c003541c2007500511840c102030300300c403964108200314080c20007950001100d4180104501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515025557 1250 515024307 515024309
    0x7081b0a0306080609060a14040305040e0403050409140f0c040e0c1b0a0f0c0603020315011d1c060c05090604120204091a040501050a05060d02040e0a051f0507090609 73
    0x100940001031200c0c200d4465809440205800c1003559280c1c103010004d20b4486030155040c20200c0e00342280c03e104c1c0d010b20411180a04e0b490b4650920341480e203c41c00070014070091080e42031190034000010b4900340340c068290302502c8a80c1c041c20a10700080b0050705014050b16034070702c6100c24482440000d1510741450b270081c409880c031540310714070b40344036a1449032075883c143c809002e0b541d94042000030140884811034461b180c0170f0403280e10b59208800304e00046554541c03040e6000d0100c40e0650040803d80e0800c0c2c0d001011140310341122010504070904031080240e960315503556002400b02c24806c401a0051a04e82203280007002d9001410b5801030340100c1042031140c4c4070b80350443d03540d94020340301c85500803101100600d0404000c3c40d00c0000b29000e0f2855420000007403100d90381c0d44a02d5220390302c010804000c0c0c561a400f40001041c03403082880c4c40d8490a002c0a0124108010408401307190241e034805401350b0a80c00c0003030b0340d0058691800d009140400340001600410040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515026807 1250 515025557 515025601
    0x120206131e0c15020c010206060a03060b180c0a090f1d1806070e011704150b13020f04081905060412020c0d0506010f060804050307021210061202090708 67
    0xc115501c960781c46204041403420081c000102c40d1000600000800418900b42040b9025101031004000042ea00c90608448096000c13610038410300000e180740d4080b050003040540309841e0703990350185240d00c1960a84400180f4080031800e060303866800042e02015180b0000611a0240344c01d610b00c10085c101a181d00004103088009a05045042000b00001e00000b04444881c1416a00600a0340d4408a2180043c1c0c003120b4010107031290000c0580101c2e40301054007031502c10200707610000e2a40b195141e074441414810048102054005401d0398003125a465a44614101d8401e24058a80d075222900422100c401d201046000c1800da5126400c012650104149400102d003401c50901800c1d51040509070400d01b80240021190b060300c500d803200d044029140c1c03030207030348001c0110380003882c035031040201d00c0050901610038402e02d881c0404440b455500c840c00070701584c0d119006018460101810343d000c0d07240002c80181c05c48140d0610000718140051405900040100c002d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515028057 1250 515026807 515026823
    0x90f0702030c01090f03030e0312041101110304090f06080a03020a03030911060307091a090f0409020301060e190506060c0d030c020f010e01023a0b010c0204020403050a12020613 78
    0x559014001d1007102d0703004003080c0003041107000c0361426460031055400b0580c0004d2038000d140e01e0018000040307a5a00701d420741e840109903200c0d6640740210013002c080504208030341100724010682000940702070321044401041c40700240e2843d10403190385a105100c961b000d084042c02003038011440c181c402d605460041841d40c402c2c200a03201a42440440b908120004100000a40d0010207007041d100d08003407810a16201820005160141d451019480100004001d100d4030b000d60000c180303031341b0140004c2a29940d441c80d602c0f2840c02110a5807041d079148a14138808001c5100310303548580101c0d51103013410071803040c1e1035981074403141d110245941c1d0114078025900802017110042c850700001d0209200c52071515020750461880195020f820060030640580d005400154400781c403a40403100380c01d40c5104002400110409030f040c0500540003d0158481c0d0009101541c01100241b15540c25494405034140c01821800219004030042c0a9106182120515002d07040903003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515029307 1250 515028057 515028061
    0xb030d0e18090106050916020d0807170a11031303030b01051804051005060307111603050a0308071b0b011d220302100c020f060c030411040f0b0325090902090f 70
    0x60040000e030f08001d50050001c42044001d107100ca51142c3e070348004e503003610701d010001d1270705951020080e14420049401d0300e00c2c0222598540c0c000c0c6030300101c0b840b00440c06c09045845215640d0040c2c4040c030300121020f00c00024103405025a40d011a020f1a01c43d140031010410b000204115407200382c4a00d03116800b290101c0040d01d00c550290900402c0c075903890400c3c00025201d2540d14424601074002e801c00312044c14141841c0d0b900304c035041005010304480c259812940510010203110a1100c0803040403681d411940c10840228443d400600b01da50502800c1c50903200c7c694880f0106502c9842005060489020069540d1040c440080102440c1d45000e03400e104000c0c032500d500c1890211040c6402e2b070300240152a0440c06400e0700c4580d110a40d0500c40c51000b110041c00c18245d0141c6161141060392000c0128200150001031948450300080d007082140c00d00c500c20b40c54003065501481a060b0780100051400d80403c0080e807806034045603858070001c02c0040d01091703240c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515030557 1250 515029307 515029321
    0x1509012102010c241a0102030301081903020a050d030501061b2a0b0c100b01170601140f19110a03140d06050a06020a110609031c0504180b030d0e18 65
    0xc22000158405800c0c038101c0604c180302c00c1c3c018400c50880c01e041040c510104c1405500100071a41038580c01c10162000d036060280e0406000d000304400c40841c0308260709000801d10501010200ca035280e600400c2c29490321000500c00000b03401e200d242903c0340030080000400d00304278008a21008100c05124800b680402081d090840c1c0c4007814000000a008140200103d0102014040114100300d24454040115401140b280141c0d0065a117100421000d40c015552400020550307100b02e49007903003400b40501240c201041c0400008800d402c050170030760b04a04910350f0800c2c0080140f1110601ea10000c0c4800d02e4100380400c0c40200140d03140000d070480e00404003500b00500003c110607581e0340003e540b2160120143d075850a10b01c01e0a01d21b01d4040129201c401c0002d0080503001c1d40d0340000c050003051428113405110040000003a95000040c00303010b40103000300e001400285400900d410404d0300f801035401c01046901c010019501c8010603d22030500112000701aa5002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515031807 1250 515030557 515030573
    0x90705120322122114030a0203220809100509011d030102040b04031208061e0f01020115061709120f0f13091d0a030801090b060706051509012102010c 66
    0x508403d0000041c140c114091140110180000c42d403144100220850205000c440c2110005d00700302005c0001c00110f602003107542c003d19009030700114000c0f40d608604400d501d001c06203490845401001103016466890702c41c0b0301c200000f0303141c01c10b9881d01c245d0b400001c0c1040b010052043c4c0d400078601c0d10380001c1c2c4095060341d0103441041449a0f84d00c0d22410012900f88805a180d400280c00340b0000b022401c00071012100304000220200d4065881e80800c030407401545007041c110f40d40d03039070410104581000040002c0c40681c489501c3c16803c001001e04a800040c140001f56000301040381c85031509404a03000c006250a20703030780342c400c26440086140720f4100c0d1084a034550032004182d400142d0300002105081002d1002d0294881d00381c1c0341c951001d980c0240110300410010001120b050300143c2e071101e0010840d80c6003001c0f5941c1c14045883c2a540c08807400c10540341c6003204e0400b4081f40d405011a030160085002c0d02c00e004803020158084002e04000740c0340c074030504200280b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515033057 1250 515031807 515031809
    0x1030207170304080415030612080a02012009010306050108090a2411040f1203140d0f0e060a0b0105040311010c02010c1e121404121b0e090705120322 66
    0x15441c1c5540e4102401c140e40c450700507015004841190341c240c5401a400381c810103040b2500d031100c14640c40601d40f900110b41c3c04c608460400d41d500d0318000404500b58122815845018500854440d415840014103c03211600183d051120010500200310300010303403c0301c201d80c4010801d298001681000c00105141da20141c42d01d4200741c641d094000c122406031003660171007468190240e03595002240e10716101a806400b24210100680a07101404002c11240280c440086203414401849800700d5086511800c2e45401c10002d00150a26078000c3c0080c03200d091926500701402e58495a01059103c440c03241800319100c0304104690251100c5445a6003203048402c2032074440d0010561204106402c50391500c2c45c2d50028089070040900e5590035079820307011380c1090b041401440310320445079800c0c0c0c0c0c150050000f0900061000c005400a000884039146450400d20002da160104941005220706006102a800454000145c54800d00d80000800841a28008240c425019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515034307 1250 515033057 515033093
    0xc0c0510020a02150f0a0c0e100224160c030c020a03050606010e0901060e090618040804171b0103020319061202090a1b2717240601030207 61
    0xd4220584003001040d4081d10711601550259400d030840d54015000b611360071a90004100e00e201c010a10164a5510802c0320301107a041c0491070400132030000d000d4480d0b2050080060b48009078020484504560041600352501450340e0542440060f0003420301c11000e2074010094a05040c030240340c46010307582c07202030300607220015403622410032a40302c403000c44441d8085240040c1e061843e042c54000c840c100d607003698500425011507400c000c40749901030038580c2c1c804d0b00000c01100300d081c1000e18070b00540c0300c1c089803a0b0303e6190029481e4200f0403602c1c665400c2d0000118120302030110740024a030403409280c01a0350348e030341441c60045024a1019010f42c28a81203002c00d28022145440001074003c44035100030782d81d240550001e503210150082c0380ca145000d4912100c0d80910080d80106c10111400d01034100780149000304904681c0c00312001008581a442c400300301446002503484400100b10b441c1c050840190311400b0300604114100750f030001d1120140190307209980d092070303c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515035557 1250 515034307 515034313
    0x20011509111c11040e01170a0b01120f0203060c0306012d030b130906021c230606040305032205030105070f050906040b0f19020a0c06080403030228090501090e0402040c0c05 76
    0x14a0b120a201c17104030034016403040b1600c0e10101c01e45282c000519081c8194404045c1c54160300b000c991100c210200c110442c1e0904080c0084001a0b40174041c80303114242d50754030b66840749843c4000401c2d40c4100c0514008001100d400704505000300e507180340c68400030381000300302c6201c0d0001141007149000011a0310a03e031460040030043c150b0010302d1001029641c0c40b402001c41d41c0c1c030104490181140e0366500203606400c6d00b80c0d0191482d802e5005500801b2142400d5803a160701d819940700c05131810130314120540000010400b080c900001e0300741a00200100d1605400240c070304035482418030148070010a5850309580c501c000c40d0003400b0040030301511400e010300440d08a0b000701841c110b80a4109640703801c000c0c4001010b114580d0070498080da950300e84042640d001102410517020076800b00240703602c040240c00c4954000c202e43c0c1c04400000315004000300320608075001181041008901004442600315410741c0181e01180c00154001e9818419164510700c0400148940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515036807 1250 515035557 515035559
    0xa12090b01050f010302090901031401020c0d021c0c032c06040e10050301140c03130b0c09040f05270307060513060605030a0201080703020a20011509111c1104 70
    0x4040d14500e4100c03071056a11100b6050b2010041d000d80c015006075640210800004201182081c50000d0081e18101c00045c608140d03094040e040507a9549170002581c07080460f04c410340340c100184420601e045c81c1010204c105a6030003480d0000c28503007a0b511003024440124445001c0038038403a1040000c21040c1c2d02c0d0fa13141c1600702941d8080f580c0364000712211034005410304042c0980020810b509842003002e6442a100d80075540018240041e01c02041c48010005110041218000c2906201c0c00b42c89032425402c1000361152000d0350418141448144880300c8440d6000b910f0b081d1121800b100c0c0b410540d2159461802008006010305040109010100c0c840d10f01d5402c116000300810300540740c441080c5030380c0381402c9034024006002600003a5840b8401d60103401c140c9400d250442641c1c00c088034a0000c200e02114020450350354004042c01001080e04640081c03c028030184100d1071545007145481c068209102002c8030707907403c05141c0f803c00f46d2241103a10307030305409a900e40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515038057 1250 515036807 515036813
    0x80423041d010506101704030509060301030f0605060d120c170a030203160306030804051507020409050c010f230319020a0302180d2003030409050406050603150106050409020a1209 79
    0x62110840401e5540d4a880c0204600e17061040e03400d00e0001c4a034444103081c400803800d24070f02c050010001c0e41005810320541c01c0d56035440300294001c40c0201c0c001d95041d07015007401c404884000c0d140500c1a4500d50003000002d244600109c121111420010301180c5203051042c0800c2c40d6110025198030001003440f400c9405034007842c003c0c00803c58003c40049440005d40c115441404040c02c00c42041c0010001440d128281c524100020300d002410311000f80e000c1000d0b00c0321038600301c4160b04002c1c42c0c2d5400d540e1001e04c01640b43c1040c40e2050030302003001007084842c4200c4c2c84281a440001000884110700d13890300901e445c4001004554400034954010002d40001400d0a80e203070594000c1c825a1810400c0c015032650854030010940c43c0c104a16100241586966030700f500091100003140d2840c1d101b202d100b540110404542e030b283c10301c101414040098011021003140c1801401000c0e40803050350145d60340c0d03e10042e6515a180c80176500d4652000d01c0c8412641030007400d40c20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515039307 1250 515038057 515038091
    0xc030408060f0601090f27050a1a06040e010e0c270312120703090c0515070501050c160b0a180312050c0a0c080f043b0408042304 57
    0x11039100e400803100b06459890044034400ca1510520307080343d58840301031200204c01d5104440b614140d2002400841a52480d0415503d080b15001d800565841e0142c04030742ca11042001c1815089900c03900c1d141c10311801da80090700600617881c60284080000e445ca0740c9007400caa000e04108900381c000800220303c11009040315880c2c4034042c0c09188901412801d520b003d0715040307140d22400d9441e0b03548200c03084008000d280800d8410f100303115800521a101c40f0040005002c08e48003a079603490303060401900b5204050442410008100200700d14001004400c91a841d4420040003494603011044009408403120120441c11504140c41c20550440801001412030800611107a40c07907003040d403034901070781d044400070070b0882c4817890000e09804001c1c000329196804007070516443d0b100c02c480c04101c2c00c1c40507881c10300d92204029103004210044c400d22200c03d82041081c039080d51062204e010340e200304081144241c050504c541d8452980c0c015014019008005c01401d1610380c0c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515040557 1250 515039307 515039311
    0xd0203010e04031206031110020a081308070b0301050a121103030f0901111c11120d0b01170103020d020d060b030a0c06030b01020c060a140c0f03030f130510050601050c03040806 78
    0x1020440704092003413981e1040c0101022241c001d440003016040305818410f24030b0788c84111004502a881c0342c5800202c80c04040c04152001051005000b03046c0040b80d03140409580000c1145442400108125030340c0ba49100241c0d9000344086903044060b141006400390310410459040c000030408a017040c0322203001e00002c403401d07a1440d041c0070514000c00d07121581020045c0f8000c5440e10220060360050b10419900503404080f21100d8400b4825040c1a4001d0248415001d407616401d22039903901140702a00350110681d00ca41552640d0f001550410070540024000c80a00044405026883d070104903030643c003400ba80d070b12001510705810106620f005201c0801e00d407141a9540d5407000804d1070000d8805002c031450400303d140280e811300390341d040c0302100b05d00070001d014492005111000382c0c000c60340000c50301c0781003000700c191100000804c04400004d00c1440500442d900061112000f940001c00091a45030280126420b12030407035429118400090001080308001400e24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515041807 1250 515040557 515040563
    0xa06110d060b07051b0109050a290406020a02041d0307030e0411040b0d09020301060503030c071401360f0806041104050618090c040c020327010c15020d0203010e04 72
    0x2080b521031122003007070700401501400030740c403010148000441c05041156a51414104000900d40d41c5c800110001038541101e460214485001e414254102030500c103c282e100c00c1450415082250080d41d84c0300c0306501a1060b511410740c06001d00040000d942190459001e0302c4c0e660390181000b4045030810742005011383e28140484c1540c0340d01c501509e040d24449041d145c50207010f51801400387c0704840c030a0303038103550729000020340e5a010001021060700c84405054400e1802406680000d980002c2a0610942500c1c514020440e0300c200c0d4124150f5005080c1204207151140381c3e0080356070440c0c881091400700104590a0000d1041d00c502d214090079035a01c40590b082c001560700031340e80310b40c1109000d1039140188500c401c140c3ea00030b080c9002c890341c260510000405a4000e0201d0b0005030f00000340540c0705452110160500c200400c0e00000100f01c01000203041507011140038014103000720500c20461116011036064000040e0207549950f100c103208100480252411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515043057 1250 515041807 515041811
    0x17041b14030d020c060906131205061501020106051c1b06090e0a0204031e03051204060515010e1f3501061e080c1b1605030a050c10020a06110d 63
    0x2400c20b902c002101070a010780034000504000101040c44215040900c240c56603a103006408030b8090704845072901014050001000c3c00c1c01c2200c01d907011000301d203503520b04690511005000780c1d00c0b04154908140152800c49403503001d0350030003080e04116458045035501e106800090041d40c000c1c3c1a40075191200500c1c80b007615800550302c1244610702c401003d450b080701040e02a2008800340d10012030103410030914040d8051034131080c4000840d400c4494907504d8051103130051038855412070707a80d030038200a01700041c0500040d410200791150340b0700485c40369200e404c1c0203114042040c2d0798610308602c100c01d142d5000a40b00110075000d91860003411140001403c5841038001e00c4812503115016200711801e400121a241001400d0b041c03055000c21031003000110481c0310003000d40482c030242440c4040340042a00d074000c04d0307111503c00d03070068100c0f40203c1d8001c240f500c1f4500f0115059584412050700c160700740f03082c803070000c0d0040b4541a406e00280e00c0c03590003003098003198901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515044307 1250 515043057 515043073
    0xf09050c030106061803021507050a0c0e070804020918191520040506070303110d051b12060d030c120e01080a0e0c10030f021c0c05090117041b1403 65
    0x104403028080300480e01821700340c0103010009424613001450002080b00005e520b400d480c0d440d0b107032a00c0a08182101c2801d407100041065400e5034034038a402c400b440ca072841c2e80c4d0405800141031048060106950315082c5180b10704684810404081c099200d100d0172030210000741001c901d42c04062452200850801440303a00b040c030110340a08031141805419800d0500701028058503401030b19041301816521812040a1518130011303210305142200003140394a400822404040501d200507a00100d0a11484000940b182200d9502c20029151000c0004060400f00c0e803030003101d0302c0600012030513680c09910039881228000405c1d02171301c0345c900e103840d40d8042d1401c0b140200000c0340030742c000b00904201c51410040030010014503280c0481e076002600c05000480e407101c11880741102c44445107542c103030014058030303886000608201e810245e0f00c50001e04000d89456204102a803c031001908000400340b034000120a03070b08a07003036207640302d01c45d0a140380c0511801d28440e1240c110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515045557 1250 515044307 515044319
    0xb191b1b0f090e191718460b0c120309070305070b070201080c0d0905070b04050109210b0415090b0103210f030b011101110a08310203010f09050c030106 67
    0x1380c002c0241d6488036400300625a000d42c00d1102e80c224041ca5070b60103c0035400b1342c2860b03407401c9668017000341d103070f0710045000d0a0000d07000301e441002400440300340500300307030701240c40840f6520400c5540c00c01c9042d80d0785500307000c03071410000004220720110b41c1c0403080c0940c40400285440550b031041085554441d02c50072a80518013904d400240020410b00024015000002c042c1c640e0107064080410b03125002d5452a00302291074100e4104402c0201d4200322a43c0e00204500043c00c061801e2060000c450b041d00c02e000c5c203205006070409210308042420441d01008266000080304010401c8506520340341341c2d240c000b0710090b80d9044000784100b01540c142c100040311054252640c0d41d0254400e035041c2d001d428400d07003503810b0103840342007529420403e0142e4114404586002c694030340b80844082d010321707006450301c140603d4408948510810084030800c8041d00907000018240b0383d81b001a000d0040c0c0034000246508040c2c3c0841000380003d078110700078004a000340139170350700e0302c0f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515046807 1250 515045557 515045593
    0x80f060603030a0c060e0703200a120311100f050103030f020303070207051e06030109060e0718030312020403020301180308060d0b130302160b191b1b0f090e 69
    0x3944065058004200124000303025070b880001c2a84103000c0410640300d906480f5041c80c3c0c1079802900c20300e400c5000542d040401b07074a1504540300450701161103030f041840710380c45622802001414465413211080344e401c420001035000c07160115007071155404500c84400909420b10040b030128044c0b03404580440d001100b560b22603401540202882403410040000b992016031516402c040300d015030110503101d6600942c00703030047c1c40002c68030342c3c9800d02051840c00d00405a00030041d14a0451205102c00c0c0b890000701ea4040c940f00078030a1148c40c1100080c880c0360b000039407640c41d0095181c0c3c10a200c101a0301418025220040709646001c01d1004540901c58014038841030300b0002044401d0003000040454000c2c4102c4418080b5810102c640901a400103c2c03002c0b004510490030200a0380700402c80030182c54007560b41d18054100c900001c4240300020500000b400301220800140d0b4034070001040001c1c1d200d501c00d82d660002500034852260150440e00800720718030006144030b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515048057 1250 515046807 515046811
    0x304080a030c210503130c0b0c01020702030c120a061e06060206070e040509120d0e01060303091e0b04060f17010b0d0e07080c1c0209010b030603010e01290109080a0309080f06 77
    0x158039060302d142c0d43d46107015110505220201c1f006103071503001161281550700602620900c4a00060b0f660046004141c40c0c0b406842a041c4513100003100c146000070082695609250b00030700105000000b1041c10305013140e90090f411055142103400540c0b644c4c002401c1d0301488103521800c211a080b40b05000036208201e4000d40668800e54184850030202001440000d074101c40000385005032621890a40321668820360014000140034403c81917294002c407100c020a680303100c0068941ba950035118003030742c4100020300441009400b007050051117031a051450580c43e8034460347c2c5851603c0140d401c00044010340602d001c060a07003212000074100d054610181c0200300d00351000c1d04100c09855503070105042501c43e1104140140c903203c10890283c40403035207203510b919010050500310b070b40c464002d88543e8104540d0b034096202c8850401e00c0169061101404102542d0068580d44659401003c2c02e100b549410028194040045000e0b581420280c0c2d04840101030440c0c0d81d4801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515049307 1250 515048057 515048123
    0x31c0f0306060914030a15050f07020607020a020f120601031211010e0a06021c050403050301050405070f0e0906240301091401030b0a2a080f010501020f07030f050304080a030c 77
    0x1070107050040c52450b11024644c000c004081701c20380481c554408150042c1c406d4a452429110070030701c80c1c2001c580c01175a9105007544000c000300e14024030025540c02280d071010f4007514801581c062180c0f240302602401802143c115103185d40c3d82d150951007480c460072080d0000d1b6641e400120a000103000d514940040d070402005200f0264450304020b43c0140d4844c8104000d4002d401441c400358011144154042d8854603201d40c541030a21060358002820801001896101c1d02d1800340c211406c95454002940c2c0c10700c1b16a80d00003c80d9840000e0030300030312140200c0300b8100a0040c43c0b0000c0d030503140a8101440b0304551045c501c0724920007804000c02d4030344503030b00244442e4440d40c8280110403030300300c01c0c038a0038800c12119880c01e0a0085d82e44000307440c2804100f005004d91000500400c820310003404204250011b10b030701e400c503a0000030002c00ca205000780c00d002d03080007540c000c0c0c118a016107000d1600383c500642495800309086950101030100c0f11007181041d0604a40d03d01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515050557 1250 515049307 515049317
    0x30a110a020c240301030b061c06020a120608060f040303020c0a0b060f040204030503031305070b040806040b01081c03090507050406083304020d020315271b0603070905031c0f030606 80
    0x101b544c0d500044542e000300000d4200611881155210300400071306c43c0d1480c050700006903603110b0060000c1c501689140c1c04064181450020065040000340680d80410590000d4509072203030300d0202c0282c0707c0d1010310384c80341c4200600c40c03052154410b2a24000c55048502040d0000094280420ba009520014003103810510001e03204000251450303840c5032044042c0ca0410b42c032075010719619081504014007a9012070200010424000c43c0c46015010540c01005542210113400407000400c14039a000c00d9200c0394200208041000418084c00700140107020107a103401e00c4035511042100c0b0b64405a06681c0c00c1e0742540c0c42200c20000002d03080524049a6442e0340a00503002e4612030102c1e01032207194640550403018030003890041140b070703880c44c0004001100414007030005015400c520340181407402035070001c510f108800c4150a072561912aa5442019561081c1c6c5a111079010701420480c6552000d0040d0040f840803e56150b0f120100b0000c8000c42c101d0344540a2100456 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515051807 1250 515050557 515050559
    0xb09040e0a0c151b060b0405090f030906181206040308160917030d061710060f0e220503031009090f0303050a06091506080129030a110a020c240301 65
    0x2603c0001d1401e049400b50420355480c0260315120721501540210581364030b41e0325002a0035a1400340145a04480020000c22024500c03112580d124410300c904d503442841d000030102e0070381c018944008080720000701984610404015a15290042201c3c1180091140c00c00503002c070307149189190111a581e40c56056480c00c1010035900300c003150905119078131003400780080481c0d0b64018100900449100040010620004645808280030300b1041c41d60910909200ca050f0400070402100ca8551240d142a2100c040281c0075910360b07144104100b020810040030302c04000015402140c208442218403030751040340034204c03510302c98000c00494280701b0b40380110384aa0085500132044600010342d4581d20048001100c0c41141007016100442c1e8013004103540100c4950700401141e00d00050110b840c100c040c07504c0d8000b0160244028021001ca0701810090b807100d04100b82e0226160b03950200100c0180d51175428a0b4802c1c440c0b00d692602c4014609100060205004052001c504503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515053057 1250 515051807 515051819
    0x219090f03110f0103020d0507021c031112131406070813030f030905030c0a0c0e070206012105010b040c0512061c02090405010b0a0303090602070b040605040b070302160b09040e0a0c 80
    0x30310f601c030311284d040540900c14412949824072800c0c0c003c0e0307001d80003440441500f0344042c803502d201e03d0b450307014589000c500c282e41040c44400c44140816080b007409040c1e88595042c0b40840003900094400b220141c8903a2000c0c3e00082e2660040c1c2d15602d52507841d5903142c1202007201c480300c50040008490400e602ca070903000c4d4222522461051040e02d040503002c101c9540f81181c1e8800c03c1d10043d0400310100400c0b1703840403c080d0409242c2c800313030250b5810b010040845044202d0b000e40c00d04d101000c0744041c4003007036000e4002c5004c0100284050018114001c003a50443d0008840d08180003000c02c560b8607010310581a19070a5000d0414600764a4082011440c0000c005a489549a4841c26020307601c682c0848081c501c00d441d500229402c12034028540070446c0c02a5260860410050100e1600002a41c0407101007074003442d9152000d2a0480c00c205841c0034417a100d90b11114040784613035441000d001800015a0100100001c03506840c0c0c2c6c0700c951440c09860b5803034601061040d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515054307 1250 515053057 515053069
    0xf03110603100302030609010207021806090c0307140a0509120a1203020f070b0c0703020f0105010e040b150a0b1903051b090622031202030910030b0102100219090f0311 74
    0x84909080c01c0b102580d95030341c010074104102101c2a070b010365400a515406c51800e00c0502c00295100481c442c968640740380400c0131400c0162001e205070001000040405100f40b14401d81c05007003004890b00d615103800050019040601d50781d00c11300701700716045001300300000c407140200d822080804051607680401c1c2c009510010811812043c2003081c0720100303400d140101e0042c1d20002440c5e07601c90450400038280b09842240d8000d503410700c00100b11200c10760490710b802c290032080c000e4650711480713400e82150700d41c80d000541090454034002900d01604000d04403160700c00c480215030307080001086049038001c0ba0000d0b0860705007401010305000c2d04000d840e00901c00b800140c5400010420513181c204480b0714040011030343c002c01c0c000c20100a58000084034140003d40c1004a000b0016180340c4540c51a0802c00d65503031a00ba401c1d81c42005440a42071034900c045583c2c6000d14040041c4022440314007011600c0c5c0d540000d405c900000c10345003105d4002203800c440d40c06000070454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515055557 1250 515054307 515054311
    0x91f020a0c590a200906030705070f1109100e010b090402040e0a0207060b4f051f15052d0702040c0f0210050c1605030a03060f03110603 60
    0x10001a11081c030300041d01081e039003404002042011100c1030f140514004003034800841030380081c5200552000031420b2000f0990300048801c0700e5258403580c4480045486006407180a44a40c0028101400380007440c0b1501b82381120940e41c0110a903034242400d8070b2440c4501c1900c900f46203c2d0010000c0d100ca002c06000180320040015142c03503555007002602c00380544662401c0c82e400240c2c0c0b4100000c500c01c0703003141c6000b40d5920741014000d403482c1c2d07156000c0b00700d6540d0412029080902c21034090100780d42c2c880304d4425a40c8400c21203450070000305000c98000c0c2240d4100b1000610503000840c5240496454040b5142036000b200ca046a841d0042c2c1c280900c0325542100c94100e2003401040907020000b5400c4090b243c8255004000079105241701100a210041c00d440c160541c0c0807444850406a0902c041740c1a140ca8526021901c40c076149a00f82040300d500c48801c0050200080000702007556080c85500d48810f110b0f8500c0d0000d02c0001d05c080e1144800c1c0c0704600b44030b40515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515056807 1250 515055557 515055659
    0x90e030a0203030114010c0206040b282708010c05210105060d020c070b03091f0b0d12020f030406031424060f09040f020c070e0c04060807050d0905160e0609010308091f020a0c 77
    0x40641e95101d07080d096481da100e0050c08500089a150120101c50440c806071042040115401e94074150100c0e40300d205010301140500d40000b00100760807020410780c00100480c01007035549103413031544103481d6000c3c1141d0520000c11a0390070341c0b012099000d0300403120307402008450190403c0c0d449070b8003540e941c80700e1802d50045400c0720800c1030046c0081e10042260303840c0800c42250410003003e01c038500078551034064850446540e0003d02c1b44c2c461000302c003400d607100d680e150030b001d80070b0010380075134891103a11034104403410315481c40d5074015100040000c1c04850807107440e0030b054030000004403480c0702c0070902403000f04000b03032040c00150f42004003424102c0c80d2021622030301040e1025800207070b0f582e43c01000707151002d00c910519140100464018900d41d800d200c00014440d420600c009082d0381000b24640616685164290110342600143e031003080b40903c001940f26285468240c503512240c0000080c03452040e040642d06512162121030700900d04040c42c00030700d4403c1910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515058057 1250 515056807 515056877
    0x617060f0402030703381303050d3201061103070b04060e0303070206090f0705130f0b060403050d03110702010e04090305091306090e030a0203030114010c0206040b28 73
    0x110325050b0000b0700e010f0050001d0404c01101510441940d0905c0b010700e40c915411b03d080161a00c0c000b088503070800ea242c5003555a451440481c1070281c58101c2510049004401100041007507480403001d05010400100705180c0c2e80d480151028810005203002540040005900040c410051030f0360107441401d0024000d514180e8840c6981c008940600143e4410001c4c00241e500400150120411131001841c80d9410300c00810005400d40c44058521a19518480603034280740e00a204801c0018001503200c0e5500d04100799507102c40d000070f1012274030f049000c41c0039480e5201142d00b07403030b011303102c1c41801c0007003009100003000c204e18240c1c1000340174010000613607644104134130003004242010030000d003400608000c4645034200100103600400200207415008020f40381141c228581910164a0034001611141e1104000039070110002801040d080d84800c003400104140118181130b0135068845009402c9402c0030007004640305000c40702c0003a0b01c0c2400426413003c18520 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515059307 1250 515058057 515058059
    0x1e0203091e072709060b040b100f050d0e120711010206010f030f021201050c09010e030607080f0a060504091220071403011b0818120409050a0e07080304090617060f04020307 76
    0x10607003c640c4c0000084601540328600d000d0907245c2030003086400c51b8200d45007800304a0340c10014000c802d8005600e070500101040910141000e580500c8507402c0c0d91003510180d0035285031040c600d07400740004a5000c44091038252465100043c06c3d4140c810086828904604584402c403030004112012030703100c7c0852021607100c000c28000c25000d404103804d000c0d00e0341c0c0c11a001412100c98060214025030ac00010000c18a0784a400b4075002007a9400c07035841d0ba10307100c40810240c0302c2508441e0f0801e04102010f001c122609100034071101082d40c400010725200783c201810041c090f0b40c481703040e42c0810800c0c012101810107010203108000e00020311041c0461f50918411581e8907001c000c160a0380c20041405c007500118241d1060900142124202030844c131120b0b40914090307028110707600c10000b246e0030200e038010300b2611150f0045540301641c40c082c20781c1e80da10600035442c003142000c50000b0444000002d0010720703a0240060042661541d14580846000a000ba6490b201e1044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515060557 1250 515059307 515059379
    0x50123060c07060810091109042f04090609051b1c0f0603050c18040303090212030d0b0307090c1d18040f0201020c0d0201211e0203091e07 61
    0x2408010b150316204c1c408240381100d501840d0314110392008a045040481000c80c9200c540204c4402003400c40700000c4800004015440702d03040e03182907820003882c2020480f01a0f03280c170054030031206880000d01c84180c8070018801a1801650103031540e40c1401c0034841500c0c000c1c0d02501d03102d06204181c07510308512440364400d80c1e0010340b1111180d5034800c010300512200303020445c1001d9003a07034511010a103210754544544d4000340054105691005030104541d80c0000802c1c0080180c401c82c0d0311010502280c0c00100f102c80301c03041c400d21920500280540682c090641e1299040c6c40c0d0104010742d04010072400c4240c219040e44c000240340565000210b50358070300d0302071030040c030704440d4484980c8006031501d01e2420140c0c0c072441442403218010313a882030b2105048500242e00d88000303600003602001a003005485c80304e1481091000360070381c03045a40074500c192150307421184010041d454001e80300e031040c950500150010b00c4c09210402c82d88012030307510590394000c5240c0701107000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515061807 1250 515060557 515060563
    0x610180f0b28090c080f040f1202030c060f0105031203100302100f0201050c030402090105040f0f0f0c260c0708040b03012d050105160606030506090705010f03050123060c 75
    0x20418116201c06980b08900210064100d10040c202e628010400a00f240c00090301c04880204410700c02c0e00c41c6c000203010440d004545a04d61507008400840105851740c0107916900410040390040c41500c00082c0790310b81408400d4102e400142c00703004910304080c000c08007940700800e5800303c18468400040180c69695034040c03250355681c3c0d09148040756060003825200d01800d402c4c0300d54018428130015030380b624011411540211400070b045021403034890050003200c254090802c2c40d1140b2522000f41c035070003100e40440c0e669101003ca10170700340c661032130024000c05007036416080c0001418084c002c00c0205210b5000b8070006080c42e9030b0341c040c01c280740c1c0240c00100d112608040402240d0002106e25808100e02001221045c2c3c10440000c095005070b0070580c041d99090402c5806000196215001441e045420b482c82454400c20140c1c2d561414804e00d40055512000c11860034440c3c41103074183c81d01d00030003044001c07050450441d05002c003074045911400030064150120410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515063057 1250 515061807 515061829
    0x103060f080f1c1d0f0a1403150c0313080403080d02090f030109052107050105090a0314032e15030501031b03020d02061e0412050610180f0b 62
    0x21800a00c09103508888041c03d1050020000404820040c1c040c0400d540000c400c000c81070203007003024188444000029504013421031080d0700051203d0f00460004c03140c500441540d8400d5089410000c500030144528400031140c56012050038008076030f01e00005032a001c003c50040e1084c5041c680c49071070b0800e15900c000041c031031007a40064490450b05152945040d405c00c200e000b00006003107622442d403a524a543d40820055511089480c602040419640000c0c0c02100801c403c5c90708901560755807191102c143c0110b041408200b1080f84500201c905c0382c402001040c90b04900320900c1208150042d400c88000780b0741c0300000c03074800c088080303084412441d560041055491420032860100d4904407800381d44010040c1400540c54200c0f070810241c2c1d05450895681041e00c407108120309448030110030002002900040d01c0d070045003001c0f5102d02900c155170135921403014100c0c1c0000223104043c000005000e0704403101c211a0700250951180074008500e08001e000080c0c29031400b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515064307 1250 515063057 515063069
    0x1205370210030236012d090f0f0905011a070303050601020319021605061e0711030609030703030b0f132313030909020c03071e02040f020304120c150b0103060f 70
    0x112208012010002d80001d06121402c2c00e000c510b06e010004134032000308500c1500008892451014111680b044004000034504030354503890840e01c800e11b6801c403048502c100402e20b07042200100343c4034100d80c4820090880c102d4213520b410030035034040d4040d100c020035607030540c0818014140314041c070902241141c4401e50242602000307804104000ca90b9075044070f4026241801542100e0456084049032051b03003442182e107072060b52600c00d200e58910001560180956028009020400030142002e24131a4406201000740b9505208500812560807580403002d601e8241c40040f0039071105009408003103009580d101c2c02c0320310000802041d00c0003d120400f421030201410350013900500a00700000b800d61038041180c0032180d5038092444060802340c001c4e4000d800120510604c5200d55170f0291080c041c0e000012410b1009400c1118141d9113045440031000101d4450120007840b6544482d06040c0040c0d04d9803843d000300402511300d41415580c000108030020103c50000003000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515065557 1250 515064307 515064367
    0x1505070807061d010b01120e0309030d03060e0a090803040b061810060f09150e01110d0206041208070c1b090e0309030d0f050906070c12053702100302 66
    0x1118620501000b01129048415900d0a0705c080e500c0c1c2e0744000041c0805040150108079031417208080342c00c510816000c2540b40c0718041c4e00f6503210b50550806c50485000d0108011f107980e440540d0802d4400c0f5140c0109040c03010030008000030703445842d4907008000600b40500c41c5100303c0c40041c0820090702c614282e02c885140401c07030039600c0103a108003520185091030070140303440082403100f00e00c41d02500c140001604c10000c0740c0d04c07070710804101c04d04681c21541800c5036090f0103512104181c40c281c5200780142094454240030740c2c042400340c0481c0e44c0d0240c00318440d40b00c8a03034a0100a00350441c5e12f03440c403800212540c081c014690b080074418051079860920b81c0c1018a00314540c001b010601c00b050440550712a000026951840002c2c1d0b00d080d500c81c520704e0901820340c03c6801010510420021907014841b0014841501180f14000e41d210030038428641101c004c401815041291200d2182c2c9005013042d94030840800d050b4203015081410340404078642c400c81d07100b1403103900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515066807 1250 515065557 515065571
    0xf021204270c0809070f030c05040b03010b030307060c090b0408100b0f04020403110a05031f09030302090a030b06011101050c0406030207050a2f09010315230709140a0f150507080706 80
    0x2000b030045000038076000c906d2403200c918590b030344201d0b01010f1180c90b200c0c0759508000b00290f1000c8d00076400c19040101a40c2d030b1040709252000007400082c0201c400143c0280d804202940107000301ca060301c2c42c1ca070082041000c114a28406081c851400c15042628140da06095441c0c90002d0405140b040040e001d080380030406101402c10190300c4148242e00503030301340055201785443d41e8007034440004049441c1c02c0c5420b054010b40308081c11b150700f00d00c007100f001062014501d0720714017401c026a142d100f403241600d00c2e5420788009031819107081001b00700c10440140242e000302011b0344100c1c180d4000000c252111810070300340d0742a103204805070030550784101c07a8080e0030344003040040790800003650446d2502d510000c0d10300f002c500180c0d600c1180b000750b41407a080005541e40040e01d040c0343c501c3c200200802040051040c0c03601c0c070050580e600f009142c903210f1001900d05815081000301e01e4012003081c400503018102060110420200e800310b9426401041aa07001c1c4102183c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515068057 1250 515066807 515066821
    0x2040501260a08030c250614090c1507060f240602030304030509040504080910050a0201150b0313080c0f07031122020a1106090a030f021204270c08 65
    0x400401d101040150005040d4400064a89040d00c4c2c0149070400419125440e861100c2c81c0303c0b03c6a030084c00c560042c804035104001c0950424034021400151003070381d54894200880d51000c020781c041d0343c070420312802c0424407000b01d009030100f20700628010070008905608002140d0341c15a0107600103200203c40d40301c036190300c52107500030041c0b440150f187d0b25094600034028044c01101302d1003107485001040500680c00143c5409100091500c414045580c230301400541c4070350350301d01c003550800722581c5881100c00d0080c400c0f00d0700d5041e80ea2460703881c404031301210300e6010303c125104102070044011541c070400500a44900c600300a00100e415820f02c0d540617071002326103501c1280ca103140029000c0f49502c0c0741c11100d001100150712000041d0b03003a070780f00000603020950f500ca0001000790b04000001e0800c2080d000e510340c12103840c40050101d80352200c1005810841e0320810040011040c0594010103480c051040340d80841150741c020410f4031065002200003412000c240000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515069307 1250 515068057 515068109
    0x40902120a050f0a05030a081009020d05180c010206010b160506010f050406090c020c2b0305090a06080601171308071a0606210c090409080d0f0b1c0f02040501 70
    0x460f54800001e04000501c2c2d91629500e21913054840c1c104000e40c0c01082505103903004c40c40c060410340000359114546480c0b910014001159080704607055118140c00c051004a031032a00d800060f07014040c1c0742e0814003034200c5907112003411000d80700901c04600201d40140041d502170164405409500742c40d01c420441503618580000142c4c900d042d4006800c1500018041d034400425210018111890b080c40f9800504030411944080a1401c100c0c0400d64404000c05584008403540030710340c2d4850b0b00031a9140f030f0840b40d983c0800c4403c0da001c1079505007107180c1a0304c101510f5861610a1190341d41c0460340d0003401c2c049030000d42020020f401503e59141540c0d10a0302030300c82d0741c100304a000c1600d01d003441d41001d50280c6070031a00030400c4021200700701c0b2814030000d4001e01c4040e110f032510104a6110f506da01c804240782c14030981c1038030741c14010018240b10080c0242c0d8443c03202d0b50b20044c40380b0009000c54494003224400300c0140c9540c081c47d4024072031203292004802d510083c80320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515070557 1250 515069307 515069323
    0xa030e0402091008070c0602131a180607050f07090506091503060601050c010f0507180e070c02121f020301062006070503190603060b13020304020a090b040902120a05 73
    0x482640107101007407258542003000c183d1007810346410a184d4590100c00e41e12410200703005030400d8000540807940130b0b20308050b40111451004801070b40c2da4440c00d40b1a06025402440306800c80424030960bd07440d0040242c030066000b00180d8100d06c050801662801c01158042c100c007a0b1514208507451825120321580030008900c02422001d0a00c0000c0d11480e00401c0d280c140f040200d00b031901490300b5030113544003c41c609130800007810507c1d4084d100d0999130856490200c4001800326003800420300d180c0c0115025101c07372080d10f965a003007080340c1168880c6847c50380b04041e0002030007840e0040c3d51030041100e0000694035410007600800d9070340402c00030004c00d00c0511304d0041c030303040000d00d4a6010129280c419242e440303070402002041d41442c02c401140b4101040441440003135880066960b0045403942040300001e00c6060903400111806540070380300344401c02250344250803181110400810008650000c1c0d40081c130301c520240201038041c3d0280784200208141040108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515071807 1250 515070557 515070559
    0x501030b1008011a090909100c0f02030702100539030a1d032b031a03031b0304090f150603050606030403030c02070b0301032f030a0b0c0c030307020a030e 68
    0x1802071010244082c0403140d041c81080e07400e01083d18500000e500020a40b0300c00d400052181c002402c2100c01c50350b5070b841d00210120024900920b003810b140c0203852041c4400c1c2c0703a0b00a1400c0011030f40030420070300310b00e05c60141405804c200900040300788111a10201c2001400107954820014070080c0d550154200c4121640c0700f00217a6111a411900885920800c0c000140501811001207428852143c60040d24510248482d100b05d0100030194a5580e92658003041116010b50264080348840300410780c154100300540707002454081220714203101039504130b80c50300f6942c0030304000301d070400b000000200f640d8001245140c00803480b0350000345594a42401035080880000d100c9220203000281070682d2460b030b0a124038001c0c040c8030001c2c280b0302e0206841e90f9417420004404404800403000007800e02c9c0c40c80700c3d81c0b5003001802c001c801c00a80286180340e156562010b580358041d00c080c228190500c01c01610003c208001d6100e0580f6901401042c1d6040c0f0b405060762420140c1d403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515073057 1250 515071807 515071819
    0x1207110c0108091506062503111c03020a031407020304030c2c1003060c09050316080303010b180a030503040e070e1e011205150a06090305060a050601050c010c090501030b 75
    0x8412010303c00a24007043d1007400021a106445500020700b10380701c4c8102c0c400340d181550b6440b604441400401c4001a4000c0d2a120a103280440300c07075458444a081114407001040041200184a82e000c1c0121810f10300700040d07402c91b203108a0081850071a000f200685c000a001e00070000125010001401031071141c00c0f03500d88002e4544a1070060340200e000818401c000100d08452083c022001581c01401c1041543d660210040c015021405461301901c80c860f94020064030141c0507400301e84040c80618110303400e00b4a80d807004e911101a07500e410a04030350825003680c41118240003944036000950703503185030001d03910090500401d900c0a000c000040c041568460019034420588681103448496429000685051b071010300e200b01550300d000c0801c460749a02000781e130290039040f42c074210090760303071142210301c03944038040103101c3d40201020800d0141d070740d0002d903080081418101c3c1044006a826400c5901c15000d080c0090003e032801c02242d609072142080c140d50030f40304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515074307 1250 515073057 515073061
    0x30c08060a06030e03120703060e06011e0806010905060301090c0206090d21060b0c060f060303070309030b0403050705060406051b2805040b0a0201231b0f1207110c0108 74
    0x289a071030a8032541d400d054888180382101c540910407a403d5441e924440d5290f07083c4400b00500030109401071440c0500c0401c08110b080d07000720700c81e10701442c0011011030100c1a055040300c0740003020740f4141c18041c1172007003c07030a580d601014601034590701d0800501c1c006a414005d20301480a403800181d80c005e80740d4180c1840e4055135400104140010340e610304020402c100d00240351690040013181004501c0a006a1000c14950f000300070304018500c45171529410540c0740d01c1601402030109510200400c002180e0f201041c0e4040d00a00f032081c2041516241d40d4100b010440d401c440840c0d0740c4040043c0084003422004c0c04041840d0380d1414400c054031001e10000701c21003480110148403c00082082c440c1d004c48000e04220510a030302e542c6040da000e03004e030012007405a05d00c40c0c00041038035001c200c080d04500c40e03155024410f980c2d0080001d04070139503001d02d070007102301c113002c119140c40980d111f4010b600540c580d90ba06440b403541004010704040d4401c000c00d0400c10400c1c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515075557 1250 515074307 515074309
    0x140a050402150711090406020c010c141c020f0f0301030308012702130911250209070c0317180d031407200109030207031a040b01062a080a030c0806 65
    0x2882c0040d180c0d0711541c0e569103080c0c1010082d803507840b00869400500d040400080010703030b401401284101d200240038208241c0810355441601d0000d00032004828081040040c1c00d4501030070700900d80303040040c5801d0444d4040074240e0f1012000c0002c1010000040080552029981c0c0c010f0a420340030348035004480b69904690300c1c90111144185401055a4015210003200240185204901007104030302c2000c044800f41c0080321080d03108400820b078000c0c1101c02e1910078000c25401032003a030709566070303001c15217458130004030503000c20103041c00000030301c80194000d030702808510b00014610044184182d14000c1e024540804060505900702040b00e159402182c0005d5242404c8040340300340704464036130711102c0398403010075800d12151209141d000302c0e404050b64000c80394240c10302a0082454a48881034034010054102c05004010061045c00508502c8284400d800702010707210b82d400684188000c07043d03920200000700b16442c0340c1c051041b0350210300ba6062501580c54560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515076807 1250 515075557 515075569
    0x120207080a020108090c03150114040603110424141e010e090912070b011e030506010303030504021c0b0a15080a080c0708121e0415210f140a050402 65
    0x1250003814002c01c5400314881399414003002d003524002600321698441d034280242c2300c584c801e00c2001d03801c844220040026081c24080c000942e81c01c010010180c09136141030200510810300c81c911490003c109900515001e43c8590f8001d0512005e0a1070644a40080064003089001000400054480444400d9800c040c071250903604c100e905071140d9403900c0340d480c10300b88010f102441029001aa0008101e15a0760050503200810700c1c0c1140005a04501221a130702400701812560040004000003403094103ca0b900c13a1025100b449442e54000c00c03205000101c44003101e00e046a40c0030840115030724803070244940f0071410700b55500b80c6003010244d11210542c42c05411103400051081100c2400c0180c1001003e6110807244e100314105a201c1e4103400071000940c6035000714200b1904103c401040d10141d810190303018001181c81c080c151a0440840001ca101c09020b03180340f50a0440e83c4038045024100c6240801d45100369241045035020080610040e0f83c58101848050303140e80d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515078057 1250 515076807 515076823
    0x30c120301141203190c0605010e25020c0a0602010903020c060313020111030c1e0607022103072a0b090f0a030807030b0405070c260a120204080a080712020708 70
    0x240c60400d00c00c51032048a505601c1045c0450408441d1410700d5180154420004541c4a015080401c03450f601ea5180302400d034025a00003459540c4a40142681400d000f21241050a240110740b6400d071310314041012981070b58840c50140c1d41d00c2000038289034050085540d180d000300d4425146152086a014013117004002c0a410850801e654001149040040301d807000030040480c0c2290901d40c0c10001040050010845103005070000300c0c88442c000500c10f00703d5810105820300d00c4038001c150403d0360b0401045601000303c544c9070780c4480e1400701043c5d240e448803020a07009480090400064481010f030495030140d2041104e240a40c0c4041492150030b03a162034400e0b40c58941c440101d002e00840310000c0c1d84189020140320902d034010501c50850751080303040105040b94091004a50700b0100c2c55a60107140401c00e58001521514840d9400341c9802b0b0300600b0244c80d12141071420006072011641e0761000550b0300240251001104a500341704e01c0103050003410181019215029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515079307 1250 515078057 515078059
    0x507120e0304230a030b0702101104090902010c12480f140307110301090201200f0102030c0702240a120e15180f0a0f06020f0c030c12030114 62
    0x1c50700c403c034803040c00524505032034040103000b10a42512810300c51000b82c4165640400341c8102040b000c4030110314003d9151040700c1919440c1010324101d030300c80141c070300e04108904200008015800195035194031607040c40e00c1c2c1c3d640d009100f159400070921010010340300d04040c20501c0c00341040560080c2051100032100d4886985000e162074603010741c0300d05400081c00c0f0510321040002d508000405801d81e02d010360109601501c0d20001c0c54200e0305400c078003a000850100c02054a1107500b02c042007412840b42c00c40c0d200a10b0240b1082c2260000d880c48240490300207410320a5180c050500100c1c0c0c0316410b2030b4004502d080c0185103841c410038130f0f030b001031020485019402c110355600030402140d84200390340c1c2c440d4050820810f400011110020024044141c50040360b00c0068900c10300b0f00c0050042403003641d1a21100b940c800994412102d42d030b002c12000c47c038290135801078601950b4640045440340140a20941002c200c0c0380e0340d0045001c103100400003a8020301680e110004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515080557 1250 515079307 515079329
    0x1210090308130b041202030412050d02010b040504080304020904080d060e0105030d020718050c09040507030203060901090b060703030b1201090308180606010c03030207020a0b0f0d0b0d0201141612030507120e0304 93
    0x700c04c4021ba00b5802194410540c4001d14018202405000304240b284841c090b8000c110f0140c030f21f0300b04021a102500c000d0000346060000400505103030b410250481d0040210500300b80160040505171220381d00000b07032035801900100494201003110040f00951400908201410020580748400d440c082c00f20748180c90740c0100c1c89040860b0708884d812000504184414a010350002d006580701707a6105000742401000010030320000d00c47c8100222000303258030f25101990720110082c0103214400c946c031000a0f604945005001d2165490700c1d44a611420002d15040500d507046000c2c030307a0400707507a0b0000001c0040603a80301030070810250b0700d0b040058961503d4004606409a40c0d080301d0007000c00041c0801e08000000c3c05045441e150500c00d020b4100c1e50414040c12140003c0001e01003010401208000660032020308120000c04502d0070f0b4001d056110841084030014020010a80d10821700900300c1e0320490090442d400d40c00184500e500f032420383d80d9a485a8070480c40c040d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515081807 1250 515080557 515080583
    0x1a0d0305090603070f18030c060c0602090406082a010903031b0b09011e090b07140c0d03050f072d0203040b031503160f030b061210090308130b04 64
    0x50144050310407507000070700035503101d00c1e10101c090a81059514400c0108002c40c3d0041e5000c1c3ca100c45d05002ea0741c1c0481511030f80c0d0702d0003e0907502c0ca5004603040320480d40900082c03d080d10f95124100040c030f20000188055100100c441c465840254926618881040d05c071000d00d90b0080d03a0001100c2e411700e4000c1c154400140b5803406030035003507001803c1006400501c500684150843c00c401000f419131000510401c131507130b60449807078440007401c2c04241c0c000a80c0041c0662502c41020841c440320784c0c034003034001040c14200f03004040000b02095850050040c84a001004a42e0100d01c1d0b00b0142c82d103410b540d4140d240e0000c01203041515034016140e004000f8400c0c0705640040400404507070300c1c0e080402c40c018070340701304220140c02841160489101a13111034030f44812642e000942401c00350642d100c5c080712941c01040e039a040a1803254203c0c0c507901c1080031280f2081000000035184590b0324000b0031240d40900000c01d041580c0e2410740100b5000c85170f0720382065000329500012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515083057 1250 515081807 515081813
    0xc0606240f0f1611031204140d030e1003050415050c07020f0f120f120906031812120a0c0801060234081509031303030c06060e01080102040303020c041a0d 68
    0x35201e00c0c503040d20300c03d0501e4985003c11096450f0041040c1d03007202501c0003003903014074081107400755110b108480d0109000102c4141010b101070003c0c28041c0c41c11021400c81640460810030024a080c80003030f030356104020500880300100c030003ca90b415418455810b100c1844042c1c0d00480201903c0380c901100c2c0c4c4515075849c42407400303028401420904050900001e810748526000640402c14010309641074018800f0f0b9040382c010440c020310a50070f6031201995110100c6448551480f64401d14110009648070140604403140b03444500c0e01c0e0707034a440000442919889461038060004c40c0c00184410394022642070404a20b588140e080045100d04406c0090305050284203002d64071040451346060109140c80e4161b0b071200700055a841e0644844e907280700e415080314400055000500001e4800c15002c2d01040c080c04021890769110700009202550a901c1000c86030360000d010010941c0610100144240071a4100b03c00040405010300c408541e070f910610071601e030300a00e820 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515084307 1250 515083057 515083087
    0x30c010e04021830010b0108040f0f05190302011401060207090b210105181c21061401030c03090f02090c16030801030c0e040c0306050a0b0301020c0606240f 69
    0x20fa150002e00404d02120b01c10b049030310200e46050080c20542490600701c41400d0140152100100181d40706a100d03034a580b51a44c6841c01210304690440191180c21b011490405c41e200182c3d40602000c003103440c2138076001c1e00311080e4400c5e802d0494844070040150940104144044074104075010401a4a071800200c0030b60340d14503200004c05007203190403000c0c003055218900c00c0036581424111900c0c01140e02d0743c1c40c0d40c0c5040c01c0d50f60420142c3d0003141c1c10b1140050140d8110b02c0c20314580100901e01141c420f0b00d400d034000c0480b05403440c9141c5140d41c2c3c10b0003159141d403100e0808100862481d1104030094a110341d0213401007042c0b40101e024407040314115090000d01e550078950180013881c005280303413400c1c841074952007007901c0045100c0b450300309400c1c02a91300210041c1120700c1d5036070ba8000380200a22909015a65092004103502c1c00c0c0014011a848a0090200c1d0b241002c2041841c08035030115140c2c40101d1228a8108104c3c01c00b01c40c020f1501050180e201d500542c2c0c0800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515085557 1250 515084307 515084347
    0x90c05100909060e010f051509010f030e0607020f0610140f0a03080a111c020a030c020a05030f07031406130303020c070324060501141e040b0c030406020606030c010e0402 75
    0x52030b0385000700001d01c00b500b0204440c1600c2c81650200201036840d0308020071018803400e03050220384108071340119907009900c40e039071504d070600300401c11400341984581421800c940d25070140e0442c1c15420110750302401320661040c1030b45904064142400c0c0c44035003255203081900d0040d003c0107240d09c840d60b41c01c402e1600650f8410307203455490001d840014070000e840110341d90640f20b513451011302481c10110041d82d15001d68000d068601c9292011640c00c0e58490301030740c0040c25000041000d4400b03000a8490343c01c103000a241540c03a525044512440c000c00a0016810a0040c03000303600c8030030402443e95400d460056101d40c071102e926810f00d40ca40e0700040041640c079000401121542030005482821201c0401515568a00554100c41d0700341c004021000d081000612005d20001c811301d9800707600900a041c181c0fa2003a031882e507070041c800c01d1039690020800b00801d5604011169010000f0b80240030b800000c1c90011345480e65026030329100b00e401041c140046940f41075041c0e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515086807 1250 515085557 515085569
    0x1e061d13060501061d0603130b0a14090f0601080114070804330b18060d11120313080a120807020a170c07090b060304080a12050f06010e04090c051009 66
    0x1d540e442c54003800845c41d41448914800304003480112074139048064038822000d02d0402c0001c000300d81d540222911004240d05012951090300040c117005502100b442004072100800841121401c0300b890807005070300c0071500c0e038140f00010420449190b9020f03042416402c1440c1d0584980c42c00c0082044160303601030040e6a000c81c40c001103c1c820040032280500c2a0042280398288010f1102b0281c004840c48004203103034011a0302420f010301c25010349406400440003600300302d800107003044140e051042c42a400400c0301071071002214103200041c05044010120742c0425502d020031508810201420701952200062601c6d00900c0302e202c0182d44848005424807000c210744a9541040f205003403244100003011805d03c0051081e02230035540140110300710b9455031303558009a88400d481d8810001000c0082c040503000307005007402030301d112071910030300d1602600052502d9095207026118034207110000021510200307400090b6101500e82011040038a4001d0b2280030841d4040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515088057 1250 515086807 515086811
    0x41104081510230909150c1803070b070c080a0b070f030b180106081f090911090f0108062503053c0606090102070b0313151e061d1306 59
    0x300091580c0c42608084455084492013600c3c0c89011449a5030103051134801511611040414808604a0044c00d0810480751058011a82c032801203070901d011540204500e07a00854a08108103001c01d0740c0000c4c04116000380b4100809417644000d6060150480c800c0c03010110720300b0107040c440c2e001030050503005016052840400c8034484060074013449410300042c1c8000114460105540000b9001d1a1884000b1151400d041c50140108464801200d0f0668400505c89080d00e41505582c4122060348420204d58506000241003079401444001d0340003a03071643c0c0c20603841c44081030f1540e07122891b00041c15a1039600000010403a240844282030346001c680791880001d55032070300d0301c00e080715a00e91542c440005005c07081c05002c01c1d09001d83c0000341d05202d054041001f079076001e9100d02c6990030040c0385860f03503413002e629902030204040d00d034035040e4003400c4440600b005000d001c02c41008950f15024402000e52036a03600301c440c4d009604007160902584010350300302c030341d0400c0007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515089307 1250 515088057 515088089
    0x5030f0307240612111e060406030e010b0306090703031706060d050907180b0f03030405030d12061e05010e0f0a090e2a01110a08030a090204021e0306041104081510 72
    0x1021004070303525407040c4d01c28108a1b0008070f5840c0344485080106402601280c00c00c1e0620340160058402160030f01c1d041c1d03603180548413944d0b50401009024211a00292220909500707000b4403034201c0d881407054200c0c411040c000140c4503501102d01c2040190030000d550303102c413804181000215801000b0f1001c4231121030714a1750032540024840407040318544d1980488009154403802240305850341078200e5034402550750f000b0314a0800c4466041070004545031070380c1441410703403042c0c00350104207070341c03078000b44040d503080b08810312414421991210f509141300d0000303260040600416602d90384a0080b24140701c4104100100c41c1241350b10702c00f11008540d600c401480840d03c10a0004070f00038a00c3e40e800c0404100d246410360801d0440b455030743c80008510141c0042681260425400c22801000c0010081c0b008603045682c5030903035aa09010041006644100079004000788081100300100240003c0000358009000200307a207560f54a00c440500211030746c410030703240c030311005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515090557 1250 515089307 515089313
    0x70e06091309122604020904020f030a08070615051e04020f13170123150d050114070815030307060f090206040f03030f1706150f0a0905030f0307240612 67
    0x10609044d40c10009032040703400c07181002c072202520305542c069005089180401c2c0903003065981c92800380300140071a480710200741c0c0d525038594801d400a0301c2c440d54a40082c036542418071240c1c402460106c4000200344881910010b03603210055115120340d0703001820b05042007080f01602c051100c82d5422815a56684860b500e0131108035056098652030200358103110200d500b00040c40201c1c80a20a80581d00d4150003e19007aa6000c0b595200010f400c104002171000d024100c07092072030f60b407021618100107401034400f0001400d0860b1120210703000c41c0198900105270307a00c240e002036000c52841e40441b8031500902e001d0b1000f030f4110000003808224000d00c0410181101e219613541c608402c0010000c41d140c0481d2004124500d44500100700686450703401e200c02e0710040f101d858a8505d190105d9000b83e4400300541c008140238100030011b40c901840021112400840514030340745040d9135202c0320806249401c0081501c040c005442c03400103030310000161140c40300c490080b07440d43c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515091807 1250 515090557 515090567
    0x1060906030b0609190b0319060903020607050913110c070b03010305120f0a080406110d0902090a0603030206010e10052d0d02100309021c08040e070e0609130912 71
    0x1010a030b40350800c100102e030680c248922403d00c1444403e400c810740a056004003c05020a1409551715200c2d9030414104102005100e58030741d8801c041c006910760483c82e001e42441c10052450082c00300034406140903403985280c0315201c00e0348030000141900c0c190305034130707650040d00203c008902c56800045200d600e0300c0019810f8078000e07811540060b5103a00d002e0024441d00d0303048a0030b06000e000071402e00c0e01929042e5009403141c6004240e10300709810401b15038000d02e4010030b07040d4403800d0b01c1c0300750b042c0018410380005507620180421170a50310060359400044c440c402c0d10751031080000c0e0000c04003003954005844c00900f01000b5244115100391700b00c10266250f03030507007010070390010b4610303000480c90100b0390701400e0350405403a034079803d8004000203041a038101c00c140c1400c803804045d40c40c055440f181f05080d521340392420f01e00030034103140b0010300c6001030000b600d000130082d42d116000e40301c2c014800c940b1401041e46081a00d0050140b015005052041010b4403012803030b080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515093057 1250 515091807 515091809
    0xc080a0f0c0506161b02060702060c0c040f0c110c0616020d06020a0201060f2301030c090305030f0307020111041208030c0f1c0e03040513020309010b0a1202031e06070f1101060906 79
    0x50795901c10600d200c03085c0c00010054201c0000d5110301c0410031180182851000b40c044540745005507010817802101180a880b40d41a0840e52140d0f07546254522540040030311025440035402032120701d5014000c00d140d40f00d5400050480458100036a04658800ca0100d08066110009540310f07803840001038047c1145005052034821030345404140c0100c80384039044c015000c6c40c111086100928015002800b00c001d50504210b200b40b40400820b10800017030250200c45001e003035981c035120600a0840301c8d83e4030141c079140380c1000300700031a92240160b441440d0700b02c01d10903540d40b85c08009451034402c00403401c3c6410300200b10a0159000b0b00c003c150f00a40700c2c481807054401c180d00c80740e2a4819402200d900c6520002821680701040d400345500c404146c00000301d282e042c000041c00001c041e4002c4c64000a807403014400c50409225001602c3d0000c0390625244012007442d0380c0707444000300490f04021584100500c0f0f1413060074444c44400f00c0d0002003051a40707508a101c003811039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515094307 1250 515093057 515093101
    0x1905040b0111060a0518030c0a0b01210303020901030f05180c01091d09070302040e33070c0c0306110c060115020319110105250c080a0f0c0506 63
    0x3800c140c0c90025402600714500c00c2c4110740142007182d580f401c10800621000d040b10144801c1c0c910513000803c402c02c002c00070380820740c2c01401e8100075803030300d2030306084c050308a002d5038240d8001284a4042d5101e0320100203605040240e142c4200400403001844840d1500c18141d081c4000d012840081c111114041c0c000b0710160380b5850410801900c10001c6031044c201d1140341d000410040414068a0542054409041d122a280d0301d80000782511881031903041142c000040e40191421066440c0d040c0081480030001d4882c01c8615200c541c50004000c04244040321000300c08001d0214001005145c1c05081003001c124500700010b051b070808100c0c03000302d1042c0f60011a14140d80c00d10407211801903802145005417810101b006424650728800c01d22020015a09060100b8090240309080050312100d14606001f42c424040980b81c0c45801441607000103000401d01c2d2310b046581005040c00d015046080040382100c00c0d814031803004e0400d008078020301c20710190000352080c405e02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515095557 1250 515094307 515094311
    0x18060603060b330403080f041502010606090b2a0d020d051306050f0c100c171608090a081b0d0206010e01030b040c050316050102060c0a091205010902190504 69
    0x10b80d20184818012000c0309211080d42000c5200244029240c0030042907429006050600d552075980c085a6004180410384a0002217410f105940361300020040c90180e40c802803040d5850490054000012030007031a000300e07400522422901c2248100d9224050980201607007070009548050303c076038000c102c98005010f21201080c0462141060303866010b0803614045d01300b4a40758094506900196925007082130074041001c0701201400141c00d446004180032074021a240c100400c0709007a12038441300081d58a080c040e4001086440240030340d480d082c5480d0035100e84821514141c0481c400420f600d00002c1c070081540c0700f003c1038900703100d5103030111102c6c2d0b440144d041c4d0303d54030240100660002d03e1001000800d5440f80c80c1d40d0024044c010074044240c40d1070200c1c0c140807034101c1000350b00007071440800495904012507940424120b40d80d030f04160002d000104506920b100b4140000c16802146007842020360110070000d40c003c10000c185051b80141c00031030022441200d1040e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515096807 1250 515095557 515095571
    0x10612052e03020a140a12060b030d09080c0103020c03090d05010f11120109020304031239080c04180e0c06031008010f0b09040b090a02061c110405010516061806060306 74
    0x1c80a481d9417040c00001e001c03507081d0382080042251290101001d82e00140c2310113018515032801d01c956001001e0760340c3c45400041c10240c1d81460103441d5012181090710401c40308001c1c1802000381c403a010000c8402c085401c24034184240580509a00d00100c145810841c00070404007200610b841c0070b86180d11941c0c0e07030340e030043c0b982240030444018010030044140b440e13003000c0641c02465114000280d0b85401c4401d0500e032160f0400c00f6007810301150110300803010784c3d504444099400b905c0e00f0b0807686440c3c1044404000b1005040c46090802d49460424490900601c03c00c044079030f010306001c1d00c86c03810092444207944a40b062070095403030722607000240c14103401447d07035500018150302d030702c0e403643e50350066170f00c0004011135110300640034100c0040e07440c1401040c490360410b84044c81d02103c54031100458a44481940c48144100000c01ca181d130000306441c003080c1051501081c1c030071a414000302030a01d2503020300c03030031201c2803040040006551000c0b003074030300a200170850b030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515098057 1250 515096807 515096819
    0x91203041b030b09340b03040c0905010e0106030b030a03020c06161713090e06010501080a090203010903030b0f010e0d0b0702071502071d04030804152012060603010612052e03020a 79
    0x92821001c0c11030502c2c04e05c401e111000f0440d000350b400c80d100e040f0000d072803540e0700702e12000c868003a04403000e0b0802140c01005480d516010701a0751310012001b404808406680195880301c117491010300038000869601d000d030894140580d480754108000010a0070321184528099202400b102800000c2c02400310b0083d681c1d12841c0480c0c5500b400401d050303400d0100540702200c0040c0032500c5544ca0f09a14001614203003c1d407910280310752000b00d2078000703840400c006824200c250604104100906040e25600c079000c40c1e0f981e90700702d0605042c1e41ca4104040f410008240c03c404007a04450304880b0f40607a001441c10708484040510211240c03248c080003031000700c2520048c001400001c00f140c0401c124a003522110500900001581e0107610616400c401840000320405c6a0114581f111505240001648620102d03040f900d03643c100b01016020182c0c00001d42085070303550b8001865551040c4a550080020031102c040540411324400c1200041e13000c100e0003410203500006003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515099307 1250 515098057 515098123
    0x31e0b010816060f05030c03060406120b04060b120309060a0504050a061205150d030e010e040c08060913170c0111071b0503010216020d0f0f08070b091203041b030b09 73
    0xb8199654616203142ca45601f1a00c05801c05001107501c80d58444002455826091400c044148284200207540ca02400c21900f10340380498094042e03000c0918140c003000001c81161103101007190055280c030380da0039084400740140e0f0086900048005008120207402c038688481c0c072224400d09105a98075459640e600004d81020305801c80804030b2140002802101d60155100040c504140303d44c810070001400d4441404001c00402d6404040c000c0340d0130038a8070f40c0d0f030162b989600b166982c0300c103075a51103001e008404070708107030000410340e0f00460341d0a40011780c0d080205245c2a03154225420101124298842e13a880250201003000400b41410b00a45030003c0a59038a2907012845409011841d0b4440341e04650403a12910010f000a20031901254424010344843d0b8640b003962070035008202c0050b00d0f03c0b1103603104440c9070ba074200242c011280d000e41e0054041d0039008440c40f8100d614002a08010403c001880800c000103800150300d45142c182c5070301aa00c11018013031540341d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515100557 1250 515099307 515099327
    0x31c18020a0b03070c170c07050303040e13080d0623040c020d0c05190602070209010f05130902030c120303090c120616050f07060b040609050f01031e0b01081606 71
    0x14004640d8030080144031010405181d000b20113081c80003c1400d1a6150302c082c0d9801541855090008165420b2031f060410804000d000c1c1078004600c1c00c1e09082803590410001000702c0210304115a000040104800c240c0f025484c02031028030520f62954092103541001c80e0261007048201000e008292416000e00392100e0b1050700a0100412030b0300d4200c600200800094805210740503000c041c2c0004a42181c8016014502c010786400c4240304200003280180c1c00394446420a90303052115a541e090551a1181d0401000907180003c0c07022030f0a050500b88444e501c07442c10b102007a094000403008522481e440025a03030008101010442c2412121014080030703403040001030005c00142650003045409030401c10b0803c0300000e603201c061350000130104c80b034589030100c10185043c503000e605c0240c50700c070b00c0622207032504028541e900c071014030001d019030b03000200803149010302c1402c510710303190401030550440da11450200e9448444141c01c00204510100c0000c1051044403e41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 515101807 1250 515100557 515100559
    0xc090504050901180303020a05040302090405061e0709051c02040f05040506160e060a11030301080106080d0804020112090201180305010e060c0f1e04090905010e0106060e1503100503031c1802 84
    0x110070a040e9481c214008d40100303010b1006d00204110110241e5a41d0740341920480c4950010416498248818502840302183d0815001c01c84000d0001850b004150740c816640103075980b1102d41c004c0c030605a14041d100c0b0740030390401d00d821940c3e03051000c25004244034900841c04c40b5640d4407035072428444070802c51951000160a803418144502d45507005060410b154505441f0160303884024a04560081e030042001d17a54075007080240e904144a0f80b0030311440742c2002403441c502a0000392030140c546402515a5940e428418216070192102d1110000210380c0507a2060302d91407c203008010128803000184581400901038900e018111500008580510b5040c01443c00312034206220000e503e042e00c3c070f0180000718160405101c7c800380b07980204004510141015110380c00c48949411020822010035440307407075a00e545980140c00c2c40145103442c0d070fa507113070800c10b1603805580d04050360601000078603001c50b00141301d032401002c0142c0420032080d03869180c4a603060460200007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 515103057 1250 515101807 515101841
    0x3080c0a030f2c06130605070c050a06050a081e07031e020304080f0c0304030b070c030305093009031204030210090f06030f0b030708011a04060b030a020f0d0c090504050901 76
    0x300d000710190800100780743c5000c0c008a013403096001080a09130503940007500041c00100c0d214043c014900000c0000f001c0907203e0390005030074164002d08900c1140502e000740440341002c11030b8200711a48c50050030440320f807100311a0412070001405000001504241900700c080142402c0410344200c2c1d0142d5408821245006080c01c0c0300f40650300a84440c800fa40000e000010202d0b1a40554034800c031850755940c00e8036207442c40c0160480c0e0000c3e0060b0781aa108808080e20a203140c0b520040150300c8001c0e01d03007460b050840442451140ba102140c25010b011304041c40040a0030140090380e100f126000c0200c50b18040c00c17108107000d4450410042c482e648100308040c080e6100b882c4061010501203034031440703e000f092030448241d0010311140c0d59003880c80c40d45140d204060301e0380360b03040394248440c51800103d604240006072850038031607800603900c0452a5010119810700009003000d00c00003c0c03020015280c80350b544225800f5900341000640c24940600c5016003a032940504 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 515104307 1250 515103057 515103107
    0x7020c10111e1204031a0703020909041b0b04120c0e07121e051305100b0f1509031c1e05070f02130e06012105151003080c0a030f 57
    0x2c11035182d0582881181140290408400c0d1020100010f00256028042c0520402c5011800a0030200020030304c501301841441102117527600d424035642c020b41c20030392102c1c0038540d4484070514040a0762041c0e803003038400200001c1070740e085020348a4a0f03001e9294641c4072580e8800c001101c10017201c0641c00980c01703d002401c0e07500281e1110340c480c14640b041c614442c15804200c01103c5c400d030798188107103280440d100100b01c01009a81d08840c9038810038041001c460001c0340c2d50b00e9900380000d1240d44102da0905051141c5c81c10381d400640700400710742c9100e42204e02d9001e920b1900c20030704001a0a80794500c0300e030516401c81040d4102907075078203242401c0d0791a90380302202840001c0f030388508444c0c00c50b4940300090041ca080b41103c1e901608280d49880c0c2f01140030340d04c84c89465130042c1c442c840140426070205510b000c544107083c071120341e43d5904001c000c6006d1103410082502038003107840210900006014499035220b9103506111245107001648d00041ca5500c02280c0110b07105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 515105557 1250 515104307 515104333
    0x150d0c0e0f04271b031a010b0f0f0c030705010504030f020c060a0804150b2106100312050c01090c0f08250512010b040212060a0b03100e06060c0607020c1011 69
    0x2080e00b2070b69000705400070014000003034422551303030540c2c0203917400140807980101403041d840c4424010301054000528010744412482c43d140150781f50311140b06004110704101e4441441228078040d84000200164580340c50040e00c400450b0100f500107214104c1c0004450420208548005000b9141c504503030b521aa17134401c000481601d0900002d4582e280e415164075400b1040099480203030031194400d90458109191242c0186044058415410200045001d0902242100c1c03150302d0f081e90f07220481c4581c60b0240280040040801402d1280014006420801201902d0b03c26042e513a180e224034407014110805410f40800058440d0020802c03440e040c1903584842c1e29940010910310100400142241c1242802c8919210400304001441c40c181d001074000c0c040c0a45424154100341c2c4181c09100a00d00400c42c50440e0305011415950750b040030780d9007074520101110054a0b056400a45465025494038000e880e847e41e40c200c071500035481104400c200030014100040d08903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 515106807 1250 515105557 515105621
    0x90f03011d15130227040302010516020c180405120708090a080f0706030b010c050313090b0d030f200627070302150a09180504051e0606150d0c0e0f04 66
    0x624401481c040f410411151895a10ba046e1050380245c000003064901804622549040d14911304c00b15040301e0b01c10b51145c3c1d10318500001d02c820248140d50550b40701d2400a281018800c03002d07844030400300d24202041203050040c1a132901c241e03041c1d411039a4540b42161345400b07180062510350041c0c0414490184a5070020704540014901220b81140940302c0c0b9041d54450104a8500400d0403070911541843e0b0040c2c1d1130780301041d100caa24150003a20002c0180b85299403080402045000702031300c25503a580603491512a040580d85075003022488580c007840c1e180080303103000790308170091314039204086907030011650040c08951818a601080e20000d5109200c01c209012131a100400d1010082e00014181124900c00043e2414142403032890000340604080c28140d848221050740000811110f0708800c06884d80000c80c1e80b5012140841e025a51004502c180742034041e03028194000a9192a01c1040c6d40320141c0030202e10034003040c1d0704541100c0e0b4419901a8400649817083c3c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 515107913 1106 515106807 515106829
    0x209070909020d022703060f070c0c06030c021e0c220c021b060711060703030b040510050411071101052508030106030f140c090f03011d151302 63
    0x1750001e652500000c10250b40303115401d01243e44940140b0502e00d1880d4410302030140e864559000400030300c00c509140313005100d0300307000c0040d5a51070035902d03207401c041002030702540d040b0106000240301d003080309802a012507074015488101c00c3c45040640c3c0c0180d4090400f150001c0b0b0b0b101c01c1d2840000a881c4501810006d041c00100401d071102c0b02114240d5110307481d0105802c042d4018100903510750380081c00d2904010ba0801401940d106030f80e01100c0c10800c007101d960a01840c3d014481c03008000d0700903810042c140c0d60262010380380c484021803454044c0300a502681d100c1f0030070010f0072a04000e0210052103075a070517000c1d44a0050500100b000011107800c041c100030040903201034038140300000c500501d41c03610070400740e6400014000340b0520818010341c0d2821410030150a043d0f00928084184000003944071601489560400006148081d000c11a03d03440c0f03 = true := by decide +kernel

theorem cover : BRFrame.Cov 514928057 515107913 := by
  have h0 := BRFrame.cov_init 514928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514928057 ≤ n) (h2 : n < 515107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
