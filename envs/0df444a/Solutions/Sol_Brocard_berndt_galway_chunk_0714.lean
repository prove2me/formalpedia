-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0714
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:17:51.681093+00:00
-- url     : https://prove2.me/submissions/9b1771be-24dd-40d2-92cd-e093806495f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128237410 ≤ n < 128417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128238660 1250 128237410 128237413
    0x706022113060c05060f0412030f061503050a0b040c320c010b010f031b111908031506130b03130501020c1e07060801030213090c170118080313080903 66
    0x8009082c603005414052024800c00c240e812a590f9000d40360500402243c024203009100c01d8600400c900030740c08602810f0708280c0200c0c40c5500c48400507801c01000c150880001d40d038004201c0300f1146845094183c86044a0a222a800c2c8803030040850341240690510780044482c1171003000c07401c0c00919000400d41c0d030380d00d89504081c403140b0300038402c500416001c54200b0600a403028441d1050b0780112a008688603108036560703400b01c952060131200d0140314454074041c040c5621500280e001c12600c03851202d0380e20300e40400440d00f044940040180910407d02c070310004000d1600000050390b0780602500c0d00e9948413081c0c1041160000c1c1c0280440d440024452410400843c01c180c1581d10f9280b41281d8108844c0040d80d40c0d1003911460000464500050005240c80082c3d401c000c81d0b00c040108200c1450386038000d0100c0550b22038141c11a150200340e618040078001c1c80401c000d0b00206c2a01c0721907039181d006003440000d0101c08000e03158211030040002e51030603141f40d80000740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128239910 1250 128238660 128238697
    0x111e030d0e01080601020c1c080405120706020f0a02030a110d0c060f030606080408090111100513020a0605070302070b0c030c01060e0a0b06030106050702060d0920100207060221 78
    0x1103000d00615400c0603400c0c00900301030300040e5554000a4401d030240400760001900352640d900e14000340c45198811075420204000020301c9640b9007051400490800c0b000e071242d40e24046d806403500510b40c013062250b412181d480c0c0c0259401042d103006560f0404009141d0419242c00030304110203c2d88024a6000620b03070100d41150301402004c1d400701580c90800032107444601c01d42c0d8040c000c880003031400b03104000700c00095204807140c0a19418000c1100d20320404000004250381d42140c0854400f42e104460f0020361501d900f8070301c01441c03070b400c0c81840c044140d2030080d281c5115001d00e0404000015042145480c1001221480c1c103000c8004c109040e103070b0341e51400f008004c0d545405d2b80b03400c04004090510382401203904850309601c031185008a030b07500740030998204c140040107103036a9107800301c0415115400c2222252012101c2000110f0700d5040003080015a041c0078119840402c4c18002e1076000990440c0e0100c803100310074842100d40e0003c3c1c1d03140c170418ac24164034401c01c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128241160 1250 128239910 128239933
    0xe030307050604050606010c05030702060d091e050714060a0819110301050306160f0e0d02090406020703030c020303060f011206030c0b130b070803010e04020a0305030f070c090504111e03 82
    0x4540b05000340d10950507285140c80d41d10044404100f909000352240d04204002d07801890300c08010301c1c0321a02c204012410f0710300c54503101d10401d02c0e0541c18001e1004400c0d21010024240306010107000c42d04604200034180d000071400c00c0c0508496001848955800f25880d154441003100c16640400014041020f07450301a40703080d0030070310510b0301031320600000c900310941c0d0441e41c214805203a0358036882c441c0448822901046c58400040e0070100400c80000940c546607040c41c46140030307020241e42c2e20340034074004003200d60402d15103003103400c1030007406059030b01c03049400400c0400f441c00d42c45400501c401c038401131500b81c1c40240f0401c100d46c0005101000f0340c0140108140021040c00040c0c5d951003040342c10f220700341e00203042c11003c000601440130710a100540203800900030011272034aa03524249158001102c001c9101000b003022003c2196500c507810181074400001c2c80141026901d01405050000c0300a106d200e52200d591554200500900b503c1c400040c01c46803d036111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128242410 1250 128241160 128241163
    0xf01020405010201110f0a2d050712080907052707020a021201060602030d2a0513091506030b0d0b0f1b131e030501110c070806040f11010e03030705 65
    0x62090038059420050800d03030300c0d003141c02540c0148074071806c801e2a01d802c00c04106c0c0c800710750074823004074001d0450b43e41d4410300f90381c50500c8502c00c16840d10b6540d0102d504000d0540e012104000003089100340802201840200300101103d2040e10825a071250f9541403480c1e09901800c0c8a0703501c05002e007000708980e070015500b94014000d850483d0310040202c8070340c1c02e992030b40c081d030400340e4020070140c210549164056580040c01d440320f4020340028440541e03904580c0c0e02c1100000e4008240312028400e0750108070020040c43c40700708040036161030b0040c040030161144805066803a0384000f100d0726269940044d141d48541620301c54036065900603501c400c1a02c07040440d20180c0e11800d001d50000d822520660000c5541841140c0b5020030305215080b500c0c40920b00600c1c100300040021000d028078002c00c1101c0e41801c1e1214005000207280500c2c562041009074001c8042c480801c41c1a80e0302104550007401000e02025600c00680b40808016a40354152200040a20a0010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128243660 1250 128242410 128242417
    0x6030f01030b0c03090c010c1a0a0c0e0f0d0f03090308030103030f0e0612040b07050c03040b09030f0715080c040e0411040b0108010513020c120a050d14010b04090c020f0f0102 77
    0x2c500070808103074840c04821141c6000440e182010f50380401801c8410b90f00448412145501c034100894948001c050300000b1101e050b546004204d0300d41d90b00303818580d080a29040a03501c2620081c7d0403000d85400941071442c1c213200680396858100081c0141403003500d07030a0142d0b401082c015641d59592900a203150080201800015074080040231030745042001c4400301405c48000c03140d541c803075031103c91002d203002d800340c1c081c0001000941c42e00d85080c0040c2005055a081d115181d0842e80189400d0a4600d040750300650030101d010b1240415407882d5041d26103243c40d102181c0d42d600700c0652400c6c4910780294811b0180c1104100401c0002c07075665a10781000c0e1810b220703c4800b03c0054030782031001c1c068075a00034200b003030000d00d800c2d06601508048040a00302c82800e05146025120f543c04244040300141d0001400e0008506c240030318554412020304d120709541c0340200302e01003401640184c41c0307544d844d4030aa03266144200a0003600e40d100d1016110b661110000b494001d52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128244910 1250 128243660 128243663
    0xd0602040f081005040b06010f020a02120c0306010f030302150411130515030a0309120c15080105012c01030905010b0316051e06190c0803130606080102130302100e06030f0103 77
    0x215a0383d0003001c1010710300402d4040c0354400c9503c190754036110015a480d915900300107003144034000001c00075a503030701c00d00c2c0085102500501855542c110500d4100b0314141c0280741b0741c141d24081000041e80c000352005a03130140701c900081342e4030355150011041038028078a560120903a2291007007415140e02540c060441d190010307030300d500d07440d0506032030f03400005015000c00c072030fa0000c201d4000b1807040010320310320943c01106030940300d0a0380704544110041240000e80142c006020950b004015203000c4184048100b10400d1400c00560300074024030807550405455030f00030410000250040b0b10b010310014160f504003145949045044000f5110b0a0701c00c4100d0303211030f6071802c0385003480e043c41c034409448586044402200300805040300e03006c020070000804c0c04070f00400c00c0000554001c3c06002401286144642400790540e8801d4000c081c09910401c0313001c0446071151420011203505407a1442c02d041081019910035101e004000c0e009003000003000f012500240105069a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128246160 1250 128244910 128244913
    0x405010914100509011815020d0903050604021917010b011407030909090203150403050307201e16140319031b0c051305040b0f0702030a05090d0602040f08 68
    0xa50381e90316500c01c1d5207550800e560480b00d9108001030b0248510014a199807060505140708016020050064205540802c2038401c00e9103143e61600d9040c440b8110540340c6240041045003542c881d252a41d0001d003000780300b822a9616441122100d01e4014024a0000c654030600c80360800d4030b0f03011b0314501944900180c2407034041d20003031704c03400c00f13650b4555003540e02c000e80389081508800040c584060281e9140c460494604060303925504918800d51090342e600d42c0340d007048030380a0a0040c80c14050a40025008141c0f00010b100099008007d41e1200548222502c1034602d9410240f042101d10750303800300c040002c150030844099041c40c001090f000c035a66101080460040c100b4003040040000c2e0b00d07990141c0c0f40c200b080784030b0741c0c143d030090006c5804242d844002803111003520303031503030710041c3c40d1010041484284902d050b40402c1c0054200550b10303001000075224414400b408046c8540451012001e4803031510342d602465210f8000c651300c5441c0c0040001034880f610620549 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128247410 1250 128246160 128246177
    0x3050f0a2d0e0d0305091902130504050a0c0905160f09030c0602072301090b0d11070c050906040c020c21100504050d140a030506241818041101110109050102040501 72
    0x905110740325461042d034100c0041c104012628a8001c5518054031f426a80861001007000d80c400b903500c01c0e1801765109200900342d20300c451038001216211075200e400d603e4581b004010004102c1580c0e4510040c030b51070f07d407003011000c0f1000d0b40d00c00c0f842c0d0005810030810f89404074004e40c0016003041994400d544150f02c40c200c008000782080e0b43c0e5001a40054101e01003041040c50441c090690601084c070045a0005200c402c0a190f42086d081a08c0326040110100000e00707191030707400e8100e40291410710114040c410003a44d07450358040c41501800d450700848030000e03044001c203405407800500b0b456407041083c0709070010f490140da0030340302801800c0d1584007040c01494280a20301d042210a410000501400d1b401080010101a041301c141701b0b0900b440c224944c1403c1240d00036480303d5407114003809a581040881c1d408490054080b000414a4240c0c031103141541b055000c4d506404400c3d0210040300e0b0701c20301e45001000c079800e200c401020400d040d009042521030030381e80e0056 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128248660 1250 128247410 128247433
    0x21090102270a0506030402030a061e1103060a0513060504052401110a0206070c050904060f0b01020304050a090e010b060304150c1e1107080f010204050f0103050f0a2d0e 74
    0x150328003101c000300d40c0a81624020070590811102440e8080d00040545404105986640080d180455041c424031016031702e85a842c3c41e064417984501000c5c2d424104c2c11854604003003003141500d4003032188507441c80788414030b510540fa0400000f03000b000e082880b40d0700b095011070f00c25002d510f104480d44020700c0e00038401035120390060014541c01c50010491040e013a001d014642d400003405442c44400039001190319110b502903140194418500002c0b9684006074035811900c2c0200182d045400800040125075262039203842071b40ea46220014038190030003080c0e4018202d0b2400d8070b4200602108100c2440300d04044801c86203040282406440080321048400c03003200170091040140c0c8a00200d000341c4104d03119000d556540c011104060345032a00700740382c5405620001c056a4000030140103034203050200742400d0302c1c00e003400e00107428210308070b45541f24010410840d290b0303183c2108484881004120a1108401c0302640aa205040d07010002e8207102107540c81a00c29001000f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128249910 1250 128248660 128248717
    0xe010e0d0e120d1d03031308030901020f0316080d06030507170d020a03050d0b03150a09060e030405060405060f0d05010b04150c0c1509030605070f0f09180221090102 73
    0x1d0fa07480ea40c0c0d641d03000499901e586102c0f03038100c0b0460031341512050046500543d1407405900c05071420744001c581f100780d58800286001d14144030300010b6001402a43d5101040ea1808415503600c00c0d0300c1c648404d00720789000000c00301c9500241c00e5100b1400e0000b05a035011414001024440e810f840c00300c1012001683c0d50b030030070074009000a00801215031000381c982d00040c8003400080c10780314000c031001c0701d902c01d8410a84031400e0666a86642404200540c801c8441c01e01810000e5420103180c840061103501551180c507000f0000020030300c0007103030020221035101c2c0e0960810007007035868144400d00c0e5081030040021811849403001005809501101440366025000c0442142080000d01e0301d40c45607960704007030208090011000942600603607114551903540d8000c0303210b100500821048000c518503007400040c41c41480794100d05a04c03c07031060800c0001596170301f544264002540e5030780c44004215402c400500145081c10740050880c40c1c0030015001d0802103031002003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128251160 1250 128249910 128249923
    0x311010c29180f03070201110319020f0c03010603051c02031c0902040c030209150d0204050310020d050f0c030126030c0105010801060915030209070e06280c1101030e010e0d0e12 78
    0x20420380e131082c402d1000540c41070140e00e074810500e00a0700e040c0582c20320003000c0580d48010801c00f603049107040100380340c400c00507001e0901e800c50081c0502442c1d61580b80d182c01c1403503e4100e00c0c0b400300e07019030440c600030400c9607507942185280e40d0b106803a5403d688014203030000c080744a00e003000d0888248a01c030b4000d58800398401480c44148515003000c0303411076489041095601078082c80002400ea030140980c00d00081030000241c1d65141d0284410202c8000806c5c2c0450b148007a010303c00801d4241e02070741e054580d100800c10480a50404254800080c803071b03507050500c4005135082e444081900714034100c43c900c00091085a440e0340009064540303d41c14401c41c802c141d0020000340c90655511500040c0c1400c000300498403820100c1c40c140d002c198550002a0520102e080d02260564042410005441d00c81c1d100f4159658020046200344021030405840c0c1d02010800314083d4882c0f500004000308aa0f00c610401101800340030780d11040500c180320708521112a0b41011408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128252410 1250 128251160 128251183
    0x203071a19050720100f051b0a020a060504110a06023702010c020d080c0a120302070305041e0810240e01051302070c06050c0609070311010c2918 64
    0x120181c102001c042c070300c001000346100491501c00c0ca05c0c0c062100145114a01c904040036802080c140741001c01c01c1240189080078020401003000f051950035404505020481c2d407088002c00e0b60b844906004030740c103980c810456448076503d00c0c00641540c000a401070804004880c2c0d021000c460b014015038500c02100185040310012400401503104500c000c014510040c81482d0041150b200c07219250440042d0001d90f81c046000c1009201c03400300c00a20480c900c0c41c040d441c0c141c9070b5400921034042c80c803520b0083c001e0444080307161400c050303444015051010480e000d4041e80305000c00039240208a1015a00e540420700301460030304a081000d0319240c404c1c040007030b4608070034840003891320300846c0d1303503540d007408400d000503400907840d00200701c10b981c0d40c0d0720b90f400b403000f550511002038002041b40e40b18a008000151051842c420080004d0038a1950600c09052100403031045025610340101c10240000c0409034010000d4024030884159604c49981d03070058503988c40c0c1c0c03041c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128253660 1250 128252410 128252417
    0x90f01090302190c080601060509150a0c0b04050a02190f120f11061c330e0c09030a050a14060108060f04060605040203040b0109050916090b010203071a190507 70
    0x141e220700200700d00b0021401489100e0900c0078660707170019181401000c0e040840080c200260807070641c6080c02c040c520706041000080d00c0c00301200b2018004d6042e40c2001084019000002030900406005090100e50060b0206540c221840c0c51200714281900804541c00c1e00b0709008107c05c0e01903101402050752040700c10b0000200da80707070003440c00b21500c1c006500c50f104120111101c1c4005501e03011503800c503203012450044440c20032040c0304040d101c0c2d440340c4403144510142004040ca11004036290425840215114292059401d10680d0a21905441803864902c1081000105001d6071801007203102400c0e405460362075102e12003841141040c2d0f0002e004114000004050309130018401c0000003245582c840128080c0c2c0c104580aa07004004400104203191050003040d5102d03003180c02800c0725003081c00318203581005c07500807034450700c0d0395124006090340200115038030b440e00941072510042100041c2c0c0007118040b101d0283d8100c003021090300e4207001e4001c40e4002d00d02e60701e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128254910 1250 128253660 128253673
    0x2030303100801050a0c05120a15120b06060901021b010210060e040501050f070504060e0102100504050609010e120d0218060304051c0314071101060b040f030201021506031e030c15090f01090302 85
    0x18600400c524049c184e014165602d4111203207080315080200020800420504080401814003007031703284008004502030002000280c04585e40481c401103603015072048040001c2c04040100c3c5455500030700004024a024030204202050340384091003544100000d015542e6200e50b802c142a800342c9000003c00e4051100b44840d40c0107408d090708406042c070442c0d1403030860407181010303200c042c3e03000d4455411850a00118000038000c075200740b05100001e051b0b6a201300c100c40064411480d0744071031542d010640502403041d20310005003008004000c652241000e00700070b0b031904071607000780038420129840e0102035402409420b4480841d410301400c0c0303984600b01610210480d5030005200e5603104804500e061000004d0300c0500410300c084464079046200291810002c400041c1d4029505400c0000e6598001410396000c901c600444241c540307c400030b41e2450041b41c6101066010740d0440340741a0082d030194504c6440d5000442d002c2c2161400c41c98200c6101c05405401a0000c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128256160 1250 128254910 128254927
    0x105040324181a0402030d0e1c031e0c020904030309110d0c180504050c010e010c0b010909030912020f09060109030204050f04030917060106180302030303100801050a0c05 75
    0x81510062028150024803031030180710400c80200c0c0c4400c0800401c2007250b4081e4400d101e0200f02400b0102815030006405051580010742d4609078199000308010002e000c42c2407544484800c4410442d040c07004034040b00e042d1401404103141c048105041d50803055a01111611885c24412082d40203890301c2819142c2e80c41c00c0f00a07007046541038504040030941b40b042c6888034880c5a40d054041d86c501c07001c86041caa03550180118803401454013505210511000c80e5003c502107101a1003403c14201d010401001038954000004e0081c1c52245030500000d9416500d401244903a0312030740d80d08603140e843c0e84200c440306000b1074020b5041282c02c00302c004d050030404500c0750090014148546000c0c4c1e254006401d44000b200d1070703590b0380400e00a1204141d00040e400c00174115003030304103804010440d1a1580d81405104243c108038600090548410781c108011014540203015641d6130301d480d01525081c05028070a146280d8a0600040c981c07032114402e2559000042e9903e40c40c1502c076 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128257410 1250 128256160 128256173
    0x50c03030a091406041805060301060801020f1602010e090901020a02070b0c0d03111308030c010f021e07081c0b01020c030706120218041e051506030105010305041a0703270201050403 80
    0xa140c0d00c9078209908202c00304030f401c01082081c1041e0300e4034071b001c1410718201c001d142c2580c0d0395922204440c3c0c010701c08407002ca005176080d614490039542000300b6500b164001240c80522802000341c02680c03403003e01403816819001407002005a400301c450340b40e580e8403255494464528241c0d159000302c110342c804140700760407000c2000304200140c1d05000f000032582421010360f50001c040359200144002c013070711085c0200b42c1c0400c0c07040d1b800c42c10f00c601d201c1780044050081007000310f10880000e050007040b601070203039100d8800344500441001504030000c4000c010100b030003030161003003136681001450001004000e840381030380c13071032000368445114a0103904002c030a1410568803984010703603519076208200402810590310b41994081026003c00c40e003000d0849114003445841c0b2801a0702c1f16000c80e03045500030300e80000c0716aa24146680d00c60302c1130501c42015a071700c40620042e00c3d45900000b5036a40030440c90080c4151202d41c0c0101c0200c02000240403070024801000410070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128258660 1250 128257410 128257439
    0x70602070302100c140d0f060b0a020723090408160602030f1e0705040504020d0e01140f0a0b0d030e0d0f11040c020304180c3b0609150c01110d0504050c03030a09 71
    0x9100300c0408c07010384914070000b00350005010100160310401041015076940c4a074000f810030244040074580c981e240c0440c0c401080140003030802070000030040c5080a81c150040340b04c1e038009004545a0500611001d003105040e80c1c600f81c54200600b0200314004c1c1d80c0d02180c041e03491525210321342850001400040d412821001c2003403030340c4400b5038451007001e015034070103041441c0340d0001610340310b103904d048082d02410011501d490800d0032002c68440c0243d4010241c1c16050100078000844000303280c0016190f40104141d6100d100d01c0304000341c1c00000c041421007128140400015040101d950b40228480d503003050b03600412135150210181d110004003641c92510320388004500511800d4446840c9042d0600c10208500040c001444420485400030455100e8a40076080c4002003990080388040d0210700350000c2c0d000c030401825849007145400801c49aa220403007000c50f81c0080208030740030b458502822881602c9846d010044420121145d101c001e801d0381003080b180441e54 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128259910 1250 128258660 128258681
    0xf06040b0607020604030804061103070c09021b0f060402091305060103020d08040305030a020708151311030709090302010518010903020a0b070201110304061b080112020f06070602070302100c140d 86
    0x110402c0201c1c0580c0320803000704043c5000b6078903e640c903032404030300a1200a405c04061144e40040c4a14000076800550940c111607400f00301603101c002c00310300149059400707100004140314012a926500001040c4103215500880e0130760040c0e07440081d029484810742100600f99084900180018901400b900e419140250680b0f41071544940c0d0742e500c0d5900001c403007400b59006500401482e038041020140480d002d91020303140c1c2c141030380d11007542c1c44040e1008240703040070220084030340c80420070440241142013052001380b102c2e0401a009090654401c45661070318104d01c0100c0b0700500440d01c4450341980203081d02e1546845003d11120080e1002c0304654840000705e988040303001c00303140104e01550340020740081806503907240841001c08a0140700021004000b0340c01000041202c554058030080400086000064101e2082c5840244030314400300e0303050180b65000851120181102c9420000d86440c81d009544a000805182c1c0b0b0b4880301b0040300c070340500d540d04045c0010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128261160 1250 128259910 128259919
    0x14060d1a0316030b0703020a05040909060905011503060f05010605040509100e0f0702010c090f090207020d020a0608100909021e01030b0d081903090c0303050f0d050a060603140f06040b 81
    0x40c001500064200100c18800402000d206481441070001ca07003191504540b03642030440c40d01c0380004c4003814a0040d40b00d9001c000d5950050041070000c40d030030400c070180d4010000c001080e034814110310a81007500060b66018038140214080d6502885600d05030703189038991a00b480d14260030044005d100130403850020480c803100081c2e41d88214908c1b4040c0e01e01c440050b401d803521010090031110701003082003c0007000e40040081610030600017017568070485c0003607924910b50012a240740701d170301c03c000c0d046401e03450000703a01907111448602841c03004a1091550b9620342c425410342d100801c01a61200510002c0480020246000b40c103244041c1008111449104c0c000358510510031f405076000c031400900600070309000b64011068647c5804d08110281c01626502041c0c555400000c05118002900340c40e503000541c251102c80c0080c0106100e54541840c0700c001030141d602c83c20303001c41c5c184020004c41210700c403000b5100340035a0402192030740c2c0d18000c05c070141030006110380c0c22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128262410 1250 128261160 128261201
    0x2091b07080703080402010e0906010f1808150901360204090807050604060c03060308030a0903030b03030c03121509040b06060c1203041b0803070308070504050d03030e0714060d 78
    0x400c6030015000b01c50080c2c440000600e0540005008581c000c142c1c0703032242a09004112903681c1000391520b14036010f14049031070304421003420300050f0f00380e08444020700c038107541c3c480c801a40a054a103e1640e04000b0301c944030076121300000f032140c913101c01100990003c0100d1411800400000181800203101046c41c00940e1184041c42d0b200d1402500d582d0407250810003404128000c00d0394040756441c0070050b0034031755100d0036482d00014201c1c144160311440c0240905103e5000507116810003410b507030391000740c0441290b0340d5102c1a030107010400d0f600d0001e190604491025109030314040d0036100b003940c0700d0360f80d010308036030060842d90b001c0700034003481d080c50100700000415501e89205050b942c0c140b90824255403401d0309003403141281c20410a105040300401600c08560f454189010303292150300c000da945008682010790400c0c01d540124003810790580001011103c0103040d221342a41751f0340602c5812940044007a081682008103520850240d07000c18600f01202884054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128263660 1250 128262410 128262413
    0x20f090a0305011d06150f040f180c081209040c0212030705040305060919030503040f0f0305070b0601030603020f011b061a0102060c070209010608060d050601150e03070302091b07 79
    0x40d4405540c1003650982e56400f0540b8205460810142c20142400002c0a1a1a00749001594103858502050003000c003040919603035242e9402400e01007280600620444400000c100d00045400d90280d40c007542009000618400104d0600c00c0c6103441520300303180085560510001c2c006044140c01148200215000c0e11101d8002031030144d45d44c0d03940c0c241d58034918205985440006002c2d031880e50002c003039003034104003104d83d015502036050a2a0307403255180d050140105890607400340c180c02d004842c0f9003c00d58080010404644501c01900482d00c94400440440e441c038000250030200c40080509150f000300e21070051000d220030480c15520055070b48506a610503040e07040c1c02d180c03030b213880d034a150b070140204c075840280159101c1c140070305600020b40460040c4621410b04c8241d002003040350700ca2446112000d900501110401e5a4501441190440b03009910000914150803085545008034007241100d400030301000c450740300d44050541c0300780700c0340b100103048204008110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128264910 1250 128263660 128263669
    0x1b01050c0105010821090310150b0c06060907020109111e04061707080a0314030c0409050f0105030c0102070501021209060c071203020c040621050f0106260f060a020f09 74
    0x5004e080c0d01009006000000c2c1600c0d002051003030028281c0500a101c1d080958600103001d6030001c0d0250380c040350301c6820013051090014140c1090111100029102c034000341300182450003010199040102030f690420128200e0344880c1d00140b40d41d1042404024519103140744485071010310341400b4140c040f01c00000c0480e0110b41c04502c0d101161001030300c4200082c001c001c014030000303007d00154482c0780c1d80101030b44502106010743d00b1000c80800c038040c10341410364003c1d0600f503208000d036042c503526002c0e8011091241e43c1c804c0c881d40300f1103041548041032140071202e06030000c0510b4501103901c011142c0103541900d42180342071000401c9902d04005010080502c04403000190b500b6040003401d0500304002e05000320706219041201d0a0440a281c0ca280706001c2510710303614244c50042e042090300411480b8075803e000c0089041402410001a601c0800032806060303e408511251100203690114410340c002d030000503a80c40756a0004c01c9500c03402c1094500d441d40344000070307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128266160 1250 128264910 128264921
    0xa081302030106150e100e09010b0d020706020708030412030c050921031207030e0a0f0201080a09023607020d0f12060603060e100506030a110903010e0c01080a05091b01050c01 77
    0x1130001030780c040000d21040c00d10b82c1c40300381c805a1516251450614500110b102d0f00b07030620840d100048001400c80c42d0b000150b059501c0c0700d0348000e09540c4d036030b00c5003030800e800d80007640d050780c00601462005003e54000d109901c41140c0c0340e02da43e400c1c007032001c0410134802070303501e450300c100e01500c1d55640c280d107400d000a0a10141044004480d0705203400000c0450301200303600001588410303082c20100300111075521410fa82440c040700d881e5500320041c1d000e0b149480e1300070340201d004200c04000c40c20358400010b1082c00300740020b989230b8800070200d4041c2e805070f5850380941c000c8124946010b12564020217800c1040c100348240e0b0545040c400c044840b2503000c5000240d85010a000c00c104c039400050308810345200b034142c00c50814001500a100184c100c4075900d03078645d44c1d500000006002c1d03d088002c000e00030401c1c0b100e807080c0b05484604d42c104d2680080c03071040008101201070320820313008901810062542030820f50182e4040002c5405450501006010803c885d0500740070b103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128267410 1250 128266160 128266199
    0xe0f040c03020310080601060c021002100617010e0102160f050304150203030402040515180703091505040308060a080a02060706020c1e07170309060306010507050703030201061a0a081302030106 85
    0x43c0d80b880c111025400000d881e40001d0419080072004200301c56000300c4030303800250103c0e0b80d02020707001c0e184160301d01800c0500385038140d820094000344000d256031080000d5a081c1d402030041c16030040140f800c034411860400007414090402c203011401256884e071103940f240e82160b02d03003038407024010f001642d1400c846005034400410071085040c03500516401034070710f116800c650710039070002404503100100001a085265000601301078401d8204203690354001d4010b0703c820400340904400713003e04030313800c0c2e01140d0110b010803030750709000e002002220b2040f800b1b8050901540e0801c001a4044a41a10103035000c3c030140440c03910078001d28900c1000d4440011404015401060404841da40805c2c0c1e04e02040d91000308169020040b140d03511703421180302d640c035501c44005a0742c60003801c6002e001440350701c40100802d0780550081050f02c111401c100e03081282a042c0803101c0c8a40b851890003e00400d01282410244a901d0304c00c0b07a100400100341c05442d0314803c030580200051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128268660 1250 128267410 128267417
    0x303030c0904200901111c021b09010b070609240e06060909032209020712181d04060b04180201140306090103080309120a050a032a0e0f040c 62
    0x154400c031031030240308205840c0ca2455100c11510182d100c0c4225134010b1a03852030502c50b664411504c128014400070b42082a025642e2050344c1c00004001c2d51018100340c02800c0c0c0d142d00d060b0800900d08141c03118120750242c80caa52070850991f450780e0103065110002c8541c000d214280c00039141808000c00607039040d080c1d0014843c001169514035000e0060001c0d4000c0c40c200c400d0103122800441251005c40100300280031f0580e210400141c401016881121018404a0504c0c20060041c2004811003200e6035100c1d81011801c40c00881804071b4841c1d1603100364081e4010036400350107007810394094022500010a510b032140801d066494881400d81e0841d1500d0a039011580c12034040111040742c1d206450951400c0380c007060400c00103000150015034040001414204100720501d807207000c0714030b00c0e41c417000c08401c06000ad801421140001c6420142590030b440e051100c80d030b103070a11040c107269801c142018140d8003100514401074001200c201005160f8a40703005900125500d0766 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128269910 1250 128268660 128268667
    0x1151e050a0305070e0622052e02030c06150d020312040815061309080c0a0516080307030206060103240b03150607030504090209040204031e0b1006120902010903020303030c 76
    0x2402012200d00504004c1400b20312400308003c4d8503808295910300948201c004c0c05800384070448070002c5001d92213554071541c0b408801d42e01d4900c9503410712001401251813000c3d500c402200340d0b20fa024000c10030032164841c20000c0d91032158070811802920016248152011003074002c641400507080212000a0b40010200201602005040c529880a200600c5c55003419000a550040b01e03400035a525501c0e42002424403c8000440d0000c0100304221844d025491410301c2e00c0d000d0f081c00c1300a140303115000000f445100841240d40c4181e055000d00250b959400054009000103207002e42900d060480c03c0f0101e0030304910f1900038101d400b04042c0c6a10740548080d140506004010b0701884041c00300c04000b035044002d48065600f06100544c4500340e00010800a004075840a8401c008441a00d25031390001030f030040c00e160040030346841640d1100c0c2c20100290320f92040c000043c0c1d03882c0d400343c401c03c80ca40c0440f0680348145410b0900c6681da40010340355030015202003d0a0a000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128271160 1250 128269910 128269927
    0x80c0922050403141806090f0a14130203151203090d140c03010b1302160b0a02030a0e07052202040e070906020c04150303120b1509040b0a05030601151e05 68
    0x5010f81c2901401341d00820300d015107840d42070400400c0e698030b460241e00040303240b250580d20a00d50601040d400b0300301c151019a075210180c00550690380321030068624204220849001e402140d00c10204581c80c1692600c40405025120f40354000c4003070740e80028005417a25680d00302c080000e80340942820305609410454440c1041070810705c461081e032404400e4141a140c403004c0d40741d03100842d100161200c00c010141d90409848080003050504010200407451145901030350003600e2104041040c0760140000d29600c0c001030040e1f070b500046030300c0520072100c00c2e1103401c2103103170b17441c8000341c102a910031800111030416141a000300c2c4003088140500e03581041141c401203000c0b5414800116440c055013101d404500015040240603010b40c0f01302c40c1d058002040707050700907048200710703a20100e00011a8204202c910312070b0781404151560740c0b074410781d80419101c00a001d01641c0e40f07401c042400c020642d01c0d08038280074140c0c001a0303081280701e1019105245a45600382c2e04da003403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128272410 1250 128271160 128271167
    0x5030106030206160f140d08010b210a09050109030f021e030f0c0c060705150f0f01090c0c1a060103060914010e040c081606170907050103150e010f0e070c03080c0922050403 76
    0x141c1003072400c01c82c184140c0d90340420103440c120043c0c42f580c4501843e03446900358030000d00301003a0080c1c070642c02c2121020405510100100301000d43c2d0342992041c50500032001040c4800ca00c1c1c2443d1a842072200b01c011010700802055110311002c121119801c0070070115050340c0200e102521a43c100f04a13210280348009019a401280140c083d141d03840c20a11019030202c043c000c281c00c080e0750b4402c103550b940c045c404000649070000880c2444110b03030411004505011201540000d05180001a9550083c050042513003c01e000c1200390342c0c03c244041c1c02d5504020002c1c0c49081c1c1010f8009441d5005101200200c0c0c2914103581300541042005803040d613400c030120380322008040402034449030204400d005d468091038003044050008822070000c8020f030b088052624940e1b0000501c0801e4410b4810403134410241c1c14606581c0c0041c2aa4038506001018010074894000900d00c04003c10083c0001d580c01072004065180e03103c060f20030352200c0c01d010150280d607a8140018181c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128273660 1250 128272410 128272427
    0x21b060f0610020d030b060906030a050709150503040f02180a0b011e020a0f080408010c0e0f010f020303131a0702060604050a0e0d0c0812090304030b0105030106030206160f140d 78
    0xb07481606001102c280d00079994440c0341030301e41c00c259076030004801581c2c1e140121006448000e010039182d05001c0307110001080c05841d050040381e0200d00000d00c4000c0007004441c410340940720542196901c0c0c60302c0c8161000c88400704c0c0c0c03003c842450b0f01d00f00c40c0c1c40036005008160030040001c0c1210320400240c00820000c81045040886a0b240001140d0003d030024403180d0000f1b081142400350706c2e0428090286400c00301d13455007400c4846a03c075502940d15190300310308440c91032502c02c0c928015108604095980700c0140c008000040e950390444080c07041d4107208040d0081003045d591031700340000b40240c80c2c200058001900f8040c0d10720385802120381155502c00208102440b01c60815601c41d10951b01ca4140030110301910280071180064400c02c034904a003800741840c08410036500c0e580640000c81d26001c114002207141e003014442c080c02e60303130302030406481c2c56040100828030501b4082c040b150b00902d100601c0014081e001d10b0041b075403541e001010141c910801c060400311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128274910 1250 128273660 128273671
    0x50f092106370c02010e0601060e01180608010608041106070c260606040902030304090903080115080114060c0a060f060503010606030e0a0201030c090b03090706090e040c0315021b060f 81
    0xa099200c98400c4450703420105010b144900103501602010305034050500c500640c100745c0110340c000600d0760f070000c2c2c100701c20744426030b110900110348002042090f0b00d28051400080d24200040c007036540034119403900f1500410158400c03107100c20001c0d4107948060001c440070a5014403c01607181003030541128616900d00d60604500203041c1c15650f20700c0144014403c0e034481c010502951024400c5502030000d00741c05018051281c01d02910400080c840d07078503100504101da11940340720300103582c1a10700140501c40a0301144003007020581120301c0b84d080c540101c1400b18001003040c03042d500c1700341d006100410b2540ca450100340c01c5070460b51005060500b45101c513124050041658040240d090800144001103d8003c4420f98125002044100710000610850200010f60501210090354a0b440980d46554001d100084196001440c1d01859202800014000d002d082140e84520100504140e19283c02000018a10540c104c07640c0215040c8040003007080d15550303100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128276160 1250 128274910 128274961
    0xb0901140f1306030605010801200307021b01030e10051005060c03030604050a0615020307060c0e06160819090509090c06031b04051011150106050f092106 68
    0x9010820210785403800c012559481a007000b0000c0d4200c0b60181c0c4480c02840d005001041150786803007805008018a51042100081c00191504041c00e490101c03403103101564060a15001800c280740b05140c6059255410b040c0c80e2202001180020400d40b806c502401c0307070119040c20045d403208000a01d60b0005406500300f0080e440d80500000100d90b040902a50001503a54608003040000e04054010088254031940c2071011036a0000241070038a00402c41048070b02c4a980c8155481c4142d5039409400190074404140120740d20003c0021050160002034a040f2440802c3d009200c0b0010811000c140308203c01d00050400780305540c3e110001d100201034040710440058114000103080c0d49100003000f0300502d04030340b140192002400e01030100d52082040d200d000d4060b80c11580d1580f40740c4100c402e905441c1090900060488607951106072178103810481706002a071000b02641d4014061310b1644241c0c00c944850300f00040c5022010f4081800c0802d10040c00c811031240c0c05104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128277410 1250 128276160 128276189
    0x51503060702280506040f1a130602090118062c1c1103030403060e0d09051507060b090a020406180b09011110060b1b060f0a0c02100f0b0901 62
    0x1e00d40014410440c2c0200881c0c1d0080d8070007a11118034901203240004002d809040c090108200c10918200b040c0380c0b2801c0d41c10031200800c42591403a06085900c4080c100540c295180442e0b0a0340c01022004018035000254420300e030100110000b050780808000750b40c0e00480d021000c035047c009684603031010300d44240c000d01d00f00010207500d8440c0369690401503100c560401c03c1480b03800001049005825203807200e030f907410010700803c002d1041d403489001e040c2804055502c00c8007000252040100b11002c4181400021507003900400304c115031040d91100341c2c00d030b5542d588a03201d20034000e00d00003580d500d0901d00010402e004006800080300010b65051100ca14417505803000c0e04c00a10340251a20301d80c03d8568a0315022841c6480c40520301540403038141d01c0c82000300814081900508118401540e240c1d45c0d0f140d04860f1004035808110200c0c440700c0c0d03160404500c140c62881111051800c0b0304034002102c0c904917541e07020581d14104600b0a041800d200d038014900100704118 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128278660 1250 128277410 128277421
    0xb0d061a13060f0311010512091b060a020601060806060d0204030f0311070605161502190905150301120c2403050c030708040b0903040b04060809101e2304030305150306 74
    0x407040020b0000a01e4030303150941217040340e4484c00a507841d2400c1d0341c5508031075050120045456400f90348100d03140c6506128421070340c1c01e14208032030581c0113940c01000d81d40c0c600382c3c0c101c07800302010b0259980718030f003000100c3d0a0200350001e48042d500800b09800d00c00c07984d2501404610349244000119000103408000068012003174505d4503400c2c402d001240d01040c41e16a0b9804003d08a80e00311310300c041803103c00d01010203460741c0400c041c1d44804d0200d64035142040780c90318201d529030040d82420030040c400c031103000d0440642e02d441258840381c040e803102c144050001150780f0f158000d5032a003800e11070050b854042c698012000014a41c60743c103052000811058001b00b0141c1950090400304082c1c0504004882c014520400701503225500c840c00200380c400152034031070f01031180300d24540e446180c0b40700380300c0c1e880a007420025080300841c01e400c1c058a1185c136042c020b9080004420004201c40c03404501c05ca00c281d40c0098030303140040303203114010b80146113030b13001c2d9015000b00715 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128279910 1250 128278660 128278679
    0x7050c090f0402011d010314010806100f050307090e0703051e06130209060103090c030215040603050609090c12030421021002060705220f06200102070309090b0d061a1306 75
    0x55031180c4d01c0170307405d01d08080180103801a0003a100c00e0f00712306482800016040d00e0101d040d90040150710040a0003d940341c40c0301540d2545c0d80a069459085803000304a02e00082e486000d45500c8203003a034500b00e5607a00c0b52828142c2e20b0030740c5040700d551542101c3c8400020301100b940184009031803010100282c000c503800985c01070190b0b040c0b6568015002c240140a40000c0c015a0700400e03940b68500000b8400c6640e4100e0312401c004a41442c010401d2454010a00c0c0d2080d030b50351000f4900101c0a80401201032403100202005002c20400031480e6441e410081454007902e600e40c4800500a1040c010180122200c0c0c80440d0003d40601024135845803c44138050344100004000b805509054082d07040554451840710054010000781c490b0030890248009011584904080345e040d070503d4281e21a021008001a10100050048007440ea102a800c1c0c800030340a170740c0103580380d40c408080301c040e00000780c1c2051503c11400b11501e032001112004a006c910144042c518045044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 128281160 1250 128279910 128279927
    0x12030406050d0f0e0106060315080c0d0822060512070305100e060406180b030d0906091509031a060f0a030b0c2107081006090b090d060b0607050c090f040201 69
    0xb12102078030b42c12403a181d1089a0008400426420000c101da5659200e0240082c10000b185800ca00c00141340010f072076101164070401c3c2e407070142c000d1428880b56651245103603c868000c2624039901125900c0f103c20449000007d4007040e210a42d8403030075001030920b030085c020300c0348040604240030024205211401c08040307450042850342d050300e50100140c00303010280c006004207007685504007100c01c0250481000a4400e40546e045c410051000701c0f01c245241c0188404500c801e101041000002030050182d00700c50314100c01740315245d640d001e400d00c0d880000c5038490080202449034615004021214401c0300326034030503881d45569690759480b100245020107602e40030815680424140d023000344078650741344050380c0c6890520005440d680c0309544480114240680c00310300d090107040008141c071800c0f414582400d44480801c10104c0c190101212240c0d211a24440a030b102c200152080a100b040030781000c441200c103110000c50001c00302030300d542980f801d001c09030f60440c440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 128282410 1250 128281160 128281177
    0x804031d011e020106080102270604061707020106210303141b09060d02070b040b09060f01030f03090306060b0406080610091a07020d06020711090919020a03201203040605 75
    0x110100d14000402c103900522559100d186154000100c440c040c130910a02099040500440c440043e1091414001c060090f40201c102145103c920703880796440d0224802c1d0b120041c0d00c004201c540e01c07a190041c26490111130a5003010254481800b010703014001c00101d0520003204403860314080c458462051650a100c214581c40014060f030241c451004591100000d401c0655544145e0324080c0b542490032030302940c011034007502055103182c011070b5090043c41040003c4641e41d007551509115084000412001e0001020700080080c9190144100504901c650b15441d5441d000d00501119001004203100354805a981100d0a030044210302c10f0700c40c004c4106203500055051001644140300f0043d602010b04880c00c010014240c00801c20b2500c101f05024003800d18005100382030109035030200307180d004900901981901000c40105e601d00062148501e199661101c613000301c1d12070042001e0307010002c02001301c0d00382302e8902e0904e0300d03610005602d40742c60303d40c000b86140035513040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 128283660 1250 128282410 128282447
    0x10f0e100507110307060c1203050f06270c0a0f020a0206180a1a0403061805072309090105091603080d050a0b1e0424031518030804031d01 61
    0x20b1000034004a2100c2e0750204001500f10b03110161161000760182044041c202c1d4903004410490200920a000d15401141c440d1082d010540b24102081120201018003507021001d11401c0943d2140000d01c0500408003041003941d2034131000310042461290f0074540083d540440282c10058030707030034201c500b83c8039001403400d42001c0080c001030b003060701c6038040c1010070a401280c4140e640c0c000000e1084920031841003014510902c6620380d4266030340c60107881900000e600b0080401101d40c03100e11034140d201d000e03400145a000146074890306603070140c03071a9566420004403178400c0040400c481018003e00d840a491f6035141061481811003140c1c501d0b44440115010310340c160807541d2400c0000341007511070b0303078540703200031290703880c04141c1e1301c203e04103210b200b040c1050400c102905290100c0c4404040d080d41c80301c1000200029840c4d401594600701c88000c220350003440b41300b0a01c41e0380d60022504050900420101a100104600c51401d424a81003030381c00c0549014030005022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 128284910 1250 128283660 128283667
    0x60102010b0d060b0f0d0803010602061501050702040c050f070501061809021e0a03060c030b03010b060910030b0d1a1b0a081f030503040801020912030412152009010f0e1005 76
    0xc0215109607109090b607078010503025003440402c91f010000d941030307407096801c0b40c1541d138620b242511051007a0007044e01044017086828090f00f8243c018800340011401d22030b04c0c01d08407100c0750140b50b01c4003105072480d0755146414848400b100d10790709405002d03880b06200c00002900011840219001c00001c078a6001d9100c0125484030400d0b90015600000204000380031240041c0c05070900c61a41b61195103028001400d034541801030320b03e058405804010001c031204c20a40003410000400c80e0f100c1f5500e10040002044400b14074486603074441c000c01141020307040045030000f40c100d0003441c401c00b40b000113801039101098991008110080c00606089c514504214070074940000c0d02d81e000c0010702084005054005000e01d2009984600e5070500e02510561280250b010710141c7c041515680f502113100440000907100d402000000da034961210212a000030290b0a100c80d43c0c00441d58601039a040502d00250001d203041c080e40020400e0300145201c0c919140030411b010012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 128286160 1250 128284910 128284931
    0x12070201060509070c02090601080702100209010207030f1103060705041a07081306020105090d080103051005040201050f03070807080138070606030c03171c0903050c010906050f060102010b0d06 85
    0x75040074000b41005004040c2e10304001100405105004030164090310542011540552046c1070003482424540d001d030001d2160b0329414130103540b1a0085a04600c100a00400400e8601c044108014426a0301403043c030641c0381031504006004200b0300a00c90300f400100051b40c800c41c50300107003221b1078a0681d0345100620307000c0d129019950001c24090a2240041403440c1c0551201e4010101c43d8225480305203ea0300071540c81200f4040248560010700c42c420500416400160308503105062850819440000b000d60300d400c220381c8040015207882c140a8181c0d00b24452501402c40156103c0107490102e4101075161000850600b2a45c408204820b42c00440380a07140c1490344600117000c0e043c1d032070030300d000120035500040d01c41003a00010182458041e4003203c207541c041d00096424001c6240808000b0259600142c00b07000e0b04001c81e00d5030030360a21031501200d22800d40040d0604040301705500440c001088a0705580c58108029640e40e90074061010440e88044042040e0070a13 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 128287410 1250 128286160 128286163
    0x4080711040f140711010b060d15150f0e15070321020711150703091401171815240303090405041203050f01050a060809011b0f031a06120702 62
    0x1e828506428a001540c0d550f00407040261030140d9410303a201c10524001d00040c03400c03221901c50140c0e11000400c02044020f44540160b8070301000c042c4400c240030340c3c8142d08003034003038440a0080050b07480c10491401e01d070025545200d807030041e10007880c02001d01100c19414840d01d440a0305000500345880a022141c001041400d4030b401d40c150745481c040d10313014104110a4900078416041c10f200600c5101082c01924405600f580d208a072241c5002035016500c1c1d0400c00c528108070051006004030214200e0440c0610b824181410000303400d8805581849507e42e6090f51a246150501000e980000703440002112255100c1c8546050000082c0c43c500c0356080342034000d402d010400083c81105020182c0090050700c05001f540d8500d00c4800305903d090180035408100c40c44144429440350070741c40c1c0c0c4800540c000082c0861002d00d0313607120455800c0000300003540c0014040400d54075001d0b03450b0342102104189003540002c800101d0380d004020580361254181c2000070342c070b94030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 128288660 1250 128287410 128287421
    0xe01031718120309030c0f06040b0c0118111002010c0905012706050307090e0103050303010b091c050c0a0f0e060f0105070b01061205010b1908150306130b010e0408071104 75
    0x1c0288150a090036442c5900d440b07800482040c0d109000d607a10140144c100000320410080d001001d2520305030801802e200990040440ea0b45150343c4c500010500c80b40742d0415107107260090780360000340111403040051441e010f00c0400704590509050741c402940042d01c0100b0341e82d090030a021110000d280c0300190083c0380340d0041201c00b1411001441d681c014000b1405000e16541e9030150903168000502c1c1103c081c8802815a44200010840040034401078511030400414205110a010811014460040c5800d6849801101c4201540d14210303541100a1800c4d8015038a05460701c42c2c20002c4440040c00d2a0107208600045516680b0620480e180140e2150341c00f4900d5845800041654100c001d404181d185800c0021421904060035a08a40360900310411300120304030080301e0701c8802500c0690b015070b02c0450f2a020b56002e100c407074429039000c26508524442d60401168016041c0d1114203e22000414080420540012681401d0300408006526455400850300500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 128289910 1250 128288660 128288707
    0x601050c030f04050102120a0203030a1a220c020a0201091e0e0c130e0402031b0f0a03030e090f04020306070c030e040507050a120c05070204090f2a0e010317 69
    0x50744000490119000d00f069031005c0e800c8451040400f804450f0702d110780c02c64140075074020700000d215200c40d80c100f0442c0241003002ea850291004c1d0118502d10080700504070301caa0b03142c001c441036030300b01c0c81500c808000c80d1000700101d0000d80c0000c2c01001c85402840c40da4001d89201c602c94144500b00c0300d00a2010014070101e40c45d0480003440d441d00402c080341050b18200e14001490210031070704038020382d001005000240c0804062910300c00704080550f403c9020549844400e60322034100100660180e2100f440c901c029004204130305000a0030440302e98564030510000d610700281c4591b100c40d00d400c200740c028140b070800b80c03801e100d8488025071040c204410854215801006007154035007644031012004076a248400035151401ea103080080c0051143c8005881c242d040079810b01d003d031284c021540415155042a07032400700e61074840d00b6080caa40583d8006244030000204010440302c003080d4111399502100e45490b004800b000000450140d482c100203816400611 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 128291160 1250 128289910 128289913
    0x1f021c1a060c01092907020a0c0b0306120106080a0c05030a050309010f02071e06030e07060f05070c090501030605100806010501050f07141c11010b2b0807050703020a1409040b0601050c 81
    0x40c101d403004448080800540d805820358841c2c086480507000081c00c21108c0da000c040c04120721700306140c500380e54000809407036010780d0611855400d00001c0c800e44000d0f00740d80c1e001c1c00c82107480b8241214028a43d40c0240c0c004d50003003007150b02180c0d0100c00ea0352420800d01e000c1c2d0b0040017180d002c80ca8850035400164024441c56100004288a0005201100c070340d603c0c10301590b00d607112041d48034070740ba10481000c00c0c0c9491080707a406220344000d00700584181040d104607511039840e00c085070000d0300304552241d138881c144901b4032000801c840c01404102c00401e01c640c140400200107008640400c00018000700f100710400c42c1114a030500440c1c9034049a41a42c481c20384120f440345129000000302d101c040380f40e42c1c100130600465a03402009440c40d405625501c2e007154080c41c00240e800105604640c044000440c0701c0700901d07049004100410001e400c1d0f004006229030700d584041410b80d120043c040c0701d900e03014980d541c0a030300040c030082e45540341c00040e2100e118405140605 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 128292410 1250 128291160 128291183
    0x30408040f0b0306010f0c0b0121050114010302030f060c0d020d270308070c02181e010b120109050132180a140408030115021f021c1a060c0109 63
    0x51250300b400742d03101d200c3c26621202d501c85031340c40540312a40e11a0b07020740640600c034010301c2002c0c14500c0a103104000780d046000d00d0303d4213403070715800c50b1001803c607003c10b140000100151b103810440390f041d5040c510041c104c40c1c240081071401510845840c145c1c1560042864806541c0e280e0000e035040302403005250b004041801d411a050249440440c0850f68540c00300e00c03090310818421107426400f0300042803203100b010000700441d000030000c40b0103654801d04004040350f80503055008140b010f2086407203503c0d03140e0031166940143c01000b4003a1070000100562458610030300f001300000740c1c80a546103907290000d020380c210469419040024451002d08901250366410301c03419803501c4c03c00115050a42100b4541230680b009058541e003070005010004001509980341c003890f00449102086540064841581082d10a402290301150b84c08140c003c0a5000340314100d003481c1004603074040f40f004190034101c031031001d02803013000c140210410025480401440e400c803040080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 128293660 1250 128292410 128292419
    0x60908070602120a05060307060507060204030203010903090305011a09240a0f08060c0723010b0d14010f0510060f0e150405030d0507030e0d080d05090d02010b0609090c030408040f 79
    0xba51012465501d1001c81000151206202d8031030340c0d0180400802038904586046001c4403140c01041095a01550170400040140c1d0309204141c54244240c8a80c00342624600f41942103e030100028500c4140c40d84c12200c1c40c0d65031042c2c1079400103c2c1100002c000d00414401e4586100c031a80340e0790460181d51020440b6000621400e04842c2408101c03610307030782c400750701620f01d01880720000d100100102807035044820301070903640700c21504400042c5001086001941108510b00180d40310803a8a5a018070b100081c015044140680701090180c0d0400b0341742812942682d100d080100600b4940240308140300c2e03000d00c40505d80080c4240702c000100c600020f071030f500601c05d0300c6c82807040d85201d260080c0194261418140c15456890209403a0400d0002901400c001180c0c0c1e05800c20100d14030403214030400e800303040c01c003004100441900e0340113400c4458482e0040c2c4516002c1c000d20090340c1c0e40442c2160300183c0c071451039171251610315013a0220b002d26003000807031201c2c4120111703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 128294910 1250 128293660 128293673
    0x11010f0605031002160201051b010603030e18040f020907030605130e010c1d060a030902030109030e01020c030c060d020901030e0312040c0e01140d022b0515090709050406090807 78
    0x40581d202142a1042e151410031800120311480c10a030340300c1409000e40c1c1c4003540c040d901400b0b0030307114039040c0004100c3c50180613007100d50a400031000300ea60101011b00b40c0c24030b044441408442d00c0405a8181015124a208041c1c1040001d11440c0041d0010314454071a400c80002080090f1185818105840321038015100302542d003000c075840c0c11101030195114004050882c11000000603007001007005101c900e0740511024014140c03245440c40c0107031400d2051072000d030301940d03030b822a14109000090a2840010806110354000c1e00c8150741d81d0b5803142100d00002d1700c8180160740d2014a0300603009050360072111281d41c0404508190450003d001e2075205a20444403007400c1501e50824481004081c001e854109010700101845820300e00d0400b0001e41c0018080078a1110055000c0c03a10b1001c5440c035000c842c82040a541000020082030301c0b01e4918400100035480c01c0d4411b190344031018420221a0b0b619a00420306000c843c0c0d004840b010340210362950394410340c1c107101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 128296160 1250 128294910 128294921
    0xd11030f0d0c05060c091c0f0c06121514010813020a03080a080606041202090a060f170111160b0c190503090607020f0606010309150e0604120c03091511010f 69
    0x549240c0031303000000310401100000c4600c950001440d82445010416150305078151030364007212106051600080810b544a148000030140341d9550b406c151001c0c0c030904256481c1e518079564441c6c80130018001d080003050320548001080c60030b030702646d460248905203860303035000207500a20380d94808000c0c06a440010105410b8984907000241c4130340c07091003090b201c1c0e481160384402004c20f00c6801480c1102c2c0c00b640044200c84007142d00341d29010f0310010210700da80041c0c200800c1c5e08108003104428003603189602000a1114245680d6000c0340d200905050b80051031400040b00049030700c503002055424403501400500e80c0d5010000014006500c00d4070000d50701d01c02c0200080180d44005441c144460640c07020b005981c803000010340140200300c03001c469440b5112501c03402e200d003601c11a0144040b89009203080c0c2000c3c20071039000320010905d070381000044845280030079000b41404040300d0281408000a20885070119258944078001d242c0319400c180072141c2400058109 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 128297410 1250 128296160 128296163
    0xa030b01030519180c1716050303160302100c0306080c1e0402090102071a040f1e090510031b090c0c0f08030a2a08010609031e0201020c0d0b070912020d11030f0d0c 72
    0x2100c1030300c598144400d8108460344236180d810f900c01c01a600c814440402c1c910315803842030045550b5138112030b4550099800784a90400000c1d510f000401c80b0441c1042144140c1209491401050502071030f0780000184001c8840c0c0503e40001c3c440c5005e0340b080020900a26034462542c41c00c400c0c914100f0201c0c1d206201c0c01000303320400c0c011801040407608135400d84024a010380d010b601d03042030384014090003071182c90076440c0d040703001000c00d40c01d01d6992a425414000d1190590420301a00b01325005804a0000c0000313030090a8005090000c250841c0c81d0442c100940381d50318031415001410341d54100065000844041c8003030349031241918000104207031105041c0340c0c1c90f0742044880b07d040d44805401220b1514541e0602e0385608602400d4500610540380e00c11175a50115a100c12015400c58445040328100901180d0201400024002c465070070740505529800090102200c80b00c0903050030302c400007842c255501007040c4070031502c200d0243ca0030504440c038003810b407500c00d500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 128298660 1250 128297410 128297413
    0x16121b150e130b0108040b040309120302060906070e0303070f0f150903020c0102010e0309091308030711010c0504030b06010305070908010c090e090f0a08160c0b0a030b01030519180c17 81
    0xa00d070071032950140000f4040103944800e2203590726155681e640001400650a10041d0800481d4503043c156503020b850b03000341c0091055081c82c2500301c2c503181000b0800d03000c1105542e0102c1041d980070044640380d41e0001040d0050b00769909004000424140d07008007038010045060355000c14075048000c556001e6026a200301d43e0703030300040e800d07548400c58500b85500b081100d0000c034601248426040405e92241e201e0720b90807680c881c45160310585810002c610141050310b4904001d02400741100c001d89421400d0910b541d0baa030300a071708081d00305810301d0b4842c4006000588100d2000b00202403800c000d0100c6501031601030701070702240c06856903016030880080c0c42040000341040c001442a40140307007100903034403007100341c2c1c0120136031441441400000f03a010404090480025009000d0040c3d03540410303820140444091101081c1030500349010007540318844e03600140031301c1071520041024642055404800c00b00da0b0707001414100c0d0343d45c001c542d0014105a80c2d101d008900e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 128299910 1250 128298660 128298679
    0xc051203040e0a0603051603021f0210020c0106030c08070303080403030e0a120906091d07050306130608060105010e04140c0d020d02030a0204061115011406040905150316121b150e 79
    0x11f200c40c10034146000c00b03500000612000e40b6020504d644001d500e6081c4d1054800110003101c2080507a0311609506146a4490b0b9061051125003642d0700001d04551000b0f0445a14581e405454100000c0c405014140d54041001210409006803000d0303076444804001c0700e10031298064005600c0c1d01464001038002400400c0f1400e1010f00c06656105012044556a80d40c0e40100e440341e000400d41070f0008070400c150f0070404018024040948a81030190009604100004001000102040c0d104608008008405203480e24295400c41015601280d07900115100c1001900c02c85002a804610000812903800919409030040d0354503a130b20f004c9140c082c200065611108070140b5460421000c004201504942400080034107000d410141016a5504000c0850310f049480501940f50642c0103000c81c6814003560003290805c1c0400d09040d8103100d903900c2d5039260035100514a007407040b090181100549000c40007070000740011040040162002001502c61890304c901901001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 128301160 1250 128299910 128299933
    0x40f0309090b06040302040207020303041d01090f090f0201080c090d03050c0f120301090b01180902070203010e0313060503040501060f23030c101209020306010b0909010e040c051203040e0a060305 86
    0x1402545600c4800406090915056401f0031009500001d0121382c144820040094511200c020400c03090100c11402e01c001c0d03241515a501382d486546100404034a002180800100001c1400b0061a02840c0c100942d44c1e03602c100a040d44502d040040d1b00c03821080b8818101075111008000c050740c501c0c1501c0d00c15a04072025aa0f448449540204408044c00140001045c560103850710610500d000403182603c101040c058050b260001e5180c00e4001071201e045d42401d000303501c100d0804600840c54803540403458540c00752107000b050704120300000400e06101c025003104c0081e0044840020925075642c0e14040305c1c103070120000003150034aa044006c0c83c503001c070b0601680503001d08100c0c10040700315000c0700c00c0f900841820840c0d940d10444032000d62810402c1d1400fa1000f04113003503444524104100200304141d00c40380201c28440100400100900b691030200c03142a00c0c000c0e600d07007100c0421400c3d40070300c0c0c200c482441c150000300b003400d21207504900c00703c0c0d01070400d803484407003007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 128302410 1250 128301160 128301179
    0x207030e0316171038090105010e2d03060109050c0415030e0a12030b040204080705040c050c010c08190c0f0f030204080102130e01060912111503040f0309 68
    0x4800080c0d51284400e00c0411591110f00c04698200240d04143c03000c442c80024074030221001d41082c180c00d0b135900110300c5520b03820030b102d900404030004080010080e6a800258101c2814040c6e00d04100745c115070300805890b0b00310704641c0c605d006200e014a0343c655022442071100c032821214400c0c810031000085101107442400c0c01001d05109140c81d2500300040c07049803000e404d24503003c05903141e0810030150000d021002d000f40c842c1010101828181b84003c0a6850118503e48650f00c1008200111100020517104482c001c0c1d50110b00360217406d40586003802082c40043c0345508080c184030b402540300000034803480b081111503003540c07c2d00186808444030304d05031902048440801442c2039000f03030602d0009001e01d18002d803410362140c2c04a403ea07042044010504102c0210078000100041980e50140216281c201c59003460300d240c504110045010107810808146180c0020352200464081d50082083e03580d50349043c1468001c10320010a00306030b002882002010644496 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 128303660 1250 128302410 128302423
    0x150f0c080907050415081501050108011e0315090213050702010515010e0d0204061a1804090b04110a030b07120b01020c030d03020f09040509100c0302040308030f07030608100207030e03 81
    0x100c1c1008025680c141400d00c07008012460085070a42100040000c055404000801112628400b042c0700c5501d010700242034800306800c98101000c04d030440c460041001442ca07800c50350490240790120400f00d074108001c1580000c0650000496141d009607400d403600403d0050150364000c0000ea500c406602c800441c1450300301e400074600950320f01d44c2d40b83c074102c21f11000340018000035004d65640c0c8003080702a00d002c000d0300500800b10b0208040010b4140040012078140d4080c000514950341c1c0919508000b8401024903c80d1041c00d80720f40c40c3d551109001c0c5601682003000350401e004050a00b02c468503601d071004d428118280c9032548080743d5254160000380040c0805804030000364080c0d000520085105401400440c103d6a101e00540d0b000b00388110181c1900c0c68994011022703103000f01c038020140b500401c02000060802d8040700e6104080e031103030243d282c4800b0021400750001798080303005442401c1414450580d59802020342910903190000d4240780d00040c141c60301c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 128304910 1250 128303660 128303671
    0x70303120b0906010815090901060e16050f161a010905090703021f02010f0504140d030204180b1801091506020c03030304110a0b03040302010c0806010806030d0e030307150f0c08 78
    0x140540450f0155016191154015001135180720f000341c2520041420740340101e403a08140e07916000104811001450b882e6003010042800b815a100b030740034060603901c20490081c00c40d0600180d004030380c22220380700c440401e6004420741503048002c40d030428601000c2c05902216481d000105250000c009040c03801c59602030310b080302c3c26458008052090140000f02e00955480e000f00b00c002460324072801344201d206041c6d4070303030a61101414900d0035101c660040b0900d441007000b4084e0304043e100c1c8864403402004003141e40048070b00403420100310f120826001c1c80050001144205c0d203034204607110741d00074444580e050380c1c0710002c076520080380001c02d40541080002c500032401100c500900c1d62406445035451990f9074011243e070707510844050f0010b0355180710f040c0d01070754007050180d0020000d1030101c1860501c01c00003074031044501c19010034000306071000c2c842034a0900650b0203942d0400285100f04150302246030140c91003800d01a6030034548401410054050001c05000c0d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 128306160 1250 128304910 128304919
    0x170313080c2e120905030c07060e0a1a07030302070813050f01031109040504021c03050a030c080f1311150705010b03030f040b07020a0b0a050d1d0d1d12070303120b 72
    0x20300400c00c0d21001002800d20700900e841380382180c0401c1040005043d050304000040c882c0f6460114005c11071144545254880c401e038240402c515045107221000040e00e01c010301d40d903a1002d203000d400030300c507002005000600110344800d9245840400c0c03000c542040c5d8981034501c06140044048030000c56112107882001c1c094101c3d1400c1075400981d02c140b01810040004842030f0407201c0300d002c0b602c0210300056000510190032603060040d4410f0412504019610342000c034002d405070b80c0c00070407040c60805511604400e0240b032183c2c40c070307030707458044d0440500608203900040c0c01c0c0e0000384207880d151b00b003064007140d0382000001c031080300c101140788a00703040c100741c81c2c1b94980d40b1009003681d0144190304041410b00c401402010360b40380c56203034140e44001d8010600c0c2035807050322000c0c411070343c608090b260744400410b400d92480003d25003402003040204ca0209101d41340303042c2d190005041c403000c00c0170f002c00003500d1064034003c2d00d0340400c840724807540001342c484801c3e030305410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 128307410 1250 128306160 128306239
    0x90f05060912030c0d0e030904050f01170106050f010804030314010f05120615010c0602091903110301050124020a080a030c1103030103030c0807030c060905030a0e030604020307170313080c 83
    0x17a03166512030b18a01e00b50405613840e2040440010f070584509031207400c80c2e880b140e80100041e11400302c00e5038400c62000000c3c040d45140c5070028a05078507502140c1d050101303240c0020304041c030a60000354980c982d040c2913a4607585485554003200490300400b80101054031500140d01800102c0310311400284c0100701001c0c20200044400058041048440316000c4c49024015620700c126029542891000c0001843c91401c05040d180000081c3d20301992404005202c00c4e0658940340311100521a8071403098000e44400700d20300022648007030b0200030042410440503515401c1510107444c2c81d96500038040b11144401d80344d03c000e2000501145507a0021000510b2440c0030f0000c45020307003811240c0c081d158441c1c90903036480e020110b445810000340048565000f0184810501054008042514059000c6552030889006d0448584d030147c141115840082088541d804a42c944420750960b80301c400716500d5000090b21846401030140c1e80b10000c00b2440010f810b221a12400049c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 128308660 1250 128307410 128307427
    0x903020a0614070c0b07020a0b0c0d11070e010b030a050708070e0103150503160303090617042d03030c0201060b211b0f090a0504050c0d020d090f05060912030c 70
    0xb00d400a1005520040005000702c0000c21008164200141040c0e12010342d142c2451040022103100c2d41c100300460755062003081c040303250000303a511020751142004902c0c0c4822030700e01c500c0c05900323910000a100d17aa00010448407440780145006d0500c00c03030b050101e512901019510000c040b590940061020280b52109611179000034022912800402c1031440d280c0e008030b82041210105d03450a0741c0e1400c41001090352122603000200135618100d0102010b50720282c44541019102070302e00e40d00000e0700510100107031141da8100c244d80341d510004c1c1d001c1e4640640a4604065124055464401c0c00283c0008803001ca0b140540c034406894800c1c0c1003166601c600c0100500042001c5a044907000b83c0c81046000411166101401f0b03161540314040800c0842c101039008030b07002d00c0c01d02d000d20130701000c1e42c000e0713400340c00400c0d0b0301603200c801144030031004100c0900003401c4c251b000c1e0041c1042c89000701e5864003034035400060381c2c4044134604041c040c03488143d4054880f41b004006000c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 128309910 1250 128308660 128308667
    0xc0d02030c040f1403060907050631061d0f0108070f02011127060a02030a05030c09150909090d091403070b04030813170604020d1a0a0506040c0903020a06 68
    0x40d4400c00350300ca100c2c100b03a200c05410f111115260000c000d15006400045114541004441d030302103141c10040c042c160078040032441c58001c500c060300c0d03032440b50110f14007600310580e1640b04101900c5444c4aa669940e0001805030480101d100f03c3c9081144c010040e034204800184084a03041e1110708641d211000e046406221071419001155038442246000b1140c0383d0083c1014a800300200580410f0219074900e04200168814410041000703a244000c2d004016621001511305010b40c490340ca190110107a072007000b10840d44000c0000000a1038603002000c1c0500c0b8809680d4108160781e04011150b488087c0f1481801280040000300420408102c40c5950070b04090181c5445554400d0544200d4110350801c41d54482d0201d8480c00c11749a5032a401d00030856400d0280074400e010a03031507200d84010308042e0085000f2101385082c0001810704103c00910251070f1a0103142c41c10b842c1e00100026548944102d007000d0000301c1483c0704013079000a99400810001a5902e0001c00350b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 128311160 1250 128309910 128309917
    0x906061407081605010f0c031406010807051219050a1a0907020111030a0c0e011704030302030a18060501060311070221010b031506031e030a0f1b08090f090c0d02 71
    0x201d8508508000d01070b00c8107043c41d0083d00481c440c00021920640c000740c20016181c2004078842014a02401e1602d00480ca081554102c002800d00919540b94881c041b50f1500c10304041615504805050002a4410b0a030202c107041540e2010460f0380c40b002621b40c1920340d50140c080c4400441c0000c109a490f08100035900980c01d03000005a400ba408061002034108443c44186507a990100ea52003a400c0b100c4140d0001c0c003440c0c901d028034401090348040e0500648060105039000c000100c00074240d0b80101d10300019014214036001c0716140200c003814003400340d0781c0001c1c01c01c0020f0400094034019a90319030b0703000701845555050034010300c0b15808028441ba00c1c0d50340314210100592014011446280200e01c0d41c0421031902105052801c10840048105055443c185070441040401031b101e000c0c54918040408003e00d2004a46000802440d403041841d10642802005203040003402910000d8030024a43c40f1039608101c0300c100100c52210781d0030360811038050059120fa005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 128312410 1250 128311160 128311163
    0x92406060f081f0f030303090611030f0c03090109021203190809030f070204020909090d0f0f0c11010c05010c02070e0105060403030813030c05030f030f06030c0307060c02010309080c160906061407 86
    0x4440596138404003132540044680c401e80200390350b1840c132420b00004c0d02407103403e815120305547c0f444c1404541d049015400a00d0b4021610b0044045010f00070203401c80c034001500148101114245694040e40740e0f4010b80800b162403500102038110b02e4014003044e4410207448001c3c41c107081500884070343c0e03944400c2c42242d00550800c010540d542d21412814003482854004150b03040c070010f0040c2c80c42c10303903182000502c08150810340304154080070803180303554488000001d0341d00348070058401d0454108000e11550034004408085c0d0390001301001220000400102e00b42d07a00c1c0180300c0203120f58000a0000f03881b5138001550300c018041c5000c82c0501c07a2504419003c0d807070b1580b0b400d6030800041c1c0c03004914000280456055050041500200114060141452440c0000342d58006034850311007881442c919000c15a8040e61080c43e03916000107100e82d0b50140c942303404c0d4a4054045003254801d02c0d0070400f042c01000d0b48242e1095680f241c881e004898882c3c401ea00b19508039260 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 128313660 1250 128312410 128312461
    0x608060415050a0f0e09010204210524060f0d0f08030709030804030501020a121401090c050c030c0109020901060809030306090406061203080129030f0901092406060f08 74
    0x40001d0903103c21801d1001003003100440a200c1d0f04041d914041d00102810b9007103260b0040c001402600f0b41c80c2400400b040c1212401010000c0d503182650905800300085a81021803581d014100c2810700d00301841124111742c82c00b280010703003041000140c5111320151000c00d680c83c2540024030241c00554001e007603810450150755483d591500c003a889500201c41c665000f14803514129040740c141e80c030348010b01e0000e000d164400069000c1d00003051041c1c442c2d950f12180100d42660044089901c109182c009483d030700c1e80e8401c82103002c1d0401c5031089004c2c4074040300000d42d82c0c0c4902c184a000e40d807060055899038031070204008206030041c00650300544e8606002940000706e071001001c40b4400e40f1004915032504200403000d0031110400004c000301c16041d021900ca400003160303400b107110101898541c9032038074150700600030414002c01100c0c0384c81a4202060f80fa0710342d20a000c1e9496010310019440f0f12007240c10080e0818800d0100c1c2c40140400c40c008481e207401e000d050720206 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 128314910 1250 128313660 128313701
    0x20f0307031205180a15030c2105060310050402030624060a0f0305091f021309020408070306151a1e0d0608160b0702060f0408011b0e090106080604 65
    0x111040000081c1c002c2503404507400045004135030300f203c540400303580303000c031780c40c0c07000354039108030b84041c034181603c03407400c00d90388076220b0252038051864449607108802026105042407050740004200c1521203900c00d206880c00200104001c0c000e883c420b69010b0044d0030b035074413803e840c546101c0030851014040700081000c0e0340a80c650f14003900100d0b81690712012075400e0404c0190458202900d0f29005800c140b0007126401c02c044070f40302c20790015120060f039542072003035501c842c41d60075085104541e000040000700d08000240c0201600e01500c410490511014440c0c0301d103019620682101044020035401c501e03c840b40130785442c04600302452030710340480110030081c0e481420042c00c1669a40024002004200000e06151102e0340c0c180d080740d030824051402501404c03500a00c606000541e000c280d00315082034500810707840c8020701480c012041e40d65041c19a41450400040d6601c0107500c0341d19103980014103e40641d241c040b102d888500c10302c4082d08285c4111900380d07500c0c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 128316160 1250 128314910 128314913
    0x40510020a050a03031a0102070302150f0d0603080703120905071505130621020c03030f040305070b0c0a0e040203040210030e010e070b070302070806090607030f140f18030412020f030703 82
    0xa20840c64014130a90b00000c3c100e001300710754500d80365070b542c2d0141154041141400141c036035a9209140c564008541a10343c880000700051a100b000c0b050400c80781400d000008000421010785145c0c0e10a4440820311140b9032401821030300403d10291040c0d00040382005a01221643c5100c90442c902e48130f0f2900d01c0260640184066540c411030020b00d28480c0141c60800ea51013441ca41038020009515142130714000940d40e000181c505d29610f141c84000c00d00b010f005208031b4031041c1d84080080c16500e42036103e890660003520344400800c1048000720503918041c404c49100d950f0040411110b86200d0508600070302801e030030240e807036684841082e5403a0080000c0070007400e50101c002d940e0750f12841e0080c103060042d4000c240e643d000c80203118510360003044090b40440103203000181052000030301c4001c0d00e503034200640340f007400d842030122030401d4203c0d00d881802c030381064200c608000202543c0da0301c2030f44940c040024214240e0b100615200042d2041315000404499119459 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 128317410 1250 128316160 128316163
    0x24030c090902120702010c052a0c090906011806150e06160b0405010e0d0f230a0807180807121401021b010605040b090a02030901060e0a02090103050a0908040510020a05 74
    0x10f0071040c1100c0c07000420000025424020302804180307034030f006828040e4034a5640340c0d480152509601014480b1071103d0002410885400c02c400001e00c0ca0a680c2403240c0600e807240740a000b0080d2140000388040c9100c01d260050900712951184110340020b418141140c95500050780e80d0f5102e001005290080404a9280704e0800d001e003145903807e0401c0d1416908481210046d203a058002c5c030301c0140362680048240b07100021a0810086080c4680020810640508010040808045590b10045601c03080c11072040710103031944c0300107018070070724010081e42511414403194000c56084c000c4421110745c21401c01c1c40b0780c0e594100032007403082c43c5083e41c020710001d05106051142418180c1001d000e25801032030181d9080000402d220081110303403100820484c441500000403d85808095000b00002e0031404082c45850900b4034ae80c0000e03500020003540041d0500c4080f407104c040b02c1c411a2000c0c2d600131b4405251626243c148a59802c0400203582940110586803021640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 128318660 1250 128317410 128317417
    0x70302100905030606180c0f121014150f0703050715051e1e04140d26010503030901031508070608060405010b1830150124030c090902 59
    0x9075141c80c40c0c0503042200780741c82c0840060200d48204400301c101c03504441e050154075000000030b12003990780d00181c0c2c590005481124003004050b20244100100d1703601d000740410a458404006400707844841d81000004440d400b4800b0b17265404001c3c0e08440140d140090000700c0c07082c28040d0030b206035030f201d82041c25000512540c0b019140c200308546000d011001d07440c581144200110b0504000104001c2d00841c1d03058403240f0303407007000410280894040e0118407150b40404848070241018402004901e9a81d101e50800c07100d520040740d441503445c01c59060311000b400450030615010011000791405e030100a803190b51040c03004c941c0010030700c4080054581902e0305201ca0909005200840c1e03016801a12100b07401d02030184507a049411918018004035150006c0d2180c407400542c03400d441c440c1800d00803615040340c000402000c511070000580e0014dd2040503aa41d1218a40d00c9440003403d800503041d64007880e108a020790300c42101d0921034034140c3c100a45030040e440c2280e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 128319910 1250 128318660 128318689
    0x1b0f09050f01090b0f0a0b0a110316020108070e030d021f02070b04170f0307030b100302031611030d0e0f07060c0312020c071a1305040213030f06020705030a0503041412040e060102070302 82
    0x47c40050030315007a40e00306114201140c1404011450101c030801c00c1403c1104d030120080c100511b04001c200706502c1001e855201d60002403d03210210544036003c0e50310400d40700e04a1070703044984850141148284255108141c2040116205641d6030761503e0129100c030000d0020003c0c180710880414080b0f1010303510980d2191030004a46643c0010001000002180402018010802c01c0301c1076031441c8000e011b25540d4205120300c1c0038040e10203070031402680411000c0c50303d006c103181e11308074001078180d01030780d045003d8402403621000c0807509240c0c420b1002d008504460024101c092442d4003d00d00703000f041050b039907c0303501c410b000d0202100e00c6000e00b8000101096901c05251441060300081608540442c50701501d00e080c07a00c02c504510028124103c00600b1105009aa8040b540496480410340341e4480b40075402500c540c105a505079803000e5006d00c5806c881340d0016001103800144058141000e250080c5081d4000000f49039074114050784c40c0010042c0c0f103031007200b003011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 128321160 1250 128319910 128319929
    0x170307080f0a02030103200f04110403060b030a03080f070507050607080a230a02070f0b0406020c0f07030b0604020d0e060c0a020c010e0d020609010504031b0f09050f01090b0f0a 78
    0x50a104003040d070000c502808641c2403d10400040000070345401c0c0b00c0041005141c03d4008095080700012007503805074000d1a000350502030400310317098900c802881547d220302c608111440c00c0e081032682e01c29110074018045843d44001c14141c0d1a50b250326036001c03200e80f4000b40b401c0139a9440318105001515a03201040201c824000340341c2d810b02489480c201c1d042440e201181d208040c4049421014041d42c40c500ea00150410911180d46013111016400c648824868181751500e00000d62026a41c01c0e03950040003c0c044480c01d020034040c08494011008801c0b548400041000a40c881d40d090f1180315900d030700009040c9824410248a0f0030b04c215600d4941d0803a0a01a013846541180715041116030b1205030f04958440945000094044d1506515035041c1401a542849035400240407840154084c280d807290061882040d00d0002c1d40b070f960f1503652014041c0544030b05407104019844410010302c60244e496001c1409804000c1110f240a0b800c500803c03070046aa40189402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 128322410 1250 128321160 128321177
    0x90a031a070e01020c0f090703091b03050f030c06010e190c030e07050a0e0c0c0114011502011103060105030a051510171501090303050a09090c030920030a0807170307 73
    0x11075041001d01030000b40a001511a0200090004004000305e04505204030018008510714500c60790148400c5940411441c20002d1180ca0400740c2c841c06106c100e0301403166001e07140101c03201009840158020340000d21040c2d0800f1002495410010001c2540600c3c3c0b40440c26031035030038080c101c840c0119840c00241c0210202801d03080100035008980503000000c410420401001710707480d40060f18002d02611108807184040c05010b0b503e01a12908100c2000811451900000c100f00c40b0620740003004070200e45620740e80d660200302c07001d80c040b03202880040c5080c0c0258000079841b03580440c40075031582c0020000381c0503544e103008481c0055000d0310b04254211402d031546400a000521107000401e52800003000c00c2d00340e020080411601041a410b2180210749a03409840c0c0d840e8144004d8040200040051802841c00d44a440272a000304544044c4003681015108001e000783ca100c0d0011744404c10305034804002215220040f0b06102850051071000d18041d0a07103035900c280 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 128323660 1250 128322410 128322421
    0x191a0708061f0203160c0302030d08010f08070e0c0c280203010b040506031216020901090f0c08090d05130306050103080405090106031a091503100c11070509060105090a031a 76
    0x101120040191452aa80c05810b42c01c0e03281c0010903141703000380c80034440e0703051041840c107980c0c0c0f0681d9a1009425124032070041e00800d030402c23034042c181c400c0050120400c81d600c4001c0e907551086403040031240e101c1003010900107004030009001c250345078000c40da030240c0380105280303c030303120405802c0800d4445d03c030f5102146800c0c0900494164111024000c5080810009490300800200c0304114034000035480c00314114503c0300c00d21250010504507007036949000c8040034022041c10908003c2c0b404469040d040d000304042d600512008004010a14042c0300c10b0328150b10100c800c0f01c1b01e00c00403000000044d00c40c00760a010f03500c242080342d1290f151a01740000408180c20020501d0309104410180910b100b80e51004200d00321011100b075207400c20204698100300d0385054060062a041c400080495003000502d0140790365426081c0d0800018140c03030300034501600e9030044071300011512640c401d0000e0720141d40c4c001c0058410540d03c2e60342003203c0700c1010030014a010034a00300b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 128324910 1250 128323660 128323669
    0xf050c012a020d050702090604050619030302011d0616120b0a030813050a0e0f0403111b0907090302060717090a0609030c06050705030304060525020f060108010905191a070806 77
    0x1030100030904000c0d040c8825071b030016401c0d400060406003d241d8030000900155540042030000c00000014101156224140240a008a1240760343e0345401c20803450081100000c0c40c43c801c9450203408800c18030140310813105585016402c255076a1965040c1d04c0c0c43c0e0b078200d5000015403081081c103a5410040b03010041c1d0030066032109120750b80b00708081281010031070b945580582c0c40d5541401c29501c600e01070720440394803e01d003002c0c0e00c07403046e02c80480003420342007081e070382d204550308002503540c902d040b1840b03116404001d410210070300c0040300160140c40a00301910040007001e080c103244902141465402c0d52021000400042c42003051003030b9a140390300030300700c2892310503d80260758580c00c0e648d11000c1c2004140365070703a0000070407402040070158002c4120030400c00c00c0c80c2071001e001303503600d0b031550248405004038000020b80140c144258906503610034080c00c4880d8115150400130740c950a82074038810b0005807448404041211402c1c410301c100d8a031450b55050000510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 128326160 1250 128324910 128324923
    0x906080304170705030303010303390c0b09010f0305180d05040f05030a0809090a0b0402041d0a1401170304080610180902031b01111006170105070f050c012a02 70
    0xb94401c1c0c22608081c0840d4602100f102e041d641c050030500140b40d8101c40c1d0381c030342039108040200b026070005200090b0205020a82c0005401650b140209a0301c1b04001c2d6118441d128900d408618020341c8400108d00035000303507500001c0c00c0380b1414001034185440b420070400c4000c02c8000341d0005818802c00c60741107084000f03040705070f00a051041013944c980c14030741308104055100d51102c0380000c1001c0a1a04500f52041d000350080d5125595607481d504c7c00c030045002c00d0b0301d00a14800151201400d807140c3c1e10001e03150441e01b880c503480c0c000b8001181200c244584054041040045a0032608000075801004046070381c0681c185858481c1314050030004a00c24401d040505220169500290b8851002c00b5540206109480d2600580300c182c070b104a04c91003405900350324000050164004011524000c64130007c0340d130b880f00b4242c2200d104840c228085041002c0c0007540c3c5101d60007803d501c2c0c488800008004500d2030314400318103810885111350f0500017440702405641400342 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 128327410 1250 128326160 128326199
    0xe1e12070302030306011722110a140a0e0c030406050405030d020307080601031812050c0a020d080903010b010503090703080f0f0304060b030c0406031a1b270a060c0b0406060906080304 81
    0xc203449400c0c0041e600103100905508c028400c500001d8003000e1040c41074004240a4000703141c4d406560f59210f19065440341d0b80b110601c505244c00340050010690343c100d522410310f01721001d14694540d96100c0c01404050320030758043c8428002d000001c0c4d200d100841c05030400e0f8682d18040c1c540741000400366a0401c4c1d09001954116281d0000940401198802c890407070510340e440d800c18a44052400407410400b80d8406034032841d000500482d000144905e16058009109620030700005440a201c151100203ca034420f000c10000304440c5009401a402c0310260b251410510081038180c43c1c005443c20758500d40d50340584e880c0c500d0b00300000940d109003650144015881e5858400440401500001400240e40c00151410740000503030303050303100780415240e100c02042e00c0e001000e460f011047ea05003948407c0c00348071490002158800c48149564200c0180c205039100e054803131010b00304451207078030750801003048130090027100007600a11004540b520318080200f80918084c145 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 128328660 1250 128327410 128327447
    0xf05011a060909041b0e1f260a0204110901030501050f010509010815041112010f032a030b0711060a05010608130f0c06050a030b01030e1e1207030203030601 69
    0x42940c054607010160303035101c8402c403240280c980d201e00302400615903a800143d02c0c4401400003051000e200c0894038020f60940004118400c2500d004003c0035a09020300c0d40c0c24411031000410030f081100040100030000c1c4150f91280200b603010a05403101100c11501d00000862145400d50f803600c1030138010002120b50071200c00c007010000c0c20034030441c4105810840e02000044e900508201941c401450180041090310840d685505031504000c81034181a1400d400001d00906400030300f00c1038a4003d0000c103201c500c51290a60491a1382496150481034a0340c0000480c8a4900311072094005848210564841d4203030103040c684010090311100c0d15103401440003a9010034002d510003140f4031040c20340e8040e801c003122600ca045400801c420002c68002c81c803551f1100203803a0f10000d0743c030305000c0c010300c0c00c0055003640d803c61508107207603004000020414110300c1c140701c40a0050002e84000a8003041d10b69219800078005a000d0380c400000d02900d96400102c1c916074407407540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 128329910 1250 128328660 128328701
    0x1e090518010b0919020a0309050a0503030103030834020a12020106090c05070c0501080403020a05191a1e060a030506011508090f06040314040e07090312050c19030302070b01030f0501 80
    0x45802e9a107143c84d0501c58103990101d400c40c0e01e00d0013030303003e2103a0325003210460380c002e034040c40d00a40c0c0e43c1c02400114001444100803481102d0081c41d14100b420450040607540d040308200f5000080c20f240e0003004511034480600007003620705011001004039540041115828a0b500c3c45c140c41040114008002080111a0200318400251410717076000b440c02c4610340c0c4075400c08071301d00f007055180940640200741c4924080e421100b103003c0c900e40300f05060390400d1400d130349544007054202c070704120500f49040400510025280065070001000703142ca010b2940f40c0d240c03985410b40903000301d003407441c3c00101c102e005e940040740c5a61220700400108000c1505864064171144007500007020320440700740f52080c08034201c0a41d000b8006410072118246406140180600c0302ca20040c0c40f6040600b030743c3d107200c074410700c1182c00300080b0307034003c207042e100e4000400405c01500205900309503007070110400107030107103020500a50261645030243da046040860840302020307154005a9544c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 128331160 1250 128329910 128329921
    0x7030b01080a0515060a0b0c0c0901050103050708150111160504060f080d050f09040f1d0613030809071a0d0c02030301050a0311040b0301020f071103010c0206011e090518010b09 78
    0x505002c800b4081003500b54545c82c0d00c000300b24032207030542104c03036280b0f004181c05821030400200f05141c40003c40c0e46200c240d03680d80c010b404031803083c0c410300f00007822040091000c2c0244940c140e014035041c0341503086c01d10610003190034a06440800e102d00d058100040060346054020000582b0018202030300305880c6c030b500c95558111804900c0b050100205040b8800c1001d08140c6074031030300181c07042c40303802201260350006042c59207035072003400d200d84098291108006890340c4240d44864282c210040103880030b0300c01540c01070401d180b912807040701242007881034058000201c0c011031200e4642c0100e075484001d0b01e01c00c10b10031301154814401000590b9500300801c0c1102c0e00800705070140e0318990046000740050443c010f805600005800d00c000c1450f4005010b050301810b4491100085038080500781ea4200000740e005a001c18018000c0005a0004010b0304203141013480c005940d0310184001c1d82c7c02210b04651603183d079250480c94220030300810f140024112072480c01807070079 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 128332410 1250 128331160 128331163
    0x10020303071101180b0403020d03062315040602070f1203080c0c1507050d0f05010e0f13140d2601170f0a0602030105120a1101050d110a0207030b01080a05 68
    0x81c030301d004021140d2007490720038900791302c0001c3c60034203440c00700798080450814980400041d50100e0051048401c2c075030505100b0f100710030988002024035450202c0c00e0000881c1000d0b109616580034144908201c0d062912000602c0184201d401074884245440c18240c0100941e9000640f107005200c10000081e03071050000303500c0a41200910f44a69082ca05503242462424405040083e00b406000c4080d4215003d002c0404c10001c0512401041c819800241c49082c4075041c027605403480402c0b10000340403001607000b08004004030321007540340c03100c1034201d0341c06019040315045080c006005550100d61070500340c0e00b0340d15250103e5802d41551400041c1446072100e0759810444080100105016040c0601141c0c81200c1c0808010708040b00290706c2886050b10030262a08159841ea0000c14844040740e0031407a030081118181006407140c0d80602c1104049070307515058502c0e00300d504005000b405010b60300624099081d403030134402c10176041e000f04281e50b11401c01d40001890 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 128333660 1250 128332410 128332417
    0x10c0804050d0f050a0507080d0e01170c07050307061b03020c060720030a0201022208100f061701090506070e0f0d060e0703081201060315140307082505100203 70
    0x180d0b0a40400364881c20000e000e8800d20a0044c201c0c0281c01e400002e12000058a00039100d80b030f4150b58080d203010b2015101e00c0303103840400d4082001041e20a00050801d6085a4840d1241103514a8030322075030b0720340e402c40e403100300125002503581c101098030032140303900050302d02c2182c1821864000ba0204c0a59500c0004010380c0c1080352200407481c203c0301010407400d41e0b4826004036610b80d881d005010f4040d42220b8415101440300d04003030111904c10021650449034940c000d007445044400100015001041c1b030607424507242c21000449a03c0410541c20f8401114000290310001b881d05509180000e421007040020300d110000c02596000f10a4210401c01c88134240784025901c0c100014004198440f001802115800028090035000610984c035801040380122b0382c884200b40d0446003502607083d6800c041940c2032000d0038103010f8007191401d00030300311a00c05584061944c54161001c140e0111104070503144241e07550700c10f485201401c41290720f95403410303103030300020359070b01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 128334910 1250 128333660 128333669
    0x301060e1504032004060f05120d09051903320a050d1b050601060c120908030f0a050d0f0b1003020306090c03040c080a0b0708010504020a0c0215040f0f05010e010c0804 74
    0x1360100e08062480c1d10066403401300c00c0040c205000e01c1380d48409690800300d4503c42c00d80250580f010381000020080f40c441c0c0c80004544072004034038240418064403240241c2d030074000c146000008404180b02d02074056401c45c2002480324180380401000141c1800f00c0d00345001c950003181c40000141d404203000d03504603440c7c40c002840c584015140c0d030080d9040c040280407030140e5000840c2050340081c00c00b40440c014007620841d401ca505045034500c0051040d4500c44d0002d00941c2908814800200f41c200210702e060b6040040d150401d03021903260981103070000c0d584846102c2a030602051035001000181000c5003145052004a4643c01d001000300303200210000005041150784021003000c0c0841c01c0c1104d4941c1d000b8a0310341040c107401d039800004180c10000004080c90303d4002c85101c291240e5407044201043d0342409101148071212000001091001203940c2c1892541c3d41d000701300c001c0c0303401a15440c1000145c01801d64101c40350401000210101c00b1501d1074085800b281c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 128336160 1250 128334910 128334923
    0x4021309150f18110a050d050d26060118090f06050a05030f070e090316030203180d03120f020903030a05040302130b220207120215010501091d090c040c050301060e150403 75
    0x600d0540040c520481741e03002107a2024040c07801001340303e07000810301410082611210380c018103004280c0c0390501e0380d580d119641440030000940651090b104035a030708600210b56000c40e5154201041a1508960f07a2046550b641364200042c1c5080180c41000b4402a4040c020521503104203985407451070240c484c1070240c00010641e41035040085600701800c545111800c6110740c5402502e95106582500b68540410304003441e5203170003220400d6141e45501c6000d0144e0145c06000b01500c1c0444400302500d500340a01c0000c1c1c0c40510081891940b140e4606070390324203500c10800018070110380800c01c03034a0500c0c500419101c070a41c034440a61000c907a403010f41c82c00590403000c0d01c0b03050380c02040303000010500c40c8440e4001811101c241020b440341c9090b03a0b05e07a001100e10b4070b52c0741326410729500c0d4068003d01070032030f2070700303094100c8048001d8079004003031040481c09642c1e080002c140001c1000004110542d4810032100e801001240d603209801e405808aa07a42d00940c00081d00d103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 128337410 1250 128336160 128336183
    0x905091303031d0d0206010905151e040c20030301050a0e0405100617010f0b0303030403210f140f060303090f01090302120a0b01080303150405060d0209090706090815010e04021309150f18 82
    0x840410bc0c071f8030140c52030004d00030302254002c00c800402c4055010340013040c2003000301444441c454080240c030b040c0d6201a0841250a19041d103040e104400901306455a00074845111401002070003118050600f14014203c204520300c4010300b1994407010b1810300743e28105001140ea600403049a420079018070380036441d021011035010100c1d40400c0c0800c556440c0481003480395060b5007044000b4205050100c035a503131610b1052141c420f04803007032a4160010400c503481c80c902000d03000c840b054185012071095480e980820250500c0003c4014950b111007880d504011211840314003411040c0c3c040c50a500f03020001320141c1281d001880d2203951110300041281c1c8170058503d80040d001040c1c9046400d00344c0b18241c039842e150007210002802680c0c04a46003100040a07003440700d00042e50308890b8030700b0b2000480c00602500407640b02c201d580d1411030760491409001c1249002d11100918440c034410044c08444003c103004e184030b4103041040d9414141c2c2c2100710001c42d00310922000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 128338660 1250 128337410 128337439
    0x1020610140604080609070311040207050c091902070b090105010501020f07050103200d15050102010b0d0b0907030210030e0d14071202011121070905091303031d0d020601090515 78
    0x40e00c0c0030750f800c4208544105c000300150030000042c64003c0728041c01c0c1ca8160701c030415060200340d103d4408013502c568814516500705080000c001a07005e440303505041e807408006040d03101a40c0c043c004c01d40d107441100b420b01141310428411079006180174001040c00580c240112601c81a8600c616414103035140603c1c4000c1c0d0040f40e04946010030203001e00e50fa00c460340161402040061013418000041003000708507540144552401d190006004250f4408160b0f254447c3c0c04000303210100c1e81c000c2050010058aa90428071003400c0c0e542c030040351300c101a000d21032800001045420400255089190920105034102c0d182240c0000c0c8040207041d481c2002d0f40901140c04d005070300b41800041c030181d0a00819803640107000c9284042c44952a890811600d60f04076005081c0c0c07180c540700108035264514980401d01a210b0305012903045090030310600b98506034078422001390013490480c9000760303060008601500300140308000c03030f09000d2140043c6051880d0728a0091540300b541d40b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 128339910 1250 128338660 128338669
    0x51c020409020409030f110309130b030309180f1e0c0a0201090206030a090b0903091809010f050a02030601170411040b030a1203061a070b0402100e03010905030c0c0102061014 77
    0x740741580150050207211103600c0e00810600031104500300141e1084400000e00c10080212003a15400516600201c0550803420001700744415119616100410421090b912100010110030915030082910342c549001c50400c0c0ba600203002070081015038404020043c0704442458010b2007444c0600c3c4c03240310926040e4010000394801a5100c42c001c42089141c0182e07030032480c20940301e207015407a03549880003010755038081c0c0d80f00141e002500036120001c082c0d0b0560441e40c07141400300089030b610000d0005c4821034100342c0b441305c84182c000007005020358100d03901c1c554055240c40032000910b00340d200c010b0f40000e424643d91140d0f40750440c8031a0380e41d080003143c00c030315000200390700e245442c00800350042c4402d200f0301624030f1075540f6001e440103901e000d803000301e070b001012502d0700d80d1942d08000340b0041c01c500101c1404003850745040140c60034481d5660042c8110011980c7d04e22084c0b56a2400c0383e800c80590444d0300c00d5042212550b80d1840100440703082c0b00104422881500000c2c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 128341160 1250 128339910 128339921
    0xb0403031b02040f020a090e060603010510050409060b070303060605070b0109110c1903030c05040308030411040207061505010e0406030c15020a0519030807081e06040e0111090a090204051c0204 85
    0xb0390700600b00901c50301a0b40d602e60003080021001d441d030750b04050740c907946043d00c0c040888605511000c14001040242040252000c041c00203180851609481c0c0103443c080b80c0140d044140b01d41008a40c0c0c0f0201501403150001409150038541c1c200919983ca80c4040c2c1c105001c0c3e540615100c101c028003003100c0b10300350342d62165004244d40344040702c0b4944204480c9603800540000e030170504040107481c0a00c2c12170b01569003040f125441c640e180c1c0c8881d0081c0a0b030011090300f00d54200030b5500451071902c11111070580441080140c00d1511000528010115002d68415031510104200040148c00244101c03007070f00c0d500c0c40c41000c00a4059052008802e0042c1c401e014480364144410740100c01d000c5041c0c8207848000850b01c4490040310300d41411248038615030480d44164a0301055070410b00e51100009101141000258840b507007590300101e41c08404000101d810120f514010014101900c01d0f482d007141494648000921203038010400103410142c48000b45e815510b9030b030404c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 128342410 1250 128341160 128341163
    0x2010b0607150b09040302060406020a0e0a0803190921020414100e010909080403060e1204080705010905030c030c0d062301090f0605030616051210060906090b0403031b 74
    0x589407103400e0782c10040302c045100081c01c58081e203030030300e07540091814000660107290560f00030852030b03641d036407100001c1d403047c928201400749141c02c02d8460303910044494041c1401501031500c4285005400c070071025101d019006003d00950f051200c0b801c20003140b80203054109400c014502c4600200e0024503c1d20800d0520f0a0494200701d803078414241c606040b01c6040441c00485da0765094600110303403440380d004080040410041000c66034980003201020300d98010341e444825070301e0007501d80380c2c025404401e1a4010075010400c56803c0040c00c0000e00d002d90103804201044e00000c0e456401d014981880307900e200c120030082c00840d500205036201d00b03109a2043d400d6100034041e020701c003446096103690034800c550200380d6a501030102114400307002004a07803103441640c00d072503d000c8124000c02c4000e0040700d20300c43c2020300950192466407110541a401d0840c0284000b071250000810b008445408101c1d01c82080215002c031b0750186030040813002c1d0340c0780c3c1c1c01484188540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 128343660 1250 128342410 128342419
    0x506060108042f060d0c23030109020a0e101107060203041a0c030f0a020721020310051506040e04230706050703140a02061f03050a170c0615010305241002010b 70
    0x4040d030146106500402803101c81f80c5803c12400300350014014441c1d00c1d01d08081884500388010802ca1050340c000d40100e603c036003424105481031001103100c50035140c0c50352000800702590380079203490a22214015046500c061483c060030710051103007810010080514410f00000c0d01c4822502c1401031703c950b65400ba000c00c0c0d46c1d030300c0460000c1d514980c3d40214508210181c8840d42c078031801600985c01da030b902a000e040808007542e0142c00a24001f44584100d000c0c501d000c400c140d640000910203400000c005407070600f86401c0c07113041000c000380395810049081c020446c1400e4001295821140350b0718003641e80d08034926080703400c5071400400c0000c08a001c201420459000b090030b40c89806600301d000c170403844030958001495524400030f0300e10303040f00e10880e0100d0010414220400000f1100f40d143c000903204003450007a0481700758442c960003204152841d03030b00d0300449800081c3c828001d150034025013081145035005603407240c400d5922510b00c3c00356038000e42200f881c0d0040100b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 128344910 1250 128343660 128343667
    0x5130f0f0c1509150f021507090b040810050c0c060a0513020402030406241401030f090b07110c0307030308150a210c0e0103080301060c05030705010204060302070506060108042f06 79
    0x150083d00c402d10038018034030541d01e001c9610030802d1042080c2da110466070707802081c09204030f0f0a0f20101c0703400503003e1b10801c03001d4103004c192403000c580140018401c00c0300401c0300c1c540d1513001508441d030140c2428921081001081403441c8000754854118080c0351000074141c0b55a164201c280b0324842d0001c0d0490f002004110600001d544211406001c049040840205200d07140300984680e0040920400075000f0304041c0d544282e02403002c02100d00c00015800d076440d00e61118801e01104e901000800c103c0d0110b8110700241b108900043d015001840a181580e40c090400c0d00010000c2004410b04e40d1466a01c2d0780d0007902000a00303506c030109035806c8115820b8040c0454209064070344207001c020008442180070100342c100c0c0e030032080321030569003003480c00c6447c54403903841504c2c44e01c010320810700812800c0c80240010202130320010f03900c100501c1d02c070703003804402171199040c04041401c2201044415815100e54045190f507202c4a560b060400080001018090340d007010011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 128346160 1250 128344910 128344949
    0x30302030901240603150302060d020306150c0a0308130b07090501020f060405060c0903210306040b060c0607120204120c360902060f03040b040605130f0f0c 69
    0x19401140541c008900030702030b14030a15520a450701c4608115030104509003410048248203a02c6010903d0540341c0500703210f83e4940001e003064002c011407260040c1d000060100c2072805901d0b060581200f101d0090400ba64440307425245c2c03208a6010741844000000540904101c00400403101d0f4040d500c2840c40c1800d583c020305221035809468054800c1d42d11440c00405c001a2052017964004010400e5a58001c1460810307000141620380610855650189411a42140760446d428407103500362a4a018800c0206039903618801500407802040030796200000071600301d40c080d04e039041c20200081c0b441052402445564400d01003080000e040000708526808140304517142d6554845000841c1b4401d400c001100169200e0503186000340c40c441ea18198001d03907901030004014606010384440424410703802224110b40220f45441003004105891080c41d8100680c7c0c42c01030341d44082c41d5a210341c003500300107020340700405c100460410410349041079000ba00741e00c1242c0c141c02c50710 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 128347410 1250 128346160 128346167
    0x807050d0c0e090a11031207020f0d080d1401050a050d060504080f0c010207060c030203100e09070308040e090f010b0607030806040209040914010f050402100f02120301120606080c0f060f1603 84
    0xd840085130717580d841000c001014503001491003900c000d00700106103490119401c000030f5144103561160025883c0c0e40d50000304051f8000b501328150000000308114814004070052010143c010f030b0b210380c008800a00c4980c80c0c86500140840d404540004c41d40c40e54104000c41c1d0141c110280d056050008400104401c10740140030b1440c0f1030302081c85a641940d400750240d020459030707802c3c0301d0b900020400081c03000f02d01c120f40010301c09050300c021039160b80320b000361544250000d0000031404000d20505601c20002d0090028000000300b04c03800d42a00022703424450b8074000b03400c0240c03100114034142e82d19170449040d40300040c0304001e05155450003941000001c0c401d000d8030351801410003891541d50089500c144e500410300031380b942ca001d000b40e405004010f030600440c89000e111440e00f50482c401140600604010111010722602d8140300340c510a030811481c81d0013105031004592180c1c12040400a42281d8903a140d003104408440305004803402c00c100c2c4070324100d004052540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 128348660 1250 128347410 128347423
    0x90f0902030f1006240c062a0206070f1418031903080a09020906090406091a1b0405060a1b080a050d0506010c02100e01020f0f030301090c090807050d0c0e09 69
    0x804a02c10b02c0f0b203558480103036500d00c00420303141d45d140e5804a41203204521810b6100d0b480e034401c910006400321900c14070310f00b43d24040ca4484550040e0284000d106d03030104801a0f11070100e1601c00480c0b074080c02d0040c0381c090807030500c01c1c103124081910403101140148029503c0c2001d401c50301d6203951224440328a0b502d0f03c0742600450310f010045440907159000740c9000c183c0140980c0000d803208028060580c3c00200281c0760282e40b44201c800055001d9141d5822007403d148080c00f50501015404010481a03a1100d501d2010032003000a80c44200c19666a121582002c03840317a6045481844901c0702d540006040c804001651001160003102801d00c01001080c20400750341d6140055881c0e07005601c002e54018001c103540d4504900c109036a102a01061043c0c4034145000c0401d50301c0d003101c0311b1071142d080e0404030050084e4842031084040d00d803454900300621519108044e9220307090340c06001c1c0611000c210100c01d001d454070416009054410319154649882c0c040c660311602e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 128349910 1250 128348660 128348683
    0x50903121003030c021c05010207050a06110703080c07030225060210050103031d03071d0609060306010f09051b04060203090102070b0a12020d060801050c0c0c010206040804090f0902030f 82
    0x1140001c10078100c074049260050301e61680325030900404036001c01c0f160500100d07101c0c04840e00301d003181000810a0010f051590700c41c0c0b00400e0420910325000054848a4100340c85071302040c000940402e40c01075a03d40c0040d4401c010aa44210034207049080c0408540b210724102600c1c0c403080030440000d40b90004030350f50b503403d84505244201643c0143d40d000c2c440500019081c10141005881410b1280810000203045a041a56400001e41406540300310320404400c1c4404010382400c0030114241d015034100e005d8450303503041105d01744000d100e500070303030440319514800645122a04d02002000300f1119660546541d81e03440025075035481140e03009c0c0103000d04100051900703030090a60b07038608419190395081c1321102500c4c00003500b180c80704c1d02d0740c80d403100e0000544003028400d0714090241e10342115a10640301504030318000720080c1d00d130b0455104508000124500f0002c1d03c0a84107c10404141400c80e0315440014000318000650305000d1300c0c9592103001e80006284200b80f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 128351160 1250 128349910 128349937
    0x501180b060102061b210a091b03051504060e01050c0903010f0e0318010314040c15020c010f080a14010801050702150c0d0c2c010e060306031b1201050903 68
    0x7540c42800480c0c03030f8030f416070342c41035803a62054100701c42d82040b03401b911080b013020340100400d0400e80c4600000c2c0005130f07400850b407591003030004140049000031010100c0e0740c0425403086451950350719079034034104800c001d20708603c1e8003140800a058010b08008503901c03001348a03e05050f071043c040341d0f112082141c8250310f8014000c2c402c040741c1c01061008070048000d1400c002075515907131018220504506d041550ba25807000e064203004c840b03d4050b5000d8224803e0f1207007840c90030200480054a86015548440300d2201c2c581e07070154a6142003d01440c1c5500c0b10f0f01c800640e00e000c0d061070803200c03428100c2c2c0b00021402c0c0c074055000314031440883c0d01325074000b544010840700c0204203444a545a900402419003100a10f41090040c00d00c5841d00d6500c940e4001c0140e9040e02c2c03100f032420241136041d00c01908941c0c0c00140183d50b1802161182c1c65424010300080c0e8565082e1a80e0715115130215002d0382559a80d0070143d80200800028041440c0424050b030b200d038458031010285 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 128352410 1250 128351160 128351183
    0x1d1b1c08180111150901060f090504020a0614070303021b0d02010e1e071205070b0a03090506010609120f080c0a150c09030c1712070f03080f090309090c07050118 71
    0x1e588501d0903402031542e142d0281c90081e41d1201803038a103420081c08144250340310400003c0501d207003c0c3c1d55004000e00c0d20300040909051040000700b40321548040d080190b03c8425003011504041260b01c202d525060050ba0b4001e0b11650ba00b072310302c58061a007080c1c024a07906032070054041d000704250031411016161103004801954943c03c2d0315404211081c3e04c003c0050000381e0140c10b8000c000d034014030840d003100b5a90b2400c00e400d035110004c200c0011362a585000208801004003901415090400312450f50070f00310202035030b02c40d038403018101008e003850040502c4a0201100d031440c4580068524542c52800d01c807500da8100d8210301056803820051080280c4540c10203016a6845000f0800061803c001c500c440404051406003134003402c035024040c4030310b050040900c0392188000e411a40e4107400c02038800b010081c01215142d20340001c0107040c0002000710b5044040c1101c5060b06610b03807840c5403000340070b10329000300035601c0c01c42101040340a00c1015aa681e00c0351b140c1c0e414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 128353660 1250 128352410 128352457
    0x90519061a07170c01061d070e0f0d020d06020f180306040803070c0c050d03090602010e010903050a0c0305040e15120d02030a080408160b0601031d1b1c08 68
    0x80c84244450289a4101c140060800201d0720f00c620751080c0340d0034010608141007050b406084581d181d10011800c0007401d9403000503081003602991240c1c2c83d0400242580940000c01d282c803405810441c852210550314600719070f2201c0100c2e9100741c1201c011901d030362520854020315800104131080115203002d106c450703494002042441127501000e03040c15511011015030f03106803c000103c410404000d03010905440d5030b41c24010701402607440d101481e00d040c4000e07003111110403400d110340c0d04010b40080800d030850120340ca2045645407841288460381021a8240107540040da00300306094140150107880000260b669482164500e0302d03014a5101e01e661070304c1c62645a00541c10600085444601812a4540c030078001c03908146026825458a1041c1035021001c80765545000240050340d6854402e80c02c3c010140c01100c030400c1c500c01040755941001410490110b240e1607981c00c81c5880d800207008113140d0070000411210214603103590f41d03411038031307007000b00405000d402e00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 128354910 1250 128353660 128353679
    0x1a10050406031101080c0417030306040b03060709060f05090307090e010c02030301120f0201211a0307082a120a1b0e04030c03030e030c060609010605070c1401030609051906 76
    0x101c07035101840604031a203803c01900c0010300240101c0144100f8000010404c00c3d04c0c0002910480d134102441e41d9107000d1301000112402c6200c414001d074409070030460025048800704c03081d50a0740c01d014016502524040781c4a1040141ca5605401400740004811b0001d070000648040784c01e0091261010104003282d0f0f0780424412003082c1181c8040c400301183d01d00354400d02242c0103151810404c00403942c2c110b4514002006181781c2903075541841a5440030500c0e16550fa001200545071484c54413041c1e0740d0355805c00c00392480001c600b80209480440c544108164400080e15130300f407140c454402d154907403040403001d070751046040d1881e610014103007044600361403d4010005240d12030752022110402d00400407402e05540c0c60004651240420242400303640c01002060744d441c022040c80f48400d410f900c803a0070300c641031040000040354603041d03e081d104517441700c3c40724100d9100101d006d03016645c00341004501d00000e121492159825498151450b4401403001c0d035078078401203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 128356160 1250 128354910 128354921
    0x915040e1f020a050304110402070b15030d03060b0a050c01092405070302030705070b15090a0f1b0207060807020c060f030702010b0f031222061e08011a161a100504 72
    0x10f00015020000900014014a14200710b171001034001420038005990380c0d801c25000703a60b0003030300b12019414400146010040102407080c0b0f80f40c2400314510b403510409940c00366072000b2050002c080b50030040400d00b50b03c28401990850600c140c02c45407031098216020001030b50362501c50400740080c3ca002d0090080f00d00400c01507803042d19024164a80000d125000b610003451482000700365842903940c01c2e2101e0240602c9000021045c2c0354103190000c81e0202c0b01004850300311488641710b0740d5000700d0042c0c210313081410409080d50360540201d043c08052400542d01c07040104442c01510201c9028602c680340c41d80080054115140030021100e0800041c103615030f10010b1482078219400e005000c0304a58900c1441005064030041c200c40b4509800c001c0c0016220320700311082c00058040400c20600b42c4c10301101c10350601c50300180008201e0503070780000000140040140c1003061030540c00d03e41103c003e030502c1003203403c06103540c1d100ba00c0c0c10808265442d40841c5070300d060f1046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 128357410 1250 128356160 128356177
    0xb030708060f0a050702010f0606030b120c1c14010c020601090506090f01061110060b131a0a050f090d030306080607110714010504050913060f060308090915040e1f02 73
    0x6500450f9500c81222001d0300d0300600d0201155207803860408104150b02030031000e00110349000c942d0f08200d400b80084070050303100011295010452094442e1070310a26001c10401031100692130007030307604081079012601c049900740d540c6080c402c1c4100d55400314419050301c00844050010345c4070f00c010000e120390705844801380702c03c000d0010800c280c0112000c00c0c92a8105087e00d5130100d4018480c000c50785198400b8800b107500007241c08080369030f91804000b4090781504058905074044542405d03024040e504000d2000024040301e251548900b82c41c040d140c003c1404405251500e0001c015000c03901c50b40304144901c1010400a5001d4825144174841a000030300100f4a8012102209800d51114906000003040045040c1d262400740d54450240f18200f05155041c80c5801801c80d590074890314100c7e868140e0600024511104503401701c0c40494070310f8040c1c2c66003803108144c42c28a00070b0a520520300421400003030404030750be0044501607402d959100c041c080e20201644500c412 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 128358660 1250 128357410 128357431
    0x305010b060703022a180109050603030a0212090102070f0801090b091b010311040b03010806011401030204050a030b041104020a0e19080a02091b0f07120212041809050a060b03070806 80
    0x119900100c810103110310039203402d21400c00441017081c0410303100703110207022001c80f14518006100800d00c1c0c2c06010781001042e8019882d00c0c1907083c00075200d04a82c0c0010222207400990540161b2003080b40001400b00040c68401060365a0f04082c020503280400711480380a241c0000d05040004c1441103988907010401d011203d92080110010401c0d80104154108103200210301d503d00b5401071400780c0303100401003003c1c0d414a4010803000c1d90b500004e604041c0101300510040c1c945c01040070840390301081d10503c40e00c6a18100541030124142103400c0791010480d000001c1e032028600f042e030303a415261014107000030f10032009501468064000c2c0c50740401000c000600b410350f1100d6000340005802042e00d4400c600b15600c0e039110700e103807852524021031003406004405400000708170140c0000c1c824400b8850140790075010300d10441c6421006141410070540043e003210340e0095104060b076000c504c445c5007000040c18003001d068045d00c201c0d50007140018001840500030040440c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128359910 1250 128358660 128358673
    0x40e13080d020913020712021c02030403060c0203160b060a09050f0402121f0b0a0527090a02030303010915120308160e120c010f09060507021c021003060305010b06070302 75
    0x2007030300203580000111034220030205882c00a4882c81d00c081c0000fa13100d41b4618510313242109000780381004544020510141d8030380d010f08e1840d000401c8400310f83c0c1c00200800d13042c426050a03030450007600e65030350900c0c69440d031220400c041140424401c00003200c04003103860700c03032002d40c04413102220101b8140000c1d0012078054541214a002008001002c031422240c9040e2803204054050748034401c00c9468000f181e00500e4040c1000e40600006c1d24050134410b51b8003c40c00d9102241409000c030041c41d880070800c0c01d40180510141c841e009411283da0b03503503c0600710000c00440c1202109607807901c0002c6900200b116641400c00d03010b035a14909619960100c5a0020403485454140881d004540b28152a511481211150140003412900e225800054040064598950f04211000300c0a00c400d580002c19220510303019203080081c0a403070360429002c2484e030100039612a000c559a00d00a0764160401020780b4400c4c0024404142940207100c202d0140d50340003030250300f250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128361160 1250 128359910 128359927
    0x90e07090b0f090f06120a050a0219030902030708070609050405090a0302030a03020a120f0b0301110310060804020607050f0a03030b0f01050a0305100312021006050a0b030c0c160902040e1308 84
    0x14406042404070007041190134101e1080044c01c01d41c8074840c42000c4003910803c10090b000175224480d1700a01982c404d5181200d45501c4404a2204000c8041490f41d90072058044d51800c22001c80900075850807a01344540b04c1e140070f2300d10b490600c201c0b41700d10f0801c00060002c020119610662550503002035007800f52961003900030307400070b80355081003110f070f00b0580e0303a1348140303008800d5038200710310000402d900d04801b40360035507110400094902e4003c009002c000368010800d4402c0f00e0552401d02c07526221072002411500c5440300140c010b2060342119040d0800104d0340b605050300c2518200400c191741d4081c132002c80c10003030009000c01c000380a092117880c000d40106a0140d02d6802410b00c075600e0707669207030407205180750f0301006a0200442c01090b00f50345c850030018000442d0385048551600c0013840c0071b4030000b0704095031100c003c101d400712040d0400414218010242e0501c540c903856500c0c8000a4102d03105204004644801146904402d4255100786a4206e40941e00e8070000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128362410 1250 128361160 128361187
    0xa0309020f06092409061306021e1e0a0b10050111070b16050c18010501140403080304021011060f1009050613180f08040e060a0e13060902060a090e07090b 68
    0x135400b0880355030f03c00b0405840540c0c0c0e42001022a400590040324890b42440390003807812811070010340d03201c0b556641e80703070074030100007020140307884104840303240409240d001c1c1d0704101c44110003d10110807003007400020116148440e0681b4820303a2101e0121120348c131844c0d500d03a0103100317481c8240001c010000500f0712880060494902650407600c18600000110b603c540c924100c4400c082c4200c0014895981e002203802d00315810607070014109070954039440d140707200140c0000d10038000b481000d4580d501640c1c40c180440b40410580e0300307030700d01450405c051000840303031107841c00b03100e5401080b032107072034843d803030141c14080d1259404a803400e5404000f4000c3c02426200c64410314118400200c0e00f80c01d10704114071550060341c8951030010018544131020303002d548244e04031201805400c1146030b840c0e501c00c6641d0810340174030f400d0381410001494100e8003e5000b543c0020200d80241c7c1200e06801100c2e148a4080300558603807000f102c6070007240c098803409032030820004070113408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128363660 1250 128362410 128362459
    0x5030403051611030d2f070e040c120b0108060c2b0e0d0309020f030106080d03110702040c0804020307090c0c150b0907090f09050112080a0201060503030a0309020f0609 74
    0xb04400b403e191100c10342c0000d03d081c80e0240c0050000d00108002209000609080c460903000380000200156919900b551612103a0003440c1c80d80305041c0c0007409101a101c86980201410030719101720968a0408410b92103090085080b00d1050101042101503071000720f80820741560003045845545c0050321b04030f041480c17601890640c50307200c00c00383c60301d040c0001c42c1031502584001624402c60300c103000d040c2c0808a82180300342d2500d60200060720001c904888141c1c003601d800100010b103113205030024010a503000e03400a14004080c0d8009130000c128500460080b021074901c1c0d0b40d51900841070320300404082000544010306400041c1840883e03010641c841c5c08089160061640810700114048a044c00010982c5100b0400e08001c1d8498001070403000000348915810f14004903400004950020144140010000c01c641e1003980701c1d03c043c00d030060a483e0399070700e41c45005014081240c4140d2040c0ca8401e07c11244d07141035411180d09407005003220707507640070b2504010388402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128364910 1250 128363660 128363663
    0x2030d1a0a09020903010b040f09050606060c151003081201030b0f060f0609040f15030201090602010b0a0b0901020c03100e1203040f111f0315090c1d0d0f050a0210050304030516 78
    0x192247c800d00301560305e50259000051a00d0800205152282011464290007504590141a00304071180d0850343c042500940c103403803c140e20105e13071105030b02015000301603880a80386030804140382140020220545040340c0c0214031503c91501d4000114444080c00c0d110759900c1407030502e0342d64450900030042c01940c00c005000062004051560009540020425000790030b007a0405004540c0c12031001c002600451008101900301d42c0080748081407140a00e52940c100071481000581c801c010950b43c5100180c00d84000c14040d5141c41c01900c88211075207000d000d244200042145441d00f0b980c800c98220051105010194031200d00e104411040c090f001003045a1030f4454014100c1000e01c6500c0680d4001825906140c4068a0380d20300d81007541c29504050a11080c240d01000400e04030f00722180990b60f0405030300c0040e100095402d0024601c0031032002c040b060060219103101c809000340d50700a80c0800e4040200c8039448100d6005011030801d00c401c00608051002040005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128366160 1250 128364910 128364913
    0x901061d04060b030618071718030a1101110901080a0f0e070602060402040b0a0e1b04050a0305031b0a020a0b07030e09131205090102030406030b0d0f0302030d1a0a09020903 76
    0x8000c400c04070701951015041114004000000c0c440305080508042040140f0f260600c0c003c0d003044070005015000c258200400c60082101207900e221100b912181559003000407660759048004000d0080c8807152110461546480e000d22040f01908080320314000050b501c1600d903686514190000780b40c0c0345078100a0556901107010b6000b000c2283e58054003141c0c006091a250520401042d030b040395001c940103400b0007400b0085080410111034004800c0210b4084040c0c1c6003603210568012588003640c41000d209c0b0000c02d225000c4001c100c1040072074141400101080e00c1a5a07900080340001d41100c081c1c1007c2000000420280090a1192030b149020441541c0014800c81c0f0640f9002c0012500404460800a25010890a41c0446d042c61800c0050000002c2d4a034092441104245621104000340315924501c40c20000c6900144000ea01021810000d560341c020303c90745001c0380e15000c0035010170f034141d2401114501c4024040c0b441c0c5400c280040f0080c0d00b0075003000741c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128367410 1250 128366160 128366207
    0x203040c0308070c030b0108030414010c051c050705060a1a01050c07030602030705090f010201060303080c1b0328031b11030d050906091504080409051009050c1314090106 75
    0x44001e00101030180c014200035213103a0941c1401080307500c060b40318a0f250b9001304000c00400f1003520144600070001d0800d04400680d905200d42800d00480100b000148007080b500c0341141c0000241c50700500030022110240d8801c0c0c3c82804888081400c003e0200d1400418012036200d50000c18000e001d26060319900ca980380e13541e405980059542c080850b40201b02003000b41007452800020708009d1000307000d00391843e10003406008000c0c01720554100300245490b040051201304654001904048a1b030300c4068048180f40c1c800d40ca00c041d0010150784508280d8030b40300303024011540b01803c01008405882c040300340c1d07980802000b030710342c1408103009180c83c0c1070ba544210751052140c40003030007492411241032410245245c4d1604102c8400c0020300c80812400c405440549103c2400022251565920342c002c228159002000003810001009803821702440649244603000b00203d1420b504c13541100e550402d40c484c6240c005078450300400803288034418016018401d03a120458 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128368660 1250 128367410 128367413
    0x60705210f0f030106141606020f070503030103050a02030706020d271809020a0617010b0702040e0303040f020109060c02061e09030a061a01080603060a0c0e0d0506041104110405040203040c03 84
    0x201e401140003908421000f0004100c1c2caa0030203d903120550059021b14980120f5150b01c1b10701050200000d1b0641c2e60209240c8a07004c001c0e81119038840e00b000c200c070303125a03491500990b5101103250480c000d0084e000001b0303441e1700002d03070184112aa5122041c441011900d034038940016026440da544071000320008071180e043d1084100c00350070301340c0410030507104e00501250300c005a001b601000341e0b80288029038100241030034155482e404540d95100024000a4090a40c00f280d541c46804004248420810421450b85255100784c030b0b0600d0484e07a520040e01c00400c2a007010750051400c00902030340a00f40d101101034088621001c50420340d1b2003000c24500243d500080721060b50b40d400c0310301255034900000303080c4c0000340ba1031661460141c0c04a40c8641016000c2a0f03034640307070a070841c641400b07102c2120013200f0150141300b621460b41003507a0340394010b85042d2103d00c190301b210982424075000d48200380c140c00221030329041c0750806000c025840107009655842d0940401300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128369910 1250 128368660 128368687
    0x6040303052208030703061401050901050705010905070b0c060108030a050316090b130f0b0c07050607031b080301090e011413080403020d05070608150f01030903030213060201061406070521 83
    0x14840c0c06440103540320b00e050103010381141c0d03294002301a01c0038031000e0035002d40c1e4004112411a007081c80c007140c903800e40d480c0c51405451600340060840c0540c11b404541d0303914070381c0540f00f110b0080040720200c0e41c1e2014419201d220f11000000001e004000141019800140440602841d407a00c6200140d45078403004054004a816556071610800100200200c41d05107001070042030f10403902d410b04c60074000d03a50b074a81d032196602540000c580102454001c1605903005e0302d155500020b400003e207000301d82c0b50f000740640c0002e10b243c94200000c0301300512440320511601d00c204806615202d0403e841c50440c0001210008410000400181c440c58100b038901c5118900a10a030f07410004090501013004004002900340d50100c52207555404e00e100c0e500000c2828009076110f0780d410100c001e40b003410070320980140700d0940018400d50543c00070b01103410f00c2803503803e14100b410412100d886090030107080c640c060f2078036035107504030760303100c00301c54100280340303900d0a4010304909 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128371160 1250 128369910 128369971
    0xa05060a0c092112140c1e16031103030c0109060e010b06030c04140406091415040b03070506031e0703061409090d0f050c120d0b09090604030305 64
    0x650109456501e0400140c0d0440d00c00000707810390410b002020318451000390001c120344803002c0d040c40800b6121140707040c054401484c2c1d0101c0c5040c1d1035501d100c602d403c10381c0c03030301c803d4440c4000c250301c042d080701408000305034070701010424050144c15500d5901c51b016581001220507074540802c01190350740c1c5009102d21031301c09100b07900103d455840100d0362402c40d442a03071194040e000400410891820920488054862140c014851040305d03201050060116410076880c661900f2001c4181c8600104035a1141c4c40744400200621a03030300134401030711543c00c0070f1a0550b102590600c080d280c4040519841054142c2584180289003a1408c1840c0300f503880001180d5519414080c3c04020f0b20b60b444403850680d62a040c80c01c0c0710751801e40e20100b41010ba4200b00d100700b42440034901c200120f80740d0402100448590a1110300898100e40c40b41040b0000d9516042d14005141002e0813013034419031444003c1c00056450792001c0c0c010300320003032071100001c00c0b044030b00800b00390a0506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128372410 1250 128371160 128371171
    0x20d08041814100602060f0405010b1809010e03090a05040b0f06030c04030309051801140d0b10080f010902030304060f03090b070f030b0901081213080304171603110603090a0506 78
    0x4500d03540e00c02c51007804010b000d000c0c601e1142400d80188080c580000c0c070b19400090359021900c043e03680e82801401006940c0c18070342e002c030304000204040c9502042050107841c805000b0007000d00b060803490790724841e480c4020b801c000d400c241004a842e095000c0d1601c12800380000e0320443e088030001c1c801e0741c82107a0010140c03070080313400d000f03141e0b0241800d4042c00007624a242140d4003a80b03510720134403052107207008800600401404640b6490412a403040c1c0c80714000900781412410001241e095000310007107840348120300885c0181c14020b685a46030090055858130341000e40880b4861040d19010003850740b1050680e00050303c401070580318a143d556490001c4910ba28010290303414248402d01c03c65000300103000c500750105d0341c55010180c0004003035a9245001441d64540300560140b03030a40401704000907244840780e00a06003d400f0010344030a00103c07040850290254040074041c007510400c0c01035107045c04002990040303940741c01c4074001c0250740e85242c41c260003100c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128373660 1250 128372410 128372459
    0x10e07030506010b04030804050f131409011103060a0e07110706120605040203250c060501080604050c10050301092003040516050d02150306010504030b01080d09060e060304020d0804 80
    0x410814020280b180e10b0240407801c1080e4502444c1d9111a2114003c50141e1445140404822402544c80380c03503950410b10441c070180f01c010450700621a81c00301c1119030b50280d508102c910248102c0540440b4490b41c0d000f01009030071800d1444d0030507189001010346090008000c00d00b00031034000c03c8008001c14041d80ca503810061820404010f4461690000380118010f00a01c03411400001401c00b007080b404820310540c0ea1f102c0340888454001e6000030780860320341000410203644c00704810748914020411106e03003807501421700407140260760942000503402d000501260f16242c120081c03403030803404059412800cc2d17040142940c8181c07012204d5038001400c074031544031886040d0000307000c112216043e8040d5500031902d105a851045240700900200040c0340b81e0251050300d001d56002040807405607100d020041e50307030020100542c08140d0740d0900065181c890641000c0f0060040c0107075003181c0ba035500b40000042050404c86000006103c042240103620007143c1080c1009803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128374910 1250 128373660 128373673
    0x30e0a090905010b120d0e0402160506060301060503032107020705060d0b01030c021204060336030810050f09060a0b030901020a14040b030f1e0a0504030206070806130c030e010e 78
    0x103082c5007102c5540300444d000708103004402c942c80001041200b1411884d0030809116000c140c002002482185400100d0002d0000d26078107202d000a07990340700710403d4008021a0361164201962030055802e5140605004650191220024000c00703810440500480d01156103990000b02c031b50300b1050442c0780c1d09a940c0134410440d80c0c140200214003035039001a2401c070030106048509031046001d0801895143e02101d0501042003945814002a041594070b403e480002c03031b000c50442c2e2032415800101000086814411410300c0e403c1151001064100d24a03c00c0052044c6440c0c0141640c0c0d102c10f240c81c0010702c00303c00800562045e9132041c00140e0307402c410703a009054500c0b8140e003640d0b4858180000d101228041c400c50b504200004810307891540c5032408c0110540c1c0d41150360030f01904207014003032100011f81241d80240d219409540140d80c0b403d1040301c60003400c8540300d81c4984074015000051110b035122031465000c9290120b03445034521100d6081d41c07485010f00ca807992103103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128376160 1250 128374910 128374913
    0xa092315040602220501050406050901110f010606120e190203010b03160f0e0f0106210204120204050603010509060712090507030b040515090c04020a0509090709151b080304030e0a0909 81
    0x644e20000d61101484114442810480020900d01460003010140040001c04a0480e80645401400314001904884071141340c041c25a0107005030784030b128017081078031b1419078160030315009201a140540d030040104405514030038501140c01e45e002c0e60195651400481c9076201405000310200d445140400800d141c514070741d080c1189035001e40c00700e42c071030001c0c0420005031444039411103007540f4080011020348410140030484100444510300d100140c00598200ea90f0440e8016500840d010030180d44c84109250071380c3c80441e0010400d400150000d8600e030b008403244581d111409100042c3c001c00c0e55115858000c1980040d60201803190820040000030402d1243c000b102400d0b0564504020101d140c1c0c80c4003080025210b00e4011801840c41d030f1240055079004403004001182c06d09084c9000b500209150203101c0d40c1845841640c0d05007401032020711298072540042d0102d21145860700d0302d207078002400807002c120700c2040100c03155482c011008041e00c08000000b075000942d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128377410 1250 128376160 128376187
    0x51c0210091e0510020c0a0e04051203070e0a1508070c140a0606081903020a030509180106180806060a0b09060d050c03090d090b09040f0b03030c150a092315040602 72
    0x1583d03507030017158088a04911940c40790204c50003140e007a80b0000306540c54629210b400c0003d8201004001c05001c010007450f04e500400040b01c06806071090000315845054079030b0303041540029400860081c0c004204a14424401c00a038980608440420ba0b15120305072030601022160903610303140c8400b07081c00412028001601400000102d010310141980c0e0003070748070100413001905000020070720318050f44400030441c841c4e144001d8124255078490401901c80724007904052100c0d019032202040c620710000c0c00c01e00031200105011100e502d0b243d451445940100425604080700780165034402c29507009003400b49050007180c1e612407401408440c1340807684888007041144003142040030440c241c08699001100341e4000c500c1d0300e900c3c801040034003184c80312a81c0600c030010700a2010318000c40d54080f00703c6030700784810145c0c0b100360102050b20001600903000404001900a5013040d04080200ca11280070075140d44401c500305101078210100e8081d41e0300f039000650003206408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128378660 1250 128377410 128377429
    0xf0c0306050306060a0f0e2d090f0604150207060e0106030506071b020109140f03150105030d0203130b09120d09032108070e0d0b040507030c051c0210091e05 69
    0x40646400031040c3c035042d802c0c1c03008101841807c040b0303021320b000b01d219002c000c85d000a62265040c064000140ca00074040305401d800c0344c0510325809201c1040460810100d40300d40070740d4000d0311035800507140b80f00f44d100941c002d0304111001a62480ca07036644010a00518006500501c081c050f2443c0c0b0030300151075581b001c0c0220940e6a24001d582e07006070780004443c8148e0709003120705c81c0c42010450208244032240c00c5200c1c0d1600c03900400d2140ba40210f117000d41138403000d8043e5040a002c51005a030307a8002c00b444448001980c0000b405600c0502020700359081c0010800c07080e880c0c0b0400c9150070300d5110f42d00c400009440310030a209025a040440104040a02010368468860b010081503031402420322001c110001010505595595a002c0182ca4108412940c1401c241c0b038195500c5610f440200c40d111410312000565181102084052100c0c400200c2da100750301707508010b902150154681d0612100b0400030541c10610f0090101408495200c4143c9500b01410002002b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128379910 1250 128378660 128378671
    0x150603120f0304060209040209030f010f0c020a020307170a080a030c030c0c02181810051906030503040b031b030903090111190f02040b12070303081b0703050d0f0c0306050306 77
    0x3602044000899103600040700d41c4182c04c4100142c65446460020b0041e1080071002ca50601c02c002c00c14503c544c1c10360201c0744a10b9004c4080240013003541d0141c2e190020a0400395044d082424200405900d035a1000181d10490081c0c80e060b0f09036596040090b04160714031800070f42d58112001e0183d40512880c82025070a0400105c0d01403294005400e0040c41c0c2c940d0940300c052180415484030218401c0b0b000100d14905075803411b007a51040c50018402202c0401d400c01440b0f801c82540300303061003030320b09803a04400070794130f01420241e6924a5500c060900c0d180d40c0d02d40122a4100700008020798000c0c0343e504007840c0e4031800031000400789042194280210340000020a4241040701c085c04580b83d0b1050503200b520380c503400010000c2ca01d0b5182a504007806a007811aa18408507207142030380e1203034407192420348446251001810318030544061031b4408004c4000468020800b510b01040c040310080741c403e80001685068400313010800307000c241c60314070074400c91074107201e02913105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128381160 1250 128379910 128379943
    0x308070c0b070e01110f16090903081b04120b060405180613081207050c060a020c0a23152e0510200c0109122105040503150603 56
    0x5600d540c89088003071501501c02c0041c0600d140d4848910b9001c1c10301c1c00d00b058200c00903141c05045d09000a40c940c130229030800744803600c008010592810302c0c4200c102d19078169035004290b94901c00d003888080182d51007074251180a100c006201c54407128440702c124070584140030b41d420248240000d5440c0640030081d941d080b108109404200040d081d80c1c07106e070110242e4590221070900281620518214114000d01c41c810819040e41240091001d1039004049401c15070b10505441c1c00c900850090411340c2e000408220081492208100303845078484603900404c40d000c0b01441e28003a55290952165000b60f001c0003c1c0c842c11052103402203554803c00c1c2070000c8116910103882c4028020680304016101039104128850000300e030b6030f0680206104031848009403141c0d540c0b0241c0000320b001401084001c603601626a40d01180203500c1800e0198449034101d001400c03200409101041003000d1100082e20354040210500349000c003081c40040d0b05085042c14140344440303991500c0d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128382410 1250 128381160 128381177
    0xc07060305090606030a08030c04030602040902250c06030504020f030a0302010f0e070f0504050421050903010f0212160201020c030708030105090702030c0717030d0e100c180603090809090112030807 87
    0x30b648000c01d4403140b90351f000e19121f9403039844082d440002e00030b0b5003000d00458408030300400c00110a6000f44042007072082e4500c41030700302c1095001c0c2c0c890600b000805400e0304a4040203403902942186802c184001c00c41c0c4840083e26001c00e181c181c01c040f0030340040c0c0d16640000b014820070b12604400a982a01070003a1600b403600c40082c0350604c0c0704075801180d8940018050080c85004000402000c50a20784014020030005280d60042d900e510b100394a41042c0031044840380c421540401c01d045286141c0d641c034592101024075841d0b81e10300555400308242c42d201030003400140710f90380c46004401c1e120350500d800d000c210300b0000c060360150343c01004011680c03240060791004981e419240b40c5801801d0410030390450003652102d030348a0341810210840340d4804108588140100c4504028840540c00111080d4545040380c00c070500801d0b00500099109400040c40c290088010720b01d8a90a40081f4030040000d07409142c502910b01d0340c4004043d880750b41ca9421079803a16040d402c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128383660 1250 128382410 128382421
    0x4030e010311190804150606080f090c1507050a17070b010504140c07060902060f0403050f070302010509040e0703021306030201080906040c0522061403070603110703081003080c070603050906 84
    0x1405880003d04018003011000003000c0001c180d4a510b000517922006101540d50360001400900c8240d400c0010032000c0c10000341d84040001e141c0c1d1880100811445c20005d19a0212180ea4400c560036245801034842c0040841c0711071040840d41250f19010b00d6640c19142090515250103802c80740c481c0e41486216850150201003458003c6421320700c03595501c6480c81d211000b0586c408009400031404516a040b14a0401c060401c4a01030000c0e00c1c60084502c0b180c94503150a4080203003c14000e028840c002d0034554400b5444651443c12240a0340c6c036900015452009980011079013511850240110350780004400c0c0c1142c1e103d8020002c07801c0a0f91500c00800742c6016440c00360408200c164008000e40d142d45612600d2801c04000342612114074504030030355a8003c40c0280701c0d100001820302d03c28824824103c000810081c2411241e07030782290120303400342c8000040740740781c20080007095504005100a418401c02044198507101c0d0240643d840180001d402d07801c030608005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128384910 1250 128383660 128383687
    0x306010b030106111608010f0513020904080a050c010e010207021c0321020405040e0c09060111030f1305150c01060b12131b030609110d0305121e04030e010311 70
    0xa0646001e4100512003480c004c40451030102080d1018620707200300000040c001c141036001000c0070001c0b050620450707130b40c4054004111400c0301e00a4105c03003050009804034201c0406000c1507126441d101d454050007150603400c3d959642c80303118842c0d5001442104502c0d0180d40c041ea070340c0303201e104a8004500d9403000340c4401c610381c903032505003d01100412803140701a0b0490f005044020401c01031016a100a04d80d28111801540c1c0507403142c0d0086185980581c104845012000000314640380d80400d070066103401036015104008081540401c1c02d035a0144448600851803c0c1162185052110103080d1805e42c0d01c44080003104120306d003e11070060f910b42d6404502950103020001103440c04d05603200b65000b41ca0140b5800640100800040ba007102113114004c8940c000079a040c0c000f00007911503800780040c041142002054540d0142031880380d484540f102802c120020007270544c90700740d0000c66007140010f11201e0346407215030705442212558040c030101141051007103450704 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128386160 1250 128384910 128384917
    0x10b07080a0201021201030308060f0103020319020c0c100804030f09030f020f0114030907050102070509090a0b04050c03030d020306120d080c300702060906100611150705090f0306010b 81
    0x9000d8000c0000c00c0c0c5000c034000d40440740120380d0b450050b90603603924103005120010603503503035115912100e80d440c89980b2900a9038040c91001c0d003407070465100210048001d5000075940e42490040001764441039444071103401c14000161204071661a0034980141a03080c1c2209000038420701410a0011400282000c80100d03410b903098403030b8500303500040c1e501060f400d4411440320000000c1207010000800e0520840c1d8080c0c00316051940c8a00c00c000c607201c2c04aa0030602030303205080b0380c808150302030509604070f40075100355201e14030b29202003425a4001d0b2101d0b1000d903000000e111203401d041d40c1488c0320b00d4048014000328418180020680700700075046001d080400b080f43c202a01c0e00019685941082c14103000d20b0388a0b140c12203203600011a0101c4c05800307000c00103072010001003801c9203d010b2007005074092506000003501d00c407811600d103003064424840300700041000c0ca00340300e0003003e10380c484646680380f450030007040000380c0e052107010380c100c0c2d00100f14000c00103054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128387410 1250 128386160 128386163
    0x220806060402030414160911030613180501024605031902040306060f0b070506040f080d0c18060504081506040908030a05040b130f0201030518071d0708010b07 70
    0x2d07990340c982e800c2008079110060440034140c00741c5110099a0018141300f50100c0e00400c0c1c0c01d10440304111450030842c007080310f2094101282d04003c00c805851030b400042020791b541e001c564442c40b103807601803c981024004190a200c5843d1604404a03c2d12150311510942034065a9101c01c0c1c0c45400d0401d1298200306080c044040003041c1c06030140e4648420503000c00908649960f0f4904280001e40850301c21213880d201c0150020940340c001384100c401190b0800f0041003551910b55400350a001500c1382a0780c03001080c01a448950668084d0190f2003070265924003401c42520038015000c809580114144401040200080440440d8262002018040b849416511800424003800c5490002046600700000f0000841850b62003240070342c0c010540142c3c1655104c1241c41c0360855000058507100500c9602c500540c4683c1045070b000c407041018228030200040e10340e25001480e08002240603146148140101c1c1b00040694803051b03c0c13034503809031351401c40101c0b00303032144440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128388660 1250 128387410 128387419
    0x5070204060e2e0816031403071a06030a1406040b240f03031908070801050f09060402033606060d02150f19030f0f05040c060c05010e0f0322080606 65
    0x1209a404101d030000500826100094a01c1022042030340c0c205e01150740030407221240d50034a0383d81d1412002082c1d0341860750203002604044060404041c0540d030040509034540703d0141d041001401c0f020b6109020001440203060909040c82c250412030745c0201102c1c2d05007441c1403001c0e0b2240e03401c4401c4410240544604980004d08000309003140b24140905003403030300403840079034015031000d4040c0c85400665075070300c110f0b620303002006105485005140e0388151f0f9100400d00300c0c60150300841d00210103c02d800700030a0f0160803d802d007109000e110400d06c04115021132100030070302560b40d1012040794a0b03116400c40754001014503010030a42041400d012404400c0c03075030020704442c040500b650a46400041f0035038020050301085101000c42404c1583c0036000480d0350003214021540b01190104590500d207040b903400000d014103507442d40d22148031405600050183c030748803182900203940c1d15914100180c902c414205904820b203003461004001054011a056802600885 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128389910 1250 128388660 128388721
    0xb090114030702070806010f1508071806020705040c21091401020424020a0c0636050108010503031c1e0516030f0605060405190f0605070204060e 64
    0x4004035200118010036004006000060020480d0001a0041182d580d18100c503d283c0e00c41c802c51350720383c0a034480c00007405e10aa004968440c00b652240b47d12024030314014000d80c00c2030050f0142d55115901000260308444020710036400c0500880c0208a618148500503806680041d2480070581422040791540e035480c540030071861480c112088101000250344507a240d151412103a40a01da24054031030a090810303160303600209051028a82021410300420b241c103105890041400a031203517100243d5201c84900286d4441784440079103240907580300300741000005050b800c2c06800503403290384180070039002000301f000c1c0d840d201c400001020070512020022500305150295440801a050a0800102e4040210802400d5030980c0d800d11410a082824504842c0e00d402555007240042206003e41e042000f0030048140c034042d410407420f42d0b28041074944202940107440003c2000030008203601e02400780703101030b00310a84010810305025840c00d071101403043d440e40c0d00c40b4a20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128391160 1250 128389910 128389927
    0x4031106072609040501060f1706210616020a08041208040504020307050309161203110307080c0d110114011404060e16031d0303060d051c031a03060f010b 68
    0x140000703076a01d0742d502d00c942c01c4080c00e0700d16034400d500300c00c2e04540610315100001604a1003400d5013903084900340c8512501c032000e803540c0e000c0107200a29040c0c00170b011030350364401c0c802c0c102140d00e0b1410003800034141a0034000382c1000a610305800060441d4064107500c00403a05540884045a440400b5040318070070030f24000d0018055680000da2041c4007200704a11035400c000290310890018054404c0c411ba00113034480c10040d14040e44480704404424203000078040d00d40458402900d03021603061401941e144501580111846401743c0c0000005c0c40046401041c801a4803000382c009201c08050b058488034810701c1403103036079180e042c206020800f40e2140c0d403104014040743c500003180c1d4500211112038a00f208260f00c0006803030a440c0608040071700c1e10b2000003c00ba180911f10f19140c10b0100007070940303604426a0b0ba80a44811701c58555868100d8190100391910017040114040742040c80b07111802ca08980260047c5040140044500c1c0302c040c1034034421182140c03120100d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128392410 1250 128391160 128391173
    0x708090708120301030201081b0901030c17040303091407030809040f020d0c02071a0909010302040b180106090302010801080c0f2b061a1c02010c060b03030a090602120403110607 78
    0xe6801141140914034260703209440c88030003941601d00130780300c0c22807a031a0248079800781504103485024201e010310040c0c0140d0710981050403004c0451504034265100c45800388641041991304501199445000f0002c11200c52840540c50381c400b000b4000c05451612444024400e007007500344180e035908000c131541a06030741910048a40028204600035004001030340d503003c0d45c0150b40c4504945600c0340c0300040168126001e091b4060407001c01646140d00380400b0306080340701c0c19841044000d044c3e00c1e0058026140f402040e06580d0001482d140d400058400031068202071043d0b00450b451010a0b210030794518440c40301551617540e00f072902e4281300614480800700305030039400141e100090017050f80041160081d40070030028080740440c100509100c1d85d80340e41024040d650901e202540c040c041082c01300d4007d001c0418a10326410000b03003558001d90302ca01c007060b0007100a2044503030401400301c50031665501107103000d04584810003400721489807284511000200c40c410000c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128393660 1250 128392410 128392423
    0x60f05071218080d0206010f080304031a0403050f0a0f0f09050d030c082110050105160602090a050904080a02010b040c2007050301050709090b0f0108010905040204090212160b0f03070809 82
    0x3d055042d40c00c00f41803118025100c180a10074100c040959501c08210202e0110445040340e50085400c0e00031120fa126654003410000d1003a010300100b030061030300039501e03031004261545c050341d100000024400005005180020100c0341040760000b000e22030b9843d000301c1107c00f107800d4101004908128a052120f074412204882c8000c00d000b030344400211b0000021900900c03503040f4051640b611680111403500074100900c810a6091b00000c011aa240e4018540e02d00f000e411150300a444501240080900350780440c2d007480e00054030201d0681c28450719106000448041c000340e20b10303400081040b4081d4541c41c0c0c2c03420550f00200c5220b03008201c500010714018000f884985130450700030f001d041e030b0362003000140d40c280b00141ca09450f2514100c440d4080584944a1070f9080140c0c0f08020f00300141300701d800940d50707107c4030003580d95a0051009414014010032040008281428548003640d020744e4510605020711540500d60b0020390340e11150514184006a841d03814803490500d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128394910 1250 128393660 128393669
    0x2031002040f060212031e07020c040c0503060909121c0603020409050601150f0503070f020307020d2a050f04091b030605010306240b0a090302040203090304060f05071218 75
    0x1480020300141c00c21081c001a8110f402a40a031207054210030700001081c4012200c9448010b00014008201d001d0120225001159441221034503c0010045004c44901038841d034045a008010007040c0c1c64901c40d036a5210142e070000e030031810100e80c00081c1c14001d18104504201c074491200b000b4902550010b80203640081040c0062840e41c01c142e500c0301004e0045400220035503241e041e006010340880302d61903190340e88951440d41c2d81d0380c04580d48180000041c0460000304940c02c0580c0c0d509440340e000c50300410740b490361000c191a401083c1034400b85070808404284034200a1139a40313107090400481c0a94020580740358034502030340920803441246014014541020003803250380d43c451410380c0d12a24003005074400c0c4c030120809403201e0008140060307283c1d180c00e00c08001000054600000d103070504003038083d01d99000170140d81084a110180e51b0003c201081400d030301480100280505060442c40d21000f47c035101400e05919035000d0522084200d0020848503083c940402030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128396160 1250 128394910 128394943
    0x61005030307110405060d29101401080403051c0c09080a0515040f1e05011a030c1201020f0706020d06120f06230c070b010f0f0e0903130f080d0305040206070f0203 72
    0x501c081c4230030384d180107501001d58003007103140006008000342c180320384e0070f4900d01080301e6445840100112510003000308101c0c10894103201500c00782c8980e01421100040d0360902044003800b10000502d081d0301e80d4800001075000840c5c2402068021030440e04c02c40086580c28031990329420301c2c4a1255000c480140f0110003a01c8050400c2682c10160440d10306c04c00083c403404245004021141003404100360f815000308889900707528050303002c00d0132030400100145c00c045145052003250b070021842690382076000290403100070014460302014064481c580201d0306101d803110300682a607501d0051444e5524000c0050503560703e0700091403078945c07440c0644c1f5032409281450440d084090110b451442c0c0e10300200e90001e40145601c181c41c0382c0482c44010a16128004c240752001800c1c8400b90300041100784900d4035135804281c041c0c035242010384803203460000e403149010070440400d03007014a060140b20041e9114811901c141d5089480f0510300d0079a800043c1c01c0114030400540d68 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128397410 1250 128396160 128396183
    0x2070203010b0a0608071731020301050c07021801150f1e0302071406010e07030c270e0f0c0f070206090a031407090506060415110f061005030307110405060d 69
    0x2d0360001000f8442c0c6125034800e04540306500c0c1d000f801100544a491442642c10b40d2030b01c0c0907003a840c1890301c07590072300a032144001640e00440d08442003601d41c6c94050400241200550800300d661100300340711500690801e41c5040c00f140c60b426038405120080061740e50100c00224801c1d288600760b441c480025450b410f0b51040b000d8000c1d4450b81d41164014101c05075128180c0d40480c15504846524000e40e0300d5030b660100450041480c0c0c8002801d128031006511040c01e69800c0d280d54100c94114044805802e1034840c06644c00b00401400c2a50420410001a150b90f0b2042d0740308220190f080c10f44403807180c03000804c43e00440d80c14a070046164a000000e05c594019401294803400007a1548a0b0300c850007401520f4080b51600e8114204100c100920744c9480b00f01040400c0d81d281901107524480012030414610700782d091010b50140040c0406606021800402000110011803801c01e080c1e6880280020790b240c9a48500e03504c40c0002d0302c60f2039403891051580c7c2e20441d1420b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128398660 1250 128397410 128397419
    0x12c220b090c100c110603090304080106081005090f0304050603070905060a0c0b011d040b0a1116020f27090c04020a02030403050d0804080304080703030212130b0601020102180402070203010b0a 85
    0x40d0b40c2000d041c00341c81804030744000350b03180b4010980c140707805401160030340101c4824001e200540e800640025003606c410800082d5800c020322403080030388903207009405440c13010051304c4c040d50030150546803d60421584001c210300b00204032001c07036906a45880c1c696035440c5042c3e41110003503024540001c000641985181c2d8062039850059208015183c81a6225099500804d50405500402d03ca881c0b02040110b00d0501c0419404007040c0e80228043c44414038028041d0407044a403014404e013029804118a4882c1c0e0f1000c81c00c005403603c41c2004070505500781c0c0b0700d10700303600e0416286c90341c40824021030042c040074500d40e10280056540300c060400c001e56a030b00c544800e403007500412080c80d01c031512030312030780c0c0c0102c0c2c0003a280c500f0b41d11180c6a601c1c49030702c60b85d403c400307141d82000380c400e000c40c5c0c3c040c3c1e6a1043c80329028140c0140e10303605202d03407246002002a811a481002081c0c17003080400300346500c40d1000d680040e1036020a00c042401000c1250701c5135400aa01940042d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128399910 1250 128398660 128398663
    0x100305090705040c17090606030a060b1f090f080a0b070c030e030d020d03050c030106050a0807020c0a0f06020c010e1311040308040e0105030708011404022701030605012c220b09 78
    0x2c003500d10174002204665120507420b40c5855043d2071480d415081400200c0c0030417500d0308138401021004001007141e2381032801c481a442001802c050100352120710421000c0310044030800105844d8001d005034502030703900e524104500a010a040c0082d160f40c2c40706240c840d002960385003001030308640c20790b0a00700f4040d686503102c54501000904160010b10174410310b50646c1d040320100d8413203e04065081c0025644805c0040400086106466904410b41e0703a24100f04001d041110242c02443e040000003402c0c6000890240e06020b110030145034131380c60f0b50000c4042c3c4200d42800042c10701b02603a01000602c05c581c000303401c80e00c001c5400703d107200a4001e124100d40c401c0701180c19480d82c2d0304015003a54071704011002c82d408240001405428402c1181c04050310720075101c07181c400b0410f1030000c05642a081600da150349d900042c0183c45d068a1100314482103c1245007a011580000300035a0704001e14006180e00d40c8007400c12485484861032a9040d80003c810507185010180036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128401160 1250 128399910 128399927
    0x50304050a0f150c0c0b0126012d050f010302100908030c0c03060f13080307030f020703020106081b0619020a0b041101080a091101181802071a06100305090705040c 72
    0x74002034681444c40c52401e00070030200c259154003507414000c9a190201041c801c01000148540c040e40300141e45281c503400b8454642543c01a068095010708544c40c5401c0050280e11000c0340c40b8a050b00348600e044000c9041790441c0e5044818880301040c0200c1214030814036842418140300c003042141c1c0c0c100011580d01c410b000107800319900c5580d40780d00c01c01401400e956080c0d04025044688010590030002542d10400c1410301290011075840c14104903403102c0d00030b50041c0d64454060012040910290768400445d900b40c0203244c440b140000c1c00c600c65005510100c010680161031100d000348100181560004403900c034034a418103048445401203960b05000410031400a4040702044c07060303081d0f442e005552455020960001940e000c03070452080300000d014000009940c03e5070a11074500840c4800015844040074074000252050060b01c8100d4a151321080080c04d8598507101d03100704104c0d11340440c0a40b142680302e03061a0a40c0c01054229003401c000c1c82101d6002400e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128402410 1250 128401160 128401193
    0x51c0504021002010506010c08211806010e0702031c090204021b0d0302180d0c030204050c13090903140d0204030609030807110d020c060c030c01021b0d03020c060403050304050a0f 79
    0x30750000310790722803ca00300c0341c0480c1c48a02089411103442d02007200c0b10007607c01146d07070940090303401b002c075084050481c2d8116881d802182c41c140610240c1c0c030041c0681c40c01400b140c1d141d902a41000c45000e5101e004000360322180d6040f0000490440000350440e0001e1500034100715558036800c8901000f40b02c44481c10b03800f5204d40040414041d1003032088400103403d004000446030840e2082217004071a6080546414102010100c00750380d035846118080c0300390301c89480d568900c101c000401b80810350b104020462500c801c1d000440e8014a00c626681c021480580d500c02034100444002e0050350400380445282502c15807c1680142926016000c55206c003808404030304a05550350203480d00480040c0c02580410006040c05005012804500300991b401e00602140450883e0014951051082030244d103416082c8414810f80810011a00d02580b40c8411401c045640e41405400101004000400a403e11005020210030b0507400942c110f0b1a089600f0401d0031500082c18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128403660 1250 128402410 128402419
    0x40e150a0e010605090d02030f010c0201020919120303020f0c1903030b0616060203060102430e160c0f03020604060b0402040f12060b1216090b010509040b01051c050402 74
    0x108981d115000c000b4100e40e401d82d1620715248110090000759400d9240c1241c0500c580e148400e090b100a014420714189075500068440c0e0740c480800c07110b04801e03054240c01070124081407200c0c0b10b016244545c01909818017582d01c2d40c2c0542500301d244100c0340740701e009002d001c09070602c00007502c0014002c5806540c080c07010342401300030001544038021407000040f440314400b000041542e0055544040140151280c0f20003c040e0030241d070b8075020b5000255403201180c05170b282d084822400c01c1e80d18080200c1c04072402c0011640f4019030107401d10750001450880e0510030b0b84618820b0301840e52001001000c3c812626010795907c0c42501c044410904103078111b941c0b8101442a2403c64001c42c030050000c41c07800364004a119040d40040c1d940544600d10300d045503d41d80000c004c00340700c50000380503001a400202003415400d070001d4114900f8402040d00503070f0f001050780ca070000111400940f0318130190040c0c495211303c03101901c0740c103c0740d1440c618941d882e0740031034400d500964 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128404910 1250 128403660 128403679
    0xd050a030b0901080a150b06040f17030708180a0314030c100c092603070807030e010306050f0f01020a140309040f0203070801030b041a0f160f0807030908040e15 71
    0xc00c80141800d021340105680311004040c0410030700c01c103a4108040c0c1000c002612111000811843d5010381c00600341050502810000d00400b101d282401589002c082c40c1468151b40d20012184196003c21a00111100761074070199200120702c030003198000b44032104052591146074a80d000440c1c40344003806182d2400903206414040c840e0a0304d00f0b959200300060a00c07442c07280b01140c0c070740d5400c0406c000341c0d0340042c621310410041c225240a082c01e0741e250b180d1403400410014203080c0d400d0406082c00020001a1a40080440b00c1c0108451040542062100403441e00c0110700014110701c2480c0b014030f00c14000440106803c8005650a1100c1000460003200360710055900d0300002e001440100080384c100744619800c41d10a0b01900f91111080c00d00300031140c0295140f1030074180e0301c41480b007080a00030340600c52140c1401c1c07407811010111009000c407000103209134145034032050700740d00b0411844116406814443d83c0f0690741d0805403446404540510182800380c00d401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128406160 1250 128404910 128404931
    0xb041209050a0603020c01150e0402030d030b03030702060a02011e050105030c060c070b0a050403060603080306180709170a020d05060a060608091c030908180a090209010519110d050a03 81
    0x6035a580151803014185000340307460310804800070340c0b026190350110b540e100040d0201d03c00144100004201c60b10400c29981014010076040800e1200c0d1401407601c4d1101e10442c6840101c1a9031a0603011600746445402500c01030f400b51034585058400c06802280612056a0039440b0a05a4105070100d43c0d041c0480001d020300c522441e050080980e0003142c0402104000200802080740c081ca00641802da403950f40b00190781c900e801c210741000c000f104202003824605a00d0005882c1260b6912040c1484040680300004074000d01e010317800c0c9036003400c5070514100049800c03241d0240c00702000e80d003141441c03500c52505917480100b440c184040000d003603100d002198007480821014001c0350516030512230484080150a405041d1175410b079001040703802020341810242c044045420136801000c101c0085025008401864814050300310079036840702c00e80b601d1030b0009000b18502c1a10440c1521150b1801034154218481c0107154440781d070380700c3c014102550f0107071810b12064110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128407410 1250 128406160 128406167
    0x50f01050411030a11070c06030b04050c07151508030c070e0601090812030402031204080c0102101a0904050307080f07060605041a06030711070909030e0a03110d050c09040b0412 78
    0x548900d89a10b032018000300d101c411a50b4402c00080f0b5490f10054a0000f0640d15415087c40e0381e440200800d641d088407500320706141c0642a40030b0741c0720700c1c0580b40203069a602c54a00000340c40c8009903c0d624030305010b8040d10282c0660262007040308aa481710308a42d01d8564800302c5014159992908401082941d40500c2004080d52000800780c103001000300230614180d00020001d983c940314199101000b0b080410003803018010ba500a0554010303010300181c540404184074140c1c0c1490000303d110800c1c0620422a1410741c221020b074010384880c107095107140504070015103003080010b541071007550000010003c440c85030505001a6035180b00b00320403200c113100600d0622045203582c50003844c100300155444011401c1ca6500000d090480c80d140c80d40c0c503008152800c1d5640b510006058000070042c5401004490750245e103800c43c0d5804042980d104542800341d003000428008004007800a0b5100c0c3d0350140401d40185032038140307001e248506440c04d031204800000b0300e0600c00d11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128408660 1250 128407410 128407421
    0x10f02030402090106120209040513031707020c04020f0c100b0901150905011b24060b030c04092703080415020c0606010e0a05060d2c0a0b040f0213050f010504 70
    0x2c00a2048282c0c2c0c0c0390500035075040c694421106520365080103000340f04e81e19841aa805002d05000b45565212a403074007a226140d005880c0020300f500804001030964001841d1455500a031005a01c2e44000c142e0101a4000d10800d81541d01507443c2254052030143d101034100301003100d2614031a40c0e02c11144520b600300c1c089440010f2000403051040f54001c010040d14440701c1b075220140311056840d600c0c0356065100c0103000b000c4900c0140000c80d0030901904014241071701c559451800c01c41c60180d403e00c90b500c503800c0c005440360048904804a03945141036824a0510f9030000c4401e40341c0144807a908440803110189030501000e150892442a10f00b82c400d51130040c070b019200c07140152808900e80d10710f03075801481c410000c2040e0715400d0150075000d0940d48007260200b05071038603030b40c040111030401c0081300110a0fa2202c0b0100010000038980d0004a844d00b41d885900302551203400f581d00294001c41c00c0e8000070750101d0135600003845906ca6000000700750341c03580b0400c030540300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128409910 1250 128408660 128408663
    0x1d010b0a12022209030c060f0c02060609060301020403140d090608010305100b03010e0304062a03080c03150a0b12010602060606221205060702010501050d02130b01030b06130602010f020304 83
    0x4039000301850040c01c3c0b42c0040401d060010000160707030000001c0680c156845041d04800241920701c0940410000c0e01402403403400382a03081c40145a580802590351000400d07085c40313184140041001601c0030f50441e00596006105407504d02c0c1034480e21951600c82c980354100150550400042c07072445100303114182c070b502001502c0c0050745445400040c2c010082800da240d581da030068840000108010001000303242c07a03402c10750441103004180c005400c3c0021210800348421031f000643d00200c41a0f002561540f840d440b81c960742000300440300070011540c1c001050180c042402100100035240301c6180711400100d684c6c076214200c0c3c480c501900c1310b60304010180710004500d080040d0100550060010f2141600e81c0c2d9101428054401d101c1a078407600940c040c042c0182c3c0c28054035024100595020b403031910154041002c402e42085d00580459480074200c800c2c4c0c0c4213410250b03145000801c0d4035160824240400344042103445000c01540c039088080c0801c2d100382c003c2d2480349 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128411160 1250 128409910 128409929
    0x20105030a142707240201141f09050606190201090204060b0702090901061a0a03020c0105040c031703010303020c010806040b031005181f0504020607060609020301060305130b150f041d010b0a 84
    0x3417020303000c0203c51a100b02420159522444d18100d5000b0240c2014801c0342d403414034664403101144a2400d140c03094026410366802c0c02c04200d015120581100c1d44c403010b50300090144407243d032049005250004000354840e062000000d14440c41e0400f5000c40c03402201c0b40e0300b9a40303500d00c0050032582d003072165442d1031aa4482c00f60442000f0000b510310b00c0c101d030901500e81200d54016500f103450495040b2886a8503445c11300c20b2014032103415884d41030b0302168a1855045880103541c802507041440c1c108140500094540d440307541043c8015440a4200c41031075400f10143c4010308411035003507081540340480010394541c006145001e590b480b900040514980000304030150900800030f0f6040801000714800051130391007032000030074810318016129418444002c0c141c500207084050501c018100d001c011801045e1781c15003084840600039800328084e40820245502010031603030262800103112200310a08103c80303a02c900c6440200031032080c840801c1026101405840101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128412410 1250 128411160 128411189
    0x20909010b13170703060c050a05160c05120a03021b0607020402070c0806010b252004061505041406040b030a050601030b1f0305070e0d020105030a142707 68
    0x20100300310000c000c68807141041e28119a1120843c80c1c0380745072465007024941c0140f42c104180500c1d40b08092032403c840ca0054030701180302000070840c0c0501d218203016640c0c5c020404040201747d001c1200180fa0203054048038042d00e03481d003900c4509403481035026004840900401408cd082e88a4010030000c0c6040c1c24400c2d02d8013480005d400401d81143c014040c1500410a400f0401081e4000d0080d0306000d4cd40340c0725006c4023740400001148490100400400000561090302c0d04025002c01205d1540090412001602070300e0140d11140e0310410414200b40300301ea109004006440030031800b400b42020080034003040d4030440c071403038107000700500101d031140342a50042c43d044401450041004c150040000b4440300300418840c208501d540544d80c0d83c1c980500480780c0c44844c1d401c06a1403490300e1404150340b125551402070401c00004000b072440c0703046511901e58100300c518040d40310301c5c1550421081d000d49030000315010f0702e540416078071500e0000748181918440c101d10583c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128413660 1250 128412410 128412419
    0x1f0612020c07030506040f1709010507060b0a260c03030405011e030e03030a05041112071a070b0a051e0403050d2307030204050a1a04060c0219060e1302090901 70
    0x39002140103a290b4040d030030002000ca8000c210043c029070103011084074400d49031500c0c038006a0500d25251002005200d1070708540e81090135907541d141c22400100e1900b00b2030001407180986508201e03080c0d01071b1648005148100e0038420f1101642000702c03284190030000301a647e0141c0d04c101800140b0686003071040a0040058000100480c1400320b2800b201940c01821900121209601540d50341c0800007400054510500000c130300fa01c50540601541c84043c3e25a01d65008060700402646080341d0611400000c40d08100e800c121054132909054407100f01a10041d00c2003030400d640b0004100011051400640c00b4651645030340d4648255034a000d400f90a0220807404610400314500a5142d02c03000301c00d104894981d00140e4032410320302080307000b2003503400c034204a01713844002c142c10094640844040d01d006007802d808034522840050b491000000b81020038002e6120300082c25a04a54040c203440b40840d002501d00094805d14822030140c95000d640c489402c400400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128414910 1250 128413660 128413697
    0x30f11010c0b10060909200708130303030b04141030050a0203010c02030a05070b100918060509071d0a02040512160b0304050a14010b0301140105030f0106151d10081f06 74
    0x1600c0d51186018032b00307010440388020182d02d199070081e4086919881c1030b0703a8510306481014415801d81c00b00754524107180c459002e83e0006405500264419840d070034103201d426080d00f071500b03c2d140c01030010590b15850002d0303c2d5900010202c0c02582000314600c8902d002106954000c10240c0e101070070131140d501d440860010103004140c00e440c02580201e008035050003422940c100304282c40350201c0241c50020101c0f0001010b5010365005280d06201c081c040c000c070403495015400103929941c41e040c0c070a50091180341d200513800002c1082c14044403101261901d0407100b10b024074980b1940c2c0364a018510301c003c80700107000d80c12070409100056503026a4048225400000013003168480020908407116804030341c0c1c0c07220385000104168074040016103c0c10418074000e001d020300d864102941200c60280b0542803200503c0c8040140703004801e100043c0030005d040d0b0000b01c40d81c0c00082c094000690302c015081e036600006190141c10300e44c036501299016590803008120994420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128416160 1250 128414910 128414917
    0x1060302090306190902040f020304050601080c1507021507030818010203010b041e050411040e06030f0a140a06060902090f0f0616061506020609100501030f11010c0b1006090920 78
    0x40341540d0350174214096111442010505500039900607601d0400d800d0040c070b840816800b60f074159101020200c8140c81c1c418080c0e512051404a040d01c034581c034400605c021010108020341c044001ca029000d043c1e002107214081d502851a403032800302124149401d0348002d002c4d0b46a4500100001c0000d40b002e06411210034454541198046449800040699860003060303c0c80340004201403291a40c013021240d0008000c4004010a407100c03000d0b50b80369450300f0380c0a480072805155210402d202448490b510b1a40140b0030002ca40e207900404009403c00c80c1c07030b5070165400075508202d500700f20340207a1100303800070080c605010307040341608218864008112005900c8006203a0705031120034030740b0003403c0c60f50042c259510b031580f081c030b24112294441c0503205040c03000400c08903010758041c01402d6045540500c9035442140161046003140d04000d0003443d5850401107420340603271034841607852035590043d4696607044c81005442114079003007146010690810225080032006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128417266 1106 128416160 128416201
    0x801091104230d140106090603110409080705010504060603030806030604022404180e120f090105091c0b1603290411070302010b04050a090b181e1501060302090306 72
    0x4040f84600e008400e41d0080e0707a180351003001e2281000441e030ec0f941c0c01200a1066051030303d81000201003a02c001d030f0005040e04007007000c524001c03e0b9903002e075400400403015840c8800403030b04521110301c50426000e20070000040d50409031103400f1240040c0700d9001034114801c1c2003041c184010200d203d00959010004049941c4065040d00c1e443c0c8828600f0715140d00000f0003040030940c152104041085400d100b040400a50741c200e284100a542c1a0058010100006505440900340302d44101404145994808410a2100740f4003070030040c0041103021040c44a419564022141034005035103501d240340183c1018000c5540004000b0010041680f140d16454000740021b0911401c90f801e0182200d91200b0402c00350381c805020780741c24250f40d100c50310f09a076a004110071400308071040c100001000d900904c01e64046000180180c05182e48041c44000205001d100 = true := by decide +kernel

theorem cover : BRFrame.Cov 128237410 128417266 := by
  have h0 := BRFrame.cov_init 128237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128237410 ≤ n) (h2 : n < 128417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
