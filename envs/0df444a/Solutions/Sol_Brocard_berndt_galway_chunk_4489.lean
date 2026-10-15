-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:47:13.887116+00:00
-- url     : https://prove2.me/submissions/af5eeee0-8daf-4ad8-bd39-a1482e4441c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807194244 ≤ n < 807374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807195494 1250 807194244 807194261
    0x402250807140a0206030a1517030417070e0106050d2702120d271703030f0c040b040b0901030207060906020a1d0d240c020309010305090a020102060a050a0207060609 73
    0x400070304001a0b00c0b07100e00e80700c0d8a040400381d041041000040e00300b070360a41c041000700c04441d016003405502c8100100401d4094000071543d40e100160900c543e0240d440080101e1800030300611400341443c101d61001c0707506124100600078003192803200070308560030030034880d8006080d2158100d86090300d40e00429400d001a4020750080301c80b204001004200f181200d0466100c0c036840c81c402c40290b048000c0f140d0641e20781c5881424010a040f5a0b61400c3c01481300ca000003151241003100d110b120a00b40685115055182080200088040705064078100c8880e0010140c07500044401a0701074810f0800091469140003091001c21180e0780c082d140d204000e994003540e00e8001803826048000b61204154842d0400c012840007802c1900c0012032000070041000ba442200005d40e0b09813107144003910056080450350b8099540d0610802e40e000812500400c0c2e441d6158002035141c40c8068003081c511603c07038001038005406601115081c03588400f0030800c3c29aa01096030061030700d00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807196744 1250 807195494 807195503
    0x702030a0f02060f1f05030a05010c090e13060906060806071107050307060c020d061b0203120c0301061211160602040302190e0106051c06030b04111e0402250807 71
    0x4103005500c0074800524548110b48011204d42d4903103400b41e03207007401070f4a483c6030b400d0b104182070b020486440511844ca5038521941c001315000820301700241c4102c0064000807014030120301081001441e46103c2c1d0071140c1c0026002403c4241c9007000300c00b03040650481200703449000c042c01186031b444460350752000b030560159403e49443d2020951980180d20541d0005150200b031140546040e03611006158414400050703410100e0a00d0300441c06102c02000140c0c002150684645041040c1d03664485050222a89150b040c0355000e030040c140741c41c5150388260f903600f06000f10701d50903040301c0b001c0061a00700c075801c1509203032540c081e40c010b0004a001d000d240300c410010300b00c000c8108081ea651840041126030038194100e40ea07400460040e001100e040007130340b408038424416100694001c800b141e00616080c140580c94940f0f002c0e100c0c0c000c40c3d00c0842d03a6020303452003440c000b14940480300542d5a4004284c0049155103d0400c0c20041001241190170041454000d04446215 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807197994 1250 807196744 807196757
    0x50a15080703052a12070507110103050412030e071e060e15120403090518040b06012c010203070210082d0402010c0609060c050a0201180f0b18060702030a 68
    0x1141da044058800036640d59014007014100c00000c3c400d08008005141c1c10070000ba402c0031300c00d41c0c0c2c0f243d039200b01380e8a40c0e01280e0300050305d8090040c00c00340138021100a0074180b1460400e030b03451000c1d00c01100003a03010141e6481e0020101e600074048000113010b1003185095002a00840d8010855a88030750340c08203807064400f94060415585100c1a242e45109181c00e2103015401080c0000e00104100c041001504003c1171950315118440343c1c40b09004e5140815183c1458102d08461021b0107150611602d882e606400c0c0c00d280b443e0450582a030040b001c9012010001030b880c500400c00029841a0720009904081e0b900080c0741d8890b00003810004100c00035500e1450005200d020410150740c10500014050b5009140c008032003032280800188285550b16084100d83c41003201c0f00c0081c0c1d000800314081a4240603c17801d286810100c405000c1312603403600803042c140c4030000d012180807800945e0794860305800b1a0001260000e44a45140c4210000c0d2694001500440400c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807199244 1250 807197994 807198001
    0xd03020d110114010504091b080a022d040e0a062310030c030b2206060527010e0a0e0607030b030d05270301110d201303030513050a1508 60
    0xc140160703500c081e00703c044094140d09103000c1c0400b40504204c1a1910100c014001c9078012001841d0350061082c030700984005c955a10412441030001401c43c1e809180305144018040d01c1d41c11112001034086a001035038040f18010700f03043c28280c80c0c0203411a450f09645e840340b5074101d8601c845081ca50203070412140d6071040f41c06074a500d06d0201408410040009100080c41c8504c0d0541042a551904101041c0d201e820701d580d0070b80300000c0f500c0948500d02000b0900306035102460403030080030441005039408401d114800d805103d00403880581c80080381000200c1da014000403503d040aa03003a81ca032040010b409030090700703841c0340284655028041c41074400c3c1d094441c1840a184281d1100451b000d0900814220003401a0306559480950f9a01c090040040c0303042808003801040d441c1a801803040c0141458200001944040080b10116192000d4100582e90306003401c0da1600345150000300280700700c7e005245c0200340140041080850004400c260a0789562000c5040d035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807200494 1250 807199244 807199277
    0x60405011a03041509080a020d020f0606010c1e0f050618010513062d0c0905033d020d050a0e070602060127060608010f080303060a0515090d03020d 65
    0x19645010101c01c034000307102240c0000d100782040000c00407000801300b0410415107a07170585510250071840540d2081e0903580003550140070340700c20306c095040549028a01100060220641d4500042205641d103014981e560341d80d40809001c15003001d08214134030101e2074055651a01030700c11003161401840310607020207050261a11558818007049240d0000385c0d5400c0140040074000303000c40b510f90000700448580c411a03110395020500000c90009006e61020384100e2168022034001d810801c601202c40448000d0f140c107044d24410010740102a00e86010f401c0190352080031030303e500005203034010b0046a00030034020411503030b007003200900100215541d4000d510840c005a0045401048122003541e100c01081c503240d0150054038082841041c01c480d1a07400c0440400c0d032010042c001444103c9d8540d024000143c000e41c03442c1084030000e0b10084507072084c03600ca00300392188802e0701248501550006800540541950081483c02a40701c102c0c121000001400c0d59200d42d0071030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807201744 1250 807200494 807200519
    0x90909010902010e090402030c100f030605010206040818152d0c070e0a02130e0108060702030307020309060d06030615030b060d0c1403030915071203020c03030a0e19080306040501 79
    0x1154140c5503485000c41100902c41445c400038426a4580901c0c1c50384581c41d1680c0400310000e520a541d91200d41e401a04003408613965a08194115440f080401c00040c007038108540c03000b8541d0380c82030703150490000014013507030034108000d034800c034003160002c62600500b20b805241d17000840c803180107044409903d1014018201c0300340d19035008880410400d20074103050382d001501c410015103002c40c11205058060100c2c8d000542c0e0b03074008001003000501c14020b070780d0001030610146d490f509256000075520300640e0312852007140e0000e04410b040c92680d10000081d580a44180000035580c00304603846070040c0b2040c0d507580c81030030004600d490728400c0c0c1508540d00c14048102c0d0742c10712074451044a100c4d16840d0701840108106082030350341082a088541d406080565106001d250501002804582090525005028203594000b01206903a4000c2c80b00d880082d031100003a500742d01d0700e407018102104d4507100c29006801e000c5808000c622888040c1c60a01c80e0b0b9a0700e4081c0d0010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807202994 1250 807201744 807201761
    0xb030a08072f1807090906030b0412032307050702090f090c040204060c0b0411060c070303140702010e0f132405030a0c06050c070b040e09010f0b0306011a0c100209090901 75
    0x2080b10109281c40d4400d400c03c0c002d42242161400c0a03801c2d0f00d581e000012030b00340347c00c1642e018006008002c10802d030310b9050301c0800302c203140900c000b49002c000c800343d03000d1900c822180f0000070400501013900c60015245441d4000308200b44a09000c15140401601500d50541d0713130040c1c50820b4581c0c14240225800c0b6502541c0d00140c13070805803141c1c040072901520844400c2a09005140e040d6181d034003400c54400640040c281140c84d5140152282e0340421002d803042400384400b8001d42e800c03a003001d6400300261100c9800120040001d0641d2a4200711213480518007a048000d0315056404160780440011101805030388a6003050303581d8003110001085070115050034000507110300050b00d0071600303403000c4804c02c035110301c81024641c12a402c1103110700b6443c000c001e801102402001144181070710b0030004200101c003c13036103a442c14081e0404001d00c00303021448600101b01180c100345002419280d04001c0108400013070352244c4015172040f10000d02140c0d00c1e1506108100c0d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807204244 1250 807202994 807202999
    0xc160e0906250e061206010f09050306070c020402191806090e0106051605030304030309060f020c0d030e0c0a0b04050909030307120c090503030a0305040203010e0705090a0b030a08072f 81
    0x2c05188058411018104411400041101c52500d0340c00300d880c1c44001e092031110780100c5a04d503240000005052101e544e44140802c504000c08020ba52404281e10360428801c0c9445103000c9054004030b0041d03c201c41180d00c0445507021f605080303944c0109415207002c640701c0d0000200c3d584030303400c407030506650096603000e07000e602c01040f00501030401020030a218242c00c10402c85a07888050564004881c141c0109481e11151410418507100340c84d0020345a0310114204810300b0f250540c0c3c1c2c8900903841c0185540d9094854408804029019443c03d000704035800081d242d202c3c1c05840c2d0498800e003400742c02901c0c041040302c4408419244a4843ca0f0b944040c400b030245000c60192240040140078040c8a40003c01c01d91414002030002d2002901d0104060a051050601312200d601e80008a0707000030070300380582e0380c48101642d0006141c0d4000700780e50b205103001a0400a548800a115040001c1e84808225001c88018024260014079210481030520034000d030b0740380c11180e0ba5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807205494 1250 807204244 807204271
    0x1206130c050a090b090106110c19050a03050f01050a020702090c07030302071401150b04051507050f010c18060201140a020d06081b2805060a02030c160e0906 69
    0x480515915000020403400303160040308040d078803800700d01c078481c07160403840f48640c5460600b113060801c954090300610140c68000e0f440910b200b07115441c0c0361001c11040c4501c0380d00d42c82990000c08000b000020700700c014508a212507503840d000c5e03130b81c0c0d0392004031504075420b00c6e0014070000b03882d00c2030f146000c0e00034103a03d00c0c0b5621088002081d0380000e108030300b4142c0c24041c4c00003040c0c525090950b11007044e400000c506a201c0e2060040640c15807003542d20740000c110620030707a144d040794034099010115046840d81107910b00942400c2c0e108142009961030001920300c000e5220301c005141c09031281000041d5030311990203d0076101c111041c2c0740403960010114203c003181e0f50040c9406020807500050700c40e1281c0302581095491055000c00e0380e01c0c003503c4111490a4610074402005881c0400c41c0c01d400c28034404250308441c4605c2d80314040c04200b0060f0b090082c0102e486c0000b56000755980c0c0f9071340d900c42c8002014240100304054040e200050320302540002e185002340400034140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807206744 1250 807205494 807205501
    0x1d0313120b01050108040f060603030309020118061407150f0617010510140d0203010501080706111f150b07030309110612040b060a08061806060a031205030a091509050105061206 78
    0x11768090a01a000b01d54403c00b10810502150662103981e01541c8243d42c0411145a18000100941004c20070404050808101001001c0c2c10250002d11600f807107807201c0d00d0303030010304004100307210800e00020200d082482e0235000314100c0d4403c0b81601c2e4035580905001207045017050032a0b230200e07280b40c9240c13070401c000d2081c803091140701c07481410f0007000d00f01040110343c007081c00e503003081c6d1040006a0100d401400300341d4200d902c01c11410b00301401405141400044901ea4422800c0c00100d1300390761b100d50b91850030600c01d0140244c1000b020155581b005440c0c010020054128142c0d0000e80a2006d06c08524080d8216190a940e08a010201d9116a2600b5001c00700151081d03901845d00c001c0011007607024802e092103130b004180c55000c141c5011000c541040c4001b00454800c003a4290240009900681c00c400c0011140c50b105840781d880c4100400100078428010708884030318014160f0a120070f4000c11409441000244940e407107d506006902c00e0f984840c00c0c01d50080d1000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807207994 1250 807206744 807206747
    0x605040f06030b040b04140a050c0a02210f0a0903030201180503090f0307050301060b1812030301060807030b0d1115031302062d0d0b060703050409020307031d0313120b010501 77
    0x29140900060000030542c02c403000107400c42e110003004450f0507ea0004000c200001c03840740b1540014643c1142e4588000c4030802502c820210591004140c0c03803035021340d0702c042202c0c1034490107030307c403004190b407951080001707007404000d803108400642c03c0a030701d840c4121440034045003159003d4009d5040150440030042d44000d044070307054162090080000d1556400d0050200410385817a0255030303006038000c92a210390310b207540b0078080c80d883d01031110881c000000301d9044035018502500c140e141c0c818110701411500c0300c06907200b0a001c1c0b07e134040c00b1620300c910701c0c13500c002c40304078080c04c1048001038141c1c041161280b00c1024041601c1000d4107040d001032802e000b8941c50318528040580240d00e40d080980042c02a034840482d103801480754a1141c1404024101c5d205400d1000d00e5500030041c3c456805600102600440454609406a0071010800003038403491041c0001c0150020f84c4e0350445225251030703c8241100081144192020142840c1c012000025980c01c1400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807209244 1250 807207994 807208001
    0x61202030a090203032b050714030a09020301060b0301170601080c0f011e0c140f030306060d0b15030709090203010f090e12030c0a080a0221090f250605040f0603 71
    0x124406180c82d4481c010040e9014801000c0610f0000e40e1084101007034404000c40c440089101c4100d03074903080610425a411004020401c1048180ca41e03496403495210009000769040007500341d030070200b0114010f00c080002d541a02e0303048048061086660b2040d079034600084c0b24065894002490750402c034141508062072564040c1402003030125400340c030303510000340c00d0031410015a114003a00d00300000c0001506d07090130906d00038103600d00c01852031030316481702821813442a10001204200b43c40903800c040881d1038001e06602281da0110b89000d20745d84219400b000140440101180e041c501d0720a0741e0503540c182542c1c0005c1402c001109000f0300560314610200d2044484540d002c414407030003075219102501505884030300c500c20150071400060525242c8500501140321349050201c490101c4024214841c0803070746403048030504010040d1102c40d91801035000726a4154010742e0071100c40540c0307500483e20180d684404942900690095071140300f072906041002903c26007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807210494 1250 807209244 807209251
    0x815100c14071a0a020114010303020d0815030f0115050406240e030d020c0a0e010b22090c1d0f06030708061c0605040510150b160f0b10060906120203 66
    0x4048036919915201c2c42e103041e5075000303240c1c1440c3c0c0380090148034032035080c003032030480c0c8640d800129019410740da03029440e80328400c0c03030200300613000b0700040c2e50b16400f1380d90b000c00300400390540304840c0600c4043e5020b00150a400e000440c40c4020010b56070506205403000c4428070154140c0c210380d111651003081c01802844002c000c20301e1000c00b5141d606005444401c0007030b800818031603106206020100419901030704ac074540e034070010844442d030030b0111003024042e88200d910b10410010401e103061025005000c40603d040f2102da00181c0203a200d6290000c00440a1943d01d41c000820044420300c1c41350340c0e0001801d101103000c031409107285a030031010040c810043c0c0b01440c1c040203049055800300340c1d0341a48400078801406402d1041c4554100000b00034090441842c21500d5041400d110354065000006501038828a21031045414a0b50146100b03c4441c21400d1805020009848140108081c108000740d100e01510f20700f4125070894aa04c85100d01c481808402500004c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807211744 1250 807210494 807210533
    0x1080c0301290417031b01050f04020d03020106080d03020706050906070e0d030c21120603020f0d080f0301030c050915010206010905070c0c0312020d02011a09100b07030815100c 78
    0x80c007004c504402c4d01104c4c041c8491424000b59280c00180200d40d00c000040104840c1d00c1e4900801d0140c00c2202c0b0b80c02c0e543c401d40682e020300300a55589412401080c05611202041c0140303201c0e0140d4582c55001040141d008080c01d0080b40c844000c400c2c0c075140243c03a0707140401c121017031428203828804042d110700e50003801c03c07041c2249c00307854211828000c407102d8110681c01120000b403454101130134103104003010b4020082d0360f0943e4003045191051109091168070070750741c40d800b001144012914140c043c02c2840d512540e41e4500110513031030a004140c89030520a0014400281414070808040e0341640244002d91810140300d004010242081d02080b010b4040100412900c84000005511805c13089940c281c991070028201080c3c000d0a00441e4140481c110404650140c00c180d003c074201c6080d40d964690350112480f07201290310039141a900410b6030001e154000c80e42c036200360000158482030a000c1070420407018191610302d40400c0c1000090342c0403d1400c034a0070f603202d50b003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807212994 1250 807211744 807211747
    0x21c030b060d050103050a03170601090e0901180f0210210207030e0d050c0a1502060c032205150609010305100c050c032802011401090207151a01080c030129 69
    0x500b05001c041d600241c0040e103543d03000c0c251f41c404040d0302521812280001711440300141c1443d0000a2000c2c1d180c0c450458400000d2011914144082d4001c0a07002041c607400400b80d11302d40780062031a04810002d904c0b40f40c1c014280c42d075003405080d140c0d1315542e08030390307206038060b14022000007074012680683c204424030013a11101d0311094141c42c01c0c107010300010442d40c8818020040e4090458028480b2004400c440044098001a501d40c00c141809c42087e2642d55609610050402d45403011180f00301c60a103c4080c03203404515100040801c24807021240c0e204002d000d9280828440107210340e02440d8040503a1030194401e1031300340c12602d04286800c40741c2c2a8245150415001148081c440d100221688001c600303103143d1800035400240480c010241c0701c400b807a8014442d90074850f4000441c0c104000d03250740601c40202040e2402c006030f200e6038000c0722110036403584003808290441e0200d00303501c03071035003d607412264589040419442012030400c4965101d91203102103950 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807214244 1250 807212994 807213007
    0x60a1a0d0609140a0b1c06150f03030201050105010203090a030204050601020a200a0e06010c03081003170408010c110c191203260106020c090c12070806040c021c030b06 74
    0xc240140401000c1d54180072555402210f00c0c02400c040181603510424035005003204992108240c0c098140d1910629481c1e5015a007803850240141111000d4075200003100407030005002e18000098902950080245a0f00e030001079a492007800303400d5034800c00da003d0420041c43c0c240c00c503a40c086018416925084000d5645128004031051b800640038030700003000310305040c100c88120080200f880a80664200600042c20808100d82c01404104da0100062000d031198035445008503031104194080d002c4420000c0a1a000750041c6000381d400c28900c0d03500703d0320909204512502c0d0301d01a21a8004950800c14096480080b051803032280d00c1c0c00060050f42c034294403043c2c0d8001e45071003454202d02011001c5081c0440290480e045c0f240005016090740010345032401103050b214021b07141c4078a4616011400303901e05540b90300d091070080001c4580c0c010b030035902440302030741c05200300800480c1c140c0c1c07185039114907a410181202542144240b20360001c2407102006810746c1d18281 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807215494 1250 807214244 807214267
    0x303030e250b2101060f14160b060604031e20031b03120c030403061104150f030207020409051c02030715020304020604080307111512070305040221070e010b03060a1a 73
    0x81d090f400b20000c10284250903100b581c00c140050180130b446c002d03651900309072018040700e41408580c0600300c1009e110024075540c0740c881c111000303903402005a12000000c1500010f0b03044246c10100c401e10b0a0244002c441d150320348945031100c9008010340302d0030a0610a4082200158500a03414880c8119010720f5840c858001c00700c001c07031440615515421424440309030365503824400715079041000200820381c450440e40729155110304e000311141005280c114040e010700d800281d800f41c5020081c0080040c0050510302d0103004040100094817000000e0341c85e40a41e100c00703070500e402d601110600703800c00c3d4001d42c3d1091000313102c24181034a030f1141502c2c540080b5001c442800302c0030b00a40e01443d14408101030200701000321813504201c25181c03020104064804000c0c9600c800c08a821965034200c4012170103c00c91440d1007411401002c656140706500c110b030700140540001243c002407074002ca900c244000303400c1d001c10a2401a1203800000344600c00b10501505021245107036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807216744 1250 807215494 807215557
    0x303070b06030106210c060e03100216060203160818031b15010608010e011a040b070f080a0201060e0a060509010611210306100918021602030303010303030e250b 71
    0x2259150142c1780303410302510b030801c0c40d265541c12000a00c108064142025903000414400c4030021103005a00c80c00184009855908400c1000340307264008410808070019220020401758070313583e607203611515040c0d20a1880f84855031030701001d800410042c0c48030820011500c40d00c040d07001c100e80001600178085c4007280c1d001c0c1c1182000600582c0100080322010903214058944001c801160314810b5000c2d001a104c1d0307205100d240c020204004060186d43c1c800059203603000350340b00359110000c8000074020845030142034a21002c1034041220f0582600c2041c00b40c0c0c0000c0d140c1a5a80d082a40c26201c443c03115161000601c261605084428030409402e1001c05101c4042ca8580c103204042040742c2c00b02c0a494010045c81a004104654800c0003051071110416401070307840d500300c11842d40150390050080e4241c840000000201603041c1e00800c0382c50300b00015289020b4440d10000030700202c010004008942489050000362149801000c500703d607203001c0c1d184852000e81643c440d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807217994 1250 807216744 807216779
    0x703080706060614090a170a120504050a0f0803090402070503130305070f06020d090b03090c030102030423160308031312120e0721020127091107020303070b06030106 73
    0x8030303140c2008000360758001c596505148000340139a404e24400038081a8075115920503507004d1082030b503071511070000038050429420741000c0d4001d0216203401c8050003540c003912a05004071014940060101c0c01c400380b490a03a01d640020390328000039001000080c1d0072880b410348031400708000d00211400403600c0c42004500c120050003000d8500304405000c51b11a62008055401c004005a030301035106298500f501c0f481c02106403a80c681164592600781800041901988004240006d00c031003126214481d4400006440c681002d0328209a2580250305060050241c0850140001f404090140d40d0000180388526602480d0b0345401c40c03145c401c8804c0c40c01144120f6813101003600140a0101c211a146004100307da02e043c5854624450034590003030b01a0b81a258801160311508003540840c0086000d40403401d203036114020354542900c9003041c882d181c4800c0303042c1c1d00c17039a00c1903e504540003005181845007684030544036000090440da4503559818020501d0b2100d58001ea81c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807219244 1250 807217994 807218003
    0x307031e090c0b07080306040e10060815011403150403030915050a05250e0d0602040b0414150703081e0c0a09140a1502032503030b0103050f160207030807 68
    0x41e8141c50741094800032036180c0008141030800c002d00c2c0c0104407030004480c0c0100040d0340002d0718401d5046030504000314150745840181c28060b001a401000003544400d0360768012103004a6681c0d0246803e1861011150540503000071040383d40c2d10100e0400c10350701c24001d040100c0e50904c161341d030741c48420031501e10a08a95941c400c2c4a503070f071507501c616503008040c501c100d000d0a1107900da51802c444913000f42010002403140c0d0907040c2d2108811900250f600100554466881e441400b41c903070420f001e40542480380790110541c41c0303401541940080107801c800303498100503850890b14403170020700b02c0241c44580910031800b6a003028a0078814840740421a880d15440d403401001c00341c842d8411240c4c07016581d1039214580c0e03400e035040704941401c656102e201207581d5050382580501c05550310f001d00b95444289020b41c2220403000500d100f80d400b080400710380d40064040b1001036034246614009000000d1512005800c14070f841e00341030048500d00e40d900c3c1d0360401c013640201e80032030313 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807220494 1250 807219244 807219251
    0xa032a06020a0f0c0209010b0f120f0403110a0c05042406200105151c0519021305093319050108070b07020f150a03091401110f0307031e 60
    0x7103030194030910f03603525010185072611064886400164206c10180540c0d100c0850020309101c038009010115000d0b90036040c4120641d2800514101415a00703d4044d000700303c2102a01030b012401094400c40d4a5104c03174200102418502400f0042141600c08004030b4600b101d2250790244d00c0170580e000300110b981d900c5e095054201001034112240f4103250541c2e040406001e03e0340c0c0003000e00c101088041c1c40242d28818a09101c0c07600b00840a405407080c080c0d0100100d105060404c01e00c40310b8026a40d190b08850810412170498100300c40040080d0043c001f04448581158114001000c003141c88040902d000580c8110500040d00c03040300d422100e42e201d182ca40a140529030050614201602c10145030900d091520300c12000e000f031080440300300364011135071202c46c01107012105036034494807841c3d00e40c40640200365091043e0359202120548044511050007010f00105d10b50800c54184403484030344400542015021506068803040c00724007100405c045e05200303628a40010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807221744 1250 807220494 807220507
    0xe0a150b0a032f030d02121e04120317220311031303020f011e08060301110c34062a03050703030605090c180f0310060602010e0d020a032a0602 63
    0x208020310181102e40e004e5004440c0100300e4076004100d116084034030b0400187d46105801b109450440d80c1d2450842c1480c0104010403041c41e044045c0180500c80e450b101d40d0b54111546034131281c035044a1345c0700c004c01203d591074000f455400704114140d20a04101520040f20901c190a5810080150303007040041c10302002589844105000101d4080c00d104410383c10090703e07001064521140d4605200071a404a1b000746c80035032141c0441034810000d180c0303035110b801c042c54591680307008004c0145c006010400016100e40d0480041954958034600345a01d030280c00d4501d02d0b40c8111840c1c8000ca1f15298655507174601c61180f0100380310340c4d6150750b101c0480c90003038115515a0020350080c0c04c107801300f00c4482c034900304481d004615072006016001044d000030b05c001811000301c64240c05451020b202804094104006a80e180d400900ca00600d4101e0240d40b0245042d4150050307021140f4800801d001e0044070300c0b00741c00201c24240c560800341c0e1401c10014032250480b1059030000701e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807222994 1250 807221744 807221813
    0x20a272d06060519050c010c05030415050708060d030c0204050c0a08070e1302090f2d010c200d140a0b160f12021e0301090e0a150b0a03 60
    0x2400c501061000c01041140c0c10308034000d00d94050807107045000004d540701000f00c1070140055815803880000203000605540d500104560415a01260842425410b00e040f0000d6401954030a814943d50070090743d9800040140382504ca04042c1e040c408030724251005620b031405094483d00c40c0c1a0b019540e40700212008208400c010314900c20400010342281403036491100c100204080003d015858031007170341c00642078103100c0d01c4040d0b00a41c0c81c0501244140d15010310302da403102000b000d610009940c401519503040100d0003c0006c1303d05005801015241413060700b800b18050814040c01150381c4e10382d441c1d010400341480050340619800810407224554440c0d01c08100eaa80e8140602c0c0c0f080060503100810349960207000750001200114941c55040e103000d41d40190b5404812920b0f00c001c80d0855100b8001c1c80141c0381000d8803041c4905000601c68100c0781d00080014408801940f024024a105580c85501c012125000400328264500c034441350b04008907080a081030240d00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807224244 1250 807222994 807223061
    0x60b070b0106260c0306131e0c02010903090e1b0301030605090105060f1003110c010609020702030f0a0206040b0a020c0405090c030c101202130305030703020f1504020a27 75
    0xa070f00b0180b0b2008603c582070346440c1026000107640402c035403280c4401000411081c1507079010300050f40781c1030442062076007507408a4003507280010f0820610660700740490030386407004006404181c0c2c00d542000040c880329070b5150301c11602079400340c50f40c080d0204a00294402c1c1d00c02c0d1919620350341404410b9a00303110b01ca8000000300c8070072039a1244900440c1e21068103103070310024180e440f0b86403843c0f400c48408403408031851030020041a51208440c000075009060143e000340301c2c072080d040070050f000844d80318043d00100024102841d000c87d40c2078941c0406482c104500074940244280d840d135001e9940200c40710005030188802d424141842d01c54900000c500c51501c110307162002039000781c0416480c600e0840b01603510340b481d04c1d60580d035070000d900080080c400051440141680400c4400441c001c84099422042100c164040884020f44019611000360a803c001c1400305c24880381d00c4042c4030b54183c80b1240e50100d143c00300d601c0c55440490401000b00ca03000c01d500300d00c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807225494 1250 807224244 807224267
    0x507030b100e0c04030b070804031119060501090204050607080c010209030307030905090a09240b27101503021c141506120f07110a03030b040614150d060b070b0106 72
    0x883c601c1c1401c2c55912000c803808400b07030401040c48030640100e81418031070300d040080b503403103181283d0381c41d440704004078030710100304009030744a03440c241c000f140f0b00403203000f12070450784000c01e820f0400f2241d2300c400d0180d6100d030310a003c056500300507030203240c0c40c10700140c117030103006c0e40303e040b4000c4c50107043c03210400004142000c010700d88602c001c0050300318807100040f40700000040015a030106200303801000900582d075801040d00900406145e00300c04400c11580c144452214151100369800c1c0a401c1c1d640074200c0c0c8038403404044072802c0d00c40d50141c08400341c0012100e41814000c0042000c641490010038200200c0b1030401c22000c000c903c0c0c080e440c0c503040e659617241241011a01044a0014102c0c1c40d442181a0218070001e03c9040b030103482500c0042036a07400303041c40c0350150040c0407108569000d5420601c000800c140c2d0840c403a1800e1401401604440500100011003a0b1104039840981980c629001c1078480d00300c0c0207458041c2c410b04a58140b03504010700a03080002c0171 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807226744 1250 807225494 807225511
    0x130b03060a0e070804290a02072d0b0a06050415050a0f0f120501111305010e0a050d140111210f010503100b210a0c080f0312040507030b100e 62
    0x100501002c241e025100341e90181c0c110a00940c080f02c28101d625150014201031b0350700308201c3e4184074840d170b510b074020710720f01d03110f030480007101410740d501c4070b5000e10390049010160a0110795813000c1003c40340c40d03035807181c0804c85c001074003516140003138100c0701500c00840c843c9021440030711003070501013038035406400311100c0101002d1600d4401800d04941e0b0144040e5480e00c090414100f24007504031510310000c501d03441d501c1b5406003019400f45c81080c8039440c0001c180203407143c41c40c1400010242911000ba1403c1e10069480d00c0c1c08035511005200c1c1c2e8a01c3d0740e40c61211070003c66a5000d454040ea43c0e06007190201541c00310391030300b0f01001e00780710a1980c107100100310325900001e240c040d61013002000300d0307040548030005088810594500c2c40b0742040c44903030064008085824410315206603941243d041e200e000c2c841c0e40710b6006070360700e10f42c1e0700401640d4910802d200c40c042d481446041182c0d01e05499139a0186800d106840318600d050000b202846590701c20a455507125031034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807227994 1250 807226744 807226769
    0x60a0e031804090203010209030a0b0f070c0f08180a09021b030c0d141201030f2009072f1c1d01050307121d1207050c01050c03130b03060a 61
    0x14402203044210071503080a1140b5500c902034011503c0a4042d925208401000e46280c420a03041c0400b103000211a01d030b4071510250000303240c01c0d01803c020b004464100703401207002d00c01a40c1d641c1c2913174000304051400703959006041c0070f00da940b16801c0016110310100581c8440c410015201c200b08444038625141e0000d2055070342d0548001600101d5100c6442c0c10340200c03a104094061074882c000b9404051110500044107009103804c82002d0075104103030800d20014000d10782000d06804030080c0303510116980210751554420514071600005810541140100303055000c000d18200341c1c448240303a000003990000c0d00c003d0101d019440001420002000980c01320701075400d4015400b03617030602001001288071144a2a21744484070207010b420480f00d083c0440c1340c0d141e00003186080080d84981d11188400000f00d6007a00c2009520000408100b25002d00644003500700d01d0942420344020300000c029400c0c00c0c1800c0e001400410f902d01c0d41c03400e24605001d0070149540001442c40d82 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807229244 1250 807227994 807228007
    0x2030727110910090902070f0311160302060307030216050f120a020a060c0302190c052a0402091507030305010e0f041a060301060b0a02061f120b04050a02040c02060a0e03 75
    0x50749003112011582100d00141da0343e07141005907143c13142a001429003c0c80070806004003c0c01d2407002c0c085d14040d880c1d4a80c500540c030800c659500c1080064260305076a000100010b0030810701460b001007050a01504201421081c1801c1078a04101603447e030744190150541501c041c080c3c01c4640a48030b400c50301d00b20300d00c40041d6a51000220040001d13a6488200c100148071380c2c10b03503c40c88142c2149121945400794018003441c0581d905442900030342581262904030b210200046844003800700d060f80224400f008000e4004025403500300b0800654040145801d07001052803d100e070700c00040c694101b600e00880380c8001806a07080c500080c0a12010030300b42511681d610b1000c02140c21141e5550011a0140509a114050030ac001090140c08150045122882803a41070110311050000300b00c001c01ca441c10384200304c600f026007544000481e1302e8040c116031282c05007048071994600c030b6000ca0101c0b000c0403021801030b000075003480707030300c5445026003249445103400442c18144c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807230494 1250 807229244 807229271
    0x19050103051b0a05120313090b0f0906040f0623010c0c0302091e070e040e0a0206030c030a0902031e0c041406220515010f09080a0311010902030727 65
    0x8041001d580b64074401c046002c107079641d144482c00344c14041c14032080c010241404a9503904054002005030720108004100b0441502c200c07035036800000d0403242d4040c1c02c10180061400080c0816400035154483c0d488400b02c00e001d400000d04030b6403032800144d448503450b034548001c3c080305241001411a008804503044030000d00549804540c103000c5919024183c0010424021f6040c1280c0064010000d81942080c000e40c0f10302c40c1541e080c0001d2032140c103040e4407240501c0b40250320a50038004074811500d45409036030302660712680056078130030f5500044e1070480341c44516507510001803002c0c0c1c0340e07107814412188400c800740c9080c000310036a00307800d26031400000e05840c0510401026410268001c5181005a80070941c04000d40e0030844400541143c99003039aa0115980d14940c10310b2600c107010510403500403801408031209181d4048954800515040c0000d40d00c5091120240e07900780007504c000d0020680e50640a00c484182c5402c00c425410030301c0481385001b81030004403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807231744 1250 807230494 807230503
    0x501020708150411011115010527010b1b030f04140402191427010f0809030a03150e0915090a0c0504050c0c1209032116020a1208031905010305 63
    0x29138400c1c00c41c0c1d0414001d000480307126038031110074a01489114100a00900c612841074180ea10545201d40850000c170004000c24500c101003040402150004201840c2000090002c4103580d0054980d447e2030084040e185800401e400456210005010032214a9820101a440c4000c0d101941807862500c0c480e42e0750705651800c0401d00c00002d12540c3c01c1c1c4941030071181015664000646e8615206080658980d03488031654085652040759035000c0b40521030491051000000461910501003001c8000c2d0150300110041c8211000004c203c0c01e02060030184204c040c000105038142240400a0050b0000303004031040303401c0341448401107062460301c0760540701d05840c042000d4079180381c00c000c1841200d011503a00c1c01404030380f11003104064010040e140781203080310081c1e80400c8072a80303002c90906004041a001300321401c80310764008031441c0f810723000030030105860f0360b40e100982c0d03894ac1c0130702c3c1150005400003c03c4180c0c0400800d00c01d80a040c800c0c00c1000d9810f554956544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807232994 1250 807231744 807231751
    0xf070e0f0103090305041a04030c080309031903051903021909300609050706140a1d030f030c0a2006040e04050712060f0f09030207060f020c04090309050102070815 72
    0x105903c5010030301c1418064001c45d801855490b408407210804a41c140764160000d0008031640603144a0000e106c4c5800425501018001009080150604402d003002c503010444124107010003403000040c00c40d10701800904040f05518050b90702c514004103a00c2d24400407481d482032101002d070500c10f0905281007070003409000c01240c0300050f40c60320444600070101c84000c1801d810b103522902044004240002180c1454451440b210f02000564816000710314000d40000c2c14101700b1f2811102c280d42840350300902a05881000ba840f0401500315485811041129481511101c04001400a4000e40020900c2220042c0540040003a2040c4580e12454288280020100e41401400d0040d44018400d003250400e060440707291500141000000486010385070400700c80755081c45004550301c0552580c068030100c0d0510805551a804c2c801d2014218421030b0700c40202c6803107038450b00086a00039101c0c00f000328a058002854011150401c3d011900013460400100340b03a40340c050742 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807234244 1250 807232994 807232997
    0x3091d10060e030f101407140906030c091008011503050c0405010e15040e041103060403020606090a0209120705031c080601120207240605010e031b04060b120f070e0f01 74
    0x1032600c1000b000902d440c80e0300090508030b000da8076205150380c0442c0e01102011401119400d650f0351190401c4d1919066205c151850100402242401d450b00900855100021191003420300ca181c1d40802c500c00007820802c400b0450301030041c00a00c40455445e14110101d240521151415000c40c0d00300340218803650b07062001503810340704030340c0d2640c458100079040d9803005525103585001c1c000704500162800d50307407030700300074075076025030501190702c138415605030700209000d403501014021010401400c0c5042c5a0b0700744004000d940d1038a04111008907080000c001c514246800c0600309031035426a60440d46608410034002a0482a40c0794090000d080200052020241100180c400c00100400c4c1c0d1824000000000c44600544200b10303e85070010403120341c54a0040d1124014412103d50541c4202c02110010070850001054054080c00100305070b959082c20180a400842403840c6150030b00c020006008581903100391710207014900b10400c50034000c0451915659440c100d0b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807235494 1250 807234244 807234257
    0x6080d020a11010203090303030c0405040b0d030807140f0d0f0e0102032403030f1b1e030d1509110c0c040506060d090c0512010e0c030703081c110703091d1006 70
    0x50b590380c000c2c41543c00c0303103030b0280650799640713484518040f40b6407050103007030302c42c034581009000c89040410004000642c03586800702c1c603840c0e104040d11243c2001034001d91034041000784c061183d01c428098803240c507124001088070b00c400003443d415194800964907032a84103100308421640d80148120b0041242c40c00107107000c0c0340c000460704510800e1010340c050100020001d5884c0085480d030242000b80100f61940d0140c0411b001d5025080040242d51581c4240a20700060040c1d501811f120180c1d00612105d1035542e0046000fa1015104c07a030341408008240051024030510400e040c00e102168100024504500010040e0042203555034446a5407414801009005039111010300702c000c16549903c400c2c44885806410000000d0700c0354024120000101d0800141410940307510080d01c0d0f05103104211124807244404002c98031581c0c171a4031502400041400808502e80290346036003005042500c00c0d07942e21000035000100c10724050402c61044003001c54441582e015107082c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807236744 1250 807235494 807235523
    0x16050c0922080705010204230108090706030b03010b151309090510050603012901090e0f0103170706150905010506031612111215061c110f160606080d020a 68
    0x20b00500911000604642c80003c002c02e58600030344d8074000c101800305644600c0320341071004480b1850300b80c0d00d003609503202c0d02e0b09000b001c0c080c0c0c100814209028000182c02c1c850200020349020f2001040000c40600040041c3c840b40e013403140201a010400b8140140c5069a41d10380c3e4681400c00b8000000d41d581001c00d00b0740e0323020b40180148a844003800f00514054260004420410013801c90202d841c00c1000500d404040c202035100d115541000005680380d52200900204c1013168031680300c400308008030004000e840345031015024294001e40c01414022a90b00b01c54068000c0c0d40700c0c0c081402009603050a05520307040b64952840c0080300e92040500602c09010000203003881d046022445480d0b041d030303a8180d18410382d41c80d940035040c4c00b500e10a000c200e110f220030081b000c80ca807000c0e40720301525a40015030509607a614142c5404005103d554041e006010794040b41d5815000a40c20301285006d13900107001440e010f0706000f421508040c0d41c5000c41c202c000c6c000548020103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807237994 1250 807236744 807236753
    0x3050705190b070b0f1e130c08030c0106030203100513020103150512060a1d0613150e3d11041203122d0213090216050c0922 55
    0x52400809081c902d554039012580b40440e04e2407004c6400b10518918280041c281200e80d01c0120720207600c2d860701008a4680c045d081c0407809440e40180d8110290040019100300100001e001c20065030b0000100b260a500c101030038001c0c50311485103654241400d1207613a00208610b03054066090130009418070003070f02140319a00143c1d21495024210009c030305205507000c40c0240c8501490107040228a1920506107101046046462a95401580003c480311080c1010301220703070088070781e00d051445a00307019042d290050780c2c00700c1a070040c1c8610080c8000003409840d545404005000110f00c9100a11910381100615404081e8640c0040d84d020b8540340200c501a1141180c00030240f4640c0c24064036203d1416002a000c030314004c01000e24010054281c1c05d1445400940300e0b000c50a580d048001c3d4000344043d02c12600882400241103059100418000c041c40040c2540b880040c00d01c0d07400d01d100000c90318003172580403007044520141d00135020100e01c1448002882c0d0300c3c142c00c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807239244 1250 807237994 807238039
    0x30503010608072309010318050307030804151e05070e24090d060221040305070f1b091b05040b0901110709060305070e061c020108060f04060e0609090703050705 71
    0x741409510b001c51403802c00401e40000c0c00e40820a0307d040c031519081184000c411800c82d10061304030b4200303000d030a001a101d0042d054005010740c1c4086c0141002e401c3c001d00b281d0018441c04001a699405501c07040300e140503456121003e4103041c4a8200321402060705400c4041c1e104c245540a94074103840c0c040204246c0314400c1c809000c044d04140145800c1c4000e6205484a18120b0341e240351035200040c142214510071540b640d5000e0800c10340e90b4440c480c440703140344111703180c2190800c0300526106003040480100303400341c80800c07811400503102c0240007182c98100c003040310800041c04048504000c03112018001c4c42c11400b411612102c550903d40303950008d801c402e042450000c180f101c0064544242e076a130351803c8003036031588003c00c66810071100d80c40301c1c4c0c40b000c06841d20156005031800ca83c841009010000010100070004003112000d400c4100911b54044c2805141d08112509940c08410200105402811070301c90783d91361001031040d03504c030300174104c01c0c1c1c1006070740c091 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807240494 1250 807239244 807239267
    0xb0d0905060c182409040e0109051b010f020c10030b1306150e012309130f0606090305071401140a020c0411030c040b091503071d0d03050301060807 65
    0x4261440e0781084004202035612846043c010b0456881d40d800042c98600f590440b1101050400209070071689410541d580281c02d00350750140d034654015600c190280110b4951520982c0a0410710940d0041b80f490b440c00c91050f5410041d65083c1800720030780025051011800407186c0f001c1220184404a0107030241a06075904088541025a544095500601c003030380e031507958225070540644000c45010528842c000e0003d0441c410000c071030405070800d90076800400d000d83d89041c0c1c101010442c400d192140a49585640e1581781e0940d43d9a4851075000d40306525018040b00d2460300da19542e501c40307020308a01139400d003840261580c003800d42ca524060b10070703180d29140c6a00c11340107510b503441200300ca4011824140c003107040307450b410304a0b403183c0c00290016040c182060314120568000040303968102d49881c000324000b142c0b801c080c51040309075581c3c4035001c0714102101c0c544980d9103002203004048038005500020b42000540341500d80b07030b01d4800c4840ea5141400c4402c12141d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807241744 1250 807240494 807240503
    0xa021c0203161b020a060f0207060f050f0a020106031205040519080606011803020d060608060f0105010504090b01090b0415200304030f1104050405060a0e070b0d02030618010b03010501030c0314010b0d09 89
    0x100030025906d174108100c0d1007028000e8003034030740311540e0b48400c0c2c82564680c0d02a90002c2d1042108100c060010390245c901c00b190707440006206a10796481c1405404030f503441c00049400850208020b14100244455089a0300c4c0701d05403480c80c0540c280d649860150802d0305101a03500ca0318500c45854814000441c0c000385040340c841000d04042005094501442010780200c100260649030089041412210b06075242480c161410b50306034003c0c40800840741c1000120000095031400ba54094409080d5070b42000c0c41803615014090f1a0810344140301d80811189000c1599969002c42903600303c035048005a440d103001860030340703054517064060a40c007910341000d000c18000001160351144c81e40041c00c110340c3e25042c80c000d81e212090700c6400c040000410070f500b440c00708e40e0041d5030031280281480205900000406a20340401d80020584110100c01040320b0f40c0d00d4000d024042c016801d080001d440800c00300000c2031014010608144c0300001c1c4044400c44560140d8003440c0c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807242994 1250 807241744 807241759
    0x301150f060e1210050f060f09010e0a06121118040c0306020307090803031602070f0f03060e030906071101030b0a0e04030804050c040612121e0305070e090a021c0203161b02 76
    0x413031181e400149000e0350700c00341840412000072658142400e1225400030010100d04042e841c00b000d4206c5654000c12200c000c5442c3c0e100024240c40f01310084500030b104034051400990580180115411005082c501402c50441400089000030181da03056981104c4096540d0390340200607102c4c8a140d90029075584800004c0100d001c040700903a40180180d50700341c980980e80d0b0607440303000700306d00e018018017040071107420400200300d51b1161080741c0c8000250b9007450b40031400222250080303001a108542e41c17003d034095a690502c100040001c0844a1041341801c000d00001c0c0502c00400080912045101180070700100300304003280300c1c50040040c04415200c200f2003030010300fa0342044078040481034041c1e0f2454029078000c0300314a1040d8000c2503444000c2022006000c001c1d10326001d0015a0040007802c1d121502c18901c82d00d8290b5000d40d484a134003210305090750800c850405054410320901010b918103200c0340c0c00b85000c901e070034009062505996132070b000204100130b40c4802c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807244244 1250 807242994 807243013
    0x120c081b0d200c0c030f1f180506011a1e070303061802070b0c0c0307231204140a0e0105010e0402160303060e070302030412140d05070e0301150f060e12 67
    0x40c504010a4101d00f40d80a40341020000e8040c90790b1035240f611a07081301c0d0440c0708041440ca924102e44a8078038020003021814030300314107a601480c0c48000d0260b480d0740284006104291030004c1a015805400099078540825401031303202421070644582d0318140001a4001454841e80080c0f01034055031b1030030440c8560001c41c60000b94400c001c225100752100740064100001c540c181c03109030f41403c01440c03400616540b50f629075149820f54002107a810000c400c40c841c401c1100440036859508100c0d42e603420507194907035103c50a0684e522800b07100c18180b04550032240074034112282800c050410b01c801c1800180a402050020078103a41840815070034181c2c141c111000300c50566410040e20345404500300c06074841202c0143c5602d03807c136180b00d6403910442d1840e0002101d01d40713281c1401c2210128030141e65003548d08800103205809410130b146021702c01d021a4070541400118607901c3c00104042c081d0941c4141028449002c0c04908a900c84012440c0d2008004007503513465130 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807245494 1250 807244244 807244301
    0x71206090c02010c020102070f080f071202150115140c030c03191b1a06060706020d0e07120c14040b1504230603150a090903120c081b0d 60
    0x1081d940800560130100d1074092980103208540c4401d8025076415034420035034440011760390201030a1140c024041041401241e09003107544080b24080d409403001000710801c41c2442101a0440c020040002c1001a01c042e040032160b201000d1300d040c4961035004088900d4294040e00707042609074040064104564054105030448042080d100c07a010b0209a142c3c041c1510820403008050741030f41c00071901d2032101c0080b02c56021100412152030144a6034842d8103036081020303260119030319058991610041480000054402d07000e82c0c0300025200e4aa8000039032a038031514070540c0341214504041d846507007000503042c070041c003e03884943c03c40b4014071807984144120320382e200000c04030000c60601c0d400d0b0a0041c8100600d05c40c04d503190101c81c2c640d403400c022600c9600040d43c1074001071a025074010260240d0180c0c86004015902002180940e102a0070560400c9a0401000320306c0341d407068407a4180f59041186521901c2c00150a40100411105842652103000e00810741c40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807246744 1250 807245494 807245501
    0x6011d0111161d0a0506100503090a02060c0a0201080c090607110d02030d120501050a03020609042a020703110906011b030c050717010e0138040c020307120906020a06020307120609 79
    0x4840a1060340c02c2d984c0e82c1c076591040750fa080d200b1030350101c5020200c64110744583d000c0d503009001c507401e842e0301610319800034105600018090006800c210001c50943d0782004080754440d214075101881c02000d80c00140f49445401d200520034028056404015102c0d01c5039605200e41c050202ca45914035208060171041101c0032803510355040134008643e500781410258202c0b54007501e52403d144014040001400c0f80200b08181c0c0d100c1a5071000030b42200044c90740380d083c1c40e900a40b0082d400c41c20441a03071003656201c07a008000030818880281d9000320019411074035454040031440007071030b08941d5540d9551026009226400d004038101c0000d040e0100c0252145c00200032030000000304500381c41000d101d00000d204000141c8445400c2201d034448090300c400300c0b168403201040c00240c101c03000c03880340c1c0d0010f900100f040030400a001d241c500d03601416007040344585240c49402941d03004100b500502854000c804542c841c0d026231880506500340342c2050000344c0d01c0d0101c50004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807247994 1250 807246744 807246779
    0x120306100c021825171f0e1b04031e03110a1109011d0601030e1005040c05040b0306040503030a0b0a17060406060f0f090b030a021306080606011d011116 67
    0x107070f80e0440c2c0c4000d518694000f00040040e010786601c070030342800141d2017006010003440fa0700100c0c032508070118100408591040034120803100001981803014180c0a0701d84030b031091081c281020001030020403104000c0000d00541081500103a540c036280480b1030480110303001e1401d100d855030200c2041a507d00900344000c0507603078084680e07030320b405540c00030301920325004e10070800c5804505107502c26004030860030120300403070b0021215406880200c400445040d160b5101c2140d0a005c5868140540c402c1140b044000f0029418280c5901e03403284009000c240c10a9500d50014070036842e2400000c0003840f40031072038260407440345855a1102411a401c40340545010030100d48080d4807000d80042d19003c24407459a6030625010708001d103100400190301d1311490402100583d280c46510141148100c001706507546403014007441c210000e400c05050000074510010a50980900d0703070148102403820800b18048080c1075400c00903201c8101c040c000c200c46c00031a181c034a85410030035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807249244 1250 807247994 807248011
    0x120c030d03020712030b062a0f01060612020d230a0b031902092509180513030c0609020306151c120807031506120e120306100c0218 58
    0x509039100320003203080344509000203040440600c1d00000311031081d4080a600500034040038038102c500080030030081144001c992040e54684400b001c2400140606110b104180b402400914200000900f03030000d00040b0f01c99503517000c03031400c285d28a02d4003c942404403c500300c200710015403448100004c8200d8100c030350642044038041c07407414005090b580b03c0501204088031160390354200032070218080c3c03841ca20111040703c3d14244100350321106c104c00071242c840c100c259181c9044034003080d1450564008141ca03027420451107103100081d0880c15a4135181100c5500c0f164501a0000c00c115280a034040c0319860030403801000345405070310320740411903440505100000c0c2034607031000032840040070305c0b1840c010f0780c03901c1c1c0c0265089904009242808600007081e090040b050b8803160b40032400040903216500c00c01046446440360f000c2003000500024900800150101c2c40050720040c010740800d13289504480c03043c082010780c10b0b4000c0902e02070f40189200c460400c00c058642c5207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807250494 1250 807249244 807249253
    0x3050403050c0a2304090206130305060907061e0c05060108010606030b030f0d030203040c030f0309030b07030e0c01050c0f0615030f06010e0c0706140907180c17040c0302120c03 78
    0x3250b5180088816044601004041d401650740c1d02c500c50360400c1210340c1e0340d0040d844072154401a03941ca0090f100c106100805041c510717245003021450b01c1c0000c0d1000025811501d028810740340d1281d203a0740381c03204050007140110041d200c01c03141c138030f114a009030503402000008584980190405001c40c0c2107541c0074048803406004250b144c0031003c15414084d80310124408902e806500599800b9007c0d00705500f11513a2625500e00780400c1860440008594843c280104822860300d107411807000d00d402c200c40a00c28060700e554121082d1154103202e00800c000c0f440e10010070a65260080103000c0e20132a040500c080545e031001803006502c00d0045510b18a4110700000e4001d040303540d0910700c14915260703404158590742c0030903000c1d9a50750302c41c1031041001d44d2080005000d02c25020050861600c0d04101d082240c01800c10700310f038242041c0807641d141e1b500421488080720032034002d28094503685001002540c4650000750000c80725001410f24801c04140841d20003029001e84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807251744 1250 807250494 807250513
    0x8010501180602030301030b0711030d05042022020f0a02010b0f060c0d080c0409060b0304060c1427090405030a0e0f130207051509010906180804170304120305040305 73
    0x402204203000b51401a4414030041010a210900040d081504c5007842d101034000121800c0c195803095419440d26a210740c180310800006209440051100300b460703205280994000a03014500e482c3c56408600807038040307800400756941140c11590040c1d804d20790304c401552010340a040c940079a14130988207000d00c1e00860419000300d403140c078281c0001e080b41c0070002500781e405000140810350600320030320001c42c0c414240d100d5400030300090300000d5100d04d0326141040239900c180b080c0000b0048803402d103040000b44407054a16400d07002841c040d03030008c2d0703038015061000a6551254840702c13443c280002d00c10040005c1c441141e15540d200410a03801e41841130004500b85280d0300580001c0d48058400915400780200d5403060003503a20300c0524051101074184181c0c0d00b14020396640701400f04000ca41e10401d12000d900e504010b0700040d05480f8a1114007452003410501d01c0344600008000a0500c22a0054040141101040181414010015085400201c80714800c0d00c964 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807252994 1250 807251744 807251777
    0x10e070501020c15090d050703050706080a0b03070f06050c160b0715020c060a1e15050a0f0806061207080a0c030308181b040f0f050604051303091401090801020a08010501 75
    0x900c0300c8a20001304c85494482c030901446031061640700191507134000c103200403000640900c056801450150344414044c00d00e1920740085940241d9200d11990100804026080103c3c0114048800500301103444500b03031500e00b070601c0c00d845600500c0389845007006ca5440702290242043d180a41e000500e82500b540007c001ca204001003119164000320002d41211119005002a921200c14504034580444840801d540e03035144014184c00c417184092110382854004a402049428403240000d468000da031610b0741c8000e8003079409490145601d04d5443d000300942d000030301170300d02118229407107410a0a80ea401c540012000507030780c0c00c0800c48495101d40c9000000810b68060718038860702995450200b002e0401080d0042e4441c03103d0000b002080c40703182e50444000740701251518201e000c00c81103d81c0100710b0004c1c1c80002ca0a00082540590780c44140d036080e1140c03c01c00424500144c8a5842c6644074290325800010410280c552200703c660403140700381c84070900000010407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807254244 1250 807252994 807253009
    0xc01020703050a020907120e010b040c14032202100f080106090513051005101d040908070b090a02040c0e0a0b0a020a0809060f070503040e07081005130e010e070501020c 74
    0x98803d41c0042c5141d000b500d849603074140c02c62842d0821000c0780c443c9515850039a01440000a45039641c0d08410a0358242402107500c0783d40c02e490b184494a000c01c1c40c0180074000940411020791070620101c028100c030440c85d04440d07400500004107200c050600500c0e0354a44501c0100046005d000082c0c841e000e04000001d5840040c1000240766084160600a06004004030092590303c0300009180e1940107400c0c52149456031800418203c2c1a02c82e040c1e11014003010340030380c0c035120000b00459082030694029603404001d0400d0358542c40b0708145003414208001e94001d1500300a410311035005203030f40440c82d10070340d01c4035160359541e00c10750040c0c002c103140600560000038104000844900c002e2076940030040005092815a0820440b00d4000d650221126440041d0038040d03a80c810400603400440f61808013802d14102218080d20700c031070310039140a120800300c1c0a83d1a03045070403444495a064000f000110710611700c03507036113600038481d032405805810b45941480c06c0144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807255494 1250 807254244 807254249
    0x30f1309060e010b030a0f0617030c010e0c0904030f09081e0f0703020102100903180b1c06050f10050d0515010e04022106061314010806040e0706050f040f090e0c010207 74
    0x240071070455803050000e46c050002c14080c002950707610304010415002c07103211030301c072000c01000454590001c0280d1508642d642800510598440070a905c0103607500240d090f803096042c581190031a100100584503401280c2144400d80159080005e9801110700003401a103408030440b08003a504541d10750b150003242c00083d0060704201d102014070741058004010070380c42441c003d00c16001542100c80c03244071903000300b004140e0000c0e8410b40890145c004005e06090b40380100901880d0200007201400c0240c21303540120541c02e07070102140c0c080d00c04c2e42e404240a00c1c0500003890075110961408000108182c081840c800080c541801c2c07500c2555011030f00c0c1d1300803005628100340d01d440e5002c402801e1680c020303001c010a00d064000614450002e090b5580203400361111034002415403a0020041c600451910510b0f000c01100001d5501c101c83c4907080c03003681c582101a0700c0c022442560046203c242d0204000528050a0391200300683c0340d07601a40c10406d089401241c841c0d50342e2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807256744 1250 807255494 807255509
    0x20c01022a0c0f06130305030702190609090c090510110d031103010e090724031a22020d0c02061005041806180606060f0e01090803040e0405030f1309060e01 69
    0x10b0701e020041c0d0400940303402c101ca2008040c1c5007800c007102c46012643e45070703801c2207965810115416046052910501d94050b4407802d0003100c4c03e04000000b4400f018a20422191640350484c24907142d0241c0c4030f15018000241c4651503201d03114002400103081e01841368861710a03901074002c0c0c0c41c46440b54045100c404c0108a141d81d1801c41c441c0c10081c0050301c40021030051001c002544882d80b000364645400d000040072907107407040700c06812248540b038450450091105c000b082036503040c0c1c3c5140710034180c40921014000300c1c442e00300203004810b880d8054510303041c0700c0000d294001820600c81d082c14046c180d8100e1b110803d100540302e0741449103807501c01001c0500c00042c2160059200642103420301c40c80c1c60400c1d211901a50142da0041000c40d00007560700c000da6a000e59070592419003030a00c1c12400e0b00d404178544e640d105512030710764007002c0140410700300034090080f134900d4500d00e012240c981d003d122959081886520449540900e441c3c4005000b800703040380c01e8101d401c42d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807257994 1250 807256744 807256753
    0xf160e010b030705070611122a04180f140f01030b010603020f090d05071502070806090a02060f1e07080904050f0723160605010807140607030e04180624050a0b0a02070801020c01022a 80
    0x4082f04000507100355444c3c021440c0d182c0c666211660401e582c040d1203250344035000029540f55003841b05034a0303010f80001c802c060041006085070003c0000300c80707549030b0070303240c00c06401007906146003048480d401818850365910b81807407080d40d00207102001d8440800980303840c1d458100045554a203041e0009420000c14000700d59548400009416690b2070f402c07000d94002ca0900141c10349511401d4102c4110102180c90030881c04c0901c943c9a0100b840c1a9100f4242491103004e849141415940701281300c40c01c0c50040b00342e01d800c003a41c0500c0903100551041168915001000d0042401204241c0c0304200d40007458010140740414040406052240b4003210364400300c400102c4e141070b16801684078016000d845078030000484c4010300840000400c2040e0722401c510032402e40d5140704070068030040a01007640c603100f0810450711640c48860b83c51081c80c40c01d074240050303a030080c091035202240c0003146240640060020051b800c042c901c0025400c5424140b03181100c9800340325901 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807259244 1250 807257994 807258029
    0x20c12070b0a0908060405010204030b07030b0a0306180501050f060405091501150e13090308130c2904060e01140a0f030e0f160e010b030705070611122a04 68
    0x70000305010403aa1801031a02515420990300d08601070782c040301d041c1e5000500b001840901381e00740760031460b030389410f0241000280c0003c1040846020240403240d4400202a241e00d4080d410181c503684a8020700032440d21080c440c101100480700c4034003860a04000032003008000c5103d0041c00000c10b982006a400c0181011040d0305c0c5000500a2185061001c540b81d030341c216094084072061038000c60ba400302450000c040b21000b425040c48090317207550280019054900b801c00b0344003403880c200984003144500c40d0007940030052180851134000790214000350310a82500b1280c40a8941d0b854108054200903407e105a100f0308000806448101c1c9000317100340c220b0810b030342e1050226400c4460f42403c4605106040400405641c00e500d0204107107505c2198190040c204413003418114070b00064041c1a51041d00801403503190388408c00d403048400c400a0b59480104490707060306030714080750000b4060b00305900840c8000740340b2919401e074001070740864059030704502d00c4808444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807260494 1250 807259244 807259259
    0xb06040c02061b0724090c0b03060a05040509010f02040f060801081f1e110d050606074b03170403090614070b1501140a08151207090c020c1207 63
    0x1040307804212040e0085640111040101c81030320b0f02ca14441c045c001078210f03c580f5041e00300c050140d111640d03003101401004241d42e0780c0350500c0d04690003568045029558004080d00510303400d80400c0749144041030100340742000b440141c041c1e03021500d42e404680d80742c0360925610038400e0070860000a10b503448850030300c9550020300d4882050310011071568044000b51042e18859400f050012001140142180845001d050f802c07490940e40140b600200d0784803558900c144110404480d450520200200c900540801d000d06038040f01c0c2c4080c801008007022038800e124102030300018200e50060170050514005980a40d525480f0748d103207140382c003c0a80c0c04290b41d01d01040921802c0c000c0501080d4650030380f034443c0c640c95014107140a08000058000c1840700190340d0355513030903c81c00700c5494115880704d801030048200440d201c00c1d0302000440d50918038a01e4862405400c40014000007560400b800c00003880d000d507210720440e5000c0c0001c1d21141e0403030103071580c003280c000c02c83d08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807261744 1250 807260494 807260497
    0x1203010b030c0c0f0f0c0f0901080a030e06070c080a030f1d010e0402250507080f0d0e0a0b0a0207060e0612010b030601170403081e070c030f030b0d0b06040c02061b 72
    0x44460310103132203003208002991070800c41d030049160019081a80f440c6840c0c90950728120703a1010455203605594100020a544c400e0403910040a21500f442c104000e507480d0010f4a2600d5401142d454080c5d40301c01440742c507054040701c100c0200304400b4449207201d028017502d078424801c24000e8810031401c6401101c000c00c03000840780c0c219030708001ca0151405040e41d440080c3e8a08c10742e02251030740300c1c5070162500340c8951201c0c2a50b002644103080100f00030441000a020300e1500001d8171441000003903c03c00c0c20340c032404d500e94002900e18007103038010407900222103050b00d46440451441040c801071b44a000391300031807240c015006226080350400510342020061414820744080e03108082100241501d0a40201d184801000f183c0800d60030700140036111070009400d94100b8000c0506401204040102440040ca0070964441d110b64440c0d031921800500200d030f11003981c20021304000055603040c0c0100e081003a040d012500010340c0d5409003144c551031980d040402d030150b2555 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807262994 1250 807261744 807261757
    0x5130c0504091404050f0c1309020303160b0a0501051005040504090809040e0303091c090e09012a020717060118020d0606080a1521140f0c01021203010b030c 69
    0x24808103000100b00740119101d0000340001c0600f11840900b02420060321381440380301c2041195005040c100c000d600d588400c6072184584030300100d0031480350f2002a042d40650030f100b400c2048900118020f0110802d0240c4c01100003020420050342c0350070a0200507401442c1400104030100010081400d195008054041c040c100090030002e81000040079213499140034405a4808824050890018401682400902800e9801c00c0c101500058418491807103854030070354680b400076080c0c050a410024400b202e0741050002040c02d0301c07101c1e0000c044450140c00600c5408408521030088407051244d0100100090069a01c1d10190284039030020034426002e5800b403018420000960049601400f85a19549024581003004804444035214085200c0300c03540e40c100541c441c4400c2480607804201c072903036001c0482c0c0c106940580511000000c0d94852607090703c08030040030601d807030f0142c026401d17140010540f5401110a000a020350880403000700040f6119a41130b00040c6070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807264244 1250 807262994 807262997
    0x14090d050102121e060a030609021c031d0d1505090f1603140312160c0f050703210e040218030604030903050d02010c0e040911060d060f0f05130c 64
    0x101004156191030980c1c0026020480d60b201c1442401303400c0e580341140c461810425022159685460800200c03642a584005852107545034071140035500c401c5646200b07980419042485814103280c02007a84820401056099031a044000340c680b6200415078000d6800c0a450807101d5442c4055034000d107000740030142c603031003401c505816a0000307006111b503454144035500c58182c5981056a01e044011100c041d06d5081001182d030940d50040340582c01c000712400c00c00c4a0401240165414100d48030090080241e0f0b840d40d80c01c1000001e80d0005682c0b1400030b02560059a00304400348032003110b074000c081703180d8555100c0c03141829800b80055060742c841103e078004048010030f00300f51003950182e0015013400e83c144140a41045880d842400701c1c0300800480c0038104004041701240000140702d240c507071003c14140440042001c0410400410780d0f90788440c080f074200e00812884c42400ca0885c1c290a0000d0a60800c0c60a03034100c54000d07041c02d103c000440c4000000b001740305600030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807265494 1250 807264244 807264259
    0x40c05070b01060207090c030c020303070e0a09020f03060f030715210c081503193807081f1e080f0102070c0b033310030b01031406011409 61
    0x10301003016100114000e01107600a004294106480101902d1520425006140c10052083c07400e9038000126a80080c1500d403a41c4413500150018040f9002d940c8070146450001c5080600c140c406002140240011210f48881898030300915890340000e2203065103020710b03a45000074080c003d07542104210795000712440e052210000c041c1c212030415841030700141e18103081248142c176074800e11981c03e5049005200314100c0f600da18894402e038042c002c100d03d00c005464001f409900d041c41c403131002d08a0a0591414030403014446101c1d0131504000090421004240390342d0303640100070754000100c02d0000d0001d041201404108440001c2040c8001c1d007030900141080040c030400030800c02c68400907a954047e0305164580490340d400007243d1500c00c2003400b4003103219019101c0291b442000758914500d400c000701c4500c0410300700442d00b051101c0c51004800e9490b40c05030a00342001d880c200440c0000c034072641c400e680704468136408203824405c0304100700200c2010b440d201c0340050061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807266744 1250 807265494 807265507
    0xf050111010b0a06031a1509131104031a010e0402030c0909030c0109050f10050907091107050a060219020f0c1905031507031103040f080a050d050f01080d0e01020309040c05 76
    0x484000c501e60140000a99071541b5400c004040481d035030701680c003125114850041058140050300c180060341e44294240e4019036119451600001100b5100711405030300c550381d03030078511f42c0818000880c004001c514070003c00e001150154040c09950090002c00b0203018a20502012400151922545e40301c140400101c07038209010303030202c03940700f400600601003038541c845107003607006488107443c141483d042210148001035203604542100c000400c901c0c90b042c030b4003070311841903034070180c13050203211015401d10501e03400a0141c020b030142100c552091403081203894000407581010160460640825207141c100d841601040e0500705c0fa07200d0315680d5001034944584d00c0305180040c03030680300300f15690343c0510405030300e10308c0d000505143d45440d40d1000c61052030880014601400850b03402860b91080b0300391000d208015900f08924140044004008102480303000080d04ca1040f07900c40051145c0d01c015200001a0001d500701358180c82084081e000c4084040104601072105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807267994 1250 807266744 807266749
    0xb07090302120c010e01050903060c03060114042702031e09190b0402090f0f19021611030705040213030807020f0d0305121308030106301a0a0f050111010b 68
    0x319282c1c0340750b500040c01d00250440001d40071010900b48103061001c2408003d810342c03400301d42c20b5800f50740e00400507a6a9a4500141c8404186454140040e8404100407401443d00b180c02c0080800d00311a44e8054a0030026243c107074807084803140191074103084221541c481d103608154000c00d0b20030559107028040080e8910440e500034068802d403109030305110035410008611a0001065035041480d460003c0402d080004060011030b48a01c0c0a051601444201ea0503110302100c03c491404490300305007014004500000710b990700c00d000d0220002030341d103058400c6071070203268a140501168919150740401d070300451000d903003200726040302100303c1c1d84100e07605110902c039480700d980b2580030750803001d10b88100034103800001b41401c0e035600c007140420040c0c2c0e04550042c0f421981c903841491007182e43c950904c10b0000e43c1d4000b80d001c101060b0030b0707070072030000c40c0c0043da000042c4460902c10080b10200f240b140041c905207074003050040d544980078403040120400c0000c106091224003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807269244 1250 807267994 807268009
    0xd3201020a0e0a080703080a050c010e01050f0402040e0c090a02090103020c0111210c0708070303092f010e280308070c150e2b0503040b0c0105060102190b07090302 72
    0x80c041d0010320700d02400c0000c1d00c0c0c02c00b00940a44a108024142c0c0b070704550752158039105d801c2c8604140036010030b00e0040c1c420250008681c010490000780301508048084040d00001505e04a108a090000e2100203000c0054443d24440004240c7c0c40b07651034090941c2c00a500c0300b40303106c0c1055001c00c028544c49070b090160305c20070100b40c04201e80e10007243d01c1c22a10100c1003015608038a0407081400b01000e101019543c65581100340150380e400c0503d8240c000f003a81b003030000c16280e012007c612091040c0ca5800d60707a0580d003072501b0084580040116907295031403604aa0040b2040040c0b04030007103030007108544c0c16681c1c2020681c3c9032640c5170782c00f440d001000304803400b154840c02071040042d0121b0840040c00b10742018005480d6103000036036404000464a019030301c0e030262070040b800c000c42400c942103401509031f958840e11760440c20010341c40846003012542c01c00d4042481c0d0b5100054010b0f0031060014000c0c0001519a54004201c40c0030f000c49007005116180072025030388040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807270494 1250 807269244 807269257
    0x1005010509180903040821390c030706030b0d14030c060c130914040b04030e060a0201061e0518060d06020a0201023f04060f05090d020c0d320102 64
    0x500550326180b0b0710340e9007071030660700424841e0f800401505c0d070420340700302c40b06230341407403c02034000e8400060441c0305500c07440c80500301201b0405859000320000c080898241e4189406605807084507481d641c059041d501c0c4804030640141d400c40c900c0020a07000c08420b4140b140c01070550b450050347d0703003000e4036000b01614280f040c0040000d400c80100c160f14040710041070a0349003031004040030391502d05990390040002e4000a405800a000c141c0b2520151010000c0141103644401d40450024020803150081c10b500b902039046440e10180312b00f9510044403c01440360000e194284c5880c000620098001078102c03604024010004e54640058a0902030b60741c00103072550b90349012180081c2131081c90059038000c0410b084002900784204424140225001e010603856078a001d070028441b04070703502c40440c40d18050005050000c1656010b200d46070742151810070b10a400c0202d0801c0d81d40300280507030160b5074003010180881a41e03408850059488101080010040350709aa1010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807271744 1250 807270494 807270511
    0x3020301050709230d120c12120506040209060712140316030c08040c09110405060f070c1403060604182a12020f010509120a150b01020105100501050918 67
    0x1400103111040e040c1c0b08000003034030034031112242044e61030046402c0521084000d802c1072820004290111b01408244c07802540c40f001101c107141050710010140c400035030f10b200c8850308040100c0c44615180c02918000b000c0105074600c1c00300395648161407848081d503003406009598880c0c0c0e400010080c0a94407407130740300158044910b01044002c00303e60b030311765242003401010070501c8086100c00040d04c064507000400010f0740708281d59a0000d80c084c0f03a01043d8060000136003213040301242000b811115201e40596846907407110108855060721604244c0c042d4085030009225190542003d04491440804c44222260a07101c60754042d01c224020010783c00c5c41c1c010041c581552490010040065071146402d01400383d001030702c03606040c3c066a0400078007003585021641d4034146c18805c01600c00c1100c03502c1d04145000110020500c40c0345580ba40f602a4400655006008140c860090807482c1400310341448010348103508981c11083d00010f140c03080d010400c001184450144104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807272994 1250 807271744 807271757
    0x80105280905120a0909020705071502030a081b1b0c030c1c08030a0b03030c010606140702030307060903050f041e0501030c05040e13021807030b1c0605040c030203010507 75
    0x88603410804110101450261203141c4084480803407008102c1d00c5a0080c40010195151100401260002c0564220040d21440000c0d0a01000740c009180c40403180c01200d404804c142010f000e903224060000d014021550300d078002010440301901440c040c6a00c40e18081c140440307020b01c40701745200760000c00126404244042001c1c9000c01c80c15034400b0b000c50301e03901e04282210b5808888102000c0081801c0d0000c4040340742504c642d000592043c2014084035155000e540040d80640254443c0c8004240d8011201031099003c0b800ca03038036290068001e43c500159951140018103660700198204074013406200b4034264440010001002801ca55680d10700c10b042c03202c8075400b0241d1016052501e0100e0b020141070b08003064a084420800e011001580d801503c82944000721030020340c03080d0355041007c07400c503100385c1040c02000300d65400c1280c10481004e00c50907880d0040070f52404c0720381303404060015000b43c100a41c802d1042000049140e902ea01080c25513405682c00000302d10b5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807274244 1250 807272994 807273031
    0x150e0607121115011211030c030d02030a0e030105010308070f05250e0a0b1008070c06050709140d03051e0d0f02070b0a0203131401020c0d0809010f0e0d1107080105 72
    0x400300000100600d03c14000c020315450000800108454442c000701001a1424440ca00c1e50f000c0c400e0098562001d0242d46111941000080d103e40c00091a0f0000c01c2c4454480c104e603081c140300d003906899201583c5890700110f0340f00c0b0b01640500c000b0840f024400c0b58124841e402c4a9240014000058981c1880341401c10400c26046100200801006440c0515041181d174a11400e03500f0380c0714a0038904e00f25262004d040300c9441c0c003400003810361424441401035440d07000c1d424a003290303a82d040100628070903608124441e600c2841c060001041404440c414003c6098640d05144105890300c1c03406190101c0b178000d0714200741c00d20303001c154081401c1040c449a016240d90106e8400300440c61443c2c41c0c522403a14192100c8050038460460300041c2d04031000754101c5040c010900101c440d00e50482c00c00802c809000c0f95510090350078a80c1000d008481401380100400c0f107603024040c102c1c190380c001c950f02c58000e900c07800d1600c1a610006034440080c421a800389203c017228412582 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807275494 1250 807274244 807274277
    0x6091e0507210f0f020a0905090c010e090f0106080718080d0f0c0b0c0f28020d2303220602121608060d060e0d080405070f150e060712 59
    0x480c2030407080881140b100b04240040c0400240050b80c82c0d0109242d64000c0c21400401c00401c4039400ca541010f20701003d101c0c214800143d400c5144100b641c494846004210030f002070700c0c0040d18030107008142400144201801081880c1d40100f0714544081070342100d001c1241e1021180e030102c0c40907089844140d25681c0c0c8280c1407010350b04c1906041d40215181d542c1c0d210f0400317005002c440c00c50320218102844002c0c09044401008040c0d00070603000811915212000a08413688805072003100116800c250003840541d0b8400302c422002900521000a6050700e944001d06d403480d64441c031214400003520040101c0000d034024000141c607840310440101e2103c0700901180c0340202d000c3c04006880e03070300041d400e40c4a40141d0308404111228580200036000311130350b40d1a1030048090b80070ba019440400d8902c0b4a0280c011200413594410030308100f481107014001c7c1881e0302d54003103020140035400001e4050009480245840e020f91120500203207100311150004404c1904c1500c8103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807276744 1250 807275494 807275519
    0x90102030313261e030105060429030a0f0e010b1e0a080a03090f060504050916030905071202041a1f1101020409050106030c1805010e0f04020d021312050a06091e0507 73
    0x3c401980d082c4c1d16550405000403a18040c070312582a450f2041c00ca41c591300b060902150400d01c000c82803440c4c481c1010400c07a0007900140c1c8422a8503458015440110b00341400f90102c4074102403c1c04044a481c558910040c0d100000066041041000300145061301000030b149401d00958415540b6400c1422071008032460f80e010104001c800c0c80144419500c02d0040f94204008881080780061001b82c00c0c2c0c061702c0400300c064240d00502c4070014402c0903401203c620f55200300c80402440d406114074628800540300986d4000e200101424450000300564030900300c150b061200c44424500c0a080c01e80c1d2164211001c55901c9000408c0001e800d809010400703003113800c05040e04103114041d01c244500320b1141a0405c15140380010b41134032910200440014050401d554800b91004100003950212200d4099880007a2001a1036181040ba00c0c546a50160140a540280743c56442c060440c1d62000d0b40c0712900c0030400580c05c0c2a40d120302c030003644110f002d0b104581ca00007020899 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807277994 1250 807276744 807276787
    0x80d0510080a0309090507020a302a2109030b18060a050a0609020d091707110634140c0f040213030c092009010203031326 54
    0x2941c2c418280580041d07040348105059450004000455680b4078204070703c3d0030071846029110b04540024060201d9081c080502e03100002205050740c2800c60703004907070b0140c005000d004d0840c00c807480d8204103417460010640e0b05000e030500050040454410341c001903113980002d00440c01d0ac2c241082080300d0406402e60001c00102c80300050040d2000680c1c031140001c103039065980d5a07200041b90401540d0081012341007810b4119281c05180c007851000303020460083e41c00100c07070002c94400c6c014440031a1600f07039000619582d07800307444007440b41c00e4020b0340781c504640034407100c1d05140c003034004081c0d04440c0c1e0240e00800c000030030341403001340640d1025610126400010071b00d0490744a0b600c1c541c01048040c0e50059440d46107140d0300200344800d80008103c0a14403c0014000b01107030464212000700310080e032514040c5091140c1148141c042e82405a001440000c08110701c840964000f2400b940c18000140a11200c628a007c0d024a07141c61310300b400715003040d01081d40d0001004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807279244 1250 807277994 807278009
    0xf48041806090903020d140408011509061202030a080703030f092103020903070608040819110f0610051915050a110105040309050d05030c0106030303024503010207080d0510 76
    0x7000f10a034800035143c1c0304c40d03800682400002c514034035041500d0821500100045d0000b00040c030800080310b00785490381d00c200b03c015030500d20041359034040c5200c4101020b50082c0140409616079699500a8104142c1901410390744d01c000382509550340112a08c55200d43e81020340300300ba985116820380400d0145a01305841031000200300d0f10700203600d2064079500d0400521b00d589a180240c0c1d039124810344208066100300000c102c0c0c43e0071060444100c4124016581c0e48600d096295665960440d10240000d01811041009042c00e4401d003888541740c200c009040c50312001400c03a583d051409400020b20300151080b00c19901060b66078000c00d12500900650509850041400e00c2e2401502d101e1003646681208005041048440030380c3d001d40240302896a03402d0150080d0005200d42c850400c05228480039207126100603a5000c0b81064002030030122480140304040f03501e0825501503500300320400200d080580136000714034007864046010f00c0c103403800c102118001d910400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807280494 1250 807279244 807279251
    0x803040f03262502040c090e07080c0a0e040e011109010908060c0403060b0607050d120e06060a0618080a140c060f03150a030206070b0f4804180609 65
    0xc80300e030041c2e04079005501c82d05200b000840103900d49881e00c03051014003e40c45032600b000d41c28582c2e0003604047c100d4800303203590605030f90f4846080c0e8007010b04980907100140200320b501c0c00940585412849010041c0c8001140d660100c511400c607150902524950355020a0a2504d5070384405100007400407400500703040d0820b02c1c00003038a0700417070000a050503195652020241c456500360b85900303800c00104c410140d407450780038113400c91000102503940d0408081d054031000001f0720343d00800002c0c040c02c1030b40d031405808551320444985a42c0d41039043d007000080c0c25001b04410000c0900942126846821b401c03020f521300103180b0105401518103201b0f60110402c20400d4a912851411194000304140030014164001d03a400c020f41c0240080380d42d01c180320108003000e201c0c0c450b941240703902d52101c41010341e40056000b45561003a880e080d1820b09046007002160017031142e44140c0207030400c0e04001f82801d40194000c2c0701c8240349841f032070150340b01c83d002d80c030000c00c040365042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 807281744 1250 807280494 807280553
    0xa0510050903071e0f05060a050415050f1501021c030204050a0e0403080106050c03040e360c15040b1b16050906090601020a0501110a271503060803040f03 68
    0x500690301c040303009144189002c0c0780e40c1407160100f40105c015622100f51215841d08500b03c0000700001d40303007618105d0718020703c51454081c61003254090920100d500905a444544808480e080808014114001c0a4840f0081180d0105a0020705c1c0242c81c0541c03114100003e01c5003071642a4495080b2160302c4052001181e0400b403601d056581c10714050b643d07980401c070200d02e14803d6500001d0b11616850400c41181647c020159600c8003180c1740340010751288140514640e081000300b44a0b401c82180040382e483c2c104800000d102c28100c80605240d9207868120494001d102e18030134602d440d0007602a108405c8c0011501075042030031141c02c0300d00f07180111719104001041c0328003490040300802c81a81c0208001c0100c0d0f6407080c024031003403084009d4541e40b41c2040c0c42c0000800c2c6520160404840d0240c0a200c1c41c0314110448815030349402048140020300d10502420f0503034521000c01e414900307000801c0540030031120b01d0b180c2855483c04020340d42c00303008d000700e0039850308244 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 807282994 1250 807281744 807281753
    0x130518040b180a05060a060314070b04060f1e0f02071a0301090207030507021011071d040602130e10032f130f090b01060e09040c06030c09080a051005090307 69
    0x55000900030180c1c1c64001e10300c010b0070b490040480005010ba1088a04210951003241c010800340c0c0e200c0c0c40000c00d0007d1514141c0e5440c2c1c0280104400740c5010b04c4140291841181d0801c0008100e03e486c41128680290010603075030441c80120020b01d0340113803021200d0701001800d000303001041c0d41216101080800301c003a0300041c02289040361300010a50305051246090340c020680041801c0407404241e00041d04106007000002c51034005e1b41d80008100c010405403283e41c40c056458135209039295a540802503201d0724440070540707207146001c9010381c401031301c01d440fa07546000c18031030300e42c1141851044550030206908441c61140b003010510702c440f40344021240c00c292204007071904c40a600703130302500b1900441812185041c01075401d10a0000085040f9006c5440314910003201c0d40610109100c115405080007000c98410044640700b0381c81681031080900e81540301c40d40700e1070b415041c50324400c810782c0c86a000030418840000544981a0480032180017546046030310740d036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 807284244 1250 807282994 807283013
    0x2013c1b0225050603060a0e070c11040e03030114150409050601092c0403032018100516020f1f021e10020c01020904090b09010506090c2a0313051804 66
    0xf03040c080d000110105005845154240c40a403221801d90303030607413411000040c482c0f0001e903415035288140303269a45c46400d2070b1003240e400742640006103103140c1c20000504181c013903032000c007604101500b60300303000b880740800500301520021102090300d0414800040c040611604603100040b84281c096811500221310101c0c030707042031940005181c2e19400e055008000c00f010221a034040700302c0c2c5202a42070324004107003002c0e40700700740c18002c0d1108081c4130141511240040215a08020440c4200711241c0e558a010348001d02218640841e003000c61003d100010304101c000c400e89810190181d018018003032801c6248011030400003007802c0096650312000c13107440a01d94000303003200b0421400c1d012583c0d2b091000e4820311058003103145c91003a5104c03c40d1400b81d40e502c1c24020400c10f01e064009107002d40c41200c0780600701540c034100484180081504023a000c0f102c2160600060320034030180000d02d0760090401c18161400007402130301c1c0d00e6135044200745d45000c403c00001940510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 807285494 1250 807284244 807284249
    0x1060c0330050702010b04060f050a0806010f05011407081c0e3c070602060108060c030702032b0615031d0d08040f0803151002013c1b0225 61
    0x407030104003911a02c1d801c3e401000c4402426800600b0141c0c003007500d52512640e401268000d6454801e030035640c01e06030352900020f006080301c508200104001541c400d0340d90f041d01c1030030055013902e404159564500da0b50f118003a0381541c0d13003100d00f0900710603000c0e00c103110f00c16842c04060000701ca007241c8c0c140000c0702c2200d46c13604a8580303a040003019425035100710300c0b40317401d90040f2050340c3c1c1c40319006175a900342403240d58154071842d800140341032030351019a8001e8003580c00131820300c014017851005d00703049808040701003107440703030140c00d5404140111402407000f01c0e00207101140c1d0980090594000d8210b040c590001180c0b010212803001449090b525881d1034031000c3d948951800480310000c14802503d282400720920074441c242154082d202c4004441c1c05440001040c0182d0a0741c07441892a01e8480c5502500140c2542c04405944a1401110f031400318442c20141341040b2142940004400d0039907000c03568000d5010003c1012001100400f25440804903091410390324460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 807286744 1250 807285494 807285587
    0x108060603131502030a2a1d030105180d030c0905190b0f090306060a0305150603100c02030702040506090f010b210901050907090e03160c0b0301060c03 67
    0x1001662060020802e14021540494003011031800c0c1c98481001e0b410940d41c180030380b13283c400180c0314545ca9007600800d50b440840d0242e98041e1303192058a40c022900c1070b007a448660151043c032155020b2085c103100703a00a60903043d051108848491900c020b50301038509141c54501ca04400f140c0103001802181d00c01c952009400e9014503074194040c1d0cd9911025000340c01141140c0c40210780b0018045125041c0c044480a41d5030001300105490036100182460b081015650001098011400e40c8051301904171964220700380c07440412100e00103241c0c80160408210101145000e0084c02d4000004650025007400c042c0c0007008055018420781019650000704041d05450803012791444e40d00501c6c4042861800700c404501808040b00c03c000a03025134640410b080342c252068580b0340e01e0660040d0708105400c0c0440000341d1903118150760004c83e123040040c1441e0340310015800303420184d44904852041c3c1c5009490614400c1c0300c504540d15030505200107a20f207502e58250008034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 807287994 1250 807286744 807286747
    0x602120913110315040504031706010905090a14100605042331050c03160207090905010c1223041406090304180b091305030d020414010f0201020901080606 68
    0x4030380080c940d0050380d500801c005062001003a4101c0301e46010f03512a000700e2048a21400d40b00080100703d80c0211001008100482040c403900051305c03c4455006006040c024000c5444400080d40202e0840703061483e03548951071048548504c0f5851a08600d03860840030110b0704000700900f8500550041e080804010103100e10f20303048084594a41c02406001103d02c0003111201c190b01420751a1a82346c004914618041115802d20549208510b003207121801e5440e00144100c4690340800c2c0c110440c4118070b07020904101501c03035056164030410000035030f417110390ba002d01040c0202c50317084078886c5404c10b406501c00440c1103a880d10507641c608088990781e50b203444c608090001c020f15659100710700411501c08000030007001038400414000407560b407400c201c0d070241c61a00c02c807103801400c2440440c840c81807031194014034034469400e59081034202c400c8901244c01a900c501a40480d540125801e5600320383ca29150403d5840258a411a482d0000e07007050f9007d01890b008000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 807289244 1250 807287994 807288007
    0xb010e042705031207092d0513060b0309062d0106030c030f1b090506070c030609020102241e090613020f030f0303041109010608040813090c0507150204060212 70
    0x8041c001c45136500203540480350541844440100b8920700313400ba1711080442028043c1c1e00d0042d0b8220603015030380001304040b04505240610468540068a41109d59100c2e40d0102d111a0041c0c0610b00c210069002018680750801c8181c032000000343d1150084281c4201f168480c00441685506581840c00d01152100c0d00340022001004507104110f00c4501c0c100000490100c00840d030200043c2e01da80d0345603003079190410040d843c899004010000d030100351041000039000c2e001a00307814014015656a1040560220162000e504494201090000c20480c44d50080d800c00d80c0f4a0450428550751450582070981d59030002606025188001ea5200d90840d60380044010390140c000c0d050314000710124404035625042980c040b80d40c02003240c0c0612b940c0c00c0c1400110f04894181e43c0751042600c1d00e1b203030b016030b41d4040486006c0c000e00000b80411118500c1c000d298a00d591555215510100c5040c45642000c51044500d4424010042003000c0c580c00103000040c00000000b50f070380c030071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 807290494 1250 807289244 807289253
    0x80a0b060a1707090b04120b0109111210090204270213090b030c030304060f1407050304050d0f0821150306010b09031c0e1905100e030c130b010e0427 66
    0x10181c5c0c000c03002c16400040104142840e0286480c000388101e1003c0306a0b6201c2c54141305841c60360600c00c503520010300500000644a0701a540c1110911660103000b41c0c0b55400442660f000350044000e41120405041c61211140b015000b02c015000c0b08505107101c0c1072054007245524400c68070b020792102008040d5950900000e00d400710010112661a40d4951000e4485816070003504041403003400080510080d036022074030119171000c0990b14040c1405c0c00c01803074141e00081604c1c2049840e1600d8002100403000b00401e20b07241a40300d054101341c401d0390340d41c010000c0042020010380601544652400500c06041d40c40d03440580303803101101c1d00440d15207002c03c0403610b401c1020110292950740c00c070b4160610214107503144030107000f1265010300d41c410300d0f115158002680b030a8000601d0320409084201d450010152215000d0820000d8848408a020300082c1c1c0d03603480000b1142d47e0400301c004907851040c4c9080c4036a02490740b082d000580090503120084811500020400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 807291744 1250 807290494 807290507
    0x409032601120f021305040b0a060b160602161a01050f0d02030a02010f050f18150304080d02030703020904050403090f0f03050606100306050904050d09231005040f06080a0b060a1707 80
    0x17412240042210f4581800c0c00c89607002d0031b4503403c52180c0340c500701241c101020000c962280e62220350b0038021070b04941d0341100940c4100c48005282840c40c008200060b4206100241182c0c0d0403641400d95051204021081100e0300d880ea00c900482ea9004005803808580d6600407502420149062104400d06468910440c29054601003000812502c0134455250a04000c03a09880510340101e00d213245410350320043e1405031030690188030040340210203800541d402004c0b41307805030a100e01c00000c14160b840907201203002c5000c2da078050109501450800c0001c00c22200a00796003403031515080d40300e40015004c81d020b45404013294042034002d800100003808041d01d925003624041c10076a4807922422049170001e140d5802c00644034202900c0d0300e01c815205042c6115007c0b40c101000103250318101840b003480401c0c08001802600c0d00201c00003002c440e22860b2031850f100d5648000c0710507680405100c3c0302d040c4400801d1036444070b170029451f4507814188000f911401416601c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 807292994 1250 807291744 807291769
    0x51e010509061c0507080f0103060e1504031101110f1c18050604050c1f081315150e040c1214010204060e03150f240409032601120f02 59
    0xa1400910a03a00800c0f40007415007024014004001c1030302c8502044038001825600803507180c507034400500108070540d1014441041507404c45408ac1e6500c0e01d00391701440101c4064012598055800034a408280901e4801a08014440d842d0003030740155900c1034083c00c219420500c44160028100c0c81140c0c0c80107049003200b03a208826002d83c3d240107559080202c40072a200d0045880849103424810441c860020004000f60103440d2000c9007220900300c014200da0300300c0303203044400c00490710700c00496103110040000440e84600f0055000700d4841a58040a00d900c9458204004103540702440310503180740c1c40d0448082d15450900b5540503030054003844080d4400107000440b5500090712600601d1f080d400c0e11422140110102c40c029402c492111448030f5450020b207401c0840c0e0030b20200c0e414030b071074080782160000c40490122041d03804210040bd011010840703884040a00c03c0501c2e101c2135440e00042e6060582416002102d50700041600150313204600c11965550548800f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 807294244 1250 807292994 807292999
    0x1a0f070507030f0309060e030d03050a090b10060f020f0c01030509030c061003030e0402090d2301060b13081c0c0807021c1202031e0a0207050d0302010204180204051e010509 76
    0x1c001d0300c0341400301c4051503021044000c98200c400000345680581041c3c5040440140a041713403501981e02500607080092240c0c0c4ca2640e5040010000390401520318000d946070040e4812040c201400505014040e1240303030250b6100c10b1002e01111000500032039106030030f2070003107403e45405900d03d146000d00150f034a01c5004403410000c400e80c1d43e2a00e00c0440f40aa40c130201c0c0321444205100172803151120701038211496002010200ea44100000300d0440106a1100c6a2101120286c01c488040d00908e425450005050644c2084401e6035005000700c031028144401c000030010084840f5400d800701806105106601804003074015904020340103480502220180c0c21400f03d0f01c0c001c001d04a4500100100b403000701e91000058a141801c030b003200a21a000c0080341e9403007a01f08131040002c5100d00303032000c070303854035418443c041c41ea11a40000d030307c2d07504004040c209a00000c10402146205004c01c01040c2d84905468441100d0000424154001c48004039035905c601a941c1c0d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 807295494 1250 807294244 807294253
    0x30903060f0a0f090206090411190c02041d071a0706050109020a02070603151a04080a05100f14070302130806070e0411090a18060914040b0f011a0f0705 67
    0x4006118030072078460340460504200c0071080146000894200b110041d40110741031242640e00c0c246a444540b00c01c0100b01214201103002e202c400c50119402001400640309052440841c1003a0007100e61420503600d090b943c080d10b151605030b444e8a540314043c140c2d4807000c8100c100c1c03109602140c850030382021041c0115a118503d0002035403001d2030840062298510014140d4800d101d2062016a148500041540f4040b0450035040801160282448040000082c0e0710700410400092900c92405800d81c1c0c07441d90003500898031004c8091000c542803080c04000700b04016401036000d28603060051300c41265400c2100d1401542c1c010703030103d100310414040e0294104000d84458102124148568204804011646e000d90f500803a0008103d40041c04201502109410031404580001a01a9490004070151800301100c1151105c075282400203200c07010344030a40c08032a00060078165454074180c0c0c2c0000301d040309600c10190b8042804007000d84580304130b5480b15004004c49 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 807296744 1250 807295494 807295501
    0x304080a11011821020601090207030306050303030405010c121b03022d0301151407030e060f04060c0215120402310203070e19060e040b1806010e0d0c120503090306 72
    0x52a44010b201d00c1504d200700d018090326a148141c000040100b1265406012680d2030310b0106000b94000d80400c400f415110080860692010000b4621540c002e10010560040708030024110030401c15001d1a49c82c01d10310b4803078014804c4020701e40c1000b000c0c540180da4510010b070000c0b5100c60950840300e65000314090b96130390544100918103072030701c81d0080c0503049641700055400103520880e0003c00e18052091601090044003840420138014082c60310f03007408419141015400b9800004c04544466040c505605000149130003402c0c0d00784c4020700e003030042c03410150000c03c010300082c8140c0300d0324003103144014401d181900701d440981c05d400c10b0210101018019400890340303103000428200265580e441c000e90807401003440140103412081c01e00408440e940420360406030486e403640c0d01200b00d9203074401d60b421800d911505c3d0200600b411000144840030480e10103101d2144079040002040d400706400c070403a01800544d204041c903030300e0a0390650050700b82650341402002c081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 807297994 1250 807296744 807296771
    0x7060e0409120f0f050a090e0408040b0a0302041409011805040830070f080406200d09020a08122d0a09031202030412140a02130e0c150304080a1101 65
    0x80c0d040c0f940c00e407907050060342c10640403500340c00748000301000241810010400240829061600320f40200300c01c629164880d5001c0c0c10741c2e8808105000000d031300103030400c00306c41c010304c00c1c6c06030842c01c407603461465160500d08514409800c6591003696564804070301084032030001c50359000303d03080380d6090440007424001540c46109180c1c804034080c100014400c10b12400c66408484610f480301c03d2607881d07030741701e0740014003c1454000800f10300820f00301050a6400c094259106880c44c0420400e0f0301d441480b120551660011441d640540319100c150a10001501c00d542c1c0d610146503500c1c05204401d220036490107921003541107001405081d86944001d42100740da0217280050b4010510010403a502d10444c4503080b0306003021414000045ca12030310314090b030f0a1002c125a8004101d4000504444820701c10340205541ca018405c4501c90501c26546296000c440081c010004003030340d40041c1c400200010b201e4000040d940342d01c1406042420745148080c07008220106280c0b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 807299244 1250 807297994 807298007
    0x71203050f0a0909060b12090d1704080c120702010f030506090c090d0f0605040b0c04050609040e010e120c070608150d050a1a01050906090702150c070506041104050c0a0207060e040912 81
    0x40c078007410408800041c2c0d17000d800141d10708910966604c0c6000c503030000d580800c9201000e8801c03201a2410840d202c04803070f0401481c3b104507904200c4643c4c42880784005072844485200e05801d040c03c000810a40341c4d21a16010f81c40140e10300d41a945094101c005680d04048010060404052005c1c6a040c001c40b0750005210301d114540410503a2184040c69140e40076030b2040e80e5010030108840c4ea210309061304000c0a602c0e00e000085100d4030404c55079800c000c3d040c1000c00c80004081415840804200f18100040071300d414891142d0402c44158241101e1110989003d80d219540544c00c0110400c80319204580100000c1d5200b003d41d04040c0e0045030a01c10f0fa0b200300c102c0030110341203142840d030340f500800b4a60010034071040b103080703224000f0a008103031420300d18050081401044091000912aa00c03c0f143c48a04542200801c02111006461071010304801d100c00951250000340000a0301c51500700450341020580014002c0d0100b10030091400d050040c040044070340108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 807300494 1250 807299244 807299257
    0xe030408010c05030c0901050706060b071a060109051f0215100e1b0702090c0d092102030307120e0c0418020312031006030b18090f071203050f0a0909060b 68
    0x900910460b0031004044800c0d010a854882c0200000c1000008a43c000c0000304000d134802c2d0004210349556507680c158030703005980c1c15503508038001508044802c43d031010a901a07424202000b80700c0c107041c04696807035980300d0141c8014881c6000751250303900800280b403c00c0b4801d035140c020703450700045403032203642076101c2c1c03090714400800440e9514411600d41402d0703071182c0c900b16060136004e40030004006000b130000b465580003000340b107503035107143d02601140c00e018040c50040600c0c801240340d04820f8007002401150018030a00c400d650740000c181d01001c444080c00306200000005007070502e00600181d81e03003c0c0c41c280e04002e00c1006800442007441c0218255001c01e1a003852040c00c40c0720480c0c010009201200050020500070341c0300c030b01900d202401640040b00c24035402030880c02e0607503044e1030131f40c00522803111040c020802540a001a01002862080c0f20341d0080d0070f40c0070743c044041414501003a0380310580c2c0702c0e8138a803008100000c01030060a40e80c02880316141d010f40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 807301744 1250 807300494 807300509
    0xf06020d0203090f010c0c1505120f060108040f0303180f0312151e0b030c040510030902060d0e030c01050f161707030c052101060f080906071101060305010e0304 71
    0x115180d9466030000c0255446008003405040d00380303030220011500c403d0500e40c11207118426010200e400881440e03990f000b03050b0754803090760b10b07204040c5c0071703961a1303000b091295070011650400c82c040c2d0f40704c54100d0b002030740320060301c221041c035140a0300940381024190142c0300d0800c16800500c141d200c0c41502d42400f80d1a040c94180f01d1100200981e00070b101196170000c0c46a008020501240e00c030035445404109242600715124003c11901c0c0e4425111604c210794081011b0100d458440c0010094041505082001c203006a01080031405044040d900703d03a503401006181010074802c99102a83d108020007403890207111600f46da90b0f040d2015403880d4040034034002018014a02c81004060090000b58681c1d40c009046018025500010003003101c00d00c1207100d003070170750f041c1070034605031130a9526090742c14084d000341b42d00e95066841042060f20010701498900114013150000c07220318143c8050034000440c28054565540010140d61a12103058141c1e078010000e401600d00d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 807302994 1250 807301744 807301753
    0x13050403030b040e2103090c0319060b0a0303090509060d05060406050a050606070308150301060b040f05030c061c050615040f0e180303130303110d0203041a09070b0f040f0f0602 78
    0x40e0401d8603a11200020745c00500d0000c4514024400140c001456014a1400480d141c1f201d0210200707080101c0121280e0410000b11407400c200326060044482800b004c2d03d4400401c0d00d5900c0007804032200d44038940c06050320102051491f01c9660364854042d804c0b2041382d540742094903201006100844000000919000100381145021000c447c0015010759803c00140c480034111402500b018003426030666840400098001802c00600000c25140c140d88090900e40824581458201c0d2805842403404000c54050724155000b91780d02c54010200c00902540c0e050080303032840900d5840d040a10002040004012018a110106581c41d81d0b40600072526014125842c85280340001c02d80e80e0030500c005400c00305c00d0340f098000d82c3e00071310b40441c1d4440383c0c03901503440e40d004400c41c0d20300d00e40000400040c085503001040782842d280b1814926407610410450301d40600340902d1407a16000a80421707181649000c1c1c40103442d4131104240055079464038080180382d81c0c410070000d40035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 807304244 1250 807302994 807303011
    0xc021012060b1903051e07050406090807230a09020d0b12061e070905060301090b011d1014040305010f05091b0a1401110f010606140315060913050403030b04 69
    0x2201029200312860110701600341a0f600e9030140c0250000400c030030400b2030003d641d0600d00310468410390041d680c544070180d840f070600600400940c842c0d0400c20303840d2b001890811509040982e04000240c440e00910008400342000614410f03040c1e01440141380041281002142c480d408002c00c2c120440d120008058040d0403c0d8407403100320b031041a801540d0b1040c4001c00e0009020a41c170485525100440e1612030001403c07a81080e0000400655106407040441d600140c1c0c90303104c08603410320250213030102400030f00e0124545400700104152060900c0f8402d03050703025074001e90f034004024003614a900040e0b800500040300c440f0003910504140c1040790190785030a846401014024401c0241001009802002c0745240141042110840707089100c0c82404080c4113400e00780008510b26141c5200101480c014191544030000100305200d40c20300582c0c41071003003060680300c2a07150720341d2400240b034a03401c0c40124404103042c00c0801c4201907150f0302860711000121000c0040c10b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 807305494 1250 807304244 807304259
    0x1060608040f0215040b12060a120b071119080c0106060503130803070c05101a01090e0610020109050a03051201270b0a0503010e33160c02101206 64
    0x21029a40075010740754115101c07000d401c0c101445583c4403880318004e03140580d90301e07075100103601500010003e4007000003407060f14603201540d040103048400c900071ba04210340e1501601140007070010700501c0a0707a941121000717001d00c10b281000c12a000d00007481082428140066400158207404552a103a8086810b0340190140ca0003071001e4404001e00304401d65845001e0b41c4054900300c103003c0c244142c0c00002e00208a05604040414404242c02040390f03102043c2d03507881e079800c60520524440c2400262440644103520140468a4501750b48a2003400d80c010080070707a001e403003401001481410306030018000c01c1010462a01a44240c0e2b039800d9820502c658030602c240301c008102a030f0325409480da0005003010070000c3c140c01c11035907a07170002421110060008019504220118000703486080e104911140c3d1100c00420704a02460303801b507000c00c00070300c80e0305281005d04c0c003c400c1621488950006683c060000b12140c43c0c102005040c566001404407501c070305040c030209024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 807306744 1250 807305494 807305507
    0xd240306020705013902012a0306050f010f030b0f040603030f0e011404350a05100e0604030c05280213140105040e01110409020309071a1204082208010606 68
    0x100202c0c40c0108209401c0750510400700511380107400c540d02c07980002301c034502142c220543e841c1014542c1c100304082080c050151442540310034495890287c3d00101c90b60010000103a03030107280b900284204180740000c0208108503400780c0c110340341210200800d84c016411110111040e207803040d41c1070007100112401c400350368a10490030400d00081107081c46114108884030011130881031510b00030094400c0981074a40e625506901c03004001c2d0078000148a4501c9030500b00b1401c0c04500001c0088558407080904020104003c24020609002d42031291507481c0040c1140b0441001042107000301d40c1b420020181e11039407600f95140c1488040d8403580d425103050aa90843c0c030303840c3c001000000c0922100c00507035552540c0100e20410b40d6580200f0150402e28070050712030078040007480c40c0c405641c000d444a03070303c02a440559007041030103680307070b600d071041802000da900d41c03800c8440c5024948150401844522010140041c401c11041c1a43c0119000300070b400d035140000c6503407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 807307994 1250 807306744 807306791
    0x714030a02071401020309040f200403200d080313020108060d050d2a0501020409051b0d0902210706081608010504110c0304060c020307060f02030d24030602070501 72
    0x907a0040004111046000c55031080383d240500580c4c0c20140041d01040a40d0040203543c03480e1581e8041c5c424074503004840251103400403c00140c00e1500755a50800d00c0303021040120340454902c4484001940d0303a00d1514892980005a03607241d0030011800c500004860000300c0c0490175220004080d82841c26a1b00f400340c1d00300c4014141101c145c074080c2e98400c00c0d8034260500c4600440c002c4403110f10b956a46084510800c001640e40d8500400903007191006419500900c402500b401400040d16044e03c1034402103000024001c00789200142c4502d10a00300b0040320510b2600d0003c4c1d0b01e80118a100849015032500503090752410614604070500e10030b030358042800e010062083c0c3c20183d01c400d5454074881c1c00c140c03600042d01e00381807464020f80e015a00145c0003088a80031820f041c00400e0003804141041c8900041d01d1401035124040c210083d80710541c0c038640440d8102410031815201c030034016012080c40e0322418038801950001c80107413240d60038890344010851900018200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 807309244 1250 807307994 807307997
    0x50d031103070c08160c080106061803030518100806100306080a083009011a09061905090a0207030e0306090312091507110c0d02060313060f0905030714030a 69
    0x5142c1e1060020381d03110304001c4083c3d4041005205094082c0c072480000c00700c46001e0446800c07524503000c406401d581085d00000100402e80c030a02d44000c4411140c030303040e02d600d8203016459103040d03451200f25044800c54140d10010b01600c2607451500103545501514094032006064028180700fa015a0305902c14006180e100f41041c1c000704021401411061004c0490b1400d203a040081c10032a0845070789034200003403c2c1c003042c0520800d00740301d6990688590702003030100d1010b4500049585900406c10790080c80c1c03401d1002004103060480d48081c0c41d000300444543e06040604400941054030101c001c695010a0501e1031320f40098220700c0f641d01000154940814400701c14010794000d08103c40f175200b0000506c18070b440d0b00c0680d51003212569540f00c0c50110601c101450507142503650360181d0305001b100c40250321241d00712640300400300300e82895901da51800c4001031a12622900764545003000e8401045804001882164000c00410840b60581202d8a460b40b085099140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 807310494 1250 807309244 807309247
    0xc160302060d0c020102090901090605091003050c0603040f0b010602010204180b0d06090f05070e19140a0c0e030a0b010510080c070b15130606030f06030809060f04170a050d0311 78
    0x551402c1c55030850505140e00f80700240c1002d04503400308940c0701080e04000e50241d180d41d014025410043c039480d81c44110003480100307007803030741e1103d0717482e011036044450180c100000001d00788170821340c409007050b601c10b00c04501c40da03540d43c000303000390820301800e038040611041014021240323000d580258900108140081031099803110000e10009104441500304900844049503003404108000d140405104210303260002c480fa42100341004038801c2070f450417521030840c2603030a030010f51140b0f41800c0043d0701c104050043d070701ca003260240903a046c41000b00441c02c0100d20f030036980c101e0304243c070722000c1e60300c90900945444104403400400315009001c02404030700320400ba141c000a40010f01051b1140e42c0010690b5481020030701d0024a407600801c00425506108a58918907000410007000781146d456400b284a0480c10701d01c68000418042c09242200c4200c9008042c0c44440750504542e06540c02d0f1502d03841b01042c0e440e40140e00d1215100c500a026a00001c45d9404086 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 807311744 1250 807310494 807310507
    0x51207031106030a06030c240305090a110613170c040507050a030b040f09060203060f120a0201050715060807030b0c160f0c2d082b0203130b0c16030206 67
    0x202907000240740c0d44c2d1031510b48100101088110102c580030b0954143c1480c003036201e08165110880d030080765042011701e00000c2104803100401d03441001c9a010800d46c404038600000540b440c0601d8694103003040055000241c01034034418000c2a0301108030994211030f90800c00c2108640003115480007045080100d000c0181c42940a00000407008000003508400404990201c1355403050448465a0010a0252628003400c8881da0074500f11100700034501000d000369100d04006200906104c0e0118950301004044402e000c140b5200090420185070b4645034140d560355a4030003950a0141d10003c42c4294448904441030700d129400e04c41c1038003019544000c0c0c031031480e080590b0410030801c00410b40f058207a00040c01c4882c9240300c130000d000c14041848005007241d00400305548882c0d5140ca034001c03840e00300e541402e43e41064840b907c1c080f45050782103101c2c4940a1032843c480d000041002603100c0c01034080400c2c04802c4034403a510450302440c3c100740300d000207503001c00d003030005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 807312994 1250 807311744 807311749
    0x20a230303071101120f09060b1207030c090207020301090b0f01150e0d080927240306270f100f020307020a020931064a0a05070512070311 61
    0x511003820717606030005075000c0030000b150212070241d4422a00380e5103c50701e10166103080c1f0891006902804050007000740b850b90382c45080b00143c441c201c0443d40103d040000c0d55030a41c4104111600320701c140c4d000b490300c02d0380110710f96401d00480c60111405051002c0c507920a52680b10341d62409014000340031031545519110303403c40c017201e039440050034070701078510514a0140c2c040010203148609403418500f0600c040002460000c0c20044520214a00e0550380026085c0c0c1144541c02554552280c0e640c072285450b0054480788806e01c6288040703d941500040c01c00356410303084804100d07400800c020001648010f8483c2030061344007084003009440c00d800c8a0b078001740210301c402c616525000d11945c0b030a00d11150b01001c07a1000d8604002d10041e40541b41d00100200c0b003503c4034800010020002881100998080c01700b807200000d82000007800e101282140d500407030780b508480340780c140d2340c031b180600035076000f0384010858015001000421405881c0d0100505d200409404107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 807314244 1250 807312994 807313007
    0x90a0308040221100c0210020a0219020f030f0a0605130f2a090902180417070501020f0d0507110d050f09061b0715180b0c0a020a230303071101 63
    0xc0d0f04400340c2400011071030100c0100080c03609080701240200701d16484c8800603040031619090803601d07900401c141e801c0c0d181d02144c581540701422403c1e0300e14481c14000310301ea491007403442541604c80c44001c3d81400c100040d2800c00180304690034402c039600d0041d9074280d2100c122008020140140c540400100064584042e4520900a0f856214540c040b010b041001e1a0300c00c1061581d030303210403019414600400840c13002d03a448503003101d08050366001e9000050150400c0c0045012811320100402901180c02d00894508101d403110403803504100280029503442010130b03014600b2096082012900800b0503040740c445508003e015041017040380d100d90708403544880200080c140c0c01540d900d8240164200d40010107890b41400c4641641d620694040070074000008a1310044505510002c0103231284521215100c00801c1000da2416289840003540a10001c02c08105c0031a22000e40b002442e5002a01091406070003d06403607200398880501007610701510802107500855 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 807315494 1250 807314244 807314269
    0x304150902210a120c0303050a0c020303060111071a1206010201090b0606071703070f0813050705100201021204080309010c0e090109090311010501060302090a060512041101050909041406090a03080402 88
    0x70b0540b0218203469680c40b9540240640240c04604003608440134143d15200e40c6038800d900541c10400281d9400c0302a55070700000702258100210ba02d08035100f103909001d41002400f80c040045c1c5a1310500100721100d070003414614100e00070f0306001a440d0b40c41405250070981e041a504982c0751900c40502c07005510a40041d1007840c2c103100c09182e0620303414000e51042c10656649010034115071801495218050701a0288400924411001c20000305401341200d030300716420900445202c4059001e8025600305c00080108102000288812000114829904140200030380442e14005949c41c610703190f001a000101c02006001c0303a52240e2154000600a044c81901000c00d403050320b0944200f41c100300e00098010501901700d05002040401925003800c001c2e0800c003207008010f2400000600242c60451058211200c0f64000c804a4081002c00382c5819960302d40380c00d0540c1c4030000011086c20300d20030f4400240000c24041604900c2039890f6a600b0300a48882d020021290002d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 807316744 1250 807315494 807315559
    0x90f23060612091c02160e0a1803030605030c03010c05030114010207080d090302090708072f0a0b010810050103240b06071a0105030102040614030c070203060c0304150902 75
    0xc0090180074005140d560740b150010700c0c01400305020500c3d80c0307075007940c01c106a00199440b504038244081d80481094041d105903c400008a64500d880f00016110746840c1c0401c4170304945002c0280352f40b54214506a941c01d81c00c40780750001ca0014142200d00c180381d48400280180014422500c00c2c155002010340140304454419440711490350804c00b48800310004980d10040401c21400c200c5d150300d40c808841d0404a03128501404040c03c0d5068400031010940c80710241e9200c1404070811034511001e1b08000c880706654186441c01c40f032074007070140d18074521482103c50300c034030035501902d0f06a0f0742c00b41c0000d4441c03106181c0c00d424542c4100003070071043d0712041201e003940ca4240203410041e000d044410405c060204425095a106812407070003a4010401400160b0300452090081541001d0345035032941d401614006900907030340000d5141c050351090048840741c2c0006140618001d040038241b40038055002401c032000c02030000c0d0082e008010520600529030b11081c10300d21607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 807317994 1250 807316744 807316747
    0xb03160e0d0b07080114010206040305031801060b0d0603050f01090f030f0e0616031e02280606060f0801242115140105040f030b071e020106090f230606 67
    0x2070b030790305080b690111403c4000680070702c010000c00001100000c1010001e0000e814503040640f001003581c0f000500342028803410858032050403070254880c0303008001184810342c0f070b038410000d408090420f521040e1a01d201c3c4c8031041c40e1042042c8038017a002540003845e001c4d01c45190350b0036607039620158168018400c114038003003070a89074040106100b49111000c03d40d030710801d00d00a400303900c0d451010350b1113482c01e076002441a500015001050780030a09500c080c10945100e0010404e0b80c034030000c01c000d090007800182c0c1ea03084803901d64803002944460030b09071b0b00d071450600f034101c1804e0044a03000711100540815405003005000710f41d1000220b2084910140c1c14106642c0100400360b202e8001c00410401c550b0441c80844008000340303012446e00c1d01e018a20009240c103800041c090000047c085150340380030754240a8007401d0303200803943c0d00340d0041d40640201441d2141004490921482640b182200d110306649031410440c00540800003224410400b94002c1c0782c0b6810500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 807319244 1250 807317994 807318019
    0x507081e0f1f0f320906060f040306110c01051305120a0e120706030f060806010b0c01090210020604030905060301060f080a0209040207050106230907030b040f0915060b03160e 77
    0x88080d6910040d01042210004c1c489076026140b04c6095020000d101ca141d21440869865580f601859004002110415140c101c4405400c0c42d51150b580002c1c070761031402809e030a2032418a005850a602c0c2030001308000c0d0fa43d22212403107220103100c02800c03078000c840c503aa0b100f81c41d040034100300f2030755290800404c1050f201141c20050b4281458049a000520400c02c2d154140101d081c480c010704800c1c00800e14010003079039600f0060241912107400031511202d011802d5000850094000b03010b1500c0104a10000e9124a415201a000202444000f003410b0800b00c0c00c50b030480c0d00d2070b90340740c0c608954400100c401c00b001070f1100106a800b045150000d40c1c580c0003810342d540c0900000140381d40b503c013100c51124108958464050003c480c0c002c603da03550100320b5401032442c24081640d9018000180040003004018282c0c00e04e4445201d040c4692298400b00c1205501c2082010700d4885469810341c1c0001c40d007002d1000421210880840d01c0340e800611380d035002800c03c007004207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 807320494 1250 807319244 807319259
    0x2120a1b08031501020c0625210f170105010f020a051c020c030109050c060a180b030916140d0c0b19091e12150507081e0f1f 55
    0x40300314006462949000c07082c002e03103061641c8250601c1d0310900080030303c1c81092001c50304a003d2528104030342c8024003000c00c0400c24048c0c40212103a8800800032180c080d00c2d00c03d84206800c0c041c42000101c0000520035a14002c59100c0c507030768245030405586030f1a02004440717210031541c040d0118000d15010f900026010800302402d12107444030582e134034080410080c6004400c0400d1403080e0f050910100101d50b0100e65041d00ea14107030b0303910356a103040b0351056914000a1340d00c0000040c0a0500007410241030300030703600460710002601c125250914540b811400f96000e4000901c1140a159848e07203001e0709a01c1500340704100a000959a0b43c2c01241c041d00030000000c541140c070b11a42c1d00c2c441d40058043c2c00b420042d041c00d00751410230290302c0700e8801d0a004030b0401d214120301da03005100c038401142c0c172000d0706003006000c4c03446c1100340207008050690b0b0001c120f4012030400240007030415102c40c03148802500008066480310301d00703028005010194551060180004200c18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 807321744 1250 807320494 807320537
    0x618090b0a020a050909100839150d05040b06090906070e011b060501030308011a121e0a090204050108071211120a03020f1c0e0d1401020409060f0b070302120a 70
    0x1100243d044d216004e190000d40e500b020b1501e505614070041c2e40d1466041002c1c42c0360270045400400d0202c0c015025001c02141c407101414488151107040410341070145e044035085503104030310508110707006480c0e1109001301c641064500c16a00e0300814000342c0014890150b80c0c040e07120500d444804400c079090b075558200d03030900d003d4595607104c400600a041e00294040e006201113805c98646182d8190304401074040c03900403080c00d014150200300d060100d54041e100031002c030301c5100c0c140d08000309508000c0984050480c060790030040006400d0f00c0214440c4110b61903840f2420f031358221543d92143ca1400c5551440e4016540000e55100c0c0c0380030404e003100c0c148250001d082003481210711a141905c40b00e11444802c401d00b8980091540c0260035001194058a42d00c04080d120b1511009550640307001030f10310361003c600010340000740d802041c110b82c20684030381403540e201c0580311440d22400101034056403016600200d0a0251002004c0706080c80c504040c1040075a8050140c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 807322994 1250 807321744 807321751
    0x1090504180209070525020a18020d1d030d09060f050403110118030e010c14060c0912070e07140c0303070c05010f0902100c060f0f0618090b0a020a050909 68
    0x54486202105045090003028903811200d5802d01c01d05001e030901d01d01d0144120100c00d44035810621b5498400c54850380c0c442c40140c0098110024121000c8007000c1c0250008549001c03070f03900700310060041c81c851007540089251100017071131600050004401c040c01200c801101e0455030340c400c1d51000381052007001c0c02148242d031100d00b500c1c2c038030813024207541700000407000002000c3c8083c00040d8001c00010418003007824108001c890504109106400200100000d070040c60100069103200d40020440d9003c11201880108096032001e40da5a0035802469000f1140c080402c1c00140118085208020781e41030552030540a4001c0e01c2c2140c0050716248046000b40d01c0040c2040004e00400b200c2d80c0509104100208035030f00028a903120b00d000e600144581c1d01c06103024400f00350080025500d0b004418807594842114500044ca0184208500c0c0707006070040030340307040c12404ac2d144100d8100000040356264000000000e500403031620041c4a820800ca8010740c807082c6800c0e11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 807324244 1250 807322994 807323021
    0x61805160501080a020c100c0e15041805060d20030f010203010f0504090219030b0601030501140a0308090103150e06121504060b01110a0c030507090b0915041401091b0804050a0b040201090504 84
    0x7130034807404288001090312000f01c100c40e19044c40240600c0331004c66002d032215407c50042202d807038402c042102907502d5070b0301a010240029000040081042402481000540c2140d400f204120505400c0380420300466814144c001002c01030391600b81c020740561400100081c1c60336100c2d00b04100d901d48582d10403101d89404404001013980c0512500780141501804d004040303121000180f50030300140401410300c98046406a0180d120b0340c400c1c40380e0040c0c4000100ca042e21500d41e06c1140c8012a0032070b1103001080b010115108000c140000a2200c8603c0384400d07849a5a52101901500d1001c504208a444010340000d000308500d404490144801600d00c2d411410320a0401d0b11580100780b03814201149501c0f992a01004117034030003010003414602c01e00c0d0300f0000c0c010308080b04149140903295000415500526841342c1c1644100c50382e0341c0d002c5004031070160752210301200d0150158010300d9078a07000c54000300c4195402441403400e00442074031100040c0c2110040c1c880102c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 807325494 1250 807324244 807324257
    0xc0409081b010506012c010305070923040c030c02060114030a080d0b0f060a140c0a02040c11010507030902010e040e0c03070b0c0105010509151c061805160501080a020c100c 76
    0x8017940c1205180100f6000c03107940c920800010000da42a1440342000700381019a03c0000800103480b03106c0d448089c00424500c2d40800c02564800680d880c1c1200180e88100d01c0c00303042e0301005000c0c1c46001a46019500600400d0386004070019600d05610506501401074500030000510b900001700a102182e907000540f4118407c14000c1840605100c640111406c211540031141c02801003203081c4060300b4003541d10008205454180500c0c9140290043d04100080d0740e59600140c1045e001c00c8100c0080201e590b413050110151441240080e021071681520400d040c02c0c5a00000d10800c40e500486d47e911010b0030129182ca0000c0d401003a00340d9010270203003804413082c0102c5006220460700c0c1880b600b810040d26018180f01c41440d40b00c1c1d4a101005041800700001940b03505402890030044203001d01442e404980c4007140031074240c040c0551015004900e1a0100292041a9250701c41550b40071040e10082d80b11070440f00d00e40c4141c1e0f21038001498103004110b9850340b00c0d500d48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 807326744 1250 807325494 807325501
    0x904170d050f090f1c1b06020912070509040f1a1017060f07051c02040303050915030411090a090c030501021209060702030910090b03160e0d050c0409081b0105 70
    0x2800302c1e10140100d01180c20a1540818118000400c0b011141c0c081c00d82c4500b85603c0802511032a54600950407059101c0030300b81c06101c001c0d4040c260103201950910007800300d540403661100014011690300c500c200780480e022900001d0010072141c86107120b10f040d41c83c2e8401d1100910b400300d0390400c14491001044c05141c501c159410503501411005245509004c505020447e000400103020884080360302071000840c0c981d108107900c03803c8030865441da200d060040c1a588004400e50180200d2450700001280800c100c030321460b00604040704000725441000082600035019121668641c00742201048200c007580707001714030400c00180e40e8066003658018000700101041c0f80340d04681c0800040707580110440d0880301c012604040c0e10400a0300c15544280c407508246051300f00407042001040f041035807890b5068294644040355544801000b5420506031401009030b001100f240c0158242900490400c81c0b01d5142c80d800c0c9003461255190000780c66010a50a0b034488050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 807327994 1250 807326744 807326761
    0x50601080f0a020a0308090a1a040f0608270c0a06110d09050102120310090606020c010905030304181d060f01060f02060c07080a091505090415140904170d05 69
    0x4481d80408024060001c51140c0d4000070040c0540703200c007034001640007842c03a0071640e41c0c541c008060020b4018100300c000309602c520410340c0003801070604206480390b0102d581c5008440c00e40c400e0702d054a25190084031f4090b00207174a501c41798048024031404400101c150380f25113000000e015180d865064110107029000d2078484410030f01001d202c0c1d61344081c0482d9034041140b0403114142c000e860b640351560040045192100c1c0e00504105182c840f012558940c0410000000f890076038490741c4145e00c80341010f860340700e40d00c03032050502c14420280c040c401d034030f41002a2002080c5165146000e21074415070410300704070b8240070031082200050003180c4e04002081038601c2684000c10310703131900c801441070910507000040c2c10040007181003c40f551103040be4001074004909442640713902e0f4071028185801c0008c2d29841a07043c0198082c1040079490010f080300e100c0040c0e28000c4c510030060005c0110b000e00240c4035400a40d04041111010000030700a1a55080c400582440c020300d030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 807329244 1250 807327994 807328003
    0x402210c0403030504030209040c1d18070f180e0105130b091f0e0109150f0b1905060306010203120f01050a080f0a1b230f0a03151d0a05060108 63
    0x100318156009000a00c0404d9020060f903040c1e0358182c4020f5001c0c0c480d800c0201c00c2c0152980110050425400c440e0108941861114003c485480c010740c200088561142d4940440e8090b2a885c0003250208001c0748240580d0303083c1642d4086d8000502c1c6142d540c42c43d080d02c9040794040525110103820004004e000000154001b100401803d541400d460b107011261010780e420b506260b480b50078002042c00f083d4440c15110758080c0401101c80000d007000c1c005041103c5142c4111481c241910910382000c0d076088507006585103800c3c101e10b00b000c04225081d04090040340c11844207009205503103682d400d5882c01500b40d8100c29029601d02010010b508601c6c2c1c01c00b01a036001081e0618000d0741c005140307030405a2168180018104400b07005c4e8600342036038400040740c0d512082e100140d1203800b404034261003090302d0841e8164071741418080c0c50202c1c1d102c010721010900540101c690b00680c0000983d0071a07031040c6a8845100c0c10262a200b001c030f02c15a0141c00a000410040c1d00800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 807330494 1250 807329244 807329251
    0x21b0c0a061b02040911030109060b01020708010e07260a0f020307060c020f041a190f0e0606030c030a0b1002030306040c083102190f090908190e040221 67
    0x242c0000c0c410880c1001000c00110340340001d002e01e0b129404802007200c1c95950341c0a1140c0036000f08090901810070101611010004034054000c1138070100e6900010702928480c480301000070080189007906809258001e206010281c480361007880b03c0c030200510007114001d018011158104030280101340c2455260741c00031040c09882c103408401a195280b504056581c1214009000030201e1503002e8200c00c10220564000700304084c44000c0314142007801b00342c1c2c4151800301c102c1511a500c041440300c0a9170025803040090000a044580d481d00a5912101c0b11501107000c0030410301040304200040b40910150700701000b008510700f0144a166440398032440c10580d9820320084260110b154040800005c43c000c0c8855040482c100071110981507018102a6228105c190f81030740e800c4540c051403402c07071b20b6080c00064034401401012180da810181300780c030b44040503080356100b54480d0200020311072710111040c5e490343c56202810909400500c0781e04d80c0d040140e03032100400e0006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 807331744 1250 807330494 807330497
    0x602060f0106081b0c10060f0e1e0f040c05060412032d0f0203131d07050304050c01031e0e0c01140c070510050c060109020715141603021b0c0a06 64
    0x81c3c02c00c00708201c6000307810f041c1801c4d80c0c10580d4421907107594508000d0300c00b920220050400b100011900440507612044442e4a0030b000c005444803104842909491100f0303010b012862800b088800c450389801c5904148034241d0200065590008a030f00c42d04140e0002d840707444030044600625411640103c41d401000761401e1800e0701984244520b400810008410070a1481c4448100b5000700204d031644c2c10380d030140100155903003a2881252130780144031860444410f010910b45c6008009403405507500c50045d10148c10400c0044006150301000140d4110160801c0c070402c078400d1103200070a08564000e4401c4100042c009080044182c2820400480400440d90124004914841995012500000d1020360200100c41c58041d401e5000020b0103a000001000b40c4035034000c14200d48a8482e03080c213055010100b10860704504098a03456a414000914001a10611002c404618100181021800b000320780d9045801205450136902c500c1d98021285001c903141d90061a00c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 807332994 1250 807331744 807331757
    0x14210f16090e120c0708010617010e070b03060904020609100804200607080901050f0a0f0210270201020f0d170c0c0304060e06070605040317060901050105160606050a0602060f0106 79
    0x5440300d1a0392a880b12a9490b404440130960702042c0c842800b0180041403450001d12071140c540e1840d00400fa101002c800d003a600c0c2c03000c2103400003000302e50b50013202c41485070a407c41d958007051100c09070001340100e91101007084400c05030794440d50b28501c4c4030615602d218403460945414000d1010a4408040401d110650318005503623100403240040c0c1c0c0300500c80d40355458500160b82901030441401001e00c00440c80c20803070365009940410302e4803c0e508990030780c0b449424450803120003030b05202600c0d007181420441e44102200b260faa030381c810710441d40c2c0120780c01e104d82e003001c0a00c8000000180303050044a801c425045d50240c200c071120341c1c4d81d450981c404200c00c0e581d108521941e824002c4100c2420b03000c3d42e9000a990242e80c100600707010501e400c1c90014003869004100c0040c0d1602000800d00d5414010b5800303041e5201038403502d2030f00e45811482c0180d0b2014050071614240c50f1000860039440340300124005019580003041c0c070382003c050340c1501d00c80c142c0120003000007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 807334244 1250 807332994 807333011
    0x7030e0d08030403050c070e0910150f03030216050103150e07020a02040509030a12020f0a1107150f030f111804020714030403140105040218071707020607120614210f1609 75
    0xc00b249d00c980c2b89400000008803800214140b11b0201c82d50b60100d15440341058000080c542c0100f203a2082d2100c2e0b401102e00d00b078540006404440034411a000e11201ea554280403105401c1c1c42140c200031140100e80c2e00418540c00101138400c22950002a5040491152201d40d000602c0442d01031041d4015805c009810040c483d0034042c00d4a0f000402a03000321080c864034042c0020406014441076080000c0340080300135055092081d901d10019103880101c210317800075445190061064031900ea85040c10090b02c00c3c0b0b4081c070b42d507105684550f0030450300c00054256a0f162103590300010107183c8413407450800903100714148640d424103904002c20440160fa40703282c008018002c4010680c200d0300c034500101ca90a005910340703052000114280404690001100342c82004142e403480544001e0060700020f40300309110311407040160b07444541143c50002d04c070f034000d055900d0ba01003460015541040c5042040558101984c21104081d240110341014100140420340000d120b02c12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 807335494 1250 807334244 807334261
    0xb040b0d06090c0803030a020306090112170d38090f0705070602070203010c020a0b010603060b1215130b011803150f1b02031309060b07030e0d08030403050c070e 71
    0x3242080c02469a07958001d0441040000e11290b0080c1403a00201c3e922072908180c00c900951080e03034075034429916a40002400e1210380c0c16550f11a903c0801c10485100c140d00c141c007580c224002c0790000d0307525541c0f8942c01011002540506041c0c0c240100400d600003a0210401144000c105004540900030041c401525014607230b0080a2440c21566030089030a09070024058080000d41c5942400384c24003c01c0d500140e0907101900074060703030003140d0f41d404c0f007a8100c40d079a1007640846d103410b0240d8030003040e01d00d0702d056015003007400c0c4030340c1003000c040000c14500c5e070541995441c0342e0750744600480f940c0c05410400041d1034030f6101407659045880f00289030403140390301c1d50f00c140c881c402510f40700c82035041412007a602c100030030014988020b0207916500070140a0b218040026000514010b03180a188206c80301c4155840c40c1481c540c804503070101840e0751031900003450007600e00011300244000c610450280d60ba10307855008032030307006050404c1e59016118006d2954103211540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 807336744 1250 807335494 807335509
    0x1008031c0c090312110c0901080102031b03091b0f03120d0608030418051503010203161205130f08040e011410020606010827100c0210140403050705031e0405040b040b 73
    0x1300d0f420100c0a020180070b4003858141500340441d0008542c00001660440540256016100d001190080d882c25a8212043d40c041181c9000b240e0348001c01e000301400040040e0140c0c880d010780f0812400d1b0884010900d0411f51480f1040f40c0d1400244030524101d9500c0341c40c0207400340b84059071615150440c14170501503500380a042840d0b564020070a408500c0095152360400940295100c0c940207609030100c00544000001040d8000407500ea609a644544d40c0310b5100401d0010604c584d82e29418031500303000d9400c45070311804001c0485c8004420407068020020502d02c8022100380d23038140400b0800012909055500174020322919a03001074a46600024040d9882982c035040c000c04c601c0482a4541110a801f600c0040010000141c01c401c0460090b40c08961080f00304110706402c81e110506440140f02e041000310300000d1081008155540c09030701128280700e12041e04402a25140ca44c0c0c072200500068104043e04090042c140440c0084400b00310445011000c200c1300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 807337994 1250 807336744 807336773
    0x622120305070b06011b03023a031d0a29041109100b0d0621030e06070606033009061b061401030f020301061512051008031c0c0903 58
    0x1419403100015013140d214005291000200d4a4450144059820040d403a00421116107590240b124124070846441f100b0241c40c00e40595084044990080d03002c5005000c0700c10400d41c9900b0038484030340d164078204207400001c0d004105000c42c081d982c01c202d000f60500032009611a10f49803007040f000c1098200104030f00802600c0b219610f5840d0031600c210b540540e0088030000030b0200c0c00c0030a018140d0b201001b0b03140c2d0150349141c04c0d520700c1c2107400c0448035040c004000908258000740329090820240000a02c10071011a584e502c0ba503a00c00c824400412400c000c80748580e002d0f03c03410303801c025001d80c903000741444602207042110003850200c065264204900844000d1804c010059110141388010a041d22140c1c0d61286040044030000c20002d174465030a141d00407842e00b03480400142180466110307845070a041d092074030702402006104c4160203401d0a00041c440c82c2c240b000307110300d9010801c00801c510025442c401141e10406510702000f0312111305100080360030701034002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 807339244 1250 807337994 807338003
    0x307091107021e040614130e0a06020702010e04050106030b100e03070527100f090b0a12060f0c032a05040501080c0d090309060206070824060405062212030507 70
    0x909000444214580b105406103642d00540360840000d02c02010580f0000c8000c0c1c111040140304001e04000d80580c1c18454230b06000303070003240c2c464002540d550f0082440c04d2042c10610164540d4000040032034109a1040d808a44c445c2142c03045858100344010901c00303503080200281f032004001caa0f542e000703401000e0107001440161201d1210801c0c020342d0a170b03c1074064454a01c1c00302d6500384840154840c90071102c200d407034007191005044c025207040d0800070b044110b1051070312081c42e039464818682916040d0750744c403610702c0d501b240d40034503041590309840114110f00030001106060a11508800f40c1300c905e45a800d04440d030200480c0d0031a00b003480d09080c591113a2904070b04074441d1040080495142450340000c06800c60b0b0708600700c0d01140c080d00c1c0d50742c1c0c88100940c1c140104441070b4002e2140f00e00c2a502105425000b40c5035401c01800701d81c10b00e500d45001c07c41d140d2110359a50700441c40c0e40b80f140002c2200d2943c06010b0841e1000900903144544d42c050700340e0180e504000d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 807340494 1250 807339244 807339259
    0x1030c14041202031c1409010e03060c03060a17070603330303030e0c0a090c05040302060706051512060402010e1807030903030b03010b150a0c0803010e06030709110702 74
    0x101224410a495503509030304400c425079956480851000e50160000100e00034044d81201460310318485620030116001c1c1d40380c65003030600001c9080b1565000c014558103109603440510b000e520200106031041080f051030300d07902e081040400061524603440306283c4181c800040e454400041624012074520f800c00ac00d82a06862250650000c040005825085804508920b140f503440b2110216806500c040001605901885454040e442034103604011410f0041051150a41c010301501c0002e251003414140c0380e5002405035071002c3c0d01a0742c402e841d1002c2c4140d20503e20035181c030300c074000c6a150100c0712500d071129484043c003c2c006418024104201c40140c3c598079890412064403240a00491400d290050000c0440c1039040d000a450716844c184641014460008006801005220701112100d0108030079808001e45204100814468400240e0141d01440c040c240b940204901887e00e003090621700001540312029503400d20840301c070020740583c201c1b003c40c0c2d0140d0394407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 807341744 1250 807340494 807340511
    0x5030705130603020d0b0118062607080709020301051e01140c010207020604090509070911120901150b1b0a11060903010b0907030e0c0a0302181801090f030f1404050103 74
    0x90008003483e900180d045607134442c0660800000100c02416600100a034841444c0b030b0344682012500c06018801c1c424600701c959040c900381c006820140c0d070300c0e0f80c0304444181d0b031500c80103424040c41e54400340b411600400148003510300710040d29850001008100000c401c2500001e04082c400401e094554600040309440031500307404075600b454010385010b541d25a00e490034801001c04070350100d40d0b0301030b1800204601040b400740c00540d4015200c1c00307081411094150780b0300203000d44240b41ca50360302d440300407001d03102410040080c00078080c110707224850036500c500a83c140340059452500082800300014084003030409807a00c1c140c3d10325440e000c130348004c24010103a114107950f000f408001005001b81d81a00324400c0643c07070070700340d99200c0f055109110784c68065000095001c944440c01e1a0582e055440c0f43d0b500c00082c0084462011060a4050859207142d00c00d550610701c1003503070001c3c144c20410312141c80c47c480c41c0090403400020340045a9000d00d000343e504268858031007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 807342994 1250 807341744 807341779
    0x60f0703110406090e090105040503030c130504111216120905010b0a03140d0203160b09190501021e130303031505040e010e06010b070c450506060405030705 69
    0x248100409400980c1d9a0f48644003c1c01000c602d02c6502d501d06003400016484c01010f010b901c0c01194407400460139515618449107458010800c602070441ca1504005041d5486009900508201d0304071296240aa0b44c15407481910007408204007a269207580003d440d4072000141e134284001c0d0340040c803102c1c6031030a035000d80800d241c0268817480c080030100a0200c421103514807070380c14008485014007203d800b6078481c007564440c0d00303d0141c03100048c0003081300c0011059220703404009440c503407a0040f0104e06055160003054849079804155400103280040103400c1803000c15032400e05000c800740b400c0c076007160a408002d0805860b0603031a10365020390641d660140070024420f003d145842c4024a000b44a1a98112414030900000003003c1c14140c04456000343c11244060003130742132a1511101c0c403402600400021a110956000410141c3da014241c0b80300a050014000361b10314901c0955001501e5144650002c100c10842503800041d10411644283c4503c24002640c211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 807344244 1250 807342994 807343001
    0xc0604061704170d06080d0e0306011a160516050a050913080c0304091a09010f090207020d0b1806330a0306090506010602060a050621011b022409060f0703 68
    0x42044084008944d40f51304101c2c5400040c19144500c08880e210380c04c042c0110b480c810081400c030b800d03800500052000010000c024290300c1c0d040052030b4030348800c0c403210361500e035947c00c8181e075582c00c00305072065041c4001c9410300003080d08990036660641010000b60060101401c0342c10203c07105200d2408002407441541c17090124103064907142c0b0755415120010f003040030f45031080b81d04d600d540140b1614140b0700c0c4074162081201000f00d424201500b62000b5841a02d0907070f840404c0c0e03c407407000150003520741882210407a8494800e9400c6513195480d165028010201582c021402e00100145c884040980308451500c402004516600484c624250b15000640000d08000c500c074240803000640034100c4000340d08403a81540c407010681d0842e1010384039a5400380148004191000134100d50f0b5441201d0000002854200b500ca04060240e580c0210005a0401400001e80d2401301c042c0700c036504803050380c20071079140c1804001e4945500401540425001c0004030321128443d50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 807345494 1250 807344244 807344273
    0x60a020a0b0106051b010e0a140c0d030e0f030a110118030506040821063105040c090c030e0a0b2a1207050901020c01080a18140c0604061704 62
    0x71005521940c40d0400140f0a50100002003450100100c0e404440b000503c41e1507100e41040d07014142030308442e83e8500c82c07000b201c140304849204e40c4d035110002d5513401502100c1144039445110003030142c10306110309001d8221a140c0319400060020340442e0400d8403281c16081d0134a01140d4006ca84254000b0101c0c181d003014203203204940c01c200400c00b0324001410040c1161420b00303d00084160410040401120025044489500c1180c003849012003144040782400d040500126204000c0c0812100203d40a407148246c0c8038003041242d42d148100820304c001032a0901801004c1424940d491502c0c400081000b00610000388442013400d1016201084c03401c03408403c903480580003078691b00719400c58000e40c0f07400070102d40860b0058040743d400c6081a005484400d04120064032044c000410a04074070381c441002d11a03880801d8170500d1310307a1182c00d040703c40760780c005200c0c2e140450212040c1d010b51030811040c08200e41003034902c1c4401c801032124a100da9910305d0a04116030904 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 807346744 1250 807345494 807345503
    0x20a050118031410051b0d02031e04060b0109080a030801140a12140c01082403010e03070318050a081504080f0706051504020f310b0d050c0f030105060a020a 69
    0x6141443c011100072500314000c010141080c4810348504621000e40e01140101c1d807a000010080c01c203000c0010b4003d107900400b500c1001c178211311060750b0341a952004840850700c169861240403003542c0c224070400d01606041009104241084d0b1300a0f2203010180618200609203a4280c00b265440b0ba01d410080d0500c0320103140c01005c0752600003400220395030a4a00f034020074000f5440355201d0a4181e1180200821700f00908008000e8000d6a1003240e186580554840d0004505030004000501c16280300e0ba80c0d505096080c0d0001440850003508001e02c07483c01c14404024a50000038071010100c2c0c2418000150707203442c9858049272099000d80c1c1c9500c0d8010885505004056000c0c5100c0c490a0085d5124426504100022407013055444160034105200e51308449215640d04000c0c4990515840d40a06881a8443d4004602d511061100400040111140d00b55024150308044002001800c14511510725841c1d0700050088901881010a0203a03206200b04441ca4055411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 807347994 1250 807346744 807346763
    0xf250c020111010e011118010e0d02040209010905331e0d060e04210206040206180f130204240504180212010609090b03060906041212050c0703110604020a05011803 72
    0x5a4019801503003201405401c02070a13810a002e055025400e0207900c020000c0c00c2e40ac1c0c4600c150708103c02500010030042c10403605d81c8001c0f80382d03211601042d00c00c2c0a0080c051503480d2180b00007080c49400c1c4514068181004d0203072603500407005c0c0300c1010800500b013070262aa00c0084040700142880c1e84138044040d0306109000501410451800c650409008084100e9541c41816030703039000d087d14000d4024104000c00d034400600480c0303c6200d664010500e41a03505080300090880c0c0f036404d000c00c000c50380007504020a818158046c50800000883d460164a80341806041c90180d0711a41505544007460b52a200005074101c81078000315a6202840756140d410040152002d070149058061034076503203030914500016214440c091040080c0001d0781c807540c03100039031400e01076910148019006002d4804481e8060309229941e650300550326803001e41002405149690201049a0460b50511000d40ca0b6408118180c4000b800c04480c201d40c9080c1516544041e5031010b00141d81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 807349244 1250 807347994 807348011
    0x50405031e041802120c0c0a230f12041e0302130906050a20160515090705100503060114090307090222062a0b0f250c020111010e01 58
    0x2800700c0036200f5603496003505110310400c0300540080b0302c540d40400031041200000559104040401003540d18205029a2555180342d80d1761001545a41464550b000300d040c10703a070410404001c24444045880b000344142d9001a80350b80f01340c030860240304135a12140e002c02c1001c10035044500011030340506080c0070b61000030101001000c07180c004a40716420300d40070403010580d038020b031455600d030540b400f8049807004401403000d502c501c40c8401d2603090040e003040428024810004840c2c00381d25102c07410b103011140182400c10035041035218800141b00000c04130381c0102074035407009081c01c00a910130704001c00c0c81154010300c40a9a4503201d86107001c0340b0307141c0e19000381ca8180d80f0b000d82c01d402107002d213042480720740040c0200300000780e40d00b1500c49400091050603035006034803210116440810f4441e03015101040304c0c0d0700d21418420090142c0440b80b00802070081c80b426440b11000041040d00624020040c4006410441d1a04800c1e14030722081d4090202182c51200030001d40c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 807350494 1250 807349244 807349297
    0xa0c090e13030210060510030f06030611070b090d050307030b15191b0506130809030d050405010f0c1721010608070207081c140705011406120a021305040503 69
    0x80200500302c0c018000d114401c24003107a02d004010540d4070003040c1c3c44404442c0c400c110010222141d4100003140c450b000000403e10344d111310708185481d01c82e503558488003800e00000c0d40c0c5014010445a42c000c07900e14020350b900c807007601d0704401d0b2841d000c078000001c4c4002418400d90507940003180d42000070000580c2d0241c0c2140001e645c0d0383d44610b5010145d102c003c2d14441c900c8800980a0b0304900d000a14880c80354121030b250324403c41e0b1031400c00303400a002c0b92400441c1d40d01c040126a0018060050f0341e08642003003c1d0025a1402c89203903203c1e1790b500c80980c820700c50100244040407030488510404201409241e840c128103480e06907940700801002c038001650120050300941c0c2011a640c803011500515803940f0007150480c41c0c204030402c4078212201c1070b40170031003901444890001103080c0180e01c80400019042043d5081010400c240b6115034000003800e98000840c1c0030050726403240d00708800118000009140d0340e541012800d500c01c5424100c484004c000f510349200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 807351744 1250 807350494 807350521
    0x609210607020111032707121104061202031518100510080706080105011d030a1a160c1e02030a0803010608010b09010203030a090212070b041502010b090a0c090e 71
    0x251029802413282d076107241c1200c00c9900c400e0720021001d4180c0c50503500c0083d0041d000c001e104d01c460007105c085582d01c0400302581d5032990011500f112060740707001070910345801440003038104d00d2030003441800c480c0c2c000b0b03030358040f401c2c0c142c2200d9801c400000c002d0081c95100c000804066420f86851514402a00700201021a540100b07103484030400b1506000000340e520640e080c5450300e03052a405c3c180156801e03000c000c41d08100c220031b00310f80c0085480900c074504c100742c4141003d03e440c86010461001120f401410301c990307003c08603400b00d103040d4022030740d0000580000003c0400047c107409144581440b20006c2e4143c496039000b8070400c4480c000a5041380c0b610394610313805903207510940405108101020b40141d00510101f19480320300e074896086244002c01c1d010011100410740b1f4105105584268410300b400305081200040700394070f581518405100800a400e41d0f00e00062100501400c2951038564403854001c0c854007130074840340a8050103640484601d44010511001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 807352994 1250 807351744 807351751
    0xc0b06060d092603190b0a120302060603010b030f03160f050f030703030b18070e0301061e0501180501080f1e0a020a17010803040510030213030c0302090705040e0606092106 76
    0x90b4110300d5083c0c194980d0b02001e490003400b0440d0654030401024944601070300443c0c1289601001011002500c0c01502d0040e01095200b60094103052034154109400c40300c0040e0f415000c0d400c41340140410110110480d04250052904190342c4116810100c0e6142482d80f001042440340c09190010580c000002d40002ca20070759050142c18800410300c003501800c040050300d500c4451000ca01081c0c011480a00310074406030000421a0b41c410907808c0700d1001c007480c3c2c410441955400d22032968801c0f90120300d407042c596480d0242d85820002880c2c0d000c02890200861911004681c0c000c0341c80c4150032001c54080b600464508044000c24025032010000c40045500280302044c100d0701c24000604882c011401344d4145490082480900d03401c0d060780004159003040b000025020605040003d18002d01070000700c6400c41c4107000789140041e21007018407000784010402c01226000e000d034007090588525807104040c10114800383c4087c450000343c0f100d8a001c81c00d80f0b29001548510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 807354244 1250 807352994 807353033
    0xc0905040b01060504050f150c0d09080705060c07170f3a0f051b060f06030d050c0a0206071104050a0b0f01030e0a0219050a0e07020c010504060c0b06060d09 69
    0x1102d9076204420703961440380d44a0142c00c181542d040300c60b549402c58801444400c0410719525114140102d0350a05581e0b081b4080410b4064005200c203940801c0104083d113410360395a0300d45080b0462083d610f0030075101e40030000e45002c0c50303d403030441d040c0012200c4d4141c80c6d049035141c074801403201201d440441600310301440a020381640403c4026810f400f800b07220788a82d6505442944115542c2c0d00c01d440b01d0040000340d00c02c900702c113801040401e1080c200d6403900301660130700d0700030142403800c400342c00d078200034040c000c406420502142054009078100c4403550342c0c0034903142c403c881e8010155499072142c0b51104000c054200c58010a07141c5800325240d0800050840c01901140c070064081030941d40b041c4a81c078018280251082144000030704813501c11035590740050351141c41604401a900e00c80014000031076010408244285000d0800c00e052500b8030b00c0c028840b0450704c1d0003810849a03000452015200c100c01c03102c050081751803c1c010b04190b400c269100110100f400030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 807355494 1250 807354244 807354263
    0x250801051e13030e03030a02070e1501021c09090509010e07080d0c1e0501090f030f080103030f0305040c0e1608061e13020d090605040209070c0222090c090504 70
    0x400070140346040000d445084a062501a02c640316250094110100100c05015503c1c550708201d80d004c0014201d60040783e40140b601c24140f000ba6102c052010304003e08903c41072441102d81da0300843d583d003400b01c802d6160f18007010720100c11215484180c1c80444040e2400003407280065041d0888144864031030101c0314901e41d14003025039601c00300304001000a11610480d00081d043e102054502109507184401010103038076080c0c2115194402210f00c110010320f20410140c011000007855021070600c0e01035589540c402901050160307030304004040c2d56400050402c00300d210810054401c1d01602241883c2c00b0102c00b16a020b684c0150300030403d1000002d00e24981160112000340320300c181101a21605800d114220100a035440222078081c40350750507041d060b12030001080d009500c046100d0a02d801401a4840301500d00404c022114517241e0150b210612802415a0820610355050b40910b01c013000900310310344014400c2c088584000780310300303041d0469030040303000380c80740e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 807356744 1250 807355494 807355501
    0x7060b12070609050424062c0f0d0201020307120203091318080a110a06050103021f080c0322150606050a0e0f010c06140708150a1725080105 62
    0x3554441d100d102e94000204181020301135810309403c19000711032400c031905510b0072144c8940c0c1c5075089907003000000920701501800300651040c6546c2c41c80202d040e032101141403480115504529004829000342c194510742c80c00c5900c02c0040b500c402d50080d0145d8030004842d10000e49a03400010074602c5500304503141c01544143d441000e421030149244043e00c2081031b61800380c140c020607510000e0014a480041e15250144070035884c0c90700c203c3c4001910b604503c100510310100d0f0094544d00112400c854080641044007680c1100303007403601c580c0380e65440680c8214000000600812200c0c19002041044035034003207100d260b00444010301ca00764403903204032028002c0c3c803620000143e08825001142c14242c1c01c0040d8500e040c03406903c0d8102c2501c4500039070355004000f107844040c1d1420009810760111513036801c030340c0040180c254002c0c035400086100865000740d10301194400000c08034140304024200444590003180002e006082000da005080a481580342950030304000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 807357994 1250 807356744 807356779
    0x15071505070207051e0328230307020d0804080d030902090a0e210d0e0a0506070201200c0a0f0c0f08120f030601020c030118061508030f0f0f07060b 65
    0x881081e100094442c5c041e0642e00da181d0100740384410303561a018000c0140740d1081000008090090800144048503a03a9851030000c8081c2a4190b0b0881641d00f0021105105000801100c0d00f06404480b01c14001e03645040a02c40341c0301f40e0f44600007602c118603c00440b150141c00c44002c10703000712442e0100c0d64580c06100207940c000c00405259400658034201e200c1200c10300000324140700c02c849820301c045020002c003140e20250150100f5400b60322003c007006000c001a1781c4c00725207031000340202e0181d403000344940ea100c2c14162034a4800032031000f001c2c0b01c0c100112400d042e0801071043c0f0342d03a00c2c3e0402e90003600c240d010311620741c44440d90224140c40c00003080380e881820226828500108801c0c140c01a40026101c03034114003560302e1100c405da50900a021215001444000001c40d4038070b002012181549000d100b05500318604221226001c810358182050310360310725035a60050b148401e554846d40001c1d10400002069000601c40550f0003c6072140e425a044a80f03a640080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 807359244 1250 807357994 807358003
    0x1d0318011d01020705010507050c03011a040f3605070906050a0f0b0a320307020c040603080409091a010305010203060a1e05121212092811150715050702 67
    0x60490141c0d004c200c003000a94072800c000d0444501030b0707065403000b00d05140040c0c01e5a41c1045003501010015040d40c2071803410f40318154120060140c00c010790012000d80c55000305603007880500750180442c99400e210344101e40001003950020641d0a0303a41c40340710000c0100814080d40d402041c10000210300d005500040000f036070081c0600c0b508008544030100c9005000314480c0322102e0806025401c00b40789002286419904050040d86a1500040c02403402808036511403089007048010800f10f01001c08680585005143c086104080d0381003565040c05404100056075416500000c24050190b0185000758421100304100d0356848660110443c0703140d004001000c5901800c1041d480c041105403085040282a60700502c03603002c1c540d00c981c111400290082c403050041280100051044004000700c0341000308401c1c5000c2e40090224101490040c5a140d220309089581d6132102c56074004020090b0085982e103800c2d10300f201d0b0741009003400d21178150404012980c414008074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807360494 1250 807359244 807359297
    0x50105070f020f060405130b03160608040210021e070501020709062313020f0309060105060a0210151703090301140115140f0301060801080c010201060b0301091d031801 74
    0x140380c070381141e1a5020000c0c0d030051440240c0e4082420440091640c441d10001140007210050015248400c407007414108a0207001001c241c0d80012018081560000741c410741158050b01ca00c204864103c0f402d070300e03003e0140e40d844440000c6c989907000d2140c0014061080d14420f03425560025034500880c01511218002e8030989100448130407100440320070600c40107540284000340c0321000e4168001280c1c400000c10042800000400500f0582000034070300500303059517140e11300140560025190320b01d160803403412986032502200d184001c09500000340c1280d100b03028928980c1c060a903a20303030141501602035403c12600ca0000d00d904564541240c240098204403802c03201411034000558a21480301d07040d040c000108401406001385018002031b48501400307505101006140c54111401c103070440e818408207000c106031000990b411950355440c08200303c010141010742d0240301c0e441200c0e5520010034074580400790002c1c0040203000070b07220303800d250203102d2141441c0540305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807361744 1250 807360494 807360503
    0xd09081b1e2d0a020a1e080307020d15060f0e0103060c08160e030111070c03050f06090c150c060703021e0c030a0f051b010506010e1206190212010b0a0905010507 71
    0x1400300d148a124654800401c2d040c41d0003d903008a0125400121610b115400c4002610b410300030301740000c6100750200d0080c1c80440d0066080c078540707500080c1d0405500d04000c0c00b001c45200c080d4807064460700003002400c204142c45408544a11244503102130910056914a003007079580017100c1d0140d8240c40c01007458050480c42141c02450555580d04400034403605590390f01e15145040c1d44c120007030003442e0705c6510300ea0802403031400e0841c40c0c01070344910b1003540d40062040c00400c00d00010740c00504441680c0c850000c1200359942002e030302480d03910240d64041c0000300062282e06078007c00600050032101e014030321003244600c0b014000d99480100075442048040200e5006030606501641c0c03a02c1d00c1440e1407100b680104031066225a041e8407a07440f082808000e43e00f1400d04405a401510786135801c0d40c0281d0309641c1c80c6000341002d9040741c074001d07110012030215012a40007000d50000502c040d656140001c0145d480b11590500060402501041c1036106400f201c00e0103401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807362994 1250 807361744 807361783
    0x31106040b040e06040b0f090a0c050f1303020a0608070905040504141506030111090114030c040f0b032a070209151206040b0f040503120a0207060912180b0d09081b1e 73
    0x49d91413040081003502d070a201400014440140c40c082031200600200c903031503001426079455441800080e010310b42040c400d01500204010071075611650000c1155411207000c00c16880b90708240c40744a0110300d109002e4024542049401002c01c900c040c011401074000b00084601c42488805a0240040207030006006420740010f00c4650406142c00c0040007410074901641c5064a010303a1119a000440218000c4100807101d00d443c4000c40000ba00181100d80020240141c0301403407140c180c0c0244214000008030f41d046055100f50029a07101400422041100704502d540d070702c00c2220121014074080c0001087c24074a04151801194410300441c01e0800794080e5101c0d83da40103007079003a059828004034010800902500400c0c60280e01c0042c0703041c0c035030000180240e400f045520341c81c0343d45041c05c207c031114960840301019044200003a02d0801d038039001507035205944254185c6000d68015401074100444c1c00400301c403109520060510003200903544500041d03220f120115113 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807364244 1250 807362994 807363001
    0x1e0a05031515070b1b1c0911091303090e06062209110c011121090c04110c0606030a0b060d030302090307060302091201180f080705010c030b040b040b0a031106040b040e06040b0f09 79
    0x6c20341c00140303140b44a4a17088805800307a10104055010896035442e01c080d12513901402c2c9504010000040d100001041d10350b0328007040400d511784a01d00c080724154520340b0781d02011a50750b00090014000d00b000501500c0707030343c4440a125070412915100c15500c1c000c0035855544582c41180e8000c0288072640c3c1c2120340c1d5071211b00c59203070003c107100340324042c0e6503090000d96514812582030046001406460303000c40300e131052030110010a41c6000e079100e2070701000403a5280720a035030f2206040700c22851082d041d14048010340100d0f1001a003610440a000c140300d601a00503148c5048182c1c0c061503040b42440303040d400c2e86e201800c40c3d41034442c0c004080b00480c3c01021803440c0c05004003002860a80950340c0d141c2110664984000001e90b9604411090301d000d01940000020459052000410343d8000845058007440010314122509001c0012510340b002520000d0050123155034440e669140541c0c080c0008031501031155107003600403d1940780011109041000280c01c0c401e031642d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807365494 1250 807364244 807364297
    0x5151206041104030503030f04030f23030619080c2e050a030b100c05070801112709090a1a010b0a0e030304090c051e0a05031515070b1b 60
    0x3400205140b5401c00c120220100d8400c1009500402101c07076410482d18050400800017942c048006040001062032405001010320440e840701d460802050765946a80c00085c40c204410403142d054807020410014443c4c50203c0c04101400080c3d5485400c2c2c1680380c02000e10003185804045c2c480c0c0c50088801c141403086d00a0001d042a90400154090149001a9820740350200d0200051000c0c030300d41c000c005090005030b00400c00e020081c40b0304010380704080b1050181440701c404401c1d980d00c00000d110040740703c0fa002480050f000b4403107418880f01d0951242d00444060303600c42e0740416000380c203882c004812812286403000ea5400c0002020301101c00b900a1082c09034540300901001c41c03400031920451036280341355102c2a680d0b0441442402d800420800c00780c05503542845000d280766000401c403503015560442426401c010075001809140c402003030200580400320300581044112179450707000c0e10502c020252140c0c5040310454540c0f00c1c0e000301e00d070a400f40c0c3c914a588030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807366744 1250 807365494 807365501
    0xd08041e05012304050f0c0a0608090703171308070b0304060c0e06042306071707050115091e0902010504210609050321010303080103020d061d070515120604 69
    0x5481440040f03003a591214040d001c03103032807090310100d400b40001404204a0b04110b441c1413815860050035041803da00018204001c0d407184209102c40c0301d0002c0c02800d402c0c01010044c40d0b00640106240c162118000d80541002c030030b00b440c0708401a00400e56102c001109407c46810400300791550b0b07240c2e5549009031040c40300c40f4060010708110520b007a41c030600507202a180001c2d201c180ea000240a0700b4000041404c844d02a500400004c40030640ca4132244040c0912043c9407552400b241c07802c940102b40e440e60066050724a4103000c00c00840c03581200301c810b021341c200400318114400c0c01c0800c80d00d002c18001e011480030032040000100d0f000c64800c0101d48601d20021121198441005030b0f220a5000ca8084c0c0002401c83c420b0801255107d1007111103c3e0743d01525070640d80c001c2c000c43c1041c00081d12a2520624090030070131203401c4044074010480f00100c050034036402466450405005251084000c038090b0400f418031b034001d849030603c080080c00200d03100c041c1800020f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807367994 1250 807366744 807366803
    0x405060318031b0d0f0509030604020409050f03192706080703060819061b0807080c0d09030206010e0912090f03070b0708120c0708030f060f03100204080d0804 70
    0x207601050080103c0552419100d2001e00c402c1405051520b148035802841111001200810301405201c4901962400500103900c1075040c0c41c0012405018144a49803400d600362030351492000140c0d500085c1c68260514113118050340341c84000b1070100c01a0419036201d02c0391000180300c2d41d001002402e110704901500400c2e9401c002951075110508141007110300e1540803140d82c015100201001814459168000c00501540c484040c0d5100c0c001c100c81406400d04040102c603001103009540481c080301ca15880e019400c011021252401a48943e424894610200861000503c001d400420041481103001c08035030b1400f044c54081040c09004c40002941611134680040b500c4403c0030000d0620a01400c0c52036150000302c0ca14a101d454001c1c40f0444500d4144841c90020704c0000c00da03070300845c1035205c240c3d10350b07140d230f0202d0a020705082c419a854410456480080741040c0c0c010016502c00100361100300e00980000d07a086001601c004140e0b2515642083c0144030070040d603d075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807369244 1250 807367994 807368041
    0x80402062d0a0305090c12061b12090f061008280633050609010e0301090510090b011a1b0102040b18040c0221131502160b04050603 58
    0x103079400411000c1c1c4003600100b0b907407404a991441844a0080c0400c60840540000c0301c1c448000e04504048580b1aa0007900240d20005030700c0d15201d01d80310341810380d4410408504503600c24038000307141d56941e00403050188107601400c804150f44218100c4004180d445a50050140d400d010184c1669101c410b005030b40c0c6c1c06030241140000a00c50700a1b21019402c03124200004010070300040c004860015004010045d52481000a07840700d82c2a91078010003400c001c401a401600880d01411085200500a004051000781044419803044400c03d000c1c040d54140c682c0c8403040c3c5540c2e0307059181c2601700c0c0e440611501c0e011000d003a20304000c400d256000541013070782e500728010550b004140e216184044031405541d050429105507601050244001c0147c030400319691007243e4503540c00b41c5101140000e42d41140349004a60500404880c0d10045201c101b00380000d46960005a07220001704e0a5103002542504080a40d0203940300100040d02d11b440c0c881850504118441c03c048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807370494 1250 807369244 807369307
    0x10209031b014a0409030c0201110102030103030909020304080d06151b0209010515130b09121903030f0212040602220303050f0d0e0a14060a0207050a150b090901090201030c08040206 80
    0x1103080d200c9000c0d00022070720030780b20b07803050030512301c000f40c0841e8000c0f0001206038414001080401d61110702c4030211755070400c1c01a40c07030300c170303810100610701c500d4021141d003506150000070b0880c5440740300d40c540c2c101643c452132440c408541ea07681207110868040c1d40100e9200c010300075481c02c03004500d004c400c100401031910000a82e9908485210350180401c1000131840310001d082003003204e124000c249000d84030394030210400b031090144c1c2080203002c15a5411402c1b80403d040e40c110780b90004640d6404e042468a49403905c080d501030728200e80c41d400644404404000300410f0901600d60640300c09007000c1c2c4c042c1007400242c0203801c0c041032254031580c4800c1382e000140400c0d486103002e000b124a0b440b9002c1a1240792080c085c1c0800120707841000b1003400300d1004101d10b40400c0d40503100002010590381c0c1400504145102c0750380c0070074088184200310300158044086a8804e07282402030114403901a90305100481c0c0c0a500000d08002c5a4480c2c5e03008600350a040c0c14258405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807371744 1250 807370494 807370637
    0x8060f220525030608010b04270302030f0d0e0d020a080d0b0d06060b09040e0f030a030e030c190c060e0108011401032405241209010209031b01 63
    0xb2980d51803000003882c00f1941d150b82c1400950828002e000c20307500e0564090140390555800186543c1c18503010509090300f400015040502c207004170b80e003c244480c1d41e1900d0340070030100c420040400d0020148144961040d81200c4d60001c100000b586400005203070a01490383c0760b0350082e000300c0248581c09000e800202000844520841000c0d19203251642d894a030a1020700044920b414400602a071240b8189100030f48004100d03140c4001502d000300e818a046100640f450103007079203c02690041c1540b80311004207400045041501400100d4082a40c6010964509000822090008041900500c4100360810604400546c103150000c3c0030740040480c41414100c0c1540108031803003000c000c0046240038a03099944408001d002d00040d4151030648e01c42d44170744800d44085106140009100340d400398160323910500060140c030180300c1d41c05036448080c003134000d805010451a031840500282c03000c9901c039058104100b1415000107030400307050000020040d0343c49403e46400300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807372994 1250 807371744 807371791
    0x1e0102070e0c250f031205090705130b040902030d0806031b010801090c0c050105041b14130b01140313031d210a1b0911030c07030c14030a08060f2205 66
    0x19411307814000d550702d203100f1245d6021202690350190448459a2050740306000d41d82d04c00e0140c000400d0340f0880010101809001305020344070040010b503140c0034141d15241056001003003035204200403826101c000b007100744c40380e1604840c2e0202d240051019001440070709085e621103a002241418031952303051641d5601c3c2d00307440c0d08850403583e01159880401c4200c1c1c1600c5154042c0546400c44460311050303078003042500c80d107022074605c40c54a07462003115990180021740c0d590011301c504681c2e01d28184104510880d82d4040480004014984c8088520310260400307829a00003070042469a08102080000340c0109a91140310b00a0b000e0100000d0307030200001c1100d800c1080c0c031003001ca14214500382111100e82210070072000401c200312855030201b085030842036143c01d220080100c0c50416002c2c08034443c00d1201c1da4400022107180070f94005901c544a6a000c50b8034640000c600400e21031130741c03580301090704180c403180b14203403c510349034015a901c04035030303003140c0b501d007802d41035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807374100 1106 807372994 807373013
    0xc030201180b1b0d11121810020d0f0e090601210c031b020c0a0b0f19021515181503121305090f0403050c0a021e0102070e0c25 56
    0x421640b601e44031f40c95001d100c1d201800c2e030f0307078901140c41d4003075691a2901c4009001c07940420607485031030f10503552820800000742807100d003034850b4401916040c20084141c811640344500a5668801503c5a4038804903140d47c0800d1036400389409002d840b4003540e410045401494100c4040d4039070034a8241140e06008606a580b000c02d44800d043d4020074070910104140760b04d00c0b400706a4001442c03081500c41c5142c0010325211a01c09a001480725600a40c10110800310712003038158520142e94400117000400b079446010500107401c040c003a06c2c00c2420500c0101d10440c850000d03000003005090140d45440721800c4c07a07100303141c05500003031005041100000760003140841c00d02c041c0211503406085c940100300010521002070303181a0250f4014401c8071400140012441c003c9409940694002450700d0020582c82c9a000b2006d002c02010f8880450340c940024514003 = true := by decide +kernel

theorem cover : BRFrame.Cov 807194244 807374100 := by
  have h0 := BRFrame.cov_init 807194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807194244 ≤ n) (h2 : n < 807374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
