-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:44.680143+00:00
-- url     : https://prove2.me/submissions/1edacffb-6b91-4c87-8de2-48483f37d78a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378417266 ≤ n < 378597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378418516 1250 378417266 378417269
    0x501050a0506031e07051002150a1107031103130312020705010503090d18080d051903021e0a030b03070f21120c050f120c0c040603030801090e0c0d0605060307 70
    0x4056103060140120b80d80c00140b0030400400365101014080481c6110504003000c551010350449007181040303038015808610b800c0700001701055218282c0320060001c088820194a449410908000c881c0210780290a108103000b01203003224900346d20110780c4002c2e03003c0c80c1e108030391441c185403030249080d4061090784c020381030a117041800c62610803401036540540214034028001c0c03400813991028400840301000c0c00415080700c04401060000900607882819500c140742151890051064824000c56040715500555032140f80c00d100d203164400c1d80900540802c1c5941c40890001e192800d001d900024189942d0301c000d0540760a0b4500000d200350007412089a4407105607000194002c2c0d084402070a00d46080030701101141351081c40c060700d4070b201803540c4c40740b95400c010427141c0500810043c640081907500103182602404180c07900c41c000100400c110703000600412030300c0d80c0503403410700a4604035280449174001045160039035860581c0e00c41d881d42c0422101e404c080090740b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378419766 1250 378418516 378418531
    0xb071202010e0105060a121703040803040302060c040308040b0a0309060603060b0307090615051e0c0a120c03020d0e0a1a0306041419020a0c020315070206010803090d170f0a0507050105 81
    0xc40d18204c0c001132911b603200c0c000c507179103848801c0c282414000c4201c0700801c0e2400c400d800a66034106410041e605800c129421001803090384001001c07045840d095500701c070f921107945820b00303040100b020615000400c0400c10540d5940c01c000100f215401104020340c01402c0c0002e025402c0814181801200c1d0040c8182c20b0902800304500c8503001e080d0681e8403064030700141c55203040c0038400e600c584c10040422640801280e181c900301c1d004a000055548161551100400035410036544000f40d9a00500941c00c00c2c010b048883d805a4004103150100801d10710445441e076580f010054001030f810344044c040270041004a081500c5070368800c0300407880071030841c07404110310052258816882c15000d030300402c1c4030a80380e0042d040d40c0d02c8660b008003075680260030540408490343e4100c440c3c134010321a000c0002090131000c0111a20120054841ea40200c4c0310780f500407a9101032003081072841420003106076554020409454000082c0e03450654844141c00c0590035290b0142200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378421016 1250 378419766 378419771
    0x9080a1d0a050609090403020c12070f060804150c051c02250f0609061b02010f0b011b0305090625030207050109150c02030709021803010612030e090a060b071202010e01 74
    0x18801c41d0344001c281c1310702c5003049811101c141d4542c6001c908044001200c140c000c2c01040c10940e050f0000f090220a40c0e2050160040490303071508111211501500d02800c400602c48a900c0e8841c01ea80014400310b102d0b04050b03140c0302581040000384080d11900c000401c0d808502040001c03541c01c000001c1da50a880301c1154203015840381c0318a840c00c03107001170a090380c5d60980420000940c00c2840500486903503c3c55203500d200340a40a008260425102513203401429582d56008031019103035500200700d0082c0801ca50307601603809a210480c159072103031041c80a44981d40904a016851114905c100110a101454003078170f400c842d904140e0500c4882103042c0400f00c01086501c03288646840d141e9042c118170300110f1f042038400c1c1c11014030300c0e00000301070003442c80056044031002c02c1600200a519561244000c2d020260a8000c000a401c94048009031600d060710980003007421030001041c0da51144865500d50107080200c580101c041c0b4407010580d020721070488242a03501c001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378422266 1250 378421016 378421019
    0x50303030a200f1902010b1f020c0405041e08090d0c03140d050f09010302070f050c1e0303030a02070219060806090f0610050c010f02030a15170c01050d09080a1d0a 72
    0x10614900a08418991100b14410b0080d1324904c01d40001415030f40140515100c0c41e44c1d10803003030801c0440c11a00026200c0c02402c540c0600b424070450340300350b801c661600b5211001400c142a000440c1074255441d620a10460701e05a403842912000148034484401103a80780d0301c0e01c02c500007580c40d80c4041e030350800d02e60b90703c3d9150460112aa0703e040c05c4d48032541c40c0b0501c07006038003e000703100303028041e1000c1c68281030030010001030718a10800202c1c1e101200d240c070540584075548804522540641050010074814503081d0090312000344000c021003044112100c002d042e100c090384c818000a170701c0300c0502019042860081e43c1040c1da100b04c1e40d0403850000d0115080521100f0580c0400c0300000c0c00d244011000e500000c000c205180040d036880c1400c0c0c030b0440140a9014417551200800348002500a2423601c8660810100780007802c0000303d01401541c0e2600704034a02218640c407607130740e44002001d0380020b00c092002510b400a6003501628a83c503d580511881802420701100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378423516 1250 378422266 378422287
    0x1050a050a03091401020d060f090b0609061806031e060405092e060609050301110717030406061517101206050a0605090c07120c0b1609050303030a20 66
    0x84030000072103818003007084400d41c50000c801350b50032038000d1655440429080b071848140d402c218211303011b07107004c8240c5a80391021901210310258505078855420001c1500d1410401c0c0035202c26141804440000380360480490440d520440e009564503050b0540c1500e441d1043e041c036a081035042d50200030b689040d4420569030804e031481c441c02070030850150410300100ca07407c92113500416174148071865959902420008980c01814403d50822050110a03002034043e5002ca541140c8041002e107000301c18402c95910180040d2041c0f6102c1102080c0301001e13141c2856982e00c560348002c0e030f034251810b000d407100c08054410b10005101c107004200c001d8110610354806c50304a00001800e4442c40411801049a82c0c4455000b85140c3c2c200603603030301c90802415146000d40344c6003403a12214001210504d00b200b00007403404150102042c2c402c0320010421380c2d2110f60f4141040b04645a400080c512b400031201646410303120608481ca0612000a5080342c45000b241142801c480780f4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378424766 1250 378423516 378423527
    0xc271f0f08010b1206060705251703130e04030201021e070201031d03090616020a08030a0809030a021e1014060f04020403050307020f01022404200112050702070b03010801051501050a 80
    0x103180c00d12a41b00030940c03905000c0f040c44031412518130822003940c9040083d810f0b0001400d6441544446c0d2610310000d030b44500b010080301c0601244101c0803c4032824003001e0000c8480c041c0099085650903ca20055a5002c11504041801c1c404001e510350382e90b4400102520701410030280301a0215903074409914002080c0c488544088803000d844a0300210341d808125aa072001a40c4084100c90010300348070040300608001c0d81558844800d81d50360314105541c0c1c032078001d20000681c0300101c02e94035603511904d2044c00200c044203880e0140065603034441551200005005c0c0e10780000e044c0400b901c2d22141103585800241c40650419107591102c1d5101e0048840c0a8029090110700409070703031091008026098606c03184036003d0000b0070817a05030b042d0885040700c1044244401c1d980802000c00308200400c0141d58024407004042c4080340a003c0142c8500190701c02e219010408801b401c001c0d601800401c000000e091524107018182e81855400207818020700704030030076100b603111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378426016 1250 378424766 378424771
    0xf0301090c05060d020706020f03090d020f0601120c0305011b0f020109020604050423010b0c1005162003040815010504050c0f03130f1a0c271f0f08010b12 68
    0x84481541341d1001c5207814000c0d00c035004004110318030000f070140790700701a00c0c00355014504110031168580d04401059a1305d10004508111541c0240c00400c071140d22a00d484400c60305c03c03200c0800c01c503500e0340c2d15801c0d03d00245444044030030078005582d08640c41540400101124802481242038079000b20744640320324007882c0d0043e5242d0101da00580c940e00a517107001c0300c0341c4465145940c0c2d141d00044064110f0030f482d60481c0940b070300100c4001380c0f0340a0755001d0102440003041c10b40d03401c1c40035030b80c3c40034011510516840d1400980244007050000d0402066902d001e410f00403058807460240e1003058210611403480c20080c880d02c00c00440a45d007005141c0010207170781340c5038400c408410042400000348014031b001c01300001c000c40000c1c030b03520130840c00d5805c45407034503041c114081a0182400c40f01100281900d640700d5104803201d1940030407030142008107130003550240c900031443d82c0e0b103282010405800c2404070f4039070301c000e14030b0051450040b03107410711008500c88850102c2c003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378427266 1250 378426016 378426019
    0xf080604060f0f2c060c04090b04090b33060412020112110904060801020c0303010308070606030204110c0607032016080a0302070519030504090c0203121504110304081b0f07140f0301090c05 83
    0x1191406052910392f075009052164006c12841000d00d8507204861344203074640f40f03010b1444240991800b01400061001d400741c24020303c0141020306082d010b02034491089016030401410a03450244c40000c1d200d21184803004104aa41d20050742c020f00050301c4d1151b000c0f0340710783e10400040041d0303140841901d054a60020035140d9031242820007001816031500007030b50251804c46d022000c8407089004000120008042c6c80269958020540854a24010030039200345034410000c00e21107220010468a4407940e03112581d14030b26142d529498205842404c0030940c00a0100c007070010800100031480c28140c14120002c00a036001040340c0034a200b82e00c00c90f0385a0000004450092090f18095150a0031211103031500d200b249040c1c40c090310070702d07029a18102003d6183c90110703040700c1c03180340c125000600c1d1050302e10304c00b40303a9800e91400d120140100981d00808039400e000880c024040d480c2000120b44850040204903294121030301e2080c1c1c54403074820300041d01c000c0d03a007044440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378428516 1250 378427266 378427271
    0x16080a02120d0204090e0a050d0503090a1403070302070f0317070c090c020c0901060201060605250210020606030105220b190903180f080604060f0f2c060c0409 70
    0x5004026850110031011407149040e010400140840c002e6020380102c1d004814248004003248641070389034441d006014000f07030042039080a01038060001146c2002d01141202d0764031020303031940720a1440c555020410303034000050302420f2540c100500d101a041d040440c0c2401e5185503a1954851081e03800e419007140040707040814000343e05400070040040d1003051000c4811940c0c002d40355281480220310030100c1f03500120f140c0c0c1c8148101c0090391040d0701e82d1032609442c030418409400c070b0b000d004841c0d070000c2e10f0800010703140c9400b0600c1036440c94005041c1410b180080500303481d0000c1262582901c0584000044000b141d0010b4129800c002400300945801c030662a802c0c01d01d00000c0903250030200c0b04400c150784104c1d805c50a040381c84080c4c03002600ea040001c003081152140c40170030f43c03112000c10007182c00f59100c507d840390075040c006424410303040b0035025a040c06401202c1c01050348a000e105400c80e1712029041c0342c0c16805000103140402201403d0b021741d000d107205e10365 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378429766 1250 378428516 378428527
    0x41805090705150703110111180d02030717010e03070201050d0c022b02071703040303180f090209040e0c090a2c07061e08010905070c240b03031608 65
    0x10041c400c04014000103842c5080c82454031102e80c0c0164400c0340c0407000075560800c89028600d040c400c1d41641c00705881003a2800c0303038000001c00101454010103503c071405400850059504004184c020040858220801c0b4011211a800c540b880980c15032141c0040240b07100507a0311a0032a00807070902e000000d40c03213180c02400ca00e000d66801290130622700d6080e804010005813220908600245c0d401c0710b1a0b2034441031000850281c410b003940c001e60040c8000e00c002805002040c1040c1000f4a14061007940c0788011003210070320386c0c003a5141c9a8005581c0415007054010300d0344804508000b4290802ca19010501420004011121255a41c1d41d1010a088175040482510024444002181041007403642d00c07520385200e520b01041032424440084581c4e00880845260340e526803882c580c1c0380c00e518402800000782041d00300440d83c040100040e80904900d15200c2201e00300440b440ca96540810450f10001d02c140d00c030381c0c03040c003446030750b0705012801c46102a407020080d512070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378431016 1250 378429766 378429781
    0x612010f06061d03010e120a230d0f020a090e09010906090c0806100803040326160c050a05030604200a12020109051039081c02041805 59
    0x410454544800c028246080019003503840700807041c1850003550354401070503400303040500326030140070300c0c0c0e4058100030b0b076841b14000c0d01c2000e400340b250141441094040c0c40500f01041034220601191075090226031784805048a00c180341e0705444082d411450020811030103407016200b80715080341c2805a20000c3e680b03000c207420420300350342d02c0742d41800851218505214110303518007582d40e843c81600001035548914038128021648024003561409080d600c0da24030604040c042c007001c0c25010f4032040132442d401001000c03030320103a040f140800c180c1d0345003140d10360300c3c168400c61040c10407400500440e6001702e01c29070032580c840d00e00c070b4a064540004409001c2d002c0000342e80b11444040000c0d440c98010040c89566200740ea40c440c90b21f85420801000c03032000c6200400140000c0900040c0650a00d03040684240418200059840050303915803a10410901103950b2000071030b90752442002c10441c01004002d407102581400e040030841c041a5018020b004a0a40c850000c038944 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378432266 1250 378431016 378431021
    0x60914041115040315050603010546020d052a03061c140105090102031311030f1e0106080d0221090a090515010306050907050c010623130c08061201 65
    0x2010082c0c61243c1e00c840d528104010460900043e070761240342070a001070031901d418824140b007007901c940040d04880394109140000c2003030300c02510405584040e134143d4083c01000039000c9003114040587c0e61100c003411041a1003026005006a40c1c040b17048010b01d60045606040e0311074258095a1650344810004106142e001e8400d858400d0207125942804920762100f5101a1000d0003800703070f510b031640c005080b44421201080720100c0210120300103004217101484500000702142c000481c0c02c29464208074903500e21200f079181013615000b0704c4000b0f004400003440c5200c041c01052042030070103500c901000f8021900c01c076204624014611002c400c1d1042c00384007400e50881d454a4450303c8009107400d80d03011908843c0c420902c0305962003402200150b50b0040c28554450f106c0200035245a04120881d0803d5520368902041800c64800000002d000d100f8411100240130f109000c25292140380a640d11410440100744240e00030452540014042e80c0840c40181c4c0d04424500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378433516 1250 378432266 378432289
    0x3060e13030504232706040209060706051609060503240a0b040801020a0e040203090d030c020a020301050a0c0807110c010c11090406090201080a061a0921100609140411 74
    0x1c81104c2d48091400b10707200d40d440b0810142c261182c2142d00d51580d4520101080580662402003001001078050308041d000341c25180000b0b02030a04120850b41c940e400d032041121981603008611500307600c41580865603800a02403810308600c4c0d81000b1003d40c41280140010103e1407445040d0381880d5101c0301482c4005000481c135550f103031510713030b00d05601075441070b449840003a00e144a000707180d14191003100e0084407510000d04585059a80a802030902e071520311003540540a00000075860a000b21b51046c42440b200103548134848001801c1150040c1503402045200e52801401d81c100040e458081d00d000d0812400703c0500b881c2260f200c5101c5050183c01c01c00304428401000182d820100d41280700342c0f610f0b0020382d200d014070700440d5800c1c40341603220580184041034030242c650040c40c058402500204408103103d00800007080044a01c2190354007016480941c0d03440740c450b450103485404001c0c0401c818181100701400005031010b401e009007684001c00700d6646031010103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378434766 1250 378433516 378433529
    0x3030d0509120403080301080738040906140a090c0f0e0609040606050c0c0f0303090d0602040f0b2106090105060307110d03020901030e07030f0813030f12030c03060e13030504 77
    0x50f40c840e1240360454207500700307111321619481a44400700c0c0c0600c155100d071215070440340d0342c0c5e012028140100e110207100c00c00303589100f0508100c0414000e4450180350054000007650a41c1c0800d000180301c1c2d010155440190070b10714160008040c20790114a108407c00249030900c0c2e000d501d82c0000e9081c2c860b03521026485450b00100103840c0f600302c00540040c6c5141816248258000018062646100c04100d0343c1174000301f16460452078090507112020b40a28030050078281c4809400032035154a4211082800c3d000c200a0054032881030132100803000611054013504020b00401d80700c6906004040c807038940440040c422500c601c1d02b4200e6180f0003402c4030707803010f2014400303402584900e0403140020b0401034414011040082c907041101d501028140f42e0302410b4480b900c00d500100d080e07144f05d00b860040000841c18803024428118002c0501810140c01480040e0464100c9181441414140f4000b00007450b041d00c000743d8409080796990101c0411482c00301e13041d21940d005031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378436016 1250 378434766 378434803
    0xb0a0b09070908060f0601120c0e03010903030b030d0504050a05010c1a1f1d010b07051203090c040e0631020d05030a0f14030c28080405011a03030d0509 67
    0x308040b64003507440001c035a81001074410325169811245a480c04c01ca5007280815107054150889098960120790300304141c2ca003c0c15098103490010b42503c031803140940000ccd0b180c00d040d5200d45401d004a1517400c40030b09000d4034040c50980403820a882d50311400d411701201d10044428400117023015028416000455079403882c2440d107100c40035012107900d0300411402c0714045940440c81202c03c1c015110000e0700e82281c0e10342460f880d92039002440803580c0f4050b1000314072201102d000a90b00494408010b410032008034400e100c200c0b849528480b4066001c00280402403521400f43c217245a44c604000540c3c50810340300e04c0a202454100030b4000c5207600521003841000300c01342c4900031f103e03aa074660901081c241143c401705041d4000c0c145823001c0000ca90454804002454110900c1020000c054508444900d08440b4030040f403003c034400d4010001040028071030148420150381e1001c1140e102007002c80d5403400b6142168044954603008a064400c00300a46455464080d844c1e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378437266 1250 378436016 378436021
    0x80409020d060807090b010e0910080303010305210f030a09140f011a0306010305071701140c07110619080402061213030306050102070308032d0106110705030303130b0a0b09 76
    0x980c0c0042850b03203d40c440c540107401021804071190300a03846800416034410b07400c00030358003c0100583c000707400003e80c2100d0410028214900744041c0d402180202e000d00200349900d0b0700c11284010340c440003820160100028100b40c4640010341c2d8015030820710000d14480030707103003102c0c5211041c2d0041c0400c0c40390300c40d0801c3c10601500200c821158500114800c0182c1506150741c4d41800c0c0002082900040e03002e00c000000c600700744602009400011441d0000280748000300f640584140050b0131001500c0014003620366000000d40006a46541c600141c0346802003586503009100820011520041015076680c2001d40f8a00c041171740001c6281d04180c41065801d01c00b00c1001c0b8003107824000005265800890703a01f0403243c02c48400c500c3d5990b40088040000ca91910307100d01506594a140c0840740160b9045001e041e9503110020300d040018403080c60040d460f84440d2103603108000700100f02001c07007d90f20250758000c01c20b01564032a90000005007400190060300107014208 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378438516 1250 378437266 378437287
    0x10320040612260f0c120a0f0806030f03031501030204080114060918060411010c0506090c1801080705040e191b120b06060a09030218070305060a14090408040902 71
    0x6898040500c00c0e103100c0b040300804082890304a03403d41e01c045481000f4032040c940c2903c0c180c0140f540348150070554071039001030503408800e5008403580c5400200344607298411a81c11001c050342041d0101c0040414452540b2819981d1100500e03140c1100800341f8843ca00fa4000c0d0107440c05011850700074010400d08400040b00102c0845485104202040110710640c42e41c80401040e8841c4502900b04c0755540c0e1110340c03489600d82c10a40c10029800402e0000c03e02c14401c1078041c11400d4041d11414900d0000c101070320b01c2c1c0100074040d43c04180010048007a00103140307002c59405560100700d041c41c004080e070131b0036010075400c20b07000f0b030084101c000c00c00c001c003103520043c030740600c1614110344410786160034042d1042c0043c1a06186800708686150503c090003003100c0c903141540c0310075144d6000c111407003002800701c0091850728050000b4540c042c000e144e0302c41c40c1501c0d0489114a0980000230840302024a035020f210382c0d07000300b07090000030070448018000c411400c2d0364551a090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378439766 1250 378438516 378438539
    0x130303110f1b09062407021503191a0a1203090b030a090302072c09070b070b100501110604063c06080105060112020f04091b110304030b0103200406 65
    0x2e0091003003031101c00107101441c2240400d5500c00c600c0310b10720004039250940d04050752089505a900c501e55600a9400c4010500118800c03141d4201c0c0b070303d0302c050000c000401c1d545403141150380d8210b5107032844241d0303d40000c01002c550140441f0507003010582400da80d02600c036002400d2a0800108011011900f07400c00e14129200b0303402c6a42103991140310f000300151382c440408040c03201c226540707000402c000c080c3e60005080310581d250303107a0b20100c41446a1040d40106c07080280e140410180c02d808c0592900100420300f045284c0b0280e5450450b110840280000c1c01c803a07a40607168041d028a055144095400c0801030f825203c682c014042104004100400101e0801002140407030040c02030030b00506042c1c407100021900c0304078950180d045100042d07045002400b0000d50041c60303004040603074403131120382c45911f04400c10003000102e496518a0055100300007c01c00941c0300001a41140e400c0380c3c4000c086109100940e03288852400540d0740300382003c4021444e02241e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378441016 1250 378439766 378439813
    0x501080f070b0310050d02040b130603060612110d0c05100c0b0702010b090a09060b0a0b04031407080604032607030e070f080c10050f0706020d06050402130303110f 72
    0x300c2154140c0e5900e100d50b94040c40212020400e10000d00b400308058146032162022045c4002e10104071100044080b07900e00641070002e480c465201c000402c00d0000c18421800074051003071058241c040a0389440800f000b107100a1400740300d1944840d4188001d00c0100c0c8061b103801001d000480c410030038020b159121044007a00c000d8240d03070105401c035005108070000e0a87c050300e248a582d071600001802016480c200390345a83c2c8800349400142e407654041ca02510300002201e4495086061445040d50a210f04e0500e5501900c010702400d02c0000307a607039002d46e2603d800c14408000c54641400880e1592500d151070303d003003051140322500354009295804004086130041980c03020441c142480c90b1090300d0050704201c04481007070524401140c80624181405450b100d0910340002060744501016625141d000c00c040012413a140903460041804581c2981440d00c1080160101c1c145031000400f0b00c032002c144510100010b2240032050300f4071009458071b06080e40241003005404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378442266 1250 378441016 378441043
    0x315070f050408100605040b060a020a0201180801051603110a0503040b0c0702060d0905060a0902010801090203100806010f03020316210212010e030c1504080304060b0d080d0e070603060506090d020f04050108 91
    0x4002c2302165604000c0140c40880d0032a6006020084481c1c0054800b00100c1444949181c1902c0000c03c0091090041500800491000e81424039444200078200c1d115241c142c1d40c02d5200b00040d0a50a60201c00c2e603800c543c000307905000546861808036114440d4500080d00075001094203818000a94010070025001b081030b2002c2b640c51282e080121850700030f00902041090700140101c00055010b5a4000084404003480039240c1621071310f8071809a0042ca1118010001401141014000d1100e2101c041c01503080c401d0809086035462180b407105100f0040e07602640303400b0340d40c45115098100b60060b0007004016080180e41d5102e034080003027022588070f2082e002c43d00194195130301c0c0c807035600001c1f8282503480d00c0c1c1e507074005448004122079000d0820b60705603010400120082c001f58881d120300084441160800341c0c200701c0386074070817002d041c5440c204004c681c80780750884640390720444007500b01c0800c91000500c0e001d100d81406030840d00d02000031511850005000c0c114111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378443516 1250 378442266 378442271
    0x21c090e1e090316030810030b01120c09060e07050c0c100c05011808070f0f1a041a0601120b03030f0408031317070e130b0a05070e0315070f05040810060504 69
    0x2c1e04462207a903881402400d101400d03580c2c01020100c0d1140c01901e030403900760b925510701e0543d242c6449400c45803c0e0007014041c4082c070044020400681c0081e0020710380c2c000140244c9152568080d4400b10081c0040c05200c1c001a00200700b05080c041c0c0f10702e0907401000f05050403d103000080c2030946801d404c480c41d61a00900300b02c00744101c2d00d5909072079440142c0d03501d401400c1c0d0320301344500540d40044940c10200c41c06100061050a54000b0040d44480107070110310341400d190000c100d05421110341c040000701481000d076808400c040340d00304140004160410701001107441e42c414220300300c5007940d01040110b01403c021004129007804040395503802a11400b10038450700103031440c0000e81c4d005c50020840c110302ea8a009030700c01580b104e125000841c85c2c031070449001c02103070010342c83d50359041006401a0440d480b2607640d03074154003d04400703070a501c0c00211440c01901c11707401e1013030b0b840d0120140780c46001118098030303003401560200c85400c0c404101420316800386910450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378444766 1250 378443516 378443521
    0xa02270f161409012609030307090905060904020618040f02040303090602060705030a090f080c07080d02150c0f0c0708030301090c0813110103020910021e060403021c090e1e 76
    0x18464020301108040b045a80c900e803003259001500c41404054000b081d50404400004540040c0506140b2034004a4007443d52840d0184005100e00c0e030726001100551720300002d01900703480d004107a40c1d01c075605949281e1b8904042d08100c0002c00c071070784c10baa800750a000c0064042a05500900704507407003619800401501c0341000d07a102e4000b140e0f41c40c00103100b4000113480c0d00b16030300030702401d80c0142c0100e442c012154840000d2a8049440c8020a600001080083c040f08000c0c40d00e0302c041520140881d4107480c07034414506003000d40b1641181070041060002030300d40030215500c401418003103c42c0341c0c0da20391000d500c4e600248107102c10146845501000240500800e07407045c09000013050b49482156a1072401e003d0005e400da0401d5401d01c030001454882d010410403401403030300100030980d0a11003420071880204c022171065007003241071000090300001e940b08454484400c1c0180e0b00c481100440300030b01107034825454030000340e0034040700c0f8820201003150b21410451064460307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378446016 1250 378444766 378444811
    0x6030c0f0b03070c08090109090c110706050c03070f050c0d0f14070501210f06080f010b0d020f01080705120103030905010f0c080a03090606030b0408041e0501020a02270f 75
    0xe0004445540201d148144d4220000703581030028004110141072050344c0700d49844d40201101c038417142c000041115401d851924001c100401d80080809142652030600103194007922405030b55070080c501000c40c0c1070401000b8003401411342c5000c3c0502540e68086a0b41801d10005213208025102469115070525112001140780340035100182c40710300c05240c0d01d0005008042820700b4541065a491207500d410200c14020240205104d40040204060505883e800c555014081c43c1c42105c0307205901006031100e15a003c10030f1070900300301000350341d019410b803030030300c18011030703450021080001104254014003200144d85082e41e8511810380c101d8000d9400184219001e4914402803054401c980d01c07a80001546601c190301c0420702d17994035541d040490310180c508a0343d803500880d0501c605a1202842c80300d00c2d240d018a010507520308070000c1c0d29100004c00c082d018142070002045103c020707142240800d000000c94580703501e08030b0320201d541002541c66080b604603181c10039019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378447266 1250 378446016 378446039
    0x41a09032e0b09011205010b040504060b030d05040e040605090f0102030c0711030d140d060b0c071a12060d111009050f03070602030f0c070f06170f070804150f06030c0f 74
    0x448000d404190f4903420113062444a5201c031038111500c1d0f41f145082c00f2151601d00030180140d1090501282c50581d1004141c00e1035003152840040200a0008101e03020b545007119401a401400000b0503440f1840120300b0085200c2825440790300020901600c804800300411140c0d00840100c580361500c941003607211588143d51400042c006404c100c1401818801040e800c1d28042d80060210340d02c05045c109604503800020f01078100500811103c0d2080050701c5210381c01084d154609401c004805a010070050420340c0078804201c000310411860013415030741c0c00c50013403407511003490f14a001044d5440d00e000d040c0c0a000701e0402091641400503007031083d40c00da83c000e075003003c900b5600040d0783c2e00014074041141c031401c880041c411f0800c4031040043c280707075a6040c0010000032012004040003500004440007034008001103503900111720707600150702041c0031400203804002803016201d0171940c40e81540c6026000400c0240707150b0842c044404c0005191103140da240f0000d85c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378448516 1250 378447266 378447281
    0x6100309080a08150406030b0a0b0f120102040e01060207050303120a09080301181b0c020d02060904050423070f091a060301080703050f030406081603020f120103030315050303041a09032e 82
    0x48d840d6a0041085c2c1c030b125400060300d0f48405044158548030100010360100e0004c0442e0f256a54000b4043c45001c0b0480300850241041e40000c088040c600800700b50381c0c1c03080f183e6000e081c42982c4003142ca01007668100726803080e049241b0b2a1030303503109c00d2030420040488885144039032601c520344100000d00c031420850318809803107000c6540d000d174003404541d100c6060104c0e4000310070044008541c0d2544103081c0903c0c01500006018130031108c481140700011100030f0303107940c855402044550320301e56807441540c55040d000324206400079003000402c11060400c3c0c2d0b101c035000c00045090031001602d20122402801140c0403104003103449601c91003070f4010342d00042c0c24000080d114003d0004044200106480c0040c90441000b803080d200d07800110302544203406010040046c50350502448140303460ba89152607003140b405000a40d03903c03032480f418101d07402410740300503010350401c2521003031603019050795410300000e001d01041c20802c0b00d103042e119060700400c0f102c0d00c0943c0704408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378449766 1250 378448516 378448523
    0xd0c0905090a090f020303071109010b130b0c0c040e010b0a0605070b0627010906031401021912020d0207060c0912050c011209050d020a0309090c0806100309080a0815040603 76
    0x554644402c0309450107400800819207a81c1d81141c21480141c13820002005071502541d8074038180d40f0320004110030b608060740b0211502d44140403031080595440c10090480b01c0001c0e40d20b0b600c00c10880c201e070401348168641d90340580b400e00c03800280001908640a4600201c900e90441034a03010240c4140c0603640b000f500100850b00042d0103414180901003580b9080d2819002040b80303035942c0b24058000360440c51045850340010802c1148054081c0b00a501001c02076041507126500200a00354040020301045500303034201c44896003a50443c1c0c1c54400d20481275503600360504090002d094094204c0d40081c0d02c400d0002901210101810301e1680c0c000054401d02e62004011107004407084100505665030741d603001d00140d0100700d503201c0c2d40c515801500503950a818041d02c110003036807088035010304001021180c85d902402e82a40408101e40c1c10384180e1891074120001c3c0100100188546d00006003003032900d0304004c84620a89200303800c150b03100d03010740030f01059585071300c4000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378451016 1250 378449766 378449779
    0x1006060504030c03080a0306030803190b0103090b0a05060a09141008030915090f0d140f060603150c04080d230f04030f15050130030e0607030306080604080d0c0905 72
    0x50001070340445c0103008101c00d43c40c01088441d2681c849400c10341c800c1d02c0c18109061290103011400340280180b40d0107a5090804005045684d01c6084000300010296060282e8401c005511b40d40c402c180e4101408054104009903621030784580c41e01c06060303c0400c81503082d24000070300010000111007052a019040300949813120800d819160002e44426a03c40c2da50310b08190756490b14081080b03400d0080d004000d40c1920303565244d05210484580302c00e0b9404c400c081000c1030320001406648000500b0304800123941d5254684558002c5400150f20740c040e408580985a41c40002846100703100001440c4800403c3c10700c0e01c01c0d10540103808003d403000d000800c00309507802581e2404900070200c0c42021009503a1070300c2240c000740c11218a01c0c03031043c50700440303200401143c6201d8100c0402c1c0780340c02d8860744003e0060001c0c0c841c02c600c6001c00142c1c00c01054801c1d003200d402030441c6400c8070202c2c201454909a2604a1021400c00918154103006040c1c17285800600721940540b14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378452266 1250 378451016 378451019
    0xc030307080d060b070f1e08030c0c0f0607230304030f05090f10080a0e0304050a0e0402130e10390203070c0b030405010c050c061909080c1006060504030c 68
    0x740300158100410702086655903c4000440d11492801403c090b84907800704a03010b809490104115a25041c0800040001c011403100244182e4212504a0200c440981e21154880452071400d05003c1e011401c601036070060004490304888410890850142c0e202c1c0d8034001d0b000c000003075000c12100540064a4a080021404d008034000c03c10300c04081d02d0b0300c0b0795240c0c42d00803c190345010038181001440040420002c640184204480260108007075450240f400d00002d4940c0c1840c01141448803240010404550302c400146901c0c000c46542800308031809105980c40391701b003512485029041c51a5803c4104c130b190341c1510114442003c2883d1600212105414881c8410710740041d07110800140001ca03020084250040c0401030a96940b071425180082c20750300c03d03c0c514800d102090025070320386540464940d81c000c40400f15031244044110002d4060f00d01e26a01510015002920328006640400c03e42d12600005800380b001075542d9500b207440b8403c0d8840584640e900440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378453516 1250 378452266 378452273
    0x1303060209010801080d050d05070905031506030105060f0904060b01030e0609012304030f0e03120c03041703031306050402030c0901140f010801060e0618060f0715200a0210180b090c030307 83
    0x10490308109140360040c1c3e5582c9035000709140a030342c0c080446910400c0ed082195510702400360551019050b078075204504c06100106413001c001400003040c0640350150100381d40d1180c2e11080030710051008031100e42c140b4900060003000d00c20020384030326403105070741a004002d40044500450381540e4603102d800c00c003803040b1020070044a541d58903000d8101a16802c82c080c81c00b40c0341800d80180556a99881d08a40481c0c207441788403110079903001031040000a0141c0d840c0354010641208011455075114400170342000d00d5414400d07440741d880c00002c54903200b4581c0c582100d000c01e03600c0301500079800005481e5034409100b440b000810918292003d402c151015010b02200c40310000440c051000005a01e6004003a07001506070380400d04c00c05020a40f40c18000c4442c000d401080b10004002c40d0340e0000303a00e00d425000350b03000016250601842000038210381030b42401f04001c602101e4046550307140c078821040d900c211044000c02c0101c0d9010904031101304006009500d031829565 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378454766 1250 378453516 378453521
    0x30606030a0c030b04020408070617070e120a050115090b03070806070c03020f1b030717030702011d0409061b0311070609140a0c030b010e1009020904021303060209010801080d050d 79
    0x40b025081507224050002c1c1915140045c2c80a0400140034005103420801d00070314030080029109000030410b0305100341540c010003100503c040503a41c0455910f02070703240e14a00f41c081c1400030325139880c0c031000e1141c2c0e41102000101303070741c1c4255080c4003054003001003540d612054000c148860f041300c80890442401010087c0185201c4c0c01680c800047c4045500d00b8240084001d6103c4414180e440e0b08924050100c10f014040d1400444041e641800c0200c0d40e0b8014200000c0c1440341054091400781501c000c080b49103c0001c00c2880700382ca840c40c18001411580118148260b8414079101d1a103001c0d000385007060070103421443c04c0a02586852000d4220070030141d816984a8040d010005010304c042005e0600603000490403502e140f800340c020a0050f403224541c49141740a1080040006090074101c41c0c6800c0007603180d50324500090001d1250300d5031000100051b0100000300310039500905403619090300c81c01c444c1c0e84c0c3c80d400c0d962503441e05000381c40080c0c4100080350317403400e480c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378456016 1250 378454766 378454781
    0x50a0911011b0b0109020702120a0c06052809090b010c02030a060504060b060d020a0219030206070c032c040e01142d04060218010e0a26121c02030606030a 68
    0x8040b40504600380c0d101d9207880502a00701200090300015000f055040400004101000000c02001c40080546071084109501d00a01080103800039691420110900d02070801481030f41c1e049611100541020b408140700d03210304040700e42460340c401404d40c0100115176100b40c000d005030075002c0c020f903034800060400900840703500d03594404c0003505071107480103007500003614040103980796900d01e40a481d0508003a007048004071121300040010b5804200c1d5074000301c541c1060301d02d0315010325082e591000102c0380c1c0c51900c0074004101d0744200d0b81100d003203035406040c0c604000d01000d411f1018241c84584d900c0012403c8030a0125030b5019030800f000400110706111101000c200741c0e40d8044030351040d58103a50b42900030909150040e07030103e0300c0e44000000d081000744491000c0c04070f0307409030f41403217003c2580503a540220342c80c2e030b000302c0a8246040400169000d0404941101019401c8403800d0040c2d1240325500c101824860302c201da0140b02d00400c640c1c00d581d280300d00c64001d02201d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378457266 1250 378456016 378456047
    0x615090d060e1c0e0f06090d140f0d081503071205120d0204050414070e0607110303071202160b09060a020307170a021515010305090307080a05030703050a091101 71
    0x490a901040140c1402a59000c3c100c1034852518074401c40b030010880010315100034800d0a03a68014a51951840c1c00c0703a40307840081e104020450710500303040d150521728004d180c0c2e16000e03085139104034900c042852410413003941c55128060300d4603541707035148010003031007190140d12001c1c5c00e0000c2e80082a40c40040d034803840031102e00708540fa80070965900600401092560041000d00c064a40740c0564a603c03c126622075007503240003100105240d0790009418002e44001a40f4424030030880750606040d0310180c116551840b40340b900b05200001c6022103801402041c41014402c005502c004080b80c80710b28909090103038004c1000440d6114802e08001e5210801503140010a5814582c0071035828104c6291a00a545c030040c0c20b10f1301c0c500c0142c0c1c5000c0e07002d0410050a071203814002d120390302841c00090b940e0380c142e0014075510440c580500705140209010301c1c00707a88030004520807425640e00740200c0e10745802c050107403000d40c44018611749145016511952140c10f507040403048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378458516 1250 378457266 378457271
    0xc0f060f061c060c05030a0b06090d08030c040305070815090a150c090e100e060105071e0204090209040b0703060b0f0a030b010e040204030609060518281a07080615090d06 75
    0x3a03803443c048425808802010800c080104940c5007524400d145005c482610101d107028010b0000954130005580024294a00400881e00040c07490040c2c601855000048a02d0207846000b25959001e030300c14560303004110000040e96440300402e401d079000e0351040c1880001000f000b85403001d010350f040760b0000c00205260000b101040c1451450148144c50114401c036400c000d04031124400050445050180c10003591000860000381c80da04041440048108000c05100280107403d14180207980034401d9018001845a05581a40a01125107042000c10740d82c0d514004140030b0320150103000a401d0249100941c0030707411039103495005240401e0400303080c0d00050120781040e0002d0352015507841088042000c5072142c980c014a030310540035484400502443e59441204000110000c03840c41005403824560410600b11640301e0401510910004603c1c0446d0b00b003102c1d0303040002c0040001c50240e04001c012002c0c0103a190400e9460880d83c4010b1019020850a0440f0717041e6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378459766 1250 378458516 378458569
    0xe03040501050d1a3106231302130e07080103080a110a0c060207090b06130303051e030a02030a0c03050408090f0a08032107110a0f020d12050c0f060f06 67
    0x613120b404010802812820603d0b9a2004250104800a8005c00f02c400b8514161003401920424180610a02d4031708803100c1d080300001d00419100807800b4910305d9500d0000c6105401804800003500035202d681c2030604013070791000740803900c1031000c5c4006000c0281c104400300d40244915202032070b4400400444240f00d0443e0307290310610245030311140058000030800e00c00c0e030ba00d6004140452100304d51150400c00210f4424030814000c1c48010240000011a805107421403050030f6145003903087d2035916071501043e400040d61040703c841d1040d501d8105203201c1c881c00ba20929001c0c9400280e003509220b203031030511900c151001080c0343c0c020301407000054480c0d0300f04000c041c0c00101400ba0440030740d03024105000194050204818042e5824040107442400070301b00700c401d6044184100b0041c000d0001c00d0503400d020802404640d20b8000d8002c0141c2c000c0014a110820711088584030300c440719845441c0e050940d0480780b04002503000c5250b43c40d042c00801c0d04400f03004910007258 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 378461016 1250 378459766 378459769
    0x603030c0601061805010804020f041e020708040312022b030b030f01020711011106240303131e03150f021309050405070609060503060108181005010302040e03040501050d1a 76
    0xa107003603100b000015003a28010381800510300700e42000340030a0a100341e1504155001540d1a581c0806c864025030742c0300041c10b84109070328003100700200e07040421596400a130a0031b03007c030b074018003060b42c21030307800b00042d81c1d042d1000507aa040704070801c8620400100c0c140c4844c0c8041c7c2c0110454003050b03240c0108500a940500c0b01c61076002e00c5100059807442240760903002050307904915030500c8402d881901c00c8900128031664010744580c00c002c1030704e4001500f051500f041c1c51003650988000300b900c92011000c070004400b43c80d91240b02c1085080410780c410101404ca0100910f080c0e50388610300c02c01d10b6180c10003400c50307101c4c00f005402d02c3d95141d04005e500b541036018030b68061700c500520050010911261000d001ea515100e02046d080100143c40ca10000d000c1c40c3c10002203200041408034500c1e0940d008140c960140c548031070049101d01d000c0d04c0300703010991290b440c0407012040c030100001124219039060f1100c508103002d0944140080004801c135038884000340c0c0004086 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 378462266 1250 378461016 378461023
    0x180a0506040620120a0507061b0521070c020f06093001090c0611120d020d0506030102090f102105090105070c0c1404020c0601080c15040f0902030603030c 68
    0xd0031140d522001c000e80c0072501410031140010440f40a9008880444414408442142c00d110010700344141d407039001d0b260100003421714520181c20002e0000c1c10305465940a00140030070a02c07042c28a0f1840054002c1040603170303003036400c00b010442045240700141404021072484a100a2407a400c00305802e01241a815083c0015408882d500c02d201c071828101e0348407114003c881000812130885960340d03002d1300408a018041c1404095002c0c1c02112400f0029291201203003210583c4480010000a020350003158010340754505003030000d20b06080510030756101000c028000c042640c410000d0225010b0004e14000c20080d107450045a1040c846541c2440c610003104001001d2500b542000d003103c4014055030104006c5403028804503840c60104410f503030245030030020208860b4000f0f0000c3c0702c0c1060341c0b01c00e4000d040c0000742407440481d80a25400059900707090300200541d0348c09141c8524001c080070345048040c14000060301e80d0182d5032103803002d01103a142c86141000b40d0320703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 378463516 1250 378462266 378462269
    0x604051e07141306050a08070207030f060906022205041a06040303031503050319080703090c0510050c061503070608010e011e03020414060a120b04080a091a0307020d050c03180a050604 81
    0x885c000080c080186070b0321000341a4051704a102810b0640e0655540c5020104511805054151624403000c14030110358111000032440d0400400c48150009100340c01a00d00c1c821503100724a800c14050792001803160300311640f04010f00b402d01d050704560f0306500030070004021300c240c040c1150012000030700800c01020b0b0148496000132101c0d03856100204400c2004102d502098202620704000a181c064000c0036035500315880c00c1d2070280418211910b000311400c01034248229414002c84c000c840d4030034541020241c040d1035a050700c80070140d074906000e100d050403413216680100a1400340c14a080c402c5502e884030400ca95640e0303000a400d40e20b1034008402011050410301082d803409202e030b130004019241802e103641080f501c6941800600810141000c43d001803000b888a03c10310150010309003402d01881642410070361440c440e0022504000540f207140d030725400c102c0c0100151036803400340c01c00071031034805c00e000ca54580e0b9a200c0300581d08100d0302c0c00081020381c3c90318050030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 378464766 1250 378463516 378463529
    0x9130c03050a0c0605090d03080c091801090c0203190e010e1806010207320a091104210b0414010e01050a020711040902060714030c01020a03050604051e071413 70
    0x9141d9402c0c10320101c3d60701d40b50b0008050007420800d4000c1602c5020141080c0c3d5010306000e0302c103030340300394000b02207108290b070090b44564040035041c03a0307075410010141a1401d0318400c02854221202c280e980344900b00c140c904200b0b400140c103c1c0d1074440e0b101d601810308103160240100d800ca0001c0b0301c7e4480f90460a8a400503110708000055904000c040020242e6041950440003101065410740750750140104408210501881c05030f03c829851600400c000c850400030807401c0e20413161540c016002e04807407103e0405d00c46a00b9040d20b42c0d81240c064000d1050107042d29141d0780c030403c41240080c141407139506c07481000d41021080c8582c51048640c00c0d40580c0d900500d182012802070742151407849a498118880090703140d400690740c038184d010035620203200307070074001c2803441c0a03080b030b442555800056516826a41904120301815040c0c500b4030403500d508005c0c42c6186502418207091121002c00190441c0c13054614591000003000d91602c0c02018610701a804880c0384c0112 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 378466016 1250 378464766 378464773
    0x705031002071e20190605040317040305030f03180a142103060603070c0512450103020717030f012103180e0a06030209010909020d0209130c0305 64
    0x58288019002101c0c54098000405051042da0765036000060b054004c040f403603940d01c202041341c5520307460070784a8400b264000300003003195610402426030b8064003046400b04104181524044071000a680581c1d41c0a4003a60a04c0403c504021050700028112111074070b104245c903520090601c0010900e5001d18400c0980070442c1c0115442e14000c3c800070300305801048110f03040300012a058a03000b12086402d61381c1ca840c0c0c0541100d00340d11440000e0a1360051070300c000b1030380c2e030303c980201041d91031524403540c00ca030b0400c5410405090760003d40c246400494803551801a005103000071000141070040c1000010303280c805540342081800842610008140f00704601c10000a9004007180c98000f41d103030640300c02da0245259905d10060500503041e052001c0c280c09904070f000580090211600c040ca096940032000d8010381c48142d0181c82c88400101e21002c0c01e01a0b4004103070082c0030413010400590902c00e105100424442080141180c003200190441021000460086009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 378467266 1250 378466016 378466027
    0xd0507140a170403171006020105060a05030604060b060d0903111209030a0b0703110a031505040b0d030c060608070b1201050108040209070c0c05030d02150f070e0607050705031002 79
    0x203004240c0ca0010121004414480403410300c2e8090b088880590800000c29000d803128034040d60303001031072015601090070400c100300a03100786041260484a15500a02c150b403070b00c405008980d140fa00941d030b010341040b00050041070180d0003036019400087d080a00e0819241c00070012600c1c4018214000750001c0000c20405100f0008070044900250405141501c41070020703a45004003c801000062164005490307180694010341c5030201d11155540d0b41d29040300028011700007641d41c00080343c10007070042498141403145085002c0302401c021300d408102d84054a10a0810710b0484082e601c400c8040384034136007030000c04020261600042d40f1000701511212180e0816080b07181040106001c000140e0360f041c2c5c50641180e59810449852070f83c81c201108002c0513a0400c98140c42600e040180c0298000341c07041d0102c00700994159280c4490601004034030003a00c9020009114180120451800b4402814400d11440807203440a81c1d89020034244a4401d000705c0342d8590100e075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 378468516 1250 378467266 378467281
    0x1202071503140f0609041401020c0d1e0807121802060403050d110a0816030507120e0a0611030714030c0a060f39020c03060a050a2a0f0c080d05 63
    0x8015421101283e80c0c0b0b2201e240402c042600003600420192464200c0f0300c58081155081d030460300c02c1004807068410072401c030100505018444001358445c2960b10300d201443e144030342c62580c000c040d80d0380c1e250280e0381d10b5040389000c3c00c02d28030f100301c003480003003800740c0160b0328070300140300561082020b81888201401d0140c03580d10002080d00b41e907007010300000006580341c8101c0700022050200b43c01c42500381c0c00c045445010303003070b0002d101d1519080d01e02611030f00603840e50241207049130100780344d90b00d40714101c41610482c540e4904641c0107011303140000d0031600d5131010f001d5009003141d0600c00403014091800205440607190700380d444103c003031149898040c45455485418125010010301d4184910a00915510042464140c2c24880c4c01520903c59000c248a005046a60904010030000d00602c0c003991081c2d545450720080031076459054103000050880a040c0c04049290102c7c2543c0c68489103000c00d04000c402c1c50000001030110300540310301400c40314006003915100a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 378469766 1250 378468516 378468551
    0x51501060908030a05070f0b0405060906060a0e010e04060207050d0e13020a1b0c2c010f030201021e01020d0f1d0303010f050d11060a0815090c03041202071503 70
    0xc00c031100308022100203010901000040380d54101d5103142056079100b0342d081040c4c07400401c02d0b008007440001300522040c000c0c006080c0d0f000701d00e80010384035175480f0f2804001401006100300361a07230407000f0040014081100449512070b0003030002500d4161540c2d01c107410411202a400d010030b440521200c00c50400580828022170140001c500c0c052050074050039009071655000002841d420b80c0004115281110b203000300441c2074ad00038410850490b40e80786803005a000610342a0300000000e116240c001414101c0e5010b801400000301d80c04d0130040714050400e10120030350740801102202040a1180300000d080340280094a0404500120a50008850507070020b500c1880180000c6912840000464808a54141e0340b0340c024504681214000043d99601c0750004c281d1000d00c1d500202c0340c0e0701c1000d004007680c1050340c045007000b1702c2040c180e4100704000400e10025001512880008203e1a0a80110780c940d0b99039420700220210a0304042000946070041030211000c02c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 378471016 1250 378469766 378469769
    0x15040509100c020a0302071e150c140a02150403030e10090302150301060815010e06180a0b030402090a020408062d0108011e09080d0c121109100c0308040605070504080a051501 77
    0x980022310003a1408140030000a202d0054000341c5403c0e00c1542e048602946800c11401d50001615081d507031105815078a0310482c0034207030300600c8036590000090324040d0483c1c06032075050f210141100b5004042c800003022103108501803106412000c40980e84940607480401c4885481654035030402800501030b00c4040c0651010a03040e001c00c44e05a0b030012442041c01005449441d1140005859486c601221b1814180c110303008001c017040e540d103100000d501c558000c0d00c030b1040a89400010703100301d1046120f0840300741c0200012138810300b44402c0081050424160400300d116076502024407c58007a40180c0440c0e5480daa55403009a4440c003036034074400f402004000015103074907007803414850442e842c90b049071b80790b42104005004031a24001e1100c80703282040540345500880096500040d4000c0c41a1550075840841fa4407441d5081000b039407698034018252101e80d5080090100600350ba01400001d20004c00d00c04020080980610b000340010700401416800e41650304206 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 378472266 1250 378471016 378471029
    0xf0602040b03160e0f1210050903040611070803030103020d020a090e0c03010f0e1e120403060f050c07021e0307080307030518010c0302030a0503060a090911100815040509100c020a030207 82
    0x100f050050440c0c0d143c41040d0005402501c20b141c0c0101c6c0e1030811400c00a540c00e501c09514600000d0003071442c00000a00244c540c6510380402c5c0710820f41a00c0d660f880244601c0f00c266008000510041c03c00b041c0e40f24020b40f000c1d025512068a41c10104103450344101c1101542d0b0007007503d90314618007402440c0507540c07640390030000340405249550719801c03030008040d621101c00c0c00a1700d9459040041c1e10b00307010040c404948613901c0b480c0c050041c1c00c035030b444280000d0406003c1024044403c1c1100c820507070040c6040c1709120114200000010f4111115a06014103100000d10300010301c010180781b80300340d64283c1c3c0e075502150340c183c0252aa000d82410080340800f4035002940010840c4c202545500300680c80396502c2000a4020842d5041208101d081000880820040d4800d9a082072011100712071a23701510b4100d805082c05c903898003807110300c811007042906042d0f0240d90000c40d200c0a944144901000600036194410400360041c0c0c843ca010005244c0c0c14041d0b040940740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 378473516 1250 378472266 378472277
    0x20d020f1c0c090927030f1d011b0f17070b15030c0904140a0c0602010e0607050a0f12150302090106030e0a0303051e01081608031201120f0602040b0316 67
    0x11407038000f804100940910b40c3c0c0c080c0d0710301000600c40300075803d88240000c02d034800010031055182c01401e10034030140950218030710640480e000583e500c20484000700607910804040c96050840703848143c0814191081a00d0705090030104400c0841044440400309151340d640845140440766000024001005a2610a513601c482e40d800f29640400b01c100711a46419034440d0b0801c0d00c24607660391241300d15807003120b0ba41020001c40c25003000803903000b90000c001400b4542000d0392621003c95240000442c10091240403500030100c404408078146030021500d16101c80c1403040b01c2c001002e074004625804400c0085103008080f09002d04040c2c6010b00c202c40d07149006541e140301c501e80081c03d05480f480010b40f008003e2492480808100d00008150f5075581080e5442d10050700c5540c100c04843c14011802c05000001c464400c410545150391507840c0030048001e00b440b01004907001402102d918000c06c2a5001420241c1002c00b60300b55641004513005050100c0c0068100c140070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 378474766 1250 378473516 378473531
    0xd050403050a260a030b040501210209070207050307180b01090f120206071b06020f0a0201091a0f0703030506040501050d0f03030b1504030c080f01090b19020d020f1c 73
    0x48002c209001120fa112980c1c54040348182480c0c180541e031800c0c0c224051001242402070640e0680010108607804d4800b0400c590300c869030002c5511440d21089441d4102481c403c0060829400c403942c40724161060f100c166440d40c001034100716065121510301c03802d91004580e240e02c54814043c0540003405c007125042c0c90156451002c114900c26005000d50541d5002c09644854084410995010f240500c03480104010b83e03040300040d02540d8014071a01c6038502c144040040c0140515170161900e80641c0d14180410010b0130a00e260f14888010902800d5540c80c001c0e8080d128061180d1004100c9240c81000d10003207402c144d012130b129814016002c804104488680d8643c0d0741c0624020071031169550105002c2003400c50a00c148581c002000010b00410468401c180e401d07000076505041c000c1c83d03403d801e83d5620f0501600c519058404907031444c1c000080003868401d40c0f81c0240c140481070305528200d0708800741c062015140000c440c40b02d6014040b810111040c01c403001c2100c035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 378476016 1250 378474766 378474773
    0x1a130f0f03110105090604060804060c0504081509010b09100e060f0f09070e060408010e0106080f1513050303040605090c01021605040c0e0303180117040f11060c01110306030d050403 80
    0x99030944000b030710084982d0015801d0b03901c243d080341c01c82c04c0c01800fa0f0350303281e540c2c00005115040860b4169403c61030f0044024150348180100c40840e00c5000040c1031540001c0c12900744c100000d003d544656581b121801200d89030050350511500000340c10280b400d10b85020070300d01c404001c000c03611905007030143c282c0e15030b940080f600c0301441c284c4009400b569940e009548412800c6181940110702141c00295440150000b900c01174080009100740c0340c1c0c42c001e0350751342c1449022032040d40d0030045a44030040001c285690b40148940f504640700b4400c0e869081c107550051328242c400c2e41d16032080100120080000009c00002071004050113520b0a203000002e01aa01940b0300c256140d05480d200584104031040216800074141c0c1d6403100c1c800c01411640351442d02044c0812022994810703001c48010b41e0138406c0c0c0e0419a2012032100c1642c58103100007075200500d5104000740204004003500b40700315000c5840d90000560340c2c2c10080101840d10f1800a841810480c0400c07052000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 378477266 1250 378476016 378476039
    0x203060708010f03120201150f081002090a050d021507060f05090d0c0b0601030b120a060c050c0705130207080a0801140301061d0a200a030630030302041a130f 70
    0x7180e070484080f100e03100caa607604901428034448039001002300110003191244065284900311201001121a080c0c41c0030301040c1039001d0001139a41c001c15101e820456418142d111903403080c4000c101c44244500c0308202c03a42904501402c2e15155a2000d0b40f40c1e00405501c41c207604039a14100400541211400007460300b00789010040418603c0408208aa4080d410107141248006e0040350442c048070032041e034844e03c2800c2950708a0070201d010440a01400469695030414005800850708080500c1402c20303c0110015070076908111050100762004094640003070aaa83e408040d490708c03034015003807248052000d00c26454440d041040510848601c4403046480241c2c1440d0307a1a5011100106902c0d040545800c003a13800c4d09000700b0414006090400305500c0c2001041d40303403c0600a014096104410851500c40d440031a908140d00e104118620915025240603110203e20341d40c1c0703c1e9481c5034101070b1000310b2524003110064500360082c1007000c452041052825248684 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 378478516 1250 378477266 378477269
    0x9020d110307080a0807050c190909050307080304080c01051627080114090f19060203041121011406370b0304021207061421040f0203060708010f 64
    0xd00020500000101e07203040c01804000d22007003007510008450350170440d0407640a840c08882c0703400b0b2011030030781510b0f03d40c0d440c0683c0520b802a880803d401d0039050340003805040d1082e15144810b000700d2000a01c80402148214404d1211070303104c402610400382514030181908000011061080701500c0d840b0140350420a0551810b151800540d4441c82e0200603507004402c44d0b5007090541c86d081940c03001881c1c0a600d01d81e0841d426030300d0555a554403808041102c801c1541040520004501150003a5800901460418121303540070400620742d00d80c0e08100c503403c0124000745c82c1c1130800030310403000140401500140d0038580f82c0d00041c104107038602410300e508410b900700070040703804220b0b05a800210205000105441d40352041c51504203d4041784104035800d500201c0103408221601116481d8440304901e010710303c44070409410010b02c0d0416640321404064910300c9841c0d01c0c500035030080b01000d41d841031500500d030400c50700030032820a02840d0401000030181c5d1114400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 378479766 1250 378478516 378478523
    0xf08150606091504091802010f140304140c0a06021c09080a020d150c082d07030506030f0105100608100806010303030f141602010c0f081503070f03080d050a09020d 72
    0x3c0c40b001c11007010803c0c0d004a8008260307492500581c5000314520454144c5914000d1302c03140c04070104084104c502800c02d0f511a00881e0302803000c2000120780c040440141d001d40f034103882c0061804004100078020540c000c80c01030740061140b07081050b200340304400312441460300e003c40c2402c0440c80b50703840c0382600001340900741c403074840001e0000d8100380e500382400c0d00c070081c00341840d00c0200910310303c01982c9200c44503201506406038000669140e00003007503030b0840403030b4580d580c8c1001d800400c0014420b0b505801020f5130803038800d07428402c41c0d100e590740712902509c2508010000300110401445141c02c4000182c09218040000132000d0451340e0500d070125542803604a5900030f400c0c502c4410904006078000c3c07040703102d269586c1c1c60801c20168020040c054414104603401c0c0030007860385000ca17411602080400c22030802e031404030031025085035001503907103070041078260b0175034001e40307240d40040355180744a00240a801d4001ca80b1007028010241c894000840910345180000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 378481016 1250 378479766 378479779
    0x60b10200f331608070e01020a0609050f0703081306050a08220b090c03010e010614061e0a0228030806042f0d140106020d05030405010f05010f0815060609 68
    0x3034000404002c0310782d071080e816041845070b00382007544031500c2c10038040c03000c04121040c2c0003030500c0740300e0708038032800d004164020b1203e150365864580040076100780548060003651981400044200808401948503042c0c06654180d010b508604001042d0007090402404003c82c1440d9a80a80010b400c030441e508007ca80e0700042c00304004038994a14000d02d0044035508108131190080b0f484007c82c24141d000348003000d1500e846900b2201d00b4002c00c040b2100315080c0741b820381084400b924400c4080300441c2000301418101d5134103034001d80344403c016401a8920a0280b4450001d0b00b2181c801404a00c40118503582c094600100102600e00550f61081c03500c84c445d0381c405500442d164222404105200c060050207074076840603c070086100d0515102508284032801e030b050403580707a0346c09030803915440841100c040d80302130f2040d50590340340c803a0400e0100c62172040b64000c29130080380400e903a2520698030b05264280300b41c02d070750101c0d0b542003240d99240e1204847d44c1da82c040321607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 378482266 1250 378481016 378481063
    0x412050705010c05030103030e0f0a0b0d0f0e0d020d05030f0106120902130c090f03080702120a1a010509010b130603020c150a050402040b060a0c02040504060b10200f 73
    0x2110540500352015100c2d42c03c005000184940000c02503044c0c80c042d035148248040010148121180490a119080014440100911000c1c5070141c1600d03a001100812200c0d10042d000040d1031840c103002d08503030840b078125601241c0410500c1e440c0c03081c9051550846c58060607407206500148502400d002d03001c5000c01d410403984d440314424550042c0f01c141e058030b21101110003881c10603c100045010701a0100e464110418180e080300e6110140358507040141d401c0c00441c3c1c3c10000300d000544501c0401100042030707001021400303101440003400030f40c5010204200c1e044103074071040035201c040181e80e81c600d004690f0102950100e0030050b0f680c109074000649000482460180c081045a0500c41090050f42205010740e00854050110003510310801c1503c0c070424044034045200c59104000504241d00321700c4d03005004140019261402002081180384038412000c00900d01e40035500c1181444070641c4600140c1000a0070030b494010040d659503003064422441038401040e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 378483516 1250 378482266 378482303
    0xf0c11060c090d0c0803120f060a080619020708032805060d020d02120d0309062a030b03010212070503070f0e06070f0c050d0c180c090902070303062309060d050604 72
    0x341200104180000c032542c500d03040340c7c4e071000313136005440c602107080300f0303138041051440c0550604081d524902c015004035141ea4050407080304013851042001d40c2c0a0007084040f80142006d5846050307810340080055100b66840300ca1001e450800c100f40c00d10342018042e032900c450b10301f144030550540e80a1550071950000400282c4d1000ca506468401c00d050810503076455044111024414802072203200fa03031407840700103154840d000800900b41d005004007924400d80000382c0c003600203000186002c074002c05100000d0811130700303000814000000d0190b00741e440610403481c2006480d11459010380d40d00011040d1060800141607820240030382400d000710101e89c50300900303006003003400c035034020b161040d0849650722541420042155410318501e09034041c3d180e02c46420740d40d002049040042030380080d0401d0b023054042641e07649020461807402100c0390000c48075104810b1501d5500c10806c20740703106c0204503038018002d0611107000148006083e03a081a4040b02d108048004180b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 378484766 1250 378483516 378483533
    0x904150906110c0705010905043b0304060c15060506030a0c030e07081f0513020111031e0318071a090d0816110102010b030703020f040f0f0c11060c090d 67
    0xb9205000e41d440010030400380d50300020074074102c400130780341d04000720740d1a82000100c3d504446c4140202c041000c220340100c4600540c0108101c40c2c01c041c0a446c8183c070302252841d005500560003181d40c625468051154444510700c03180301c400300610507581410003140b1140400f5229010301511500c0d5220218042c0e00301c544401100412200c1d850360303c05425560f0790640c1c40d440325529039602c00a0044419020700c0d48910322190100d07044044503801110150110940201503010902c8014254034420303060303400300490300107015100d06103030044a40c0101820a503065a074070000c0104282500381c6203914000300401580c540340c081e05804900070751283e060086c1107040004d22200142e010150717141800b802203441d0300c0c001b0400001a07003281c80500c0610360590100c070042005203815181814204005400803910121801d8044c1c20740b006400c40225880e11441d00504241c0e1140c07400c0e8071a0006c02c000d1909040814807520240b00d8500180d0044140c052044184035141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 378486016 1250 378484766 378484781
    0x903111804061d06153106080d0f27050d14070f140904060b040e0a02130c09120204180302060403020d0f092304060b070605060904150906 61
    0x488060120380762500e414402041801440341c246107145240d06a030010028200d403150003042403c203040c1408004000b1500643d000810100341e10040003131503440070f0b0b2000301d176103d00320340b0109503581170080a505004007a809002001102d00b592100f01d68000130f049030b103071700b8100d54101500c0e034081e050810740b0060300013a0b00b1109001d2148200043c000185404035510010b44062a0f21141c1e00084440035202c3c01c07208100400300b03000e241c50208440c03600103104400000b620034158001c03d00b81e640c525803901003900314a9805042d030800c10600b10788102c00d05070030000c608141001500d507070404e02418031501d0315950102c1c00c54669500c880a0400450035060300304180c0c2c5030096481d84100c2e001c4006008024449040f1801140d41880000c03903512145591418441c8501080c400c003410313a9010840681021140e888070710588002d44080009103036030b00194100403098810240550740110300e40020000424490000080780500411000c0b80403500c2e410800b0103802e25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 378487266 1250 378486016 378486049
    0x150f03190603080a03150609090e07030203160815250c0804240e01080c0705070b0c1e030c0a0b0601020a02090c040f090e0304121e080a120b01090311 66
    0x1d12501209021003500a0086640d444c1e505006015280440c010950514411840898101d000034044010581c01c8202d001103c00b00f01d82019590750002440c024484c2c0c01d805140180200520218a0074400e00320310750980c1100302224101207202a1025215600701d02d01d14440040d00003d00c1d1044281040e1340e50000c00c2d040e1595200c5128007001070100c5988058500001c05501007140284081c0184000584810a0300d03a25680d00c003086500000003182c01d0300403260081030300000386024018004103000141280c0440e064240080c0070a00d48501c1a0352051081030388040c40080c0207003480740e000c11f01c800f4646400006034030303150180744000e500400716401c22102141c5c1401a00807198004400c40840f03554424a000715042d0313803080309a58100b00030034409410821141c9000d5882881139811102c403000c030100d00b00300003000860340d01030300143c5a1881c81c0e1001c0d2001c808081a074080003500250310000c2c040504c0c41c80b0040c244401003c0d10320341031f40c1d1310601c3c01d2040d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 378488516 1250 378487266 378487271
    0x318241810020315040b0a090509012705160b07080d06150c0b071409150405120102071b05130c0302040f0303030b19030b071110020d0e0c150f0319 65
    0x5000740d02019410488500c000e4810010b0b1803200742c94940550342000301c024140303c0f640c0742403c42c2c040107403000030240341056403140c0d00206850100132001c010300c3c0081c1f0301880c1071a0146031680c28000080d02c19804070444000034003a00040d036040300c10040c0c2c4104040d035030325070800c40d1790040c0c0155444260083d058031001080e140d0440c0b1041c0c40c2d03910407624205a0340d00d1a0301079512210050144003688414015014a42409203001d02216110403125080560b1100012010700601143e62220b94011500c5810081000444002160400e902042060070040803411900c0040301d0360b8151615094044072150180d07040342d0182103e100c1ca41d90481d141c0c100540503200d00060a4051600040b50b1400c801c40503500c082501c0e800016409542c9a00714115205c0103141e000840c50302640600d4001240188020081109000c10116002110707682d840c0c2048810b1604038007034049400000f010420ad1002c440812a9001c0c0d026225100c00081700003250303282c1000001c0b2072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 378489766 1250 378488516 378488533
    0x60703020706060e04110a0602060c04060309021224090a110405100305060a0e07080307030903080309011113030302060f0603071208090a06110f010207020901150e030a060203182418 80
    0xf5241000b8560007000ba0384800e201f55440030104da49103c122590038800c0c9041c082030141c80d04c03c0c1c018036543d9000500c540100090351504605058007032482d1034100440c030480c010f00c2035031045080da0140302c1401901c0c07201c0898655800910305804514403883d69540081c1c88020701e101107070040c41c2c0000449085d41303080310710039004046c040028550751140d050b0024a4600000860b08410351655403212510b02c2d42d034580615800140c10300e1200d54883c4002e220341d14003100074140070381d00c6285040b04d09180d4100681080f8001d402c0607205485602005203580340050504211000c1c1d024803400d12090b8104000702c0d006500c860760b4020030f01c180005080e64410214100100e81c281034442d42c8100c03040580c202d21440b10b00940154041004014000c407940f027804032403400d0300b40201658000c000103400d2546608040360180d501009129409016604400c00c6048640061070740e20000700240044030018001c40c0004185200021700c0b5907800031000c0d504004040c210341c44d48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 378491016 1250 378489766 378489773
    0x51201090609060203061309020d17120c07020a05032d0a0602070b0105030d05040317090103111303060c0c0b0a02090f1c03080c030408030a1a12011418060703020706060e04 76
    0x1e6000346c071050310401d082c100d680c490011502c5450307901980203044810030000c035901d80c02c84100c01040c6496543e42400070400c500504051140314049000d40300e9501c03001c51042103203942e09904003d00a5003c600f0588003014550005610401c0107036852030740004001105203401080d060041c034076800816408100f142e404c000d00d050792001c4081d034003e10098081100c1314010b920000d8448444010300c5928030102200070202040c040c0350100d01000c0360002c1019580c0141120b144074042e900003001400030a20a40b24555083d01d880c034010b02c40c0d030b25800c550f54070141038000c0740ba5001490f900f1680d541d50b040b60030407001a200c1070440002045202004c00d4660b000c1d0041160040001d010400301021a0700c59030b408000181903840300e0b0148401014041c0e004c21208070b10000404590350740690b4103c0c1401d840340042313806416440b03000d8031440060480101c0f41c101800c0d0034200304022a045901000320b1400689032040c40c205035002d80034540c07001002e130a40c4014003051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 378492266 1250 378491016 378491021
    0x91d04020d0c052707020f06040615050a060206070e03061b030606310902070807030f0c080c010b01110a05060402060d0603060c121a090c0c0f01020a0302031905010f05120109060906 80
    0x884c0131481e83c1c501540d10990203a8480100940302c0d5515044800081c000030940d0340100c8080e4010005112401d803120086104c5070a0382e001075015134450702c1000400d40d800000b4500b19082903001d4a45410070030a84226403450803d015608000440002d00d80c2d10303002c00307581d20b0000b200e48843e110b00382120355510000103603201e406540c1401002150806c0a4000c607071080d544200c5041c904001500c0441e51041c20710111030800c5846800480802d03004805070000344a03c000001e00c10300c0301000504407801c6084148102d4002c28540b0b0007280c03010820326030254050724100c0e551135000038800300078031464000401051600b031110302000d41c842c8a802e481c4403109010010b10780d00d049a060300401c8003160550001803100006c010341d039110060400b0545080454800e0a0741d445d03501d00f641c004c86102d5000a80c003200304100c1441111441c81141d17120311040060394103160310303281401902d000c0c0a001e07245083c540da8603507500354046c001c42074200d00c040001c200c00d403a10001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 378493516 1250 378492266 378492319
    0xe040906090b07030603021302030a0b091906050307050d0602092701030c0902090a03060f0f29090121031e031d03090a030b25080106091d04020d0c05 66
    0xb8140385050010b60114004d2181c00c040d21740081c102d10401e10800060400b0b0742c40180343d1303140310303481c1c80001040781c40362062030f400340d56841b4503040329030144402c1c0001c03100182d01c840e00c00d80c006101004030b03490310280304c0c00d126000302c2c0c05642d414681c070204841c1c80000131182c044460030050310f4410b03114500004d0503070b4825004001c9180e0b5501422081c0c0c01001c510702d5121170415020000614968021104145c54a1020455802c162100300c00c0303c4040d101498032112070341101004c80110400c00001d18021035108000394100300041040d030225501d1078002202d900805070900d80500c030300440048541d0030f4440c4503001800010090404104000d0069204a400d04074030080401515400c42001c0c00d41c280d01c40c03440d00c4002000c240034198000151030146a852485003d203d140201c2c600390700c528840e5498454010460b0515520240e010b4940e9404245020000e1201680045e0110744c480c1800c6054203060b910001140d000c5030307000700d02c0c47c000107030541800744008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 378494766 1250 378493516 378493523
    0x1003050312190504200310090803090f060f391e0406140f120405060916060f12061710110712140d020f0d050a0b010509100e04090609 59
    0x85500c5042c0d0302c9054450a46005040c00d401e10003100011100000c03040c070000008040b1209802091100411240140c00552380030500100b0402d4501007082201140e001c0a00244058900240c40c3c001c82c043c003030404810200d200c08228848100c1c004942d0070003400401c4244a51126200a5100d5000c03451049020b0107007510001184410010f5408966040d19030000c03080404d2141010f6601103002c001218009020b1010101803005225103d41d00c40e00080180f130500d004d403503160407020100740141401203182031040c41d5010726209004403044c1002c02ca2500000e0001024040c030390801959110503810703040c440500091440c11094031110100540003500051103039510900b20094100c808104010001c64441c01458000250b1100075904007010000c0b1242641c1c00101010f90300c1c000440c603805103010780d00c54150802c0ca003030001c001024541c0e0003c1c1203800b5400b113662082c039081c0e04804a8500900007040010310044c4104052203151074400000d007c09031054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 378496016 1250 378494766 378494791
    0x7140a0905120a17090112022d04030f06020313201009150e0d0b01090f060b0703020a03120f0e0307120f08010308160b1801110702010e06031003050312 67
    0x42d0520042007840500c0d401c2400002460000d01d101521a40900c02c000c1c10400100c4070001d017a04180b0162800300d400900c08115020101d116003031480030740020500000c420801000001c0c00c00b250040042d600c07130009030300c9945402510500070065000985480403c0b500032840c900000d80f502800f510482d8404080405141d00315001d100768022244000c00c0461401c122500441510310f8800e00140f104060f00850355070540241030070703030000c641103454000701c6200d4806030290002503c0065461810140759860003580c4001c0c0e07201c06401c0c020309080901d24040617400c81420303044222400e102e038140021002c0d9983e400041d003078800c2281e40d503160b1700d56407107038040030400c280d43e42d40c038580350b421038540e05055400114100f900301c501c59603040025520000701c038070a25408011500c001402c03008603003905c1c0c2200850000760020840000142e800520342000032720285c0d0201e44a5070307900900c4c442c000c41078002400501c40414214a003030040d01c14644107040c0110700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 378497266 1250 378496016 378496039
    0x2030d0c03140f0703060603090812090c030a0c0e0c09062a0d0923010f14120708071101150905100305120a0306060206010312030c090905010f0302010e09041a07140a0905 75
    0x1101280d2030500020400d00c81009514001d440c00580547c1040c0b0405c15034440d071813700b0002e817600c2d010910841703001a03c401c0400840104d02d2640780d0210060082c40e01d0310000c000010254440d807801e0040746505016484106140031182d14018000760080f01c44145d81014041c0c1116658400d0500444a8080688001c4a0350a8000d000342045c0c40341c0d8001030101c3d41c1511a04000301d160300703d11030240300001d0068003031940d05004090907160070410741043e80380200000e20465090200d41e04001c40e0590b020000145481203641d88240043c20340c03a811038012603400e06910250a074469035558074a02207038800141003902807528200300c11a6983e80903a2541024800501503903012080f005280e8003d400105002e1403a04d0b12100d0035440b5021801143c8081e0400b01002c107990f0018011540c00408100070340740200d070500980d103066aa00d0003801c4241340305072080f03a4103d0100f080d260140b040f007105045544445030702d5800c0e840c0001e141c01518402c807842010707080300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 378498516 1250 378497266 378497279
    0xe03030a11060a150e04210305192007140604060b090f0601080109020a0e1905030f030909010911040b030f04200f0f01090803031e07050a02030d0c03140f070306 71
    0x1c4e10303440048000c403191441d4544031704006995801801600c800511500c006100000000c20300d0321001c40351000242c60920401100c01001911681142103240044603e4928420340c145007805507400e5030715940701710600d018000c4407a4445600d81c40d100340740a0104000716904462503088040d01c01a4050351000c8400c0a090000d884c502d0200e01401b0062108150710703001400b0385809402d240f02d10000d00c401041d1102d41e03000725129018a034020900417460240141e10440484900030341c10000100000b403040d0906100711806207584280106403281800142ca00070801e50310740c60303206d00c1d082940c0004080105c1d02107402d102c02006101400001c820056403101000d000d082c1c040700a0310501c5a940b824901450510600103c0050b29100c20801076101d003400d4001c0c1d07091211203110390b405910020b840c5a06005080c0700c0c03150b80c99400401ea41d460070081d08086814202680705800400e80b00c08400ca00941c00b100300718800c401611814060030b010f03581006440d03610031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 378499766 1250 378498516 378498521
    0x50403030c06051b0a0e09061e100c0c06080a110313020904020310060b0702030d020d02030706050415020d020c160f03140f0114040b06030601050d06020a0e03030a11060a 75
    0x1004194586035081c0452019070100742d2104201501550040d070311403020445401c0041c003500020348001da8035043d800c003800c581d90005815212282c1da1301e40d844643c4070752481000f0071800340000c00745e4540e61a00c907000d0303402025000600c1c24001511403c0041054404813205000300341069a4a1780040202c02201c1c4642105020708a040c43c4a600300b0092141c090001d170381c5032140b0b00180b4004003c510840340185451003c0d19507800c1c280c07040c90b04090440124070f056400c02c0e1040038600c3d8000c005c481440e9030003000052281e80d28a003d44a250500c1c0e039444070b00c0d10108101202e1b003450b9001b031185600311400c840340981c1c410b04100c0810120300903c00d0703807540c44d101003000604601014100035030403016030b40e50303114a4817410b0031142095450120291120180010b102030030b003061b85c100b40268040c214030760504001c120000034128000740107581c0014510b11082c410340702107503c003400405031b83e614812410000d1003051200848495401038001088052a051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 378501016 1250 378499766 378499769
    0xb010e01081c0c14060115080f06031c0203120717180705060721090314010b060708030601110f01050115032a0203160b01030b0604151a0c030409050105030d0504 71
    0x48111184040300d000b100c100000d0340f01110403180307034540815403820034000207010705015100d07410210308000006000110213803207046106c03241014000151400b060003c0020451104580c524080310360803031852007800c14101806240c0030500907010b0303000001c2c100107a07028146a0094845007880306100e000c1d00c010118682c07050301c04101d0360030500c0c00b40174401e0165024023441c01080d1516480c2020044d034410004104500900c02c10509148800907082620000c001040b0700c030000c00d0091040240c050105040800000d0b200d038030400031881c3c60f403100c0e025900d130f1444034413141d8041d1100f80240c1c003020050400c1d160134180b00b0700c1680d034003003040080c62080d4581c141c0310b42d4030040d03403025840031170100b0040141440040044401c41c10f124440b000307115851428243c51004015042600c17503810030a40e10950036440c4107803c10381c1c4012600b0b008070300f0709a41c9540103200c0d441c6c03160214000420000303082d103041e50181d41221419026034140c426000c90844692245 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 378502266 1250 378501016 378501043
    0x909090c01020601030b10090f0b180403020a0809041b021005090a05060c070320030c0d050f0319020c01181205040e0c0309030706061502070509130602071109040b010e0108 76
    0xfa00400c0400e03038002d4200d8000d400b480c001c00001d0f4950900209482c02078807240c1415890b0350840c4042d080c20301c0488a201e1b20303200040c00702e04150f640252030342800d80e0082d1001c140403500703600683d0380d580103984040810b200e5040710101c409020351504904a40441c0300c0b03140c1400a0130030140844c00c070a019500070090000c036901c112205829412000094080005c00741d1440c07000440d91030740d0b511900032034004648441c402c0464602e0041040e40c2402000018020500c4001028054a8011340950742e020031007405803a299000340503000010402e9800d14011070460401490359281e528050400c100c0031806140f81030b5401d109034400d40040010303000000f41c118109001440e0000001e43c2070b00e00d0b00300d09498000a8921540104403602542c440015256404116a0000b03150541e415840f0b4038020070200d00134114443c000d00341580010b074038020000315841c03048104000428494890a00d0b081109414609008100323407080000300210f280c10300050b030070780107000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 378503516 1250 378502266 378502273
    0x11010f05010e250e091807060503161707051803030418060b04050105031f0b071a0709030507090e0304030605040b07020f16140d140d030c1d01080c040b0f0909090c0102 74
    0x4001445040c0c0380c02003444040d48074054400f1600310b4240b00381f40c002d0429a603400d480b410504210ba213290800c10084080c0403c400c2142e80d0150f11590360360384210541400b40c0c07600c46a031740d0400d00310020790000740d00d8000014042403d0324030104940c60211905010090030f070321500c80403107510580c0a1240402c2e002e0001414154003040107156a0340c1400c8044482941c0300329152543d000440c04464070010303003003003012400740828103541c08415031401c0e0804a01e1500d42c1a25250b281c0211440716480729404440004104200d0b8002d5a104200b000715207401c4c2070001d18510280c41c914010300075004d2a5a030b02500040a1100d81504542c3c03620b903c0c42d241d0540c2820504d0b030240c0d03411080d2384100074042450200220241d151640280000b00344c100c1005045404c0d44582c20184650a03280001440d412403880034018001e007014045500c60b0f103090340550065074010046400001644504200000040c0180107000d9450002e00d4072400f08080d110b5850300c01840c010390 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 378504766 1250 378503516 378503537
    0x918080702120a080708091305040210050a02031b070e0c070c1e08011a0102010501050a08060f0604090c09140a020c1f150f05091305070611010f05010e25 68
    0x14250801210340300c409003c403465200103544160043d044010306a0700c034034012401c0c808600b0800024548085062020021850594009100445104010020008017060301b4a400d0f00802c1143e445800380344118044d00c508292403075488055016054143d032141c004200c0d226011019500d5841c2d020980d019810700381b207121032130380c401700c0b600c944501c146001c0054107200030712808207407114820000304040f0840001a0a54006a100318000c1240c800c080140340000f10321660400c0240b9400541c2d43c41c0d210000740500b9804101408003006070000103103040c0168003041c03007000000e020020560340c0104034002c901440c21480c1054015481c4500140c0c4603001c81c4814200b90300000443d40c070159070144042c6040d40201e416102603c81c14480c628090b4003c6600c41903c0c6545000b0882a540b407070f0b05d4182e01e20034082800b8030000800701d11b160a4005a15010190100f000150396449d0715030240e8000b07449900841c0076403141c0c50200c2651846800c1d44840d10744640c16507a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 378506016 1250 378504766 378504769
    0x306060b040b07081e030c0c07081212060a03231902010903030c0309030b01150908030c19031b080d05070923040e0607030b010210060e071101150f0918080702 70
    0x40c1d01c51120407000200c03010900d50417141d0300c80514001c80e41c040000c1e0300d400c001c4a00070b00c2d0141d9a045824203501141280c0e01c403a9503201103940410304035095408a440324008180d106c603291f00000c1602d500d540c4920003c1400341c011004080c115400c4640040b443e0f89151030404d0003510190009900c1001031000ca03024800c640b0005100c1c1c41c00c2d80d0001d649848a4154850a80021480b24481d800185019034424090006008103a014500e448812034046aa8200011210240807035035000c10003423601549214285016000759440710078a00c0c91308a1141d0f00c40d5060780d010b2450f180215448603c2040f02009803039040011510043c3d65140c0c59401c80d0034002c9669101c0d0301c84480921103a424410203014040f0f580b00450000c1c1d4150029003481e0502c520500c0c0c41d480c4c240c0400441d00280951a0441164240f2291004007450640d016000950320004c09608d1000005011103600001c0c00860301c03c3c040401500d4440c0b00c0307150b03480004880160183d8420300007000907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 378507266 1250 378506016 378506033
    0x1b060804030827010c031a0301060b04140a18020702330c0f03070c050301061208072d11010e01031a040e07030b0a050703180308131104090b010306060b040b07 70
    0x11011428007008255619030800e034251003121102400080e11f602c000581c40136a4050711000c10400c4000780070603402c0000d11f209900940c880c0101a0399065401049034840c000201c000d0103031001c0301c42402c9403101c80c2202a61042004034052a040c4103003521509104800c90b5a5001c1e5446803070325800031022400141e048840e01c1207850103203251150280300100001c03c0360501c43c44044801c07510b800101400c40b186503010355030000900300102d0003e21140c04032101c0c80c1e40301811440b800c885d400e06000400d2255108101850300d40d03421014808488081500010260303240f0108030482d0004606942c0c4035034041c41c10b203010000c04003491901d50000e001c0740100300211a40c1e280d130b039180d1820a81064803103050072951002446152a458012a112030341404d0403020656915030f001041140018103c000c050f10302c04d5201c00b0000b1588040d54690f100600c1402100c1c1c0504000794110001c0c0302c100c4405281801c0050325440d0780080d24103c440040605043c88819143c0282 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 378508516 1250 378507266 378507301
    0x90610091d01090c0c021012020403060e0309130c020c0d21050307030b19050f0a1e0e09010e07030803090a05010203160314010e0a0e0f0a1b0608040308 67
    0x34032100310808140360700701d14100c0256502808a00c0825450104103004469900500340b0412428100110168503800d24503d00950140f929850400001034074078000e0145400040c240d90a0040c0414000340c000b019042c000021203140d0200e81103400c03054100e406001e014030250304000341b452030700c0c0f804420280401c0d000f6034030401301ca0795a107042d440b1000001d1103c400310718080b0a00450f1581171161014202d010340d22903038002041d045100e1071031201d1042070320840f11901c0c42d0b0f1058a07410b1b07000000f01427184028410302640e038070380608200e4038003070303c40b00a99140c00180300c450b05001c1c0c1204928110701800446003980c07a51012036100518036940b0748143d14100c00028400d1009610a01c000308183e445030003214002818ac40a01e00505100b480b0b91005110040c4034803c295000820030384001544c40c04001e01c076040070a0102041c9a80c01000c10240a00804201074881c1c0c996440c104a400e80d19080240c505c08410f46015002549200000b0018800b00c000b419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 378509766 1250 378508516 378508549
    0x2030c041a040f060e0702030307080c07031d01020a170423060301090b0102030c15060907230a0309020a0803120f10140f1023040e04060c0c0503280309020906 70
    0x101d841c1c480b6018071712114140c4000006038000010886081e0b4004000d640100c840116070b85400d0382500d0041800e4480522011243c0c0d945043d12038681c001c00521408035030100000c00c02882001600c441508a0b100c0c5002e51003231743d0140a591203040303025503098000140100d0850f400e150100c8010040300b40c44074154481000006a1144108030540f006c60303072103103d24000e00c1c06100740012424064124002c0c00081d4410381524070800d1400d02c100f580301c4841d42d4540c0e20b0b84808031b014000300000650840d5448001003120318004c0010a0441d800172440b8401d511a8120b1181d1f8490450b044002540310071003d210a582441d2a8003600500902c0300300e56003101c4000a940c0302c254409200461000900480d96804001760746060895a03c0c0c5142441c0c81c00e603058241140051005098594850030001d665009921180c0400d03040411203850b8101540418614400084448410b0714061083d003d0f03a4824000c0c0004240d010740f807039055486083c00c0c081611030004440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 378511016 1250 378509766 378509771
    0x130504050a14010905010f020a1b0510060b030906011a0d0203071e080a0b01020f0c011b08040e18010903050a08040c080d020307060605040515060c1f020702030c041a040f 75
    0x104003051030203010510b050444000091514401c3c0380c010b0841c0ca2404440c400c1a00503c9240081900110f001a0200044410030104070444c600a41000c850143d0f9400b11480d0000c045540c88508001d103109400c6c040849105036298155055241c8100e007814043e40c004004102c1e030404160051034100b03030941044039040b102c1c0f55603445e8000302400312000207480c100421115080c40d0040b0742c0c00d03440c00c0c0054543c2d9222448011745981101d10b005041c8240c1258109030a0030f840c85125807141c001102a071520740b51140740300383d45015075600402124070500040300d0b820621402c415245d240e140c207450060800b4066807460001482958010705c981e40000c0d600400388090b00451070785071302035507036400d5610b04403003114180e820441c00b0314a1b100400c405c140b002400c0868080c2d04484040d1a10701d03912502c0e24040c1803180d24424400300c01604a000e40c45a0050701f00349108900740c031400c031800e405010446224249440101c1701110f40c01c4000d0500368856280107404040c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 378512266 1250 378511016 378511033
    0x70b160e2115010837050f150f06010c080706140a06080a020f0105090613120b09010e0606040e0307020d08040f050915060310030b04150b01050913050405 68
    0xa03992104690480c45140d810718045146003810b01c8044021081d1002004032541040e12003a620880411104420250b04e1180e1460951444d101143d00c4481c00c416461090146132540e00e580007038859841520075030700c00e46140c001d41c80415210b440c42409980c9142c0d142c000449005800803400d482c0400c0400036800031031441d00860000450f020f003001540e0600605074401c940a5034003011076504824030040044c0c0d6411044804a1000d1800c603848100900014109208030184010500b080900c001130301c01003d00760b0742c0100d028240d22080c0b42e80d900c4a0341d0170b0710501c0d1043e0b021a00000c1c0007640c030f450039901103913179108480e04032410a030581d400b103100380011643c16940f101d408101000400d074101400400740c601600c422005041c04a800701c951068a0f44440c400d00002c000a8410099052108000d6400c00b00c000201e0920b410300301d403589010141d00343c019042440d8000a540950229100ca02c4043c00159140303500721440c400402e00648103c03480d00600c8035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 378513516 1250 378512266 378512269
    0x1080307031718061e0702030a09230901090b1c02090f0c040b040608220203071802070606031401060603050702030913110a0203130806130b070306080d02010c03050c070b160e 77
    0x19145c40748207091010300349100b21100f0901c1c01003000f8003030740465100b0410914140d178040380d00012184000c0384207481208400c3d04aa400a800c826140c0040e10000001150b000903040349414040640c6d813614080d11444007c03249950b40e0801a401c503180c2c4e00444d01c2d01401c00101940035124082a40c2400d89800403a00c0303990140e408500008e07855000d0101040f0310324281500038100c1801e00070210116400720351245610312440f00c1c1e00d402c152070001203c2142c0c048400c0c16030b001004021058072450b140c0c0030f080044250b415251302c1d010000c14680e019100320390085c82290011801d24150400304041400140715100c240da4555802c4540040c0e032001030040c0c1c038101c0e00655182c40048100a00c20391946c1d0050400e03510090a20248007007280d00f10200a42020042c001c0307980e03a4000f42c000d08415800139007184207520211000a0303042d4460441c0582030b5a060083d03444002d5460501e02400902500480c521000301d004010346410500041e10700d8200880d14090f0f000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 378514766 1250 378513516 378513523
    0x40e010e07081c0816030605061201091802010e0f01180e07081b1b0c0d03050c150118020a021501030302010504060e06150f0f0a1d01080307031718 65
    0x8004425510450050004020030711560402c0c6034201d00c0c208034541c8000000f060b0388000b801d2542e445c400c83d8000c04110b4840d410140182c0b0300038186035910300c82a0a0441224800d10400721420f1609402843c0700101c1e8002c3c2101d1601650340001d07500490b4200141c1302c014130030060500c042c900050580c0340f01e4803408801000f042c1d6000b100f5160407031000d000450f0080440c1e00d40954501c5420040da2084c0070794400c0d0341e0704c5c10200300d442601c114803403030140081a03040c4d00c000d40052035030800d40d008004151031120351059a9020a0381c0100c4000441c081c01100000c440c0708844088022096001c1c10b0840c200d481100c910030791658500210010a0f001500141d44500801084c41041d00a81c1007101c0440010103440c41d08160b5400c0c8007a61202d803138071460740014840e406a40b100541074454030000d200c02c00c3c450380e40010701c4120b640308101c00505141c0c14000540c5500c080240c82c4030a4054aa40c070380c0c0c014a080145030100c006120640c01000009045480803080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 378516016 1250 378514766 378514781
    0x4150b120c120a0b01030b04030917070302100f090e0c040f080a060c080601080610020727060605030403120e0709050c0304060b06030105010c0605090c10081506030103020a0b09040e01 81
    0x20405012500300e07410921503420310211000110798081e00301c00300003c8040441604490700080203080c15140c0345000c445c11401503000c86422111a005501a41808106281100d02c02c550303038181003000000030381d059030302e420310710010896140741049500703070428000e68170020707001000f40741980781c105400304c5036020742110b65180c0c040f604100c00c0280501c42d0380c50180d124204101d5600c2d00c100000c000702c00080030385000d01441c410704049180201305050280c4103102000f000500310ba1150300610440702c8070100b502d400d10b003002543c1409001120300550b01540c2c0d142d4051220690000030381905500007030244035001d000505c2c003016205090045000ea102d50707030f0724101400d1a005032004484010321641c000c100400c590380e0031000b0f101030544c0c45100820960740d10740303d0a003080d45544130190080d0120000d10f04450784118500d2041964000e001d000d0300a090a001007408240002908211304070740900401c071808000d0001240020008100501c0c4c0c042e4503401d51300319 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 378517266 1250 378516016 378516049
    0x50415050909071212080901060f0603020903151e0a0c0903030c0f0606060e24030703200d020307120603030c08161a0108150c1e0706050c04060816020604150b 70
    0x1490120034a170756100b42d185802180c0d50009100d410f0a04015510b020300511401090550004898076640c6050200003c602100b0100552a00e442e030348148168002040c030302d0740c002d41040001d440788858411b1290584543c0c1e59411001d086076016036140b000034409459104d00e4020000c00212607018050240526944641640c003060050000032000031003a080182031760882a40c98140325010380c0e51000307241c500441d07505101c05140d10380c09658458280c00c404006440c80000d08150000c5001d034445550b0780c0403808000c00f201e070072201503000c0140098bc1c06080c2c400440c00010107000b480210b07010550580503190f440c0c031a00b41002510f465a2407802700104600c0c6014040e0342107000f600c40b00c00d422858201c3e040c001600c00d02e075200200030020a0005150b80d1100142e410069201c0c03801c102c5401c10503203201da250024800d44d8005400000029010b80d10903455809a203055001040c0139162907841201c0a0000040440741341d6803142904460ba881411100710580e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 378518516 1250 378517266 378517283
    0x3051b010905010e100e0402070f0807022404090207080903030703020f0c0607110d1103030706090c12050a030f1107181401081b0d0803011e0504150509090712 70
    0x104080003400c0ea40140c1d0140f4140410310004004540303880343c900c03020b200300c0c0c80c0540e50071060900140c001e0040480113040140c2c1d21903901c0801629100402405008403190b4030910a9660041c10100c1a40e075000e01400f1309010800c001c05064004d030111030f120b01003032828030b440980030034a16004454150f005030711403003480d4149041030100411100d01581c07054500070141d10b031403040c05054804540608c184103030b40000c0c0700490000ca134050400030150383c3e0354411402c20350058100178000782d43d419140c203030009421a036603c10071600f941c440c02400304008552019141c04600302c2014080c400c034401c0c240403490003400307184c0180400110003407007040040320400856500501c000300112412005115000c40028520041e5210015215425020750042800440040c01c01003a418000c40042a02c08070300e49201d5070300d48040107a00c1c4807541d42c000c000550340c07408201c44c031001c401e0720b06000e581040d00752984c1c0138205508a42409030703101d174481500c1f03406180039a020807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 378519766 1250 378518516 378518563
    0x1403030a0e03030112021215010314011a0d021c2111060c160f1707140c130c090e0c1c020705030306010302280801080d0504030515100305 61
    0x4441c4035658586041800842c02d540c1008148050701c4d541803c0644600103070322a400d00c0342c0e01000740d800d110719072448048440d60b40e0718140e420350310640116289035090080400078030049079602009060000e24212880c40d0f03036000d00ca540030070200381c1c900c0070401d54150700228500611000c00122000d484801031003107130340010420960004148400d070060018040c1501521054828480189c41d0052201d00c03280740400385d108241070010010707064420111820b181c4d44d00509445400b83c9440c000d6904940704968487c07100307100d015400240a101c824242515030300140c4482c500f82001001a51a6004166083c100711043d0b0501200003441d020907013483c0d200407440f107144039029402d1a1543d500c031070f01ca000050500c1e04255000c41c05020380150700c0711000b030344501d00c9500380b4000d20010b0000c220f40400d0040c1070642c41120840010203210b00c0c1254116500030024100403501e000c1d4100031107501600a0501c1e0a440300d010011071414811040c034903080300800d81549 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 378521016 1250 378519766 378519781
    0xb0a080d020f0610061812051f05240f03101d06010803030703052d010f12150209030a05030301060804050d111011130b040302040b04061a030a0603140303 68
    0xc01c1c10000b00c2600440144101c0c096002c500070207844540c1403402d000340100d140c40c0c443c1d5180c0da004400130b64a14000c0401c0c0440419401ea00059640429820396048841c2d80103407801650840150b8075070102000521405502810b242407008110407150300c0c2107800a4034081c092031102c080c0f1507a40c4e540c82c050843ca07114070301c1001c0d03840c07014100c1c5600d03040c1819140e00000304500c082c103407030740b0001c0c0e8480c0005114034958503e2603028480d500c81400b03444507a000034041c013a1100448000400c3c00c807101d2100780c001950100c240740032040d80440c0c06029400001d0000c0e05031050145840004100b8005075021340b500342d991101c9031819007012880c1410f10081d400a0007842d02c20a02d18290102e54921066055180410a8000c059a40380d5902c218060008548022800401d5540040c0c5c000c00c1124006c0750144944600541040300720340780b5201c0c41e10112001068800000c2410707010390381c80030414178001403036070340d070b40303e806c40d141d003520045900d031b0400810800ca4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 378522266 1250 378521016 378521023
    0xc02130c090914040f030315050d0b0411060324060d050c1c15060c0f0b0910050c0c03040524040e01050405100305121c0e010e0f0c0a0512010b0a080d02 67
    0x41161150406941d404d180e283c048120b0000350380a07040503140d03602c040010f1043d50000c0c004120150901103450418100304514140030b4a0844810390659a1190507141c800284e90080f920010518944482000b903141008420030300390303800c80b2007440841034604152007001d12a011100045a440140c2e200b0000c0c0d8034480544503084514060500215100b0790104809850300c50601d80d0300c10711641031a80703682d904040011b00c0c110085040154031000801c03040844c0d0822181800b0649a0000711507007030040c2c40c0c034496039038001e0008000034501541071185035034040040d02c84400c0740c010301441c01e03440350b00100f42155012004100758205449695440690700c00d5440e603c50541d0786058495056030848a1001404140211084508a24605082e42860301007100c1e01305c405225020b404040380c10b8509010308210040008404503400b061808014800403e0a08100401c540090340211020866607101480801500c460032040080c2c40f845004020901d000c0d00000d24 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 378523516 1250 378522266 378522281
    0x305060a06030f02040507050c1606022404031808120a1202180906120f0604020a1203170a020c03070308010f08070b07150209190501090902190c02130c0909 69
    0x300c1c0c9040d404101080306001c1c442611941183c0104450304c42040c00c60381e501941c00c0f480d8090040801004d90020184400022142070380c0a840d61110040c05040720a080502e4100c52001024000b60000c1e100d001810a11403c100c070000300d0b40d4944510300c1c0303414025075a45684100005400d44a00d400007901040112411350a62038a05101480c9a0300a000e903109405465220301040030b681e02d02c4410225840d9240c11111401d080742c1240e03664010139102070b40140d88141002c81c0c0d02050303050408141d609502c4001e9120303203150202142500c005c0c01010040d46c28024510303000740034030081180300d0107950b4520311541030103007144000405901030b83e01c0c0d0380002000c100c5186091b0a881c035582e085108030002e40000360030000640b10320383d00160710207d00c1000360341780e105569030501501c8080c3c1c1c0300841c9549130001c3e4000c0344030304185001005c1030781c0300d0480542d2161810046603480a05003000f60300d00034405a041d03c488072000740c0070030703040d080a000c00c5155105904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 378524766 1250 378523516 378523531
    0x30e06030103120c05010f0e010501051807050a1d0a0801050a24030201080c12070512060f222c122a0a080a08090c030c0105041512050709030506 64
    0x14035552660b0388030403081003c40344007002c0c00340c44404101400b00030340c0208100d400c02c01007801078040d48010f09000744024090588103544000009440509054489110701400d8a4082c50f00303040b100180d62686440760000e5440c020400c06480d50b840d0620103e000306540340c004110360419581e103000340c1d00c0ca620f03518140c03400c0200d0000c818088007030f0b0100f00d81c4c0a0a21400350b840c2c1c29180009481120100c00c16021043e007440100b0341d00c02c00902807107510040a45c900e031590b1082250700c003c2c030b400c010703801841100316851692140708107255202c0302c1d8100007000028000f8021080034482c8050f03071601040501c03c03203000760501009140c45104202c9915160a84402c0104501004010706c01d5200c0300403a030701c1034031007081801401a040086140c841119071401010814110740843c0d40d8000c100d0b2000e81c5007800101c400c1d40020585446007000e0415103940c280c00c440708275090801c0180318042c41030740814400c090068100d0b42d0b50800c1d80d81103003810b602d4410040d2a52 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 378526016 1250 378524766 378524779
    0x60d061412030a1112160c1205030a030b01050c0105150117010812030711010905030720093c0601020f210d0603080d060f0b0c1f0618020403030e 64
    0x502401008981c1604010b0400c05500304050000300c5c945028801904040800041c2c1c5415410b1000c41049940b842461014581c84e180c0414900340c000c1c40303100420f41c0e4024021042941d009822103c1480c00615200d8100780c03100e4001c03400e41c1c101b911640c0c3c0c02c00b0120178580041d41d000d03407140c0c6c81c00d11203804a04a0351400600d03640d82d85000840c1c1204100200104207203d1040004181c603180e004000e021002e91810201e85a40c4910011200008108280e03c000541c80030034a0072158014951200b640d1681c00341c00c001d812000c408107462680380d080300c04a1030820071209031a05040e141490307515010002901e00130b5441d070040070a90100f4500c0700511251002c000c01260020348068440b828201150098159030700001c0c00d030400420b00e58140c0300c0300d6004ea01103611580761180302907610401c0c001680b10700c0d016001507410201d07202c0b100681ea11392960030b130b901e141b200083c100c1e03035506585508410f102101840d280c001034100f09265000000e46034100d0100c400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 378527266 1250 378526016 378526039
    0xa1a0d020a09090809100302131d0420040f02040812070c030f020312120a060b03090304090510030501020c060a0b0328060e0304140321030f0411060d0614 68
    0x41d00a0310303103100700242d158444104004110003002912210300c0c010313200f1b00f5915046c682c06806900440d405446100d100c4000140c045c0b02c0e4a003142c007114604c400ea42d4261074949400261018100002c610a035150440c2c10b0291558890410030340307807940c8010307140d03801c0c08056405d00755000006134006100f400b48001098030380010004aa0b03000c00502210b600f10f04c0400d050107561072005101da803000c28841004001d50001c1480f40b5849201086000e448580301240c41c0800c0c0c420700055030050000b4020f81c501980007540201c42a44110060b42e84c0e0390b00d060076a0312201488186030401800e01c5402ca126000b0041115000c402502401c1c1c1303400d0080601511a00d14118600c0e4a070f020381e0305002d0142d1045079080c1081098942e500d86a181c09841c0603002800e0901030f22507040320210000021690012100740300040510799114405075642d44c120151060302c090503a091010200d90301c0c50002e1000b80700c08030011480e1890951072242e0140139500c2d03a030045008141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 378528516 1250 378527266 378527269
    0x5040b151603140406031a180a0e211309052229010812130302120f0d031d0a030c0813030f0506181218060d050a1a0d02 53
    0x1c0d118440d07600850552014030509040b10b80b40c48007058603000e04000140810040d5260300100c22000140c0101240c0c41e0198051004000c64840c203004008066030100c1c203079421030340101c203400208c101115840c0300d03000e03040500c105008a5190b204100010615015840560041c0003001602d0b401c001c4c600e020034220400c0203c1210074080403114001e207604003e050818440004200e039182190111175828045801c442030007030f1010b0b44900601d0a10b41d002040c05caa91400c40c049203421814515406e2040c84080038821008500401c807442c00c50260411200901881c980d84c0410304d41c4045540346100f503400da0002e011504072001c072402283e00400a004016800032a59a0350700158110220f10b21175900001c100266542080c0280200059841d018800e10382c0100000802c2c101840d5407008e80704071400c0d032040280a0100e034444900104484810090526071404c0e14040112045a8049500410700c1d6500c107241100c514041220301c0c01c42500b03642042c0038505580 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 378529766 1250 378528516 378528559
    0x151b040e011d010b0f121902070c03020103051621110c010203041203111b0f0d11060906010f030b040510020307030207030801061412041109070c062d05060d120905040b 74
    0xf4103480c0b030130741b0310000700b40c4a18001d5103c40f06070b207020340d085466141c2482c0c0308100c900316100990000781040040b0796040c4035401180100000c80c0c42c3d40e8a100700c134601c0703080801110340d281c0030003682d00d203030300f039540d0b5017560082c0802c034200000145d8900d0103240800030b800861040e8020145826404000341f0282c100f00c0d082142d1800c60700c4240360b08180c1080c80d1442d0f90300a5091809150101886941c01441018400308020181d4000340d80e00c01d40103a80351824410400c41b000fa6110410103e5100b0640307581080c003500640fa80301c1404800c07a81030307078000e940d40300000342d000408a05040c0d1001903240904258070300031b11503040710b02c05c4005901444590f084540c1c071420204e8200510322920010440c0007604600082c07910b184003420020b03058100ba501d00d414140000801071203002c02e002001c24034640c130040d010074280340e0001460000d0600b07400c85162030381d040c08a138141a141c0310761600c0f0f0341e070220006e0508040c0419202c0d100e02c013a00812100700008011300c200c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 378531016 1250 378529766 378529777
    0x417070b120106120e01020a050406120c0503041e1a01051801060e060a020309040f0209101b0f0318150908030403020307030807020109090204140f03151b040e011d010b0f 75
    0x80c50121300e0951103c0b01040103080d00a1440030f150f10002c1e1440241d0382010140c8111061612600c82100025180c0320a450f4030900010003c0c0c0100001000265120030000f4441d80a8400000d0080d0540d01c2210380b9900c00d40a0ba03546c10304400400c40d41c0f4024990108600c3d07004181d5426505d040d40183c61012144078251080f400801c25401c10b0340b0030010741350218070051060001c101d1404414000b940070400f29409031000c4800410100d004a40744200410901d4090002254644070003000c410802c408604101a400b19070780202c44c1c2c2190034000c6c000c3e03001c0e03e4800410706c1c0b0024040c5034159020700c1180c0c02c188402c10240c1c3e0081040011a500038021554840b070520040361342c0e04041d000050354920101e804103402c6043c030741c0b10b01d00c5001a556141d140840b002059a5a5428020040b090400c0800a0a00303002c10742c802d40c03d0100c0600c02810a5151680c00c0300c00c0509030442c105005610100c8100403981c069113500514452804a10b0054407001d00b00051064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 378532266 1250 378531016 378531029
    0x60b0f010203090f010f020a061d0f0f03070201031e0509010b01110d0e06030702150403020127080d0b0a050d0b040b1803180604030210050304111f0c170417070b1201 73
    0x303034420444080c020300040e040241c9c4400b040151a0200b807400711000042080d41c0d003644560841e5400e11407000a4034038101c20380340b0007181000207680c01140a00101e03507201c410920300c190811201d000500a680c01111207030b0000c034205400c2c1000400413541842d142c841c40d0f0103200c0d105140340d0401c1e01400d0007441611036568a650f070f143d050349000049880321050207200d0040009040e41035000e1340e000a551a20304541001000f0040364201080740058a1120200140c101442071030740030100001c80517020440c030503035410001d1544500030b80b0586400c0f0284d400c0004100001414907405449010030320000d034000d80641d84c0e130340039000d1000c3d9041c0d910303d05a04290746035415207004581c0200f90320603c040500c401000ca40040e01e046509030410000c0c1c244a10341006a01c042c0540750305611a90102400204d0391a4000ced0019152080e165600d080c03004010741c005d1024101d12a5801c5941d01c0f00c0c08000e2801d48154001c01049100f4003403032620350030b544800c6044840c1e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 378533516 1250 378532266 378532277
    0x3070f0309050304030b040f030807020102190f0315090902090c0a0e13060308040f0806090f030a0c0c090f0204030c060519030902130e010606090503190f030903050703060b0f010203090f01 83
    0x1d54900145075110701c1d04050540c6141d10104410400c4a044044407507100742e480440340c6d120010306900380c0c010310b44020460309030882036034041840360b180100041c00524001c282501c040104034245a6550070101c48607454040080a41c01c0c403512040d0803c640c403000a1034000020b0005081007030105009200d540d000c00d44002e09440342e04141c02030343e0000c8600f40e0b1039a44015511000c21180f190704da0362f001d40030001e189000041105c0040c1841c3d1005540341006c1018200c54445244804650000b1041d401040c11121485094013400d050680143c0d00da04504000110510a078484410007a00b042031701c0d84210b08804d810f01140c003074100401c82102c50f10000e4004041540005103407490318100912506054001204844243d20f41c0044c45032030701d090645400040c1900b01503140d0a40c1603000141c5002c14480d5543d009141c900000e54036595442d080260039070041c1d42d40c540310710318030901d8604044402807407103090004500c0d12000002185040c81c90804443c10300c076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 378534766 1250 378533516 378533531
    0x1050603040c0905090a03120c0905060310170102180306040312020901170f0105091f0312020f07031212090209060d0201030f06080609120f0d0f02040b0703030203180303070f03 78
    0x1800d00104042d0480c03040910151a24685c120b41d101042c103420b500040324054145c40e01212031262007640c000300c1d0756541e0464205024040c1c55800500490b410105807030000440307880c1450140f680052017000582e680005941090900304e4a0307803d2480791b0801e00a00c00000c0d0886041c03014060354440140e1a000c0714401656207030140030245100c000d800d8108031900c12140d00d540d040c4d4204075428039060302c0340c10912003010f8030882030700408490101c0600c04640c00c00c1d01519000454411648885c40c11658030781405d046500c02c440c8117012002c203028035500034520611200d200c0c9400c020710803031600000c80034080580a10b02904406098100f564800e40240700303400c44c00d41081c804503590788a0300740c0e1154200e95504c1d140c0250720450610410040c215402d80c0c003080038841c00c0902c0300302c01400500d45055000c0c40d40c0c0e82080001a02200400900b07946406501c00503140e00e0b20801d168000046901c2e00e5400d60000c0003000284c03500800042c408202e02d00d000180007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 378536016 1250 378534766 378534773
    0x3030c020c0d030e0405070305090309121606050d0f09020f04150906121406090a2a0303030c1107030c06031802060d09020120060c073e0a0e0105060304 67
    0x48151075141c208654800721014140c016034812a03040065a0402951340c4142d421411100c054801d103040d43c0080160002a20340040c00c0d0980120308401c0c0c8000140d030f41c0c4403d4895046a00c00004103c0c085295000c100641c4610010f40740400b40c02e0280c545607500190090080600c80e0b03114a540d000201c40f40c030341180c9804060720f4008000c2000c81c0c3c507000400040d12400300b08490a007500700801c803d0704804103101c0d01400b00a0024008000759a0324021488921404200070b000e1505512000e108040c03500e000950090b1000204171280207402400340141e209038074082d61214008000040d02c2c0a2108100c030301c01e1070001065001100380c61102103815070003035407020000c00c00c0030310300f80d95520082429200362a000d0103e0007040c68180e65800108400c0c0e46a00180002142100d000000300086803169100141c2d03074000043d07050aa400919100302505030100c3d41551150780c1240d07040041400300e45062040c0e00d4052101c1440c4014007800c0d010301804030105040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 378537266 1250 378536016 378536023
    0xb0304080903101a0406030c0e0919030903020f06071a090c0a0305300301180f0f090b010519090c0c02030a03020303060a0509010e040b190617010614030a03030c02 72
    0x91101c000c0603100c001d8035038403400000e01031504c0031025010350070700c81e0291441c0c103204100490f940b0010820209241021030100480d004201c8109800b03101003000c010040c1d512002281e03446600ca407117005045005214801c111400030a0250300200556400b00d80c035400c0740d40f04481880410811982d8460804d4204421480708507082880c801c07002c0304102010070304c80194100c1c0217040e000b0441c0106020001d8259422a90302c20b00200010700070b0398131b03003040156441e92003030022448003035818403d400c94403a01e854108031599414098204600100f401e4010311003221a50308400d103403103e4012942c0c45100d9000456901c040008185001c2c81d92078500b6900201901c110240301e0402035101d600c1241e10b80d224854046002c5028034211100710306030340c80910b610710151f6840d030b00c040c4440d002411666204468403900901c0d056140901c0001d0300000046443c0740380605105802e485c150b804c0401858151617003c289520009420f180e03031501454041409080d203101a400e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 378538516 1250 378537266 378537277
    0x4060b0127091404170906040e2a27150f0406180f290c0705090f04020102062d07200105040804060e1c0b04051b0a0b030408 55
    0xc601840075586414070000504210480702e00000c280010368454403691859007003224000c0c116210b48124141010308200a0183c440015002c1841c00303449025120460341c0c211020a0002582c0c204a800090035050001c1502c900411a03400c0c20300b8000d5000074041e5400140d10407200c070880d220043d0381e40d03c243d40c20800d0188111036a584000c050994160f0203400307a01c003c0341c4029884c17807140050642ca08122889480b04200343e50800c5006e0001100341c944c09031500071b00100d04110f42031100b004041c03508200c40149841442c1c84140b14081c000189410703a905208010000941d80203c5c0300703030b44008000c090080e40c0110074010816958022004180c040581c8100031946400009041c0031900700c3e620401007400080146082e5517045800603d008030900040101c2070080361000d40c1c11a0051225018107007010304d48a400c0c901640c166003030609803050000707000060019080031100e5217031030250a4822004103400307410a210310110510000000f4082c40580d03011f44c2d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378539766 1250 378538516 378538547
    0x41502070513140906060105070b070c021002010b03010b010c08031302060c0d090e010b031005040e0c040203040f0309080d0c020d020f090412090902040608060607060204080d0504090c08010e04060b01 88
    0x111403411108260003058403c40012014110101145000c140028000d202d0351051b0350741c514000305660703290a06500900b0501c1407020a1248900582d101c000364a842000c0340d00004105281d001050300351220b0340d4407281071002c01220640803c1c0000c04403607000103000c5507850b2402d40e81c03010034100e10440b001c0043c140035800d284900c1650140503201107401d00340403511680d8135058a02707124070013540c0d003104075505441d003080941003507044440007aa14105540c071030650700740490141e900c11641142c402c1c0410020004141e023000301003015004880041030011003070030014111444e4641e000e485002010750000442d901e04a00d20b0b0090400fa0400307040307040c00c0c6082c883d41a00701a00d1030119403840390100c1c08152920a9504a42e030031b07903d07104551034220901045500c02038082c0c0d0711980070040812240b00402080034102000ea440030b41c0c45250100c0c8604559940304000100803480c0010031400d09440c14060704030b504000d001920b0011200182c031b03c02030000c18407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378541016 1250 378539766 378539779
    0x1a1f2a08031509130c05010f0215041b080705040e07030201021513020409050d0e01080714072901030c06050301031716170d18020904351b01110415020705 68
    0x407135400b0030320300c501e10b5407003001511841500c8000650b090b020307840810300103a1210b42c510301020b505952712a00709000d000000c0800001941b80c00c40c06c18030390041d80c415032041108100d1418540b140383d18050400000d0515507040d907000039281d409100d8042100c204640114158a020030092406698020410032401a45103002c60300d5001441440011510340f094005076540140182ca00c181c2543d0303a40c1d00001480c13151040203400401095491002d134410381000744a15180c2854107030400d1450215546c0746140102076496650030100030480c040c80108002020300000a039810082c5200d00d44844103422107080403060b2a40c0942010103a030041c804206545c0e0080c203100384050b905200c140002100c1711081c0e094035030b00a40100b0300000103004201c9504800c21071500b0003180e0340c01c1000b06c1020601c8032040420f2040c013003100107850003980795000c11100008000800900a101001d031703c40f803150041d445600102080c900101800d14820300218000c1c19009012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378542266 1250 378541016 378541021
    0xa0608010914061008070b0f0706050112140a0b060111160306150b070f06110417060610170402040b0303090406230a03050d031a1f2a08031509 63
    0x1104002c68403040c00c1440d400307118003142c402004c1c0b050710707016112001d000304400d914081545c81a54842d40b8a6100300d0424840c0c4800558a801854001c11007004c5400e0016103608001c20800701c40b0100480070b41c81885c8910000311000c2c05654800002d0070f210101c5a0702c42c20700382c04c020550f502601184074283e4048100503c6500444812038108038440c41ea0f905c41058080328400c2107030281c00091381c1c0902c680081c020340c2005402c2051030742500d08003036035480000c028054620918807650810030401405040c0005002d084261602d001741c2c44428500c610b20035804050b10103401161142d0941800f6201003040b20f44101e40900b08021059403060b4110180000307810061851096003003a00407403030805003501c240d98000001d0411805140801c0e030080c54407404189170f0410494034a005a2346109911081702e2a030309040c080940f11280040241c1c0c041c0b1101500c4002d04e540c60004a002c03144070024071503002010541d40c0e1180703109c24204054030a8400d1340102c54404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378543516 1250 378542266 378542273
    0x10203040606081009080412030306080a15050f0601080f18030d061401020c060409020702040906020315040b0108070c1407090204120c050306130b0a1b02030c06090601120b0a06080109 81
    0xc02e00c21034907000e054072942e000300f4034688140c1d4102000540080000e010510105032401c220800d81446810000344147d6940206c5003040a02e0301c040e107000c1e074100e00d25101c41c0300a025803a484a620101c0309a2480e2250001e844003170048c08181140c1c4d92100010050405058950081d002400440f03441c0c14001400c000500040e01404141c07604646010015500000f100d6010741e00040c1094101401d21028000075041202c0aa074001c0d1103010200c04a40140f009500515185100c0c0e18071020540030f0006444220303034028100284442005505a4042002c00509602440a546c02103034016640c1c681101030700300060f40f82c80001c0010703c03000e101d010450081d104070700c0d20442541d101c0803d91600001c681c3c980307407604034191060004442d0030f0410b90020b070483c000211980030210620003407220031450000b5a200080040380c581c420841d131a4000c40090040c1120b604005800c5454861035400524044028000c03c144040981001d00602030a5000f004401c2e120308 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378544766 1250 378543516 378543521
    0x30f0b1f08160b0705060f04031403070c03230405040f020403050f03190201020c0718020d060e0907090501120204090f1712180703080a020109140a050706050703090302210102030406 80
    0xb5500070028640c000004000ca002c90680e91255000300142225a45481900000780d034010030850800242c8916814000400005140645004d42d50807000283c42e00e00905406001112254503c0104a50341c90700c074507900840301506d45c155000b090409091210328003034080d40c0c200034064010b10300b030345100c4100003015010341c810041b08a0310803a5000d07026400c0388109514081142c0140c5424444d07621408d0b4810070341440020014a80388580702c0c1501154900e400c2904541501e40a00040300030400510000d840c00100410580d458038140320b0410840300f03c02802107850b401c444051240440d601c414054111603031040b03110382d001108a07581d10041c240007542e603030000070070003020110400032400300041c030003800d070b039403c54580c4c0d0b44641043c84410b04542d01e0741e1107040000d80c03541544540355203843c01441401003e00d00f03103041190075004241000b02c10b0020324040390303000221804998041d1181080c40700d901d00070300000f9117030590640b80342d0f0001003448200301959 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378546016 1250 378544766 378544783
    0x60705060f04031b03230c031b1011072a06020c190305030702041505130911030102120f0702071a09030f0712150213060203031f030f0b1f08 62
    0x2035035004a40c42d0409010031a0030442e480c045d00050031240352041c0040c8414181010428640c0d01c07506000381010707130324038661004001c0c0041c0d01201c0b520408155040150884d0491220300a002010f1030300300c0501a03015905010700341500c681c03c1404c1c1c901440c0f080411490781c0e460180109a11554085e41e503088102c0024001e007500c0c5c00c0d0030740c8050802c1174181a02d6000b000f940ca05407964003040041c14403e2040c180848500600049580e940406024440840c07807001c60907243c50b04214825605445515020740d004018508144074014091a4481081081300d4442d8031508403c03403a18000c1e4101541286195904003900780081c805007490030411070490f000f20444854094440070305115205103a2043d010b81e03000540908916004c54010754001803d184941008c407007140b601c1d81c44900560000014000345083c1c608004513068070403040c8039406ca26540d40c2c500c0d018215180a0103d064020204c4d55070941c0307040d507000c1d090020840c0c04d861912030700000e0325545035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378547266 1250 378546016 378546023
    0x20310030b16050703180510020a02010909060b030612010612060e0d0329040e060f0702120f0912030d110307030c0c0c05151608030a0b0d1709060705060f04 69
    0x501c0029080c40468003148101c2a82c550340c0500f0010300750f034140c8280003100c4039441010400d100120316510b0320300d80705103041c0e0780341d0081400c00d00c14000074210b0811908443d804904001d41489100701d10700459800400039a121104840c0300d1410900514541d005000c0c418201d074820000e0040740d4005003606030126083e100300009000060307003220504041154828a1040b0b030a14a00a807450800e0f0150098400310315040b05030f15484c1089002c5810402081601c402d02c1809a4108000100240031042d043c2ca00100000c0c06501070146c0121184254000c98240313090003001c0c01540c2c0d54003854003080c00720880d290750b641c565030000c98880c0006480c0811485240c1d10079265040107540101221040707a00b05010302c174442004c120b82000e41ca41c00c0003841403881d80c1000582190307010ba1070712500c905024484600b80d89103d0070a6101c0c0c824200f5090108d03c00f9040100305414800280f40d84488060216106000349000078040d40165070800082c0180c0307a40403031280b40f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378548516 1250 378547266 378547283
    0xd1b0801020306101718121207021608030f07060b060d0c1101090f080708070b040305030106030b090702061911040305070e010f080a080306030a080301031a06030607020d03090f020402031003 84
    0x2644c0c50b08540a034032a0f405000c04229810209101c0704150a10f400c07400340140581e1080c50315006210440d03440110103641022010007002100d550602094044207440411140320b50718001085075a070180d421910340810b0001184400c001e069446800358400142c4000d84500000702c0810042200544110110300c04400b104c06410045c441c00000651000d00c0e260b61100545450005130800f2004841a030420081c04001c100503030002c030310451181c0d8455540351306042d40201034907070005086001d8202c41040c030030100c1d008168140e0001c101801d0800b1890040200d1014102c1c49081001651000501106114002c1907420076204010300200301644e03241c80454090340244920962a0003e18540c00082c03c40001540c00240050031a0303280ca400392518036480e031083e841128543d039180344d080d01c403c1c0d056071443d6200d0400c83c0035189a02e80070101035100d10210410ba4200741c0e840505904200d00808080f203103a8018200b151a0302d0460300d41d02011406000c103032030065 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378549766 1250 378548516 378548539
    0x3040b090a12150507020c0a1a0d090c08100603030f03200418060506210c09130506130c09050d1a0f0601090803070c0e0606120a060510020c030c0d1b0801020306 71
    0x6000248147c01c40401034103070000c29241c81c0009003c103050110716106e8000c01c201c094034648060150000e103502402200f207045242900107403514403251085480d482c14100c0800c0440d400844031014140d8608020403480c2c00d10b100720100c445a5401344c08400e201250102d4440c10b40384882040c51500c0c20100550350310f5400708481801810002d123400030508001d0901c0fa540104075036041240200304030300307019802000030744c01f80d00619482011540c41040155520b8035001c445000444a003017001041c030700750300c01494880240a1540500c00c21000e0504004000e024084046900c8071000704508103803005480c0366009813a210f00081c030480c0d001c140c010000c022241b00a5000700b600c030005180440c1030f0800700b801019641c0c0080d007440b00100350000c4d58000c510a041c5d05d00000b49045c280800c004c01e0f10300b0761701c028045502c1114810010380340042c80c040e40300001c4032149000311080c41c105103c032144071040070118802400009a030041500914001c0408450065524 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378551016 1250 378549766 378549781
    0x30d0b01020c060301091e0e030d060506090f33040501080106050c060f150316050901090204080a0b060d0507090603030212120f06031c0c060b0904030203040b090a121505 75
    0x40c2548400c2c03640c010003c1004100c0e07140b031a40100c0703520044c001081d003038030a0182503600b169003118000300141c0002501c941400f1541c403518006c2c00f800c032206400e12100d2004107600520f03050040303005140603150442520084460304040840404265480d0210800e20b8400c0b5007242c440e050100342d50400116040c1d01960035504980ca01c00700070203883c0d465101861014801501203880201458032500e0192014880d5880d6840c2c07890b11085268a418240003550034145d101c4194688148400d1100520209960314100d4004001400360381341e2030300080682d40c1f00017000340385100d487d01c00150f040658201c03a040741d000703130290740b41e007650098001050711600444140254400001401503100031240d41e4002e50041c1c11601034002003219600c41c406000c0541011500c400b105008001daa406400d10003201501c10304294241950042c0d620b000f00d014401c0c001001240940440c0c88003003258004140700d489500d20070350282070101c007003140114130038900c5d03003082d0004240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378552266 1250 378551016 378551023
    0x51305010305220c05060301061d090702030f03060a09020309060a0c053405060a1d070f23460510021e0d020708150a02070203010b12030d0b0102 64
    0x2400e034540360f00860500408009003450300c0c480c0071100c51142541c0400e040c1c544030040c5d1702a250980312002e140d943c10400300c1002000b900200c2c481e10070301d802c000b8410350200c01da424a804106c02540c82e070b214000003484d9016190002e4114134030100c1001040e44002038014040c0542d1030003004440d425a408480520620101ca0160109013081211480c8002960f8070400703808211180100710300c4c1d42c0c0e5420315030159020400c0d076441d40d155009038120041e5211072820713400010500a4500404a10407403154400c9400c5641c0b6060b0703401c2000c118121041c10301000030655480c0d0780200d4800d4190400501c0102d0700521000d007800d100d440d80f01d40924455182500c4600701030714102c1000708883d981c614503011401000c604900c0905c484506810711291680580039003080800d0003072030070f659a442206282e00400c00c800304c1c80400b0310045c3d004081ca9801590782c108500110f805403c00050958216183c006841401c88010018105011102d00f0901410030044012a034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378553516 1250 378552266 378552271
    0xa090614210603100f020a030605030f151f0b03040b01120c140d02040603120807050a0e0105090f100c03030e010b0f0f0d0c06050301151704060c180303051305010305 73
    0x41001d0350152092054541204040d88114001c0844284d08050b48014003903840e00324185069a40104560201c0341d003601841c0e02800c0e0540040c14120031500c107466a849261021070001c4d42030502140000d500301141e013031746a1301820064091561203003405450345c0300b120103541080c580800031584101468078221659000850004a9030410342c0c10050b0f81440c0d030076168482140301880d4016120f40c000c1100641c010f041c80c4c10050031101000c0d281c4d0380c00130664003c01c4420401191202d0b00601402c07640002860300d1521442e0101c04070300d10390606140f0540c00711400601003801a800b15094011300d103c0e940a105003940402c0c2e0500b42c589132034815500042c42c41d00342c1402d0074080c1032421000002801c4030780d52209174444600e4001150810400640c00000503c00f02d40c5002e507260076910185041c042c2440e41d02003007214140d000d00010209500c3d1860b8003442881940503446c1c007a50200b6200600355179140c06082c0f43c3c80007402c0101e0141748240060703c0c0d80688100c92 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378554766 1250 378553516 378553537
    0x51809010f051317210f0718030609050a21030b0103020414150702210105090304153006061106060d23060f04021f0905060d0e030a090614 61
    0x141450000d56462481d10480044a001e6502c103112620043c210003006600040b06045c50803078034180304100b540328100042417032040c0100a01c4c0c803035000000c40e81800840b40c200c900010442014034146007000210f00014007401c01e0034050b40d09101003800348511039640703070b18200103003400000150b0030303809584a0120056501e980340ba210381000780e61502c100c1101986246005d030039600103018407400303600104225400d80c030164180c0409100b00341d080400301008604142c82c1c07091080d020b52007001440c00300051045c030101d9002e0740c03460104040c24001401341c10f0f41030740405140144601d00c201400a016062001e2106402080441c0101c1000d480408104010f488101000ca51039445504841480ca099000007000b132058ad4000d05071041c0c4002d96041500411512104100d40003242d030010702c0c10700b044280c10106041c00c50300d00b40c1e00582c0f0741103001c404c0c01c001c00032003003001e21034080001d0319490f155110601200f624015250790403000340d0521303002d44500450b031204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378556016 1250 378554766 378554791
    0x601020c03060c0d0204030c031212050c071502120a1a150a08070c08070c0501080a0e0604120323040c08030406230415030b040b040b01080f0907051809010f05 70
    0x103600081080024001c1113245040585456a203603100c04040c03130507078001d481f1107600d0340c01c100d1400da0041a51000001c0e902c4240701c20304054101f8403062061140040a0600401d244c01e89a0b0407501600c03c0c00071a00145c180724079010384080c1c007400f034600200401d44039a1082c0c0255241007464555240b001c0030181d81003101030141512010740140829061020794100c01c000030329100d00610429215000e4507016514140c001340c141040540180d151030705000c0180c0c04041e001400c01c0d4080c3c0c000c0c1103542e8a1100e104160000e218000303c03610182c07a1050460034214881c1d24607401280318003220091181ea81a10544038000e0b80211070005510009003992482a409100143d807101c0014a1610395104003070701c90320b2060400000841e813a03044142c480d1510b485000703021038054030244990f900740340001b40407003802440702418101032800310341c550008001c004040c02c8041c0c40100114510350b0050301200c0d00b04d0b00c00c0380c0d640c24030042e80401c03500c6008140c0551510f1048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378557266 1250 378556016 378556021
    0x103061a09041104050a0314161203030f02040906080a0203190c0b09040f0f09020307081b011101020c0a0f06050601020d050f0307110706050705151b03250306050301050601020c0306 80
    0x10840607000001c00722590f6001800042100c0d03032281024401148209a901400c1c0c2c010402c01d82810030140e504600c003802c0e00420008000c101080e5240d03558145000183c0c81061030462009000d15048521802e25084011030000c60010304009658000c504558540c1c2c80c204044c61000817043c8020304102d100d4200304115001d400141000b01c03001000402ea84035810030700800c5844c502c5a1020341500c030720500040d03013000d0142c680540980f03009090040b03d2211481c680320424450941008076601d10806410021741c1a5001c140c0f00d00c0982d042c094007810501b120039003c01082d640a440c16021401e40e600019110201d070f80f49448440c02c24075000c490380c07000d41004101605014825111102c0f0810070b010b03020203002240c96540d01ca00c403506289191440301103102000442001c01e206a850240d294103c2e02d519084480d0381d00e6441d90780d0307036001030aa030510801214205024006072074042d0480300582d41c0903030003000950b0302c000c01240d945500200305501034101102 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378558516 1250 378557266 378557269
    0x60f06030a09020303070c14100e010c03030f06120c0f08062202181b030f150a0e070c151a10110709060f1514210907050103061a09 58
    0x650380c0184111000600c2030403980100317007183d0040100300c9507484401030a0100c80b040c05d203050b03d10072081c0c800d98010900107202402d40c038020004503040c0300c1e40104101c05c1500c0382c0c011000d0348940460900010750740c1d04026504001502040365182c15081011500d909400e074020708485401d4010f2025803107149000141a4506000b000940501b6000402688800110700e440c160b00712a014140d03d03004194000c02c00000080302d01010b401c0050024803200399000c1a04562a0b203211a00201e074400002c9190021f603112104503c0074004204945030085500c1d5241801038040c44000d01000340000129a1244450754103100c00f010603107000c0c10104e20484070702c45142090140d489100308030518220082d44041d036119101c00c1c040c040c03d44203a90000091849081888c0c100c071017400c0141c0315505124a100e161080441c0070010004820183d06090700100420307101c1d070411a040540381e1748640a0180840d04100000a8504100c0d055023600d80341d5505140c2802100d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378559766 1250 378558516 378558529
    0x7030503060f22050c07020a030b0a091a06101103031503010612151503020310050c1207020c1504050105121005150a0f1704111504060c1a060f 63
    0x1c1c8081e401018070181c01001d51140e26862102e0512201034011107240b01e928241a1900103100f5441c100c0280b001c03900580300c0c1d000309070540f03500c107c0510071503a40f107980000900c0b4103407010300040c0b024684060396000d0b075514a070140700d00342e0b00319001181035034040d0780650101c0c2c0000d200d68810130004044c041c0c40c4083c10441c1c60000c00118025941d8017540c01880003515051b83c0700c428041c4000d02c407401c50300c41c84920190b0508000c02240c61600020740740c903641c1024080d00d40e2100c000031046034006045400d6134180f5182080c80381072000c0000d5071071080c9081c00d030040b0f0035111100300d07101d5a001074500f2160141c0d1507500d03260240c4e039080078008007c0d000d00f0700442003000104555850502c8500c0c44400102100e48130140307250024480c2c240c269032882031103080c0201e14941204516000d61098210244002c4031160380081080101c0400c2d400303824100100b00070420590007a0b04940441c0503020318880000840c10103280d04070300755402e41c1d025003140084800c03420400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378561016 1250 378559766 378559771
    0x2001090e070f09051e1305060d032012071202011b03091a0c3f0403110a0501020a02071406040608071215090e011e0e1617061b07030503 60
    0x80c0f901140c81a610000309030b80860950905100062050031000d55041400d49114401d80f0a503052025040c043c02081e000c0080d07176409000c0001c0716446480f03200ca00d56403105481d001078100c404034003c5a04603c660703003003001d08480352001c0700180c08102d0301c140110f550f0850281210a901d420700072040d0014456010700301c80c0c12082c001f1000001c40c00b400182d10960004880687d1580001c003158042c02001c91205c2c0310007000040b400d40108100a59604040c2c004001d048648403402c065418004d43c4ca2540c0b4a40f040c1c600c2641000010340180c0a40180ea400301d40403551901d01c00c01c0081d811020840e00315070700341700c01c0064522801d07050b50070412038100504c08440c0d40c1c010f081620000089400d440c20303d042d0130000d8403990710940c000c541d50381d4000c0103104409a03081000025030700c0000201358441441d080101030600912506100b912821181036076a03111041400c5094206107016024100c000340c040040810079001d1410800030301443d0081030707034080d82e2a4001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378562266 1250 378561016 378561047
    0x9100c0c05211b0a0e010b040e0c1b1b0a0b091306080f03121303120b010e060d1b0503060a15030f020c01050603011a0a0b0c030d092001090e07 63
    0x2c0e10000380000305015030183e44541c2002c400c0248440000e11100d10034541c044002c190040d0300402c4200740071415201507803040a01850039440d04907113042c0c94010300c7c2c07500031071a01c80f03048100c0384500001c0d8604500a00c4010400d0b10304070b602040100042889150f051000420012145150614421011840c00b500c0041c0e80c1e610f40b084145080e200b000d84610907030002031400c036010310216400e5031104462500c502840002e5034000e1001000110403401241c0b031f04080032aa81c0101200c0c1103500300a0400350b11000108441d8000d05521084a0340388017402a801429600c44c0c070031203110360005010105154038240e2860518011008140d04043c0d03903c03030084031004c582c0024004002100008181400c00b20201400c6400500d00910b4800c1c4001c142081500c60503407100488100c1420306840742900d01d80c00e0b00310304c40d5003166880a40b0301800d5000304011044900600c50b101e036400c140e529201801500d00a8460042c01d00022013500000d541c035100f542e030707030f25900381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378563516 1250 378562266 378562309
    0x302040e0a0c032a05010c080c0c06030a1d0a1101050a021213031119060c0203010b3a0f0b0705130b0c2103060603041b06020309100c0c05 61
    0x405444282201819070401c4030520190070f46001042c0104134422034042d0300e0364040410710729083c006409850722400c010910f10f40455401c0404900303000040300030f10013070512592031924962020040a04040445c01844c00c203410030410000020b00d044000c0c3e100c17010340580140c4100659554004d024404114403820b84001e1500c01c0c244d019003100121122407402c0c081c1141703084100e07a20711426603400340044140030141c00700318400d050122650350824123102ca20600220703000d4002c60340d91580100030001b00c0100503000c444900c43c403070160b0380c0000007031082c12605c4941c0412450050548111100c022020070519141141c001420303003412032401c0c101c1c0f544080c000d013491344400d03880c036004943c6a0316a0018000c10800000b2414200c1c0c4110900a2422590101800c41801214084000740810404500d50f06040806000340800c41e951101c0c025969800303820440c5c0503d000c0181c0f8007445000708410030000d50b02003211801c4504140510040000d21a403603a03d008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378564766 1250 378563516 378563533
    0x21c02090a0f0b0a080f0f0109050702010b091f0b160204020307091206050103171c1508030c0a05010b011b15240e0603060f07120618090b06030d090302040e 69
    0xb0042e1480760003030400030000d94807904140c0c4040d02030300c0c000b01000c240300990410020702e400000c003d01e064986001c000101a120700704200e0043c01d41448890300030300c42400b8490247e900c14200700c2083d6946440010300b030b840d041071225034041c0f624066911061180a030f0300500d42031b0081c56106601d13286c283d002c03554a002d40d82030a114104141c03456540c400c010700500905080025001494083d0581b034058400c1840c1007410900201c58405513860240550103205441c4c40d00041c0341c0c1c2e1017200d0302d860840c2040c5444400c1594103d07a1907180c204500d034954080c0f014002d00f0500288090321715943d5031180b03060a2680c04503070003100d598003401110110150180f00803007003446041401c0c0b038141040040c00100160405209600ca0410080b1007125001c201d54055802e14000b03091a19424991010340b10710381215020319030070420451965001d07800074515600810342214585c68a000749901c40814090400000794183c005001500b4141c0016140c842d50000311007051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378566016 1250 378564766 378564779
    0xc12070302100f0b04060b040b1c0e03030103050f1009170a0309080f07060e0105042a05130b091501050f070c050901060203070b0f1e060d0b07050a0909021c02090a 72
    0x40e8407072102000f403503680d645085485e0409100310805401d170420f9651415041024940c03041c0114800c0142805068051104100b1035070030580250fa0359000b225240e5841e85001e5880c0e80c41d40d42454901d06c213807040c804280c0341d039008110816030003013030240003188080c1c407004640c0d00041c00300c014162201c07014000190258020701c4055010481c40c1d440301c103070385009000d44100c03a0040c5070980c105014000402c1044006a4407c94007040b01000401d907480c2c013865400311079101e2a84031504c001d54182008051b0041520f103142207808104a81d0340d02402d0300c001074005c80700b50000783c0030721090485030660ba0040c010340e40101407c840607940c400000d140564260040f40060b00042502004c01c48d140d02d10b16000120a00446428a00020300407546000100e44190030640751010548a45401d000c0488c015001080c012591034005d8004d07189601511001c40041d26a810002d4003803014070903191036601c0304906402c1c07180412065030294100e49409580007c1c24803001070320317 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378567266 1250 378566016 378566021
    0x711160e070c03030e101a0a0f050904051e070312080906041b031704090b010c050307080a0302070b150307060c03080109020a020102091201060e010b0c0d1d040903080603010e030c1207030210 84
    0x8a06e1000750204484040c0600488503a240e80342040c06129018400d0080104040c001800e0b200f098520000301e43d110300f80031b0f1070a40d070303035015490f103500e412a000e0302c2c2200411400c0c1583c3c0a50840003440041c20302c2200d0040d002c0b00c4900c000d810520201d000210b8202e07035112040000119003010341e80325280c1101c0748a4494180d003404d0000201002078114a0080c8910004242800d000a50454881584920581c00028030300180020b2407070703a0901942c15078000503002a1140311914240609032440380780110600d1185c030a00e42c1c0000c10502c62900d0501984d41640d0709081070b464480540c02a420209070401555000d10005071543c40c0c800031142d82103070400009c550300c0c2c500401c00180e0b0f030b010381103911030040400c140000003900140498810741c40703150a4909030a44c142015901c41800551a03101c3e040c0040342040c141c0c4200c6480c01040204d000300041450022001d80d13a03c03504041c12003940040c80790034008105900a0402c02c1d000703006030b0f1080420310100004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378568516 1250 378567266 378567283
    0xd0e030f1014010b0403080a050d1415010314060310090c0314060a050105040c080f070e09100303180f151103040b03090c01020604050c040e01090b0711160e070c03030e 74
    0x3181d0b40d84400c22202140065142401000d0f4440040d1a003030035a25000014843c202007070040c04800684416400a160303c029031018400b0b00c4007000b4107028108110000c4d142a4a50009081000800015602030040ad00400f002002081740000700c0802c0000781091520503901c10603602d0000000c02c803102c0080c00c041a09078003620580c0f80070b004800441e01c041e04914040ca142085e501e15203034021502035009000004400115a94000300302c13041c0f0081e0301010303001003404c010300c01d128020f5010f4800f940d00c40d0311168814981e82c00c1c508231602c024490818021141c55040040c0351100c0801b030200646403404404001092068900d141c0c4158040c2c08112000810803000000510007500d880200340301802c400d081079100c130703039958068001080c8503954480080303040358805d6114121a60f40000425802e00d89200050100341c0c060070504003501485207202842d9682c0c00310a0281c4018641045150320340321030403030364180d10041c03c41c2815620b406000710190308120000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378569766 1250 378568516 378568543
    0x30609030301050907050909010b16050109060b180c0f1c050f0402011b030e060307090f08030318060408031501030b0904050a14070b090f0f1512010501050406020d0e030f 75
    0x15901e503d0241030003003240d00105140d041010a1000d07180543e100328040c2d04649e094004280c80310340708100c201070b08c44000402003156207055005420450b40390880780c01a001140d00109002d0313172094201ca40901203603030110407032081085c414214189000ba000c62a403412051070b01d41032401c804070481d02d0940d1040e9400350840100011581d10080f00c0403c0004080305140180041d580580010291807061f80b0076180800090016482103044d00300034500030890f0341e200ca98500405071241d20a90304030002c440403410541c9514000546180140d522049039403540d0b403152078404880d80c1040300c0c0c80c100740d21554200704990747d603000315000c2e84c010b13000340800d00c142d440c0c840d042a40003014120340b5004072008001d01c0488000f03641010405540d00c006090040000a8038803040c00c59080e4011100c196006072241254003401050300718800d80c010316622040191241e00692140c0c000607888600c40401c0c0901c0703000d4800b2001806422981e040c0f008000681c2040400c40750103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378571016 1250 378569766 378569773
    0x60f030105030c0f0915150703170105010f02060f070c060504052506140d0f14010f090213031104060806070e030c041b0818070314100501141e030609 66
    0x140810315060000340f0310310008036280c1070399201d100041402c448004213129804088140090000e4856112100040d120080500e45e035400314503002d008594070441848207558010000b149035401160402e003114030340c0c4c00400440e5280203080400d484002e00c104200261101150006805030107058081ca1144010300340c80c0d0031640c7c1c407515203540c0c20040c00b6012091007007040410f4104061020700805803210a40d0b913510700c0700200c06000c1490300e404401e441e24001920b2841d014000505855041c01c058215540d901d8100083e402505a0b244020700812410800200800c0d2074030b41c184809000418200d0750b42202d0750500f40101c6808010816039030364841146024400c1c00410041241d0030400200002072a52060f007480c1e200e8400e0100c032074049100405003581e5101c0106400080b0342d40c0988a05d0424800000d000b01030400d40328034401044140407a00a960681340004130011104c1031403010004401d80080740981c000d2a0951301416039281801080d1003011410004c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378572266 1250 378571016 378571019
    0x706080415050105131d030309010603120201051924080c01030e030313030c03021507020c0414070f030c0905030303010306091103030c0d0c06060806040b0412090f180b060f0301 78
    0x1552240c1500c248034034410b18080041c00702da60303512401d45142d004241c0c00106159400384400da501128100c030481448040100404548150099400d40b0711451040c1000e044d108400d074280d400c01c0e42e54460b051038034035801c2c1308241d495101070f0345001c5c8540380354013460240d091610801d0254004000340e4225100e02c045650300750103986103002c645e800441c41e520785282004003a1114480083c100302a40300250706151081190b01c1c0082090900f003d2582802034001e9502d081c40510709015908002c003d8040020025190384183d401e038030b9103004041098000c80c010680803a124050041500b004141c03a14108041c6000c3c602c14500061020240c0c10b054182500d450a030760f1081d030042041d24009900410b08100c4281e803030804162102c01d038a48a0040c00710743d004402140308410800007480f5807062451301550060720070900c1801c88007812100e070b5400d80554620303140f00000802c158840c00840d0741c40440441d20001c1e103041c1c1000001c2d00c42e84400c00300000750070702000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378573516 1250 378572266 378572273
    0x6060812040305070b090f090109140a0218011101270510090c27050408030720120304050705030307081305030309010e040506030c0310140603060f0c0f0c07060804 72
    0x140c03412005859450801e451a512a5601d0a160048541c5000c01103141000f0341c80e684281400c565009220b500c541d038580030580000d240710408440034000c0032000c20155031241c42120100c03002058140c04001c0c0703810054519401d6000d00300001e40d40d03051400c070510301c3c040c00f004040f80ba4003002d416050321410080d14001842000c202c4282c03500540d03000082c1514509800c540c140008145030100c06400c0140c5170082c1851040441e0500041000300542c08008500c41d01840d00c1e14000c1050400386542540014089810a80d1029014032031454202010b942c6c400e100f40100d40240391280c5c00310b0f05503000382c00107d4602c4408285806240300c2c06e0500b40107068103400640c1842c41500000f4400020711104034001d44d91000410000e0314140698516400040c0c101c8516442034000c5800400c000c00d13003000030040c400041011440c000c5134942c080c4405408191142e11441c140e00314590065654940c40002001591002c5205000c0a0000c01c4c1d0354440e29410300c0d2509 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378574766 1250 378573516 378573523
    0x3180102031302181512030705120901180303050301050d0f0c03050705120f061611011409010e06011a2d120c090d06020a020102040e270a0c140a12060608 68
    0xc995661640208002c44a002c11500c0d41d1060403120f403600d044480c43c0460a501c501d4001030480e01410840c51401d0603c00012f000c101000c0e81c82d41055a032045250742510b449000040004004100400040ca0040800400d55000d80d14900118910313a80d60540b422150703108640980101400700281d2030302c0c19480100040031805406468044210141c80fa4002800031200e41e0070914400a06803007001000c035065a540c1c004c10607500c1303030050038000e00e508580740c12a5600740aa00030649402143d014104c40540c258024407850310030880d006500700c40414040e9400b905420010701a00058038a02d0207255681280d0f14801c0000c042d65140c001400c4c0d801c1c05c3c40400420200d5252005180070040d0011030041c1c44010f2104100e000e881698032040086c0c10f44800c3c444012802007a80104041d802203c02600ba00c450300340b40c40b440000c00142241e040a103040282060070880d6884000380107085854a0f5100d0703040240d803549803071b4113507146680d0390030901c00c0030000c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378576016 1250 378574766 378574789
    0xf1401020a030c030c0611031807080d09030b040501091a06190803070b070504091505030c01090e190603021c031d03030403060f09020a0e07180b070803180102031302 73
    0x80c03014061941d0319441c041c09050842c0c00041c01c0100703400c41030060020941c06100980c0c44900329941e68100f24a40d6050000a043c0c0c2d18903501440f4800241004000350351550000240c64030042945581c40e41c0a181000500656044d505c2e56610000680d40c900c0903048018421000410703420030700c040c005810084c4046400c0000c10040034820481d0000994801c03680c82100320485130b41d405812078442c001c0303901038011603007040100b400c1084103410301310980340300f41d080b00d02e156820001180c007001c1500c01d030722030558200041000000799040500c0750000c03002011512030340e00e40c08100200c20703080704e00c2d0b52010302c1c0c8045410540d104035012989035205002d20252100180000c0d107e202d20b101c0200104d540d0042d040103c1c2c813980100708559001003110341c0440d55640c6180041008580500000740110b04100358402175056120986204d803211600b405102c1d0340b16217240c2d001400d031685d8212004003c043e91071090008603c101154022002400e106105010107851407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378577266 1250 378576016 378576019
    0x304030605240301060b092701080a061b0c0f0606050607060506030609010501080606190b0f120f0c09090a0f110d180210080c0c0d020c0907020a0b0606030a0b0a0f14 73
    0x117010080000310400c0007a01d8110504a60a031303d149403009664100507074040540752104850000018140004101c0b13003a064001c9200f4003081e40081d41c400c030344c1c402c02c40000001c00d014429a07400310309903d0000421501c15800080c0003502c80c00003842c150821101151002d488501700111403c003403021a030090740c02c8000380942c2d41001c0f685619038000a04041c05000540c100544441000c21070f43e009140280c400750340c800b900090158642d0122411000c2c51059101080440c50136586030b5215001c0054024109400f440c00c200076214050000007640f81c540742c40341645480b0380315200203010f2000c0196900c5c490b021b91882540e8042105143d88051380903400c000d41ca481201d1542d030010b528041003160f44501269074140101c1140031030521880e002080c900b030f00012101038100040342c1d022001c3c1e0395000f0407640e4250f032280003043c000c1c0d41c03804580d650800740c3c00f540e0000542900483c0c01e0300e164001c42d044c10f00380d5202c01d01207003130a001000b41e01058604009070600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378578516 1250 378577266 378577271
    0x90803090a1e090609050601020c0102070e04170c161403010b01050421080703020105010303020c060432030a030804060b090c0406050f070212010b3f0304030605240301 74
    0x44600054500745507100d0707400060307002c0382c60180c10300c2c507801c0c040060890380c0b0b41002407a44480c50754009120882d41d55015100e0590300496030341c00058800c00f20744900141d84021f81d169641d5175070300500041d5403110044140709410025409102c002031005800031100043d030302c0c0c0342d44480d0404403000c18038041e91529582c10071320799001c4210303402c4d01d4021180032803500b401c0c001034801640c00340c1d0180a00c0400708440d400c040c3c1c190401c2d4100c1c2d0081e0300f141c00d00283c620030080c40d03101e580300d201181141107102100403c01c1407070321811620502c0450184100c1c1c9004130303041038000001100007502c180104020004036100329a1038850a40313003814640303405030854400f48a140030324010301c9000320b884c140c0320f40036200301c40c5d10a5010384441512407502440e0740c045c00b044901640310b0042400c4050007031003000c454400c000c500c103c5e4201d10341942c1c00c560060080785881c1360024001080084046240d80c02658024040c801d07250074800c200101d8800e001019421441c4240d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378579766 1250 378578516 378578527
    0x20f10200c030d1d121522030e030f060c03010f06090501122a020f01240303140d18060b030f0606041d25090605010507030305280b03010f0b090417120c0307090803 72
    0x1f800b41d803071030314254181883d5035041c12100010b482c180d41c0c0000040d00b4800c90081001116455010714100e6801c4400024000e03250001070350a0300340e0307001d8103002a807030380f027140e032002003542190b40110403d104107000c6220340d00c81c03030b02501300003a00e903030240c1d000201d8406115400d1003203111526015002d420600c0b8030a480115402d400c0c0720140401258842ca9084502310070b04950642c3c4c80080100070250800441c2c0240b510a11001d031403052820744039111500b8040364500c04090034901401d01030b903e071410800100724242ca0161001d01100811006501c208001c40d0b201d03000d41049002c02d0340f10001584440500c0c0c0051407030506001c030030029a6000401c2c0c80c2039980c1030802003141d036541003030011805103200a00f04c0712801103261001007400e50b801030007090f805078000d00c105d01c2c08000c1e98003070f103507003502c01d0b90001c454000217400b059080c10151914100c110205d4a0403c0c500a01c400e04401550b403400030203400014044101c1e0010007501c001c141c404051420308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378581016 1250 378579766 378579811
    0x2040e16050d1a070504080109030e090915010e0a110c010902101b110f060d0605041a060403150b03060103060b13050c0d09020f10200c030d1d1215 65
    0x1480c10881c030700f110090340030108020034041d200b41c4018090002c0200b0101c180c1e801c000b01440d403800c01c040d0150a6403000700e0a07856011503c00700c450700c208803030031459107028070013000944020504680290b8949102d000854400001d00080c2c0f6074200105403c4010300421032840781da00d03290f0051000e440814240161202150800c20f5040703204504081c6d03174a0f0204500f5a40c00b40307020740c00b201c00114603010403020b47c403150075924199004c000351150090300081c4540e034652a10742c000b1090008200050a00e8500c0700783d01030850012401c180200d02107171903d2020303007080341e01980f1000d40e84e9903400c004106110305018948140118245160342e504140709182461407215100c803c03070304c2552580d00400da504a40039000012054140c00d00421203880c0449448401c4280d00c500b082864000034200410700d4001c1c0640b41c1c18140110503105628504d4606012054045201c4c00698036041104110701c86800681300c844101c503015404990020415516090301c1ca0058010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378582266 1250 378581016 378581033
    0xa0c05031905100203060406150c06050c090319110402040b030108060610090909050f070b09030f0d05090105071401060909120201050421020307140d14090105030609040f02040e16050d 81
    0x12143e082c0e00041e0b482c0c90303581c042005007903203410001300381e4601c040b00e088443e070000f01601540e004800400240c2c0394031680000d0741c0b00d00691590315070321400d140300b200c07005c0c2c00043c41000e100e180840f100c545120046000c2e42c2017036101c0c00d07100101100400c407800f014840b05030b00100c101c1d50241031695186015080c502c96009004000d951800040100b1108010f03650b20320203108211440c01ea69841d000d842c1380d0112007100c1c081d02405983c020a1f1800092001011a8544881d400c001e648001100c0c56042218250b07035030400500d0103d03000d4000e110350740242c0100c801c040303104092030500e8508481c0450512046a15110401001c05e41d210354a03490321540f48160454128004030481c6907004440000d46a14144a00790700303040c2e400074041e1083c051a4a0f080764145404580f03845074014242004d02040b0204001865440c2031800181c4c850311071a46e222260360b00350041000c4451000040300340ea44042090300c00d4920070407078400100011594002c214005a0b00d1018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378583516 1250 378582266 378582283
    0x10f05100c0206390d030b010801080d030507050409020409060905061807120e060f100b210604061d0609010504020403020a0506030a02070b070c0c0e131704080a0c05031905 76
    0x319000c80800d10b5070800350765000022911071408013201c80c1582102c54546a0f101c00686101003841c01ca00000a07500801490b8100da0007600600312005900000790007402c0c0040000040220410010802140620190010303004c0d01d1130000b10340f070a0100c0c4004031000506824400c3d8003240348031741c0000000d4071a541c414441e140030031080c01c45090480c042c040040208034940104070801c0440040c1d49681803003807044400f05a015580e424903d140c0344a410040d000c07403000c540041280d10007041c0b0070781e04030303c000c0e20000d140c85c0ea40d140006d090300c070450600c0480640d441441054a00450718074050316003168110701d05842d503400114140010b2041902504c008000906c011030b19070b042e20040754200b8140e17411442c1050000301016003000048800c03007070003000411726900710008688075005580c1e041180b0038440e240c03844149849241c00c0c0380d80e40204030104e01f60109001801c080392049a00310741c107a0501c0c0c201800c0c101c1d03c0e0070204603850410340c001d0128000007840071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378584766 1250 378583516 378583537
    0x50d020d02060f2107030e06011424181c1712070203071a011a03040f060f1d0604030e01080a090b0403050a08060306072114010f05100c0206 62
    0x150500a188040b803900d000301142d03103842440202d102c0c0600321030b004128010b0301c031108001800d42e540410641c01c4030080c05894041ea84160014040f08010303102c80030101c000106014000112003c66002d0780d40b00322242d400c4030300089124098460204480366000000b04c8207072109004004092000e4010a04050212029021114594806030f03045a4515441c543c00013104e01c2e1260019550ba403040d4000c0f194030345400317950410800c1e00034525061350382d1503d50466641004800500c15040a001603e020961002e51340c000f991520900b80000c070303c1d2901155080300c00380990020501e14624a4468004004100020340d000c50560417040382401c0c441c1c195220741a5200051485100050103104103400f84001c1c1504207029148000c050b41c5d9008403503076050700703140d100c2c401569402c0100300d04054020760001000d90701c03400350300b070b24200281da82e202805405400300e00ba400034055610a00c01400795046c05400610382040ca81401307400080385e5400f080052003a03d0011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378586016 1250 378584766 378584779
    0x8210a0f0908031b06010b07050705150c06040308011d040503040e10090c02060103060501150f05033303210406032a0314090d080c0a110f0a051006050d02 68
    0x40c2490045125001424280c03040700e03140c0b844050b200c08484134808011180d84252000090a4641c4030103e8040542c40380160200515080030300101d80c00c1a8450b10311000c0910000555400420480f44a103000341d640d552154900492504010b0f01e5030b540c40d40c4070003d5410440424070001c111812112a81810b01065594020f5080e04100c6608800700c6103040980100002d640015618140d03405910100714590341c40d01c24582064401e40d071400450300e02c9038806501401230000d1079100c0c0c0f100504548414403024282c2860b40c49000c14003141e4040b80340340419080422103520007801c82d148a0081354504080b0300000e0043d80300b128101a00d40b640580980e5907032403201f030300c1c40e01650b241548410161001e005080310b21a00c00c02e00d070b000c0d030008a08041c0001c00549100e0769440300c0301380e030300c80003002c00855014281490a01010303d5801900002c2088262811400c1c1c10150501030003d1a100e4100424210b61a600301d0900c5814801681e50f01840071510703034103c802 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378587266 1250 378586016 378586037
    0x6130509040f020d030801090b010e09160e121c091d04030309080d020304120504050d0201110a0b01150206010501020a030e10021f0605010e0406031a0c16060608210a 73
    0x52548070ba0100300250400c0361619160105604045814161142074400340b02c072421200c011980301e605a041c041e03100f020303d8042640b05040956542d0722441138a03182c91244600000f03e44034060300070340d40d0590b920451141c0b050101d00d8408050b48602131030440070182ca0304440002d52110f0405082c40b051045020a04041c0070350301940d515584942c6460302c61529800c03103070094004076010303034607002483d00c107588030392061080390150b410003000da81c6241001c1e001141c05502800d8022201d10988000901040700304911500034600541c46481d17050b22080d000741010303c1a409581558030460302c0f08000780e000a000344241d5010b032540030061460345012450001900700c8a0403070301042da42400c1e440d480780c00c05c4054580030f80312600e141d040f542c24441111446d01c8044d01c0e9103c41c1000ca8200c00e69800281d0b08458002092403c003920310091140780d4002a4040300c0c90f039078442003080006407c3c041c880c1a007030fa0300c442201c84802e80c400d05500d880381d0303240181000203400302d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378588516 1250 378587266 378587273
    0x51f120516300f0c24050307030e12030c030103022110050a0917040501170c03160c0602041d0a0c0206040b0702011e05100b03040c1e12110f0613050904 67
    0x551810841c0c2200411080083c81d0408402184c0107010341c1c00c504079100c0380020401c1e58401502c802c1d02142d540c3e40e14581d1001d9040b0000c010b400401c15241c0582d101d100486d004160180d4012000500c1107580c0f035145104200c0c0b41204094103400e144003418000e050604085420584451031070004615580c41c0c807031300c1004080c00c03540101740f02e81c00742c4440102c3d1050000380003502c4080e210003000c0b18880e2640500240c04882424841c601000043c10040781064100411580d504141040f140d5568a0070b00343d8110303400100481000408419000444102c000d4000040200c108550760340c41c54000c0d01d5240084c80030f02800300c10f00200303550342c0c402d42c040c01c114040d481846c1044140f2841403c0a09000c2d13400110000c5182004946407180c1c1080b0b902841d4450440c41046181154803000c07400c409407c4180310400c48400144100c1c0529241019449140079841d001880000c10514128055607039014003020b100081d020301c110800c40381036400c100c6544d0301958942c503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378589766 1250 378588516 378588599
    0xe1902040b0a15030609110c1f1517100b010e2223010515040611011806140106050901120207140327060715051f120516 53
    0x280800c1c0020301c011803c5a00d43c0c0c0c075038003400a5a404180900141031480c2d1490f60744e000d0b110b00700780765030084100d2200e0000182207101d0307081c0a81c2e03004100c202e4548612454201954001104192070040c0c10030303101403d00200502070440e28080000e5111580001c0c00d000040996600640800078111221100280741c80302c01030103207906014503014810b01141c1604101b00d85e0b01c480a01000101d0540b500000c400391502070b018a0794105460900c04071410083c03002d840c000f5550700c4003884100881c0b6100d22001c42c0c0944000b04185810203665040d0940590104041080c24425008280e0740800b140503250042e500150301d410481c100803006076002d0303015920620000844400d520a0f2602003608420000300321005241881c00340702062103001d000a042e126041500d078a540301944c44241c001c601603c074513544002c0f0403007004c13400c0c1f607907000381d031000c03052181e0300c4204030042102c1260841c03c4c0b4030894120340f401c16141c1000c01d58488040d8240e051024240c02c210481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378591016 1250 378589766 378589769
    0x501060e011e0f08370f031d06031b0d0216021503010506070822030813050103020c0a03030905100204181802010207090c1704080a030e1902040b0a 65
    0x103540c240240d5070340340c058000d0400e10754190542114002c000203610a075030540401207828030409080152200c05856a0303010564005074042e80711512000c2d100c0300c1994005151074810410b884100b40340e030a0181c12581d4810f10509500e4141004c26216240d03c810f6941050701c07500341555289907441d40f40d80c207009481d080c8841074400f244000050410101680d1940d0090718076001940007003010200500c0309016064005104101c4a00084c611a006002914040c81e5078040c0c070481c41284900d00c0c81d190710a45501d00c3c0400c85410741d84120258100a10090808525100c03031182080d44400e4580000340c01d00d540c85070701c0802e00c042801200201181c035107007156116181c9014902c0c00c40d0765040001e0380351a01c25a040200c1c25403203810035464050b0014038500d8949510f400182a2188401080206000c22184000d8a0359030b041d00680c030070403d0a884080e03004e00241192601c1001301d001d603200c0859501c0300c1102c000910b0703180d6011ba401085100b141804524800d440b13 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378592266 1250 378591016 378591029
    0xc06050a05041d0a060e0906150a080105070305070e0301060501080a110412150c030204030f02121c0306030b100b04060503100b07150c2613080301061106010806040308070c050106 79
    0x200e0700c80e0000040e10fa00c154421014000b0800a040d200c03040d240421204603061841a8024000308405000020440e030380070380005d00055a0030744030700100d42560b0f0280c80440110380c96100340030300c0b1504032103200c400355010b400800205140c403000030007201c0007800e042c0300c00307a1781c0075103034584903c1400f01c401801c80081c40100c006130a241181f011548800c0c403044051034802d0210302c161182c021102104e401141d20030620315180c00700410103010300c0d0005902d03ca02c6088807124603503180ca6408106880d01c000a10300c1c60343c00d100c1900400146045008004841c0c14050841510143e400342c409928055440340e4a807081226a4102e80d080f07440140b2010491004004506070498903c1c04060340a100e1071104a5080d2415503200707204840150060503080b03a900703810250b46038031106403070721103c039800356455030229a403080e0800c0e400100e0b240019800700004000c082c0c0180035243c020582440c0684004140207000780240e001c0002e210505030038840250000c101800d00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378593516 1250 378592266 378592289
    0xc02040e010e060108070801021e390105010b0901020303072601030f2a0b13050a0b0406080705090d140f0d020f07080c031504032d03180c06050a0504 66
    0x10b01020300c0d900e1400b48a0b894840c42220700110344040c043c020b48208480302d00903030004525020b0408056004820440c0021403400711a9001800318625a03049184109c0103403510800700c0340090035034005800121440004100380700c100d0340d0000450f5407001c6503141c004d100001803c0b000300c40355000c203006100396600a0000c01408552440c9071000c0c0d210b0b100e01542a155459510486204074140f13641942d4003010400906620717400800070305030089081c2100a0300d40700081c00c3d001c1944c0000401d04004038040c4403076908001020382050039402c009007400484070000b0002e04003094000d10109080c0c8007070402480401c00286403502c010261180c4840d0760700001d54502c83e442910300540720303500000804441c045034003040398134040c011388140302e4201c3c41040350540141c821020050303050512912203006001c8401d164010182c06151020403810003001c2e214000021801c02c0c920084900c0090b01c1c2e0140320017114518280b00340c607803a0185040c0d910380640d0380480c00c441d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378594766 1250 378593516 378593531
    0xb0307060e0a2d0608070903030f020f0f0f010606080421030605100206220308180304030f0c050a050609090708062101050414030f031302030705040606050a080f090c010c02040e01 79
    0x40c0c00056003d030b0015440341e4400041d80c0705400c543d85002502c4040c04607800803001e2011902c225080940309003240112085c08111481081c075182030412101d0313840d0001e0070199405442802401e00a01151802c440282055140c2c40c00e042c450404904002c1140580195520701170303003200780181001420701841601c8010040e40300c60048030071211a2510144c141065164000b50010a81c0c242d035030002a5600d0440450081c0c003001043c05040c4400d000000000c0c40c42c030b0740c5070000b5119080006a0303515190501210b104141c10041c420101800041c1164844052aa0344401c8503d0103c20584500001c680a02c05c1001d001d000317100241801040a001500140d00031441501020803141104122b0b1f130322801084403100c0344210420100703802422189141407200d0008040e25506903903500004c2c02c035004d40d400fa0010030303808600c3c2d44420b500300510340d03440840e600a070009444d0211185442c1c0d64542c8820741441600002c1d003040d0f444039030140d40c00070b10b2800200000b6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378596016 1250 378594766 378594809
    0x2040b090708090c04061d06030106051c0606050103020313030c23211801081005040c11010b01020c01020606060d0204030503030421020c030705090601051e04050406090b0307060e0a 80
    0x1c0c02c1228440b03403520a01e0a107141c0340c00d15202c0c400031540740ba00d107204281c00305400080e003c00b01030710b01a450f64a030400881c10359181c1080010480803691440c544080310301c0c0c2a01500d00c0350344824181417040c000c00000b604e142010004441d89844d0001c1d03d0041c61174028280c480c0190480c192010701591921800c80000e400d48200c050310235aa4100d085c43d0350b0506d171030304c41c201b1604403000c41300700e42c4601540242c01c600c2d00305548520300c50185440d01d000c0b904031455038500c4000100c0078005009441c2c0300784106009810203102600c3e44081240c0081c1d620000031f804035020328000500ad240000b0715906850155510405a940e82c3c00c2605010b503402e0300240c14817010300030100103410001e0001404901c00c0002501030001c542c078200800c01d1402c0010700303290602104024460241481d0340c2d01c89103080c0151840b90702d5034103140500088a171190001c3e00c4107841c0016014250b540061050211549840c10600c0d146007000400c00c001c4141d4407601c8a0501c00c91109680b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378597122 1106 378596016 378596027
    0x60212180d05071203030212091501030323040305032a1203060d0b07030c080601020a0503041401020307050a030f0e0a0605090d06021e030a051f090902040b0907 71
    0x181d81e503160134442065008401c0b03000943c0040e509004035051000250002041d000810030716103400ca0301c01d10300b0418000a820701080307496042c070f401540c11107480358010300e4400e903032116682c1c0f6010b0b980350059070b00c220b441032003c90f90329100941684451818001b8000a10325034440d5110304000c0d52018181d00d07086100744003040085507030505490300980746558009002c4c40000700080400e40c000d0300160454009070400130100300004240c0c3d05451030202c1001c1c00d9241c450040c0e2851041480087c02400342000c010245504640891000c40b4151248400c52604030f0420a600030140600300c080349040c04241160f003002c4070b0500ba4144688001441e10403186044042d8100c4c0b000c1901c0250000000c10211540901076a500203251021a50501d1440e4218014615540c040d52601c180c1e501d03e510190b59681c2c201851f00040035010384828140384000811 = true := by decide +kernel

theorem cover : BRFrame.Cov 378417266 378597122 := by
  have h0 := BRFrame.cov_init 378417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378417266 ≤ n) (h2 : n < 378597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
