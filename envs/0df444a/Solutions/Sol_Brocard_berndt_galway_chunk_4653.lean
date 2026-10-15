-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4653
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:28.498106+00:00
-- url     : https://prove2.me/submissions/b8925dcd-1d1c-4f49-9fa7-a698ca2cc0de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 836690647 ≤ n < 836870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 836691897 1250 836690647 836690671
    0xc06061d07020c030d140310150320070c05010c080f0a0c1b050a0510030b0603090c090a09020105090f011b030201051008030304050d031107050a110411030609070521 73
    0x2001e5255010b10660501c41c00980203050b505025413406400207003408806130100740000001604d840065100f140600042801ca5a5004140b44018044e10b0707141e480740701003002c48086544140c604401c5885c0c0e207038060500d111152400c0c005583c01c2c0c45480301590102801c0082d03d800704142c030006d042c074070203d450b41c0c6980e190504120b2a5090034140e116060b0348288000d1200c1e83e100010481210011a94925901c10368041100900b1046488a80010011013484260000810b0b408a0010260740b01a020399402c0c0c900c0081e201455000703808160104060491410300b42d0b611171400c0c4040c18440a001c2c015000c40a1240302c00c0d0301a80141d54400521805c0c81100c0d13540c2c0000c001f0030004500794103294850903181e401529094042c103035901c294204a03404001640d40d200d0b00002175550008841c01d00e941214901c0804500c11450305000d030074504079501c1541d02030304010f80241000d40c1c440909803960b600c10748005100424440380c40030f02d0140c100c203140c400d5400201c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 836693147 1250 836691897 836691901
    0x160f0b2d0310090b0102060a1104030c0b0a02060912030402060d02040513050414010b090a0e0705090112120302040b09042007081804140714070206030411010e1f0c06061d 75
    0x2201c0d0000d2095005000036904082180e5800c5e80d00048481c2c00c02c0382e0070b800183c0004402c7e18202c49200d564030040040701c082c00001081841c050140080318516001c0d50f140e5502c0b42451510743c035423404c02c0d00c4580e01c140041005810a032015180d00102030400516064075540000c0400421290f2035000c1034840e020802007212101c000200d5009034002402481a9440000c3c0d0103100100082c40d919921960014480d01c2000140c004110141ca0b2040301d5840305031304a2402140c44082d02c50380b074400c0c404e0380c2207403103407003154100c0e011002414180b000b8102008094103d5581229040064226508210148100410b500c030720403c003d41d03848104001440d0f040d052074040718031440c940baa4001600c0100c8491580c03113289450301340e1074144000d0510f0458083e16002a41044004c0100010040301c0322580c1d4140740c09881d85a001003500041000d00240044070070884061000e400381c1c010300544c0e600380e0540c0301d03a0001c5841c523141c03018859040c0b40d09905070752003020101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 836694397 1250 836693147 836693161
    0xc01090807063c1107050f150412050d0e0d0f0b1e18150408032d0f0402041406030322120303052406030105010c24050702160f0b2d03 59
    0x482d00c04d00005070414515140c0043c8010041c2c5d40030364020700d4948075a401098500084401800004a0910a4108905013135035141c0709030f00d02201241340400240755624041980ba0140c03940001c20035059503036503603030414030100541203031410100e030040045c02c03445080d0134031302c50181403820b84001d51100302510b1420901041aa441c84011001d100c0410542c004980e0311000f91308026113510780c040312100e00445400001d00f00b0384051030038000e03860f0342494414001c5000319800d103d120790f01c51140b24003010650b4850390541c42001500208041c070903002c03089044840d02160510f0f138800360001e000d40d0001040300040d0380c900c00c0048102507210040ca101002203200a624690070002c10342034481805181d042c0640f003032117801000414059041009900010741d1881c5128a40502c043c08060710740d00c0c05802220b8803001840d0043c3c83c3c00040300c8245404000b4036280414442e1568051501d62000307103010010b1424900d004601c113040744030348071005641c03071420301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 836695647 1250 836694397 836694407
    0x309150d06090608030f070f050a061509021908060f030a14060c030103050d050f220e0c0a093308090714220f0e0f0c01090807063c 58
    0x1801c840591490400c00340304c2d07424004140d0344405904010655604864103100c8517a80238248024078a101c2c2400041c01c004803078100002807407184d151090b905456030780c004142d005440b4144007550341003a406001c81c3c071130301f0f40580096001d001404031700c0c090030203e4103100883c1e105954140810a01841c140001c022403503111141d045081c1c00c5504596810391203100e0400c0c00c108000b0041090900c00013003204542380001910700c560362907841603440e10740d00040b511030003000451510000c1c001c10800fa080b640240c1056945003a2541002c1d403200c0c1e200c550550020540b0700e0700f00c1400c1c0c10000c907090410b850200751203080c03aa00d8150070080c07404505411144000d0f410300001803054442290a044020171280011100c0404990200040101d0410107041d241404155180c0300000b007a4041800f0601e4140c99201581c0c200540d080d200758450340c12154004c0b002041030701d01c1610100c8290f00c602c04030106515001201c080d104491060740094242209202c460150b080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 836696897 1250 836695647 836695649
    0x315040209011a071709041812080c0912010605040905030403140705060d0e1006090c030b0925030902090109140702060103080306120703060e07170105010e041101020309150d06 78
    0x800c0200b4010889007004030780502031002c00070030030703403422100c60042145517003650883d1034081c004108043e0341c1301c0415445505030300c1c290340031208507990040700c91048203182e100710700086d0510314010000041c0301c6030304046948000c00c0c0d5a00d010124032550340e03000303104101e4011802151034500f5800c0c5804e0300400341002d42000d91052004002a48900058895407101c4580005c0c080d0910141d00c1d080c118855030721482d4610345032000c9003811041d4080014021030380d0b002c024031403450003489003c10050b680055400c0141891182d610b81249840c1101c024520700414603c1060b030200e0450882a000f02c6030711740d11403100f03407064020140c0c3c1d20b038070a5891000341415455a19210454400a021940102084400102c4460081282900440d84003004000e400e00c018100d50f1201342c0c0b40686941455180b403d50000c540500a50f070603034112a400a009446641c5c07072182e00c04458201078103500083c071179000541d85800041c1038904034402501d41c1d440324001408122011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 836698147 1250 836696897 836696909
    0x61201051903030e090601020a051023130813031401061a090907030b0303040b03040b07020d1403060d021201390c020f010c050f1f020406020c010815031504020901 72
    0x2041001c02c04640e000081d9101c595090322603001c41e448200040b030800032060005003103031041d098221748101d283c0d0300c0020001d9030b00c900c43c011640f5002400c0310041c0c0948140103246501c5401d030001c07460800007002500780068001800030b60700d0356501d116081044602600765900c100420046880b0074000e1501c41c001c101d458a080400c074001206558054050303c02c040c2d503810702c44240c0e1410001c0380c000c0c003900c050b141c2e1689403501e0021030007101100d000d0010b02620200d210b5290140580c3c140310314503001c2242c1035549110030b1110031146198140da0101420b41c0b14a0940c0082c4035000c2e1004000401c01000c28007905266100c44016003411240c100c05c90030012916801a810f07070307044e603044070704020b20340030500100e9070b240341c0010261132401604020902128001408881c0c026040301e02803c410121400d0801c900803072242c10096003005610f001c03a5071050302d845a00803141d541c0034550800400c042882c140c421039400f50007074400414030007980703840c0300658010a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 836699397 1250 836698147 836698189
    0x1141014042a03020d0905012c0703030809010605060d05092b050702121603050705030714010f0210020a18120302120a02030d090c0314010c081b040506120105 70
    0x194201c00b2103201c1c0180030101020031030700e03142008582d1103a01115458a83c003030091042c01c250b410554006c003000040311048004a4038003261a80840c02c0500e010203112003d004502e25503281070f02c25400050100301a17540e1500003186030b80c0d80c180030b45031419031410001440e2800d901080d03e001d007803008a200c031507403007245550b03040f50842901101114501c2c00c20303150f01241c40401c6138084501c00c0e40610f401b45802c0002a034402c0c001903002c50340240f0440d030705540d592042c035072549424000d820113002800c80000040d40107040202800312144101c0d5100320020392444102e030003200046001842c0011a800740c0c0e480d80d0300400240800701c0032203800317181c80e82c1e010755a080300c0214000440c501190310040e40b0f00074015185800c82440081c440e4000038900380020500900045540c07400707100700300d5400c883c1441030702d092042c140ca1340580398440c10015030708000f04160441d40403000b0800400c164072100c0260034511008540c0449650412040105406550714101d0200b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 836700647 1250 836699397 836699411
    0x210210506030d0507020a09180c060503090a02090c0c0601080c0a08030405131817030f0a021602010e13020f0a09052416140d0207080714120114101404 67
    0x3a4011402d00100c00c0300c0d01302584e07101c00310320118131255016401080e1003071601c8642c0040c2d400e0455004c441c00e100d10b400382e440b9902d9010541c2c0c60302054802c802d595121003444001410245d04a540044c1048001400c1000c10a0b40e1840c00100360130080300764001c26100f0340b603070500c4602d00000c0c0250001840c1401c0c103040100c0c0f00c441d01144016200c98031291043e080341c2f1403406040c07480703400c003101201e050b01e80c42454100341d00c283d0f5100080411744001881c14041c078800d640c4000c0401a0744040310703e1580046402e40c1400ca0300c26030101c050070041d0200d03082440200704080d210720500361240d0403210007410010f40d40c2c4c0024080d41c01200f0a4034900b01c070300c8a906201d4841c8006030b8952130201000c0102301c05005004050710030b0404081c2540c44002103450303451942d03900f12070b4882e07201c01f2156141c60652243c401003400c9803010307040914045525119130f0100000029544000c0d2500b80b1202005540c182d01c001e01280b0248418074400701010454401650140004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 836701897 1250 836700647 836700649
    0x80105100c0b130c120209240312070506010e090a170d0c0c050d050a020607030f231008160509090321010e011d010501030f060f180513020117040303090210210506 72
    0xf8600910403501c254070038003004606a0f808107402848c030400340031282c0b58a4117543d200344c5a8020034003940d03c0d02c00c0a000040428082d000148902c20800240c491070032683d5070628142c80011032040c03248802e000581d105000d92003450780843e040c0d070310144002c00c0380c2030080c10100030101400801000700310704554250006003030b40d0041e0861070300092018500000000800e02c181c4100352003400b00704166000c0002076440380c010240283da01d115240d031030300d61a03510003500342c2c50605070f41100c1c810080c9140200c20320368415140e9049c0c4c2c0c904440380c0c090411407070b003040b00700c81314440300b5006000c62400c005242e409424484a01c25025000c48003840301a80c4c14468241019100d40c6015034030750403900a04010801c1184044a00c1d8a070300c0145030740d00c907072440e81a00e50326200000f003141003686256135955070183c5615680d02e8a0b400c2035046030724002d10a4051644481c2c1c2d00005848500c0c0049008800d945c6100040c0c0307007401c52400c0c81200c030000514480c2854244409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 836703147 1250 836701897 836701909
    0xb060304030c170906070317151c0309050405040804170c0d11030f0f0d02010b15070b060d1208060f0f031c02160b0901080106050703080105100c0b130c1202 69
    0xc403904102d8181d000c3c00c0c802c1d008050362095031030540d0025404a061000c06401c101d13111552440700c41803029983d10040700209041d00c410201da41f08415010210180f0800300400c0d100078001d15080d1446900c60000c501916000d0381d00712051900081c040044820760032084020002034006403168840f54400108c41485c0e0b41c9020300085228507031140c45950400c50140c4501e020020740310800c9050307100325298100e050062001d5400c1c80441c640a19000381003440c2a087d6a030001d043c0030b180d40310388040440041c10035821940301c9a46401103990219171009020f03d6955030140391070a0000d01c1928154128098087e0000c1044007645a40100d4040030405800000d000c0401c1030901c120700c0c0c0092001140650301030100003061551a034001410400c100f81ca42519590341d03860308840c28840c4400c060001099500180401c1c0b528209485144500c0d107070428000c2c446440b51840c41c1e1007622090702c0e81104a81c0442040036686c10b890061807141c0c2910703550084d80c1c001c00c803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 836704397 1250 836703147 836703167
    0x50f0a110909060118020c010905210c121809010308031005040b0d060504021f020c1801062a230601050406063501081f0c0e040b030c040516030b06030403 68
    0x30751070046405d0031040c2c1803180d0541d484481400008e208402250410716201d400d90403050b1400400700c0200040c500d81d120499580110810003072110401d0b441e410392340c03604442c2d02e00c024242c00b810088000d41e6141c000302d01a601800940d5503a090050985455404a5003d43e0065003800381c100c200c0d13910280d035030840640086000c0b0360356449100244440e40c120510f000280c0000040e1072400d40d000441d842110b41c1030741c12a01240400080d0900c845003485814000f9002c1c140078100840700e00e0420150304c0300501c03a002a41541d650325000401e4041011400404581002104900c10000d090041c0300544080100170300f400700051025144443c1c000f42c044403600b90003403000c6d03124400796080c40c4041141c4055619826440d4488802080c20990f81280711081620349003d442756100140d5143c0303038403610005c088140400b42507125280799141c01207401c940c0d1203454a0140310f102d018103040b6400014240d04024045600f03449200f406514203004210019800401c540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 836705647 1250 836704397 836704409
    0x60f0e06010e04150902040602060606070b010b070303390c0305162f03061005030c0d051603081b030f0f090a0909030801030b010608091b030a050f0a1109090601 71
    0x80003070061a0b001c50007a002605040d9107280380a04005140803a50b03010304140c2d0f00aa00352070442e201c180400215011790400a403541c99114010010000a00c008000c428440d003000f09230000d4500c4140d940303024201c1541c400c418a20300c42d0f00d05480c1200d5441c1c1c414440d0034000c4505508e80ca002f0f0060041c04440c210240300b9641c0c810500c40348081007029135440c120021480c48026035400c1d0303030001003268103000e4414500410401c1212a0f01001603070310180c01880c9030081c407400c1044180c4520029a80f600544129800d542441225140a180209292561a50302490a5082e1703203070301950046c40e0700244800c0c1c44410054086424003441c0b589a242c844038818006100384940d540300003a001d1408040d0410503422815242c103ca005894540c181da0743c40304c088d10079810032201c19160390443c0c100c01d2040341c0d0694a504154001030708482d01d403016940c0c1c007842e0080c10107000b1044c0c1d0081d00c40c001042001d10702c6009c1104241c3c2d000149041c06400140c0d2800c060143c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 836706897 1250 836705647 836705657
    0xe211c020a0b0a0e011508030a0e06030c191b11032119050412111e21190506091912051c0203040605090c010e010203040e06181603060f0e0601 63
    0x280704d0b01d1825000840441a610030464800d550340c03090700e50740c1d8801c101308400704511480000091403c030050b6485000c10304a168945819030f2007510345d0a504104400030300602c06c49914445c0080c2d070388080140d1090003012402c040d048201464500d581c5414000440c0088280d40302d400e8503000d032100c050b08010040c1000d961494150780f0750007260418180d2007090100c2209000d03004181d25180c8100703541c11320441801858040c11983d45054981d08425000c08890b015610818070492889101c3d09660917107424480079120203084490a0b646a0b201c0d0040c00849101403003402d01c200302c2d207050f03018402c403e6501c081510341c0c142105014040b01185089100e0501c0d650241c00c0121424115900d1600e40ba01e0401840141d0b118241c6100394cc408084a5008082140e03174843c05070000c60a06140004058140340010082500101195a01105501050000d03405560449504800400d229500030203c03581307a402004403410400301001a40e140800c0d2075000380c428602 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 836708147 1250 836706897 836706911
    0x1b0c03071b06350c190309120e0a0e1503070807051f14040605070302160e1f030803040c170d050f030c090d05060105100504080d0e211c020a0b0a 64
    0x7810702c0d1a21440b503080311544000302000000000300c001090601440348171320b00b0755009044101c0850f042580c0040183d011001140900c034001d8038141e2001d00c00901c1c80d42c0c0d4545900c044c064441c02500d60b120301c0314440390300d500e180c40c060045602511201008180d12450038000030031242ca1241c0c14180003030400108440f49200f88920500d07440303c50587c541c0c85079103110040c41e07580210400c2c0c005010384001411024004035900044030000f503000c003842d444006e00010084a41242c0d81803400c0d10300c0000000401a0003d54410b500803416002440c0c600551039003182c001400e550b105030042c0340c0040d541c5402c030381503d4840c3c9201d1301c09502c903a1203440f40901c52080151280d440600c19000c0c9040140014100d8180c9a05803141c040c2080d0814080c0c2c0c00b0300441c010540250000d0402501c014801c140000da400c0d00203000c0e01805164000304040d01800c40462041c5070800041218008804001c030600f41d41c8601c001d24030a0708a445180c00c07898080c0041803441d0b11041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 836709397 1250 836708147 836708207
    0x91e0906020912010908042d030f0b010605120105040c03090203011415150d1a120a060b010c030e10020307170a020d0c0b060409050304050402360a0306051b0c03071b06 74
    0x401d00682c02d02364440036582c0d113030706101e40307408107a050071208001c2c140000b140c558400c0e801d948403142c441c9408403403079080904020151039001460000c25030744242400150341d0900403044081140c05040c0101d00300110300031422441c404541e4018034020143c08001c496940c12610321009104000400000f0300c0304c10440169201140e5034095030901d50310741d01c030002045c5440030600c11002040020b061100540750a0511b00029021030301114005e0a50305007651100b001e03030f41c180305076481c0c81c81a82d90020450707801190100541000b203040111107404000c40c52440e0348a00f0160007000391036540d400b000d11b005180034021380d12a84500100813042080d2806001e009006644411050442c03101c031510340c101c02c0700c0c071a040c0160413000d10003000750400c5101c400303021a40c1e464155154000900b402400d65601200002030001102092202420010640300301441c0e60300c41900b05203294a01001c0030319108010342508000d1643c004040b403c07040810040c82c204200032070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 836710647 1250 836709397 836709449
    0x306030a060f0b01080604110f070c32010203070f0219170d030501050901032102070f0f090c0833032d0303040804091e090602091201090804 62
    0x540203020724288459006001c074280c00106800c002070313841408560b5a0401c01c01a540d004491001c0031408000000915040d900205841401048043d0010b0340e54540c0528000189030300d203004c40c1c00c05241c2c0c0c0041514420070480765000340700460810a00c0c1e21010180c0f010103000901c41e140c001e00c0c0504c2d00074600740c0d9200400e104143e85040c080b904400c01d1712251042c202200184c0342000124091900305a558140c9401804440d054610100d0070590f05c44040c2c1418254807558400003450045182c48902406407003035882440b520300003c07075041c0d480c2040d1410038004804100001da480c0300041040e5012100c4021400101d1a42c02d0910b001075540003603054094403c02c003030140103007102c00400c01e06540303540d201d6016481c5069164002980c0090a505041008020016007600810f074400e0490384030714240708042c2140011680310844c200c03440c680204800d1040d24085d491a890b085402c1c000b44925515a41d070b41c08a0310440c003900c81443c0690b03c542c90403241074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 836711897 1250 836710647 836710663
    0x2190e06010f030e06070819110f130b070501060f21030807090b040807080609121812030319050a020703050702090705040506070302010501140a03350a0c050708010203060d08030603 80
    0x4e501aa281410100c030014880081240c03002080070144041113040300561048021840030f135200c85003001c0303408803504a154000a014031042e8110b58022030f81c00d01050040040b40e00c40c1000058151402801c00303020709032940401c04105480e2107080d02c1390529102c03d010a41c0c107140080c0c1981d1840801d60312480307150000018803034040703004104002e00042e10000e031407401049854580c2c0b04800340303959000c50005a140220140120000f40b41d090001d10800c0400800b5000c04032010301055145410807214008903050700032070350008031b00c1c07403280c0340e00b04040c010190304e01001a14040c2c814030441100034040c3d00340d0b030006100a03114a0030741e1b014000060000740d82c2c0e051b03030a0090180800780900e410095808102c41c0755460101941d00c12a41d1048042000070403c0c0640c0d030380007074191078140c0e01d102552050040c00356010010315294005403103030340c49a00c090812918090701a007006020343c0c030400601c0855035a0704407401d203440c1e00041e031666030342e580800b0904011003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 836713147 1250 836711897 836711921
    0x804060609060f05040515011202071e05010c09050a050a0311120703080307020c09040b0c090f0604060306061103030108060112050a06050c1c0b0108130618030c02190e06010f03 78
    0xb0b48540443c5084a01d01401c0407607000f210244600e41391640c100e60390740d03110300609001c20079120440b881005030750094070b40c0034000c5503048509030810907064601d802813801161165554202042200d42110101004e024251445503041303042c0000b0602c10b01c0d090001038000700580c5a03903c95607488203c1640460910420f407184c60f0b03600c2c5454051a001510700d44058020041c0016013414080070315031099403c6850303141103441e481052001035004103440307600054030b104001c1e480d480d140700510041001d640e00140861400ca0010000484484013642c3da030403c0004200c0d89500050050554500d03414800300380d040341c40c00301c0c03400502450041460b4105000c010500f600b8130040c114001b0a0000060001414000c150440300e1840900f07004c50055070120340360b0320082c0d0312100510300c9841d00181c102c108410702d115543e0001003c80c0001c0c1c88120800450a00440c00300d111400d20390094483d40c102519a42e006000400150400c04142c80b40d0810900c00e8200c0386640310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 836714397 1250 836713147 836713151
    0x30e0f0304121509020f0d033e01020c1c181e080309010801031704030f080403062702100917010b0f060c030301030807020604050901060314070f08070804060609 71
    0xc2d962a540441601c09803003a19002c084982c3d02c0079503d030794003418500c1039000b040d148208222000f000008041030406408110045085036140c0440950014000c1ca44020185207031143c18056840c54a00c80840c0c40e43d1b0740180a01007401c2e40011b41041c440310405460302e00c81d040024100c45824412855442040c900d510000340d00c0038a00f5184a200d1140d2804800c1d1602c0d500c2c8503503244904442a40040c4c20000100003150440024030f149468079000c0a20b4a03590340c0f502980461a42800c0e41ea01d280000c0410400542d803044040c02c86080c20481c3d088a0b034400c2100c803c10a0150182c0103070310108106203090301c1108241e005c1c10110b10042880c0651118080c000c101c00e81d1420300881411030103100614050060b5007180721503600440c51070f0309503515580c2075000400100d81044051001048550b21010900c0c0a403071155400076040d11030305d00030b80007010040c0078041800b1144142c20b00036580b04581d107038005000c0c24110341a450313525160004113484d81c070079a007440c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 836715647 1250 836714397 836714399
    0xe040504020d020d061413050a03110f07062604050a030e011205011d06041b110a0b011503061a070803070216060e01030f020414130f050a0509010c0915030e0f0304 72
    0xc040c640c440d04144540d41100b886c1079841e24403030301001c0310800c03001e01a9488074283d00b00281c03180544440e03151200c010b507050b0f503402070706480c40e01e03005410500101e003002c42042e00112846400b81304403810000c65400c0c1c1e040c513480702502c9041e084006800c000041c1040c0c030380c0740d005000490f02003600800c00c200641e075a04240310380421048a0868105802c0c0115099245c0350146045268441340c00c100107088040e410341d2000320210070f2411130302a600c00c20300402c44c0800d40302c1c020207002040035551a030203c1d0080446450750401e10403006c0180d42c0b0860004140d060340d030060707030250b00d080d034a40301c0700b5007a86881003510441e429061446c9021640c1036001c00310001c1244280c03414000a10000c08041c02d0f13020b18043c00c030050400b940b00c180a407030700b41004902c1c1441c5c0c850014200450a4001081d00c2301110074240083e120010304c4140720091142d0203450b425417410650039820138080054001039008141c00309510340904039402c0b14284194030007400920112940c81e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 836716897 1250 836715647 836715653
    0x80a1520070524090c01030c09050d030c050601060e0901060527040f091202010c0e030c010806010c0c2606100b0c0304050307080d08010806100323010c0e040e010b010e040504020d020d 81
    0x10710380c11200c0c441d13a40140c24044620754068081c1c00e0882a0300d440d9140d855040405014440050210176010418043c1c500e5012500502c8158003030a01c655a02070944804400c0c040a5041a8840c00070410100001e80c1c0c1400061018284c0c0300441c4031400c0076210307050005014103205511081d2940c68000544d04028070340041d280a108503400030b0107031148401c0203a401c5070500d5101a01078119582031240b661140304000e9204034141880c20070440ca03034851803410800d58000d00e055620201400301e400d002c6001d900916404840103143e0340c0340c07203102000350a1952062400403840440d01c80144c80c028810b0350040c080140842d000c0a03130b600f140b65543c03503030a01f1303034408607400e60008210303604045040340c03060500c03044200d581c1e0314564031018640e034904103411142d00703020340d202c41608003809550310f0000b00b036a0f20800c00d40d1200c1004101c0d10350b6003a1070380d01e03803401d520415540d03006004c0702c4200104036000106c2d5a1140049815903107440d400941c0200108c100d0781c20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 836718147 1250 836716897 836716963
    0x40902120715050405090a1d150106120e031b03040b0c03070b10050a120830090309030709090f0503071b0605071716080301080a15200705 61
    0x111240c0010520000c03140440070b0300c10313200f94001d007034200508000080140b0f0b0141c00015141046124410a0b2083c1d203024505040b00e1411205071507450600420550741c1c050310110526411403010030440b4521800c071662449824818030b981100e400710b0003c0000107005440082008a81c01c0d41c1e41d0100340000344d140d40c000b1008640e82c0070040c01180002465035202c40c00e84c1c1d0080c040ba0003413070400310703600e601c02c10354101121040c104209004984881c02c04010070f0a0801ca41c0d8540040e024240781c00324500103008106951041c840d8440e69078000981e40f045074041003002503801c070070381400400701c841d2340006440c174440003d8440c1000340002c0301c241c2110061903035076041c0b83c6907041102d0b18818008041e12501103800b8003104050850020007004240080658229025036a5030110f0703002640a1406504080744400a000341041244441c1c08800401c0002d4031240b00308044480c0080c51000c511003001c81c50b5020404c0422107801e16180005500c610340c2811a41084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 836719397 1250 836718147 836718149
    0xc0203060a0e25181506080402030c0f0306160210020406050c0706090b07020f0f121f05010b0a0822050304180504021e0102070306020c060702010b0108071202090409021207 76
    0x859100d1205855095410000001c0080300610200d41c0c04502d0420f1543c2e607944c0e50380e61300d002680d0f280101d10300800403142d024003c008035290a202440c15004141c00c0c049003120390b40c0652544c41d0f00010701d0340e000c2182c40d070003000000b50140003000030f1000c92419141c035100480140c40024003068061b04030014040040361082241c041e152601c1c0b003198540114802c260714050709019071001442c01064a802941019022500c040d503454006260100340084688403600200c0c40c55142d5116180d5103c00c01c400554141320f40c0d450030318607000030720810350640d0404c803404000c02c903080044050740c502d8400311018403001c00d0840c180540c807030713005114468521040600380d1211000c6c60003114402d46d00108024081618407085055070452030013001d0450242107004000508103101420142000100804151410800180c211103084040324180080d400410001035446071a41d40c030710030002d0002d80c4880354600450050801240025070280c1003039440d04c8680c90008602d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836720647 1250 836719397 836719421
    0x60c07080609071d0402120a0609140c180c0c06010f18060b0d0f06081b0f18191b05030a0b1c0807050c04020c0d09061418010c0203060a 60
    0x142594950b1400d05a0b515101d02c83c030a6204401003007501e08840d01003200344d11900207048000e030840075401542c01c00c107440902312005541c4070783c03a1060000c41030322001070381011f2004018420078a8005510401a40d41c0ca4103890038201c001050b09190030b003a1803540544004840080d61108030310703100300c0014003d1076450314001608074007180701c90280300100c840c603050071032501c41c02d115090040c2c03408910420101c1d0b15a200051400710420407903440c1e5040d0b03c82240c1c48071580c801c0000090451403018440e12035400b11640162014030b202d07401c26400302ca5a0800c1004800401c0034050040d8405242c46d807503c2d035420600d401000851094291203030030000d1305840401c000c001e441604d9124980100540701e0800220280001c1649500035011600c11034945000174090340c0c800c0000003880e81003420001c0240e43c1213039410010704043e041840d5030b00c42110030082c0301c2c012007043d02c00402c000d80c0300d5041ca9000b618101c21080c1c0203000d03030f64540b80c40c89500002e4143e0020701 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836721897 1250 836720647 836720653
    0x34080d09050d0f02180a0c0509011d011107080106060e060c0c060c0c0d210206070e131d1f0504031b03030b090a060807120804060e0604090e0a0605061f030f0209060c0708 75
    0x10b0200182301307030101c803590329050f103400011070b4911200d401c44ad03c80c4a00d913814000c02c915031603030f80307401000410000c044400001c00c005050000082010550b540914080d200a00400c80300400c041000201d03104107880343c1c1d80300c0403054101490b0030465a152500701080d0b0108a050005c00c411100200d1001c06151141141c5600d00300d03030380c00c0111041400645501242c080503d00403681030050f0840103000b140c0803051986507034011880c0c142d00c907101d5000c1300b44840300034078040080d485104e4109080180f858280c502408200414a0b800c4400c0d03d0264036038109406507108602d40c15000e4036481c11840c00d4003140300100b00c02e00170140e25100d0b0701000241d044815030a130760030030380c00800720342010300d0000d0503a1040b10b8600040e80c8900d051002040008161240141c00000500100050074043c00c0010031102c029203181d01420b04844141041000035038507800d1035099190000714101d4000c0b4400080c0124081d241d4804800203243d020540c0001311035080d00d11a400fa = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836723147 1250 836721897 836721911
    0x4050606121c051c3b070e07020a0204061203030c050a0504211a060a0807080a0204020309070806040501021207031a09071412040b063034080d09050d0f02180a 70
    0x11041d2250454464213046d0f10210061041c0d20406030303034a8000d007984c0100c40354141c0c50303030008050f68030503040015803400361743d4510301b41649800f07030b2030460307078281001e0307182c0028400000c10502c9207001d80c0d4084940c0340c0c4000015502c1585c01600e10350071102d45561251189801940d075242a10014403481e510900410501d40105900b4201e940d00c200419230030005a0901c0080c3d003000709101014003840e034000429160510601e803050323109100040c0d41d9200482e40e81d802c814040d00e402c0c02c142c54088072030310b40400d013141d000302d02100700e5039241c50b541c03103410407140d0502c184040702011401150303503200c405060020780e0086114003980c5416907500310a02002030b48464040544210b81401802c5d0b201000854050b110956010707154001d52400c071034180c50700c0b54010002d850140680443d030400001569001420b00c0320b01500b401e848046000301181c105000302441041242000000c20141c07485c5520b1450b409803c01c0c0c554100c4194003440000d08458200c13300b424090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836724397 1250 836723147 836723231
    0x1509100e06011d0c0903030708130e28110406110613170307020307020402030c040e15150f090a0b09011404031709061204050606121c051c 61
    0x22042c1c140c1e14049203042c902c00c01c494004100000152901072518001c02c0241a162000c2c4003c00d0306a003c3d080342d503600c084940040b514213615a01c00c01900c1d040340c0030700002c48a5080c0d41c0c041c8014002070100600703010b4007500e0003455100c2c01181200380020740010b1070b68101b035240c07401c0400c00c02035482d942c0e01c103d03010940c4100f140e401007142c0c44000c5590020300010001d160400480d10480b420440b50f0b9012034100d900a44400801c810003082c10802503800c8118194440c3e4044001c420719000c0740c02203020b02103056010380ca03d000105843c2c40c14061703207050750652040201444000e0b9130700d00e504081360340440801800241c8158501c01c0c002d1804003200d089039404810400c0340d100302400303c60107030000b0340c030568403517400c004142100e0038402c2d00b58051070041014181c2c5007415000c10003030414204c0140707200d8000c42c00c520008500d01a020000114078100180c0d180c01840300c41c01c040800107440d0868618041c2151290203c3d50603c2801079040032002000c0c1b44098 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836725647 1250 836724397 836724403
    0x60504111906021b060a0c150923150a02030a0b030601121a011503020f0d1a0a0602011103060d021c050d030b0f2805040f050405190b0114031509100e 66
    0x1410407900245c0c10481a04024400e050700a06640524240c0e007031603c45181400a4810060b4240e40303010303003030068896600301c0f90400d400c0d024a90009098005444540107100d020003030003075500c5540030000403e07134050342c3c0048108900c001d041d14129a100c01940d07480c080c1c41582900d41c0e074101c9600b40c28001c0e500300c409041c3c4980c0c45919899030004202140031b9480215003a2910006201d011a511120701403050003000e0225040c4015000034140300302070040350300150844e811718a0000a40040c201184c0c1c0041e001c1d41c91b80058400350004c40c1d0426040c05440c40043c20080802c400d003d40071a101548401946d01400314100074001c01c03c81c080010025a40700c1c82c40506000f54001c0c1155650703101c6c40c1a424900d40d542ea5000080c1201c075184004681c85403944104000c02c501400301c041040034400500700e003018641c445000381181401010460f0305180c442800d81d503000c114110680d58164080343d92454200b01d00c41d100d90352182200320319814070590300c1c0055408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836726897 1250 836725647 836725693
    0x3080a0b0901180509010f060602010b010e0108010605220e07020a1101080618131b0f1707030b0a1b09050f01090303120207080403020409030810120201090306050411190602 76
    0xf52418095400c1001030b000109809410641690743e6600703900584403903800b500d0001d001035000020080f1102d40003400081004042504200d440401809890b8000b03040d41c01600340030b0780903940f03940c1e6040220b6800b90141c0000303003084007800411510690028603c41402c0c82054441100a200750040d0382d5071100707540c519800054a0b00039450500800c0318140e10001c440e00c107010140c0c0c40d48a85040c510384040304d003a030104d13014080c00307851809802840240310104444c42101110a004c5071104101e007c010300341a10500460b0410042d81c0042002c111760b0044205108500c0c0c3c03014060311024842c0034065480241a139100b58041c144090841c0e80540710030030380c00107103400d4000135403021904403031000b0240310100161301d440c03161440b80c030700c2511600c0060030104501e940e104072030303801382d18201c108018900040c1d80c8601e0010890b503010038003149070345440c076120080f0081d2000150700102a03503801c01814940d242c5603c22500143c080d902c280a40521b00ba055282c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836728147 1250 836726897 836726909
    0x30304020d03120b090a05100503062e1e06030501080c10110a0c0801051803160215040905040f1101030c02120a0201020f040602010c0314040b0601140c030703080a0b0901 75
    0x79010001011030300490074141071045855001440040c0b5000240c00a1000d13904224900d65800c1001040710303a1507090400f81c80200d00805592a00040c0740404000b0030815854071019895002140300500d295000500843c3e6400c4450a040002130644c00b031a51250314002401c0600000c2c3c80d01c401b04903080543ca024010182d1229844070544000320061700080c0c5c98441c588070b85001c14071140c4044082d0140324000b08840c00c2026050300990b0804058041e6600200520380340140c1340c26003c0d01c5140d041e1400025502c80010a0000f4015a489200218140400c100803c03080c1005410700621517600380e0381a104079001141125084900c000141c2c3c1300303000c2d2200b0800004041c101143c41407001510f0150412901c84043c3c2107079001c10b015039100c0ea20a1506601801084e82840f40c01d215101d031340ca0162281406400090b010300e042c0403100c51200ca00b2641042242d00343c0050900300e070f540d10840c1c0b40050980728101d442d4441d0b9460024440400e10b03095210074101c2d5a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836729397 1250 836728147 836728159
    0xf02040b010e130923030c01050f071710050409080d0c0e0f1531060201050f01050402031302040c20010507020a150e01060b120906010608131a0109020310060203030402 74
    0x70300c01c031070f0000a142131081038850301c04074441c550182d0842184c011010b4002c1003c2c0d500e820f140d0400500392140074141c0d0450395101d000700160303a80d00c41c1e00300d119011821041c101075110481c01001d80402a00291307009800c0c4614002889174100003448030804c2d441c404c1188800900046500d4003000606680c031105038100044103141000c44624640c10750b51041345401554181350300206c60a20b1134078440c0310b03403085495583c40e000503100d0040c09940024402c41c604101402030482050165520803176021000c5010b4040d01e0300d40504147e40603008014a01c00140301038031860703081c3c5140b905511194021900c158041c00740d61300501c1650020100028107958070080c1e1084a040d607480c40307076901b19200050809001c0c85d0020300c0c00c400119518207800d52a120b0141000f001510f0940c000c0004105c001d40c0b084081d076009030b0684049010800a1038000343c03500d240580c0b01c840604035000414515040c2d0300642c000d0030020004d4100c41d5031100d050b1b07240d00048030040e61040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836730647 1250 836729397 836729419
    0x9081e120702040f1401081507050703030c0c0f03110f010e1209010521270604080d021317010c110a260318070515040924030f02040b010e 61
    0x1404403000d40746035440200081440c00c002000c001c105d400c090304404900200200411006409101000b4111100c20078851289411800500380b441a54030050030035a032140c00c14142c1b80f042c60322100341544840140c1200c030441c113008003040040b2088031618007980300b00c4040c813481481401580c46444001c1c0c000304c000410300f00d046811404019050040030002c0903100071070025604900d145890948100742003183c003c10324014103085040d03005031915402001940c000414070780c06a0312000142e81c030006080500702074091284501c0c04100141030200301450201d459102580c000d00003009403942d03542c02202e00c5090340d41c00040c0d40c1c01242d0043c012076905540381d850205440103003410001180030b1044154801c0b610342c0204d15001a45081c4c013102070100f1001860119180c031822412181c240e000c6200d5840342c5441c0a940b4007038000c0c0c1555283c0007404044440c0301d0001e4080e80e034201089018201c42c0224491440c090100100e907008a1504044540250400e0b0500b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836731897 1250 836730647 836730673
    0x30b070216090e0c060f0403050615060d05151c05060c0f030f1302130f0f0e0d0e03011b091502030315010c060605030d03060e1308070b04060b0603010609081e 70
    0x20009264030310300034040c1588613910758403030328020070f00500e81869030f0b41d540d481c0d0304201d070900c1805000403515003105401c0d0a1143d41d068282c074040803184c18009040e480c0c030844050740804004171281c02000d242c040c41c1c20758007004003403200030f4080c1080d40c40c10b6888440c4203240b40704104042a001005101042001689a03210359100d284140c0000b444811600000e14200030103810101168407107038403d01114040c0650175039480042c03070601c40805218046511210703015111010064500301c5503406560941100005103d003000d404451014004010202040c0f8016880d21100040c40615003510020031680f0542d580d001460b00b030000a80111070f807100405040d1205034503101d0100740c5035001e0256580c0d51075182c80c0001d11514016070205080e0f401094011118042d00c90803002c42c00d5081102c905541c0101040507039035a038980440148400700800d0b410500210004c128a034019503030205842c0550102d808235894111151012108011000b0498010407401211 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836733147 1250 836731897 836731901
    0x140d090e040c0618030b0f06040b010c0b070302090109030209090105090609420c09100219060b120105090a02011b03020706030e0c032a0904081e070516030b07021609 73
    0x80348a6040840d02469803a11b40c0d07811000300340d9102801e42481c20512105103014800c1c0354403040b0a0030a50022801905ca180021200503d020241500000c00d0803140e803085200c003014507030082419150342800d00c0349030300900c001c4031000308070b128503000300d1385443c80058001503212411241361021600100041035041c10998602601c82207581c5c40305481d04a81209481800240500780e00c5420304000c00400308111302d054025034200c1000b107032460048114074403413035030001004039401074810003240160b4802d4400b903526500e06400d2291f403810124014110714001d80c0c036602080d590070060025982140703001800342e0301c0380d0700401000303010f40c0106088a100b03800381d0b42c424a4110200c0e0800d50b10680c000e2140d44842c00b10003134804018a08009a90203803800304131407038195141c254607c41d01c0c644481e00c1d020500b6481d4000190301c115103400e030780030054401c051100220340a071042c1c1400211065403020001854041c8000344039031103170500b1000030b030f0580e00e005c0c103900c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836734397 1250 836733147 836733167
    0x30305061c080f0c03070b04020118030b0a0209030f03040e070905100e040903050d09030c060c140a0c020303040302130203041401020903190203070e10060206071d100309140d090e040c06 82
    0x2000c40028443c401302d0310001d2000d0303c486800740c1030101c2c0758a0188001804070240c18a072001100d0b0f10003060010801440c426544079420190050fa10f00c411000030381f90603030b403100761b207040d100024011407995910781e603890080b861a21400b144945910800117901c080c84200c800181f140400c400c0306e45043e0300b092081901a0600c0c910304000011118203603140182c05902007005425004100304e0305115041c88a0217900d405607001d00138440b90a080d1044485900420504010850a642e014400c59006580c001c0c08128034009401000020750011202031f540f0030348041110303a10341010f000f02c40c54100e00802608218601803820124044801c1d0207030b0301403142c26004520000c4e0006840c1c010011000940e0000c2e1400300001c0c0f806a00a0051301000040c51410420200c0080f0020f4149401c0311040d071700c3d02c0420b2084000f0306501001038040e2400c203189c00855500400c0751116542a41c3e596041181c585010701c900300c0c415a00240b40c0301c0c440c0d0081115030311802c41d180f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836735647 1250 836734397 836734417
    0x6031107060f0f060801090219030b06100302122d040827061602120f0304150516140111030c070b1008061501110c030a060c0908150103030305061c08 66
    0xd44000c441e0480f421910990401d03a51603540386502c005520f089031814505003100c1180603091403d5a54402c0f0101d0094003007805046d0318907014140e54001d4054481c51420901a6007482c43c20105501e0030218403c8690902c041c88502d0007000154041d140f4400c0b604160039610b0181e40c1c04002e0103d22030010100d4078107101e4008981c0a60b036280051a03a66443e45c10300d100401540100201c0c00c0c0403041c04900c4d0741c458008178591807000700581c1c0032030b61813201c400348840140b01c0c2031b04c892103011494031411641070361100400c044146103040c1d00c1c0122000b0031241074501410852484165100f0604034802d022500000d00d8480420f03510014400b90b4a20090359aa0716030700d000000d880c0300c20b01d40419010b0039215640700d03145000107414a4001c000040c1c8840210f40c40705030300c00b005040d560300d803442d142185001e60612402410b500e02101d24414110f041c403c40e0940c28001100060300b0000800c1d15850048004108245440740d0003041000b20703540d5a0b01503011800c0c034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836736897 1250 836735647 836735651
    0x60f010611060f13140c0f0d0c030f020105041d190c020303040807020d170c0d1707230703020a0c09050618150d05030d06060503270f0f10050106031107060f 69
    0x801c0005101d217a070503050260781c01c002d2a07500c11003401c000c1c1c84103021440a000388000c015800124442a6064085a40001c0d02160218041c00100e44500c15600000c01d058200c02c82444452041c1001034840c403042d213404c043c00206010003000b90768004014200680c81400070401050144009003445031004040f03164101c05c0707540c4c202a080042ca4010524079000c80c00144a0304140035410f001920f501d403240107020101d0001c034821001030030040410140301425204144c001804a08440d4020501d41e11220a07140081d40c4005029089424110606c000200d011181c060540284401403944007020340c2600c0f000d20f450130017082c1c040009072101c08598561075104030350f00080e000354051940c0740d103925005c500f035075040e9001c042003290070400c000204000e51000b0312500d060344400c884844542e0155071501141a050042c5801103140e40425070303500003220503503504020800e0000f81c0e41d4483c02c0e0308a84540d80801c5207420200030201c0002c500381d10502c9289101000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836738147 1250 836736897 836736931
    0x1214070e012a080d3c0506012c0301020f0c15060306072d0507020f03210f04090f0209010206010b13030303180f050f011505060a2f060f010611060f 65
    0x200520000d03440740e4100c0c80000ea41724042e090706912004a56480d1901c2d000e00060410000085c20062000d0f10381640e406104042c1d85100800c500c941c0c05600000d000355101c507112803401d54558024031001141d07208140500d5000300307a501040d0b114100042c0031305641c0d03030341c10015110351240c06d400d040d6042e802c007214211548581320140855600e0f6444030f88900c0a4410f01c040c00442c00c02d0f180c40b9901064862000040101c46400710782ea403610129212003e5800840da68040c80d003180745000d06050700440220110f5003e40306400090b405c4880c0b0766079a081041161003800d9110080400a103800d201180c001c1d04404810403003c603010004181d6901d036010020341494040700d1982003181c281e0841e800034011401a01b8100b590900100d20b80000101e881c411020301c20240b11501041070060003801c1f070007640c80d99180c030450440792401c100d00e5444007821500b042d41038076038100205019105902d4006514800030042100c1d0311141c884042007038004004071403450318442 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836739397 1250 836738147 836738171
    0x80a0f050712050717032707050d260406080a090c03080c0703112e0e0d05010204030507320a2606010b09030601061214070e012a080d 59
    0x100b4490380c50341959036075107a024a00c0c06811060310030b0040d03050210b051003807100041b5803600060a01c0046d04e030038207521001c0b040b8242000740c1540712591000030460840c2c1445400407070000503a900e000c10f0100302501350f00e00300540c0a14024440050740040000304c0c800440e0f03104c00740703003801410301882c510381d25a22404640d21601840b80c0765004400f007007007004802016070141c00c4c0201e07400c841e046251408000b1124001250302a46c2810080c1d445101d0702946006040142c06020080c08840d0340c280680070394403502c0121482d1103134490000d503130f81000500044510443c074242c5d0300300300501c42c0c51268100c0980010b60000c081c010010b0f60201380520440e2a9486040340100b1a503507196090034214142d01003002c1000811607001076030350114145054403054106401004c0b01c00c103950000700100c1c224040440300d40000e102c059500000b1450b01c6003400d0313032503080c5c18a0003100310300c480d82d1008015000107031843c0d6010001708000064000c0f01d990200029890a00034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836740647 1250 836739397 836739413
    0xf030106020f061006020d050d0e120403120801050117062b0c0e04081e0403123506011214150307080619051906060e0a05090103080a0f0507 62
    0xa401080581d00c0400080c50161051248a41c00313040800360706412880d00002a4403015000c01e040100040007601d211441c9544d03010300c051003620710803512a00e441088904143e84140010742e0b001f41e40034601e0300c5891144080905940041e176802c49150a4040002d0f40c190700603001543c040383da2181550a080001c034542d04640d0354015903600000c0b076042180c031205044d00b014100100000411000c14405802c541c16400003030103103165240c06c01d2505c1c3c0140170720340004203030071401054440388903440900e2001101604203001d85014242c4250740d00640c0790b00000840150400001e002580551460124a203c80c1000b00b14501c1c1d000303002d05404c038212803010401184010609490034100710780405010564014019410941015540400400300c400f812646036400500003c102424600e80030f20f18440c00e10081c1e403103c001900181501075079500a0030f002100051510748040410b0489800c841c00350701d40a0750050440710fa4000c4841c0000b800390400000d00091a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836741897 1250 836740647 836740649
    0xd141312030e030a030806040b0402070f08070c0803041d0109020c0706030209030304120510140415050c2b180f0807141b03012a08071115090d020610060c02060f0301 73
    0xb0b0307a5808420700e0498208821032743c40f18441406944107000960015014080700e00d04a0381001c103080c1c40d4041490300300007160031034003e140035020106000404003c1c0a05200c03125a030008401c0c0d0507030b2a107035000202e0040c87c0c800c2c00140c0c007006080040a0013940100b0a10f070f00501500d1030f05444250b403140b51420401c0c101e81552080d1520f14030700410780300b011400c1c00e441182c040281440c1d181c021280045020709240645e64801246442e050f0340126141e9212010302d1400d1010104410502c0703034403182224840d07a0a00c1c0b4141c125911010302c0c084501c0e4001c1c03a166000d0300d1034940462a401404041f01ea45c162001c0c003001d1241c0400041c0380d031101c4900c0c0750f0b017550b240310145400d5614840d55401c010740400700d02d00c007100e2410b0302142070420501c0c0502c40c541c0c072000704646c0c0201c1c0d40048210750060000c9480d0681c00301801d28032a200c08000c4030114014400201d030748074411075890403d50038822050201c41d100d03900001049000809107410805405405280c40e402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836743147 1250 836741897 836741903
    0x71a070215191e0918020d060306090302031e0405060f0d023709050a050409050a1b03051603030509120f0d0909050906061509060403140d141312030e030a 68
    0x80701407071000303e81c0c480c034454050040d130301c0e008820501c0c0c280f050003414002c1c561484000d4020940140c1c94480340c1c070440046030011418040d841d402d0402a4a86d0b002d00100d402d108803415420045280c0c0c00112011a0300280c2418540074000c400c0c03039465000500d072203400340d800700280e0044c0140d0041000c003c41d1441000d9060a40c030b90031804800142e0746c600020f0144071141040141d480301415812170300251404160b0080c10b00d0b140c0c0c28201a0000107000100ca803100c070003203400344205101640d200d00708851006040c100e40c0744210221f0b02c0300a0005904000501182c20000c0c0c0034044550442c0480e005005264006810a0750002d07100000032078840041040c60038034068aa0403845a601620340b5080070030210710816410b14a030400150f002800224a880e08022140190307008a5003d416811041c0d142d80c44078414136800c1d0004800001503000240d02c1401c8a01d40526211154040da1520b040e440c0750040c03501c0c042c1c05224810f44190081d403810b104250802d44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836744397 1250 836743147 836743157
    0x60601030b0a1701060e0f0103020f0d06390201090803010504270302010c08061905010305060a0e0903040302030d090608061507080a031e1103040b0a0b030d0302070203071a07021519 80
    0x420200342c0301c003a100087c48400440610001000940c855004850b03407410140c5a4503d90707a15814004c01410441c3c0703200500d00c0e000301d500e00c01140c82c82c60007048448045580e10211549502c200d00b6210b07000d03c003420648003000104680d00d003d038015140008034000403c00080703c0d981b030240900315008150050b03519a060b840042c1e0b070110880341d00c184205c0706201d210b0070300703e02500416030030700526040c19942c00c003003140c80e502d070040940103000341020a503040c58007490345500d03900320f440100c0c0139118807100d5100060045c081c01042e10401e40d1001c1403541d035101000301040d640946000340c000c04111075808070700404024900c406540c1c03004580002c000303083e000382c1890405240203c0e440d0036600b5003101c1401c0c003120b40042d000202d1403041d480d100068401800c410b480d8030b40c144126451031200720b4140d0064400e582c001c0302580c40d0903950b03c407101103030100d88004800e0901c0c2089644018901540202c0d5541e00e02d10509040c07504074074000201000008044000c98 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836745647 1250 836744397 836744399
    0x9020c0727060f060507060e120c0f0607030905060f13020405040f02010f020f030a0e03010f020316271701092009010f0b04290d0209090a050405060601030b0a170106 73
    0xd0700c0e40201d600603d040750050715060300d0440001c1013800744d198001d00b403a0b1240c150010180d0f01b00100604c1514002c3c41c1980e501d48460020360b80c5812144540741e600030840042d21190181c412000d49a03000300191100da920340d1103030000c0c40402003013145a415000003e601503159440b130180300d00d20882c840d1018800d50300004d000d6440001d24001198024401400320310008015162540070301d04203040810454000207024000d85d4400701c250b01d101104200610900020315142d95256031a010b455074000320612182490a141e1920120f051500400203074201500c055031284c031500c00014940c0440c0d540c244014114440d1071002c18488115820611b4000045401403060141f151003081c80c1042040c281d00031441640ae1928000e9400c40694035403035000585501c05c010555903400082020300000d4201030100c50141c04100005000c1060510400c1e004507042002000f141d0345c1c0c400118050045143d040d40c0240e2032500004001c031604900310308008490300081055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836746897 1250 836745647 836745719
    0xd030c0618110312040909030905030109030207180b030c01052503050a03140105030a0f02030721030908010b03072d08010e0c010c0c15140d060906061809020c07 71
    0x803801001d0032034440c1c1c201c203204144c3c05003c2c004803000c072441502c021a01c0b15030b03414291070304100703688074940550801200c0420941c0c042995800d440c1c0311440b02d10501010f224540c2103c2100c0142038040d4042c485070092036004034060840341040c00d0b501d4420798a625101d400244c1d68440c200c022900101e44150110f4040c024400d0780890213910741125898000040d0342d40100e14000b50182400d80450340940d02c00780402000780a03803c00e0b140c41180c1da5440503186490521080c3c2c0085c81c1071001041400d0180125050101700400a02d801420300341000301000b2131050441a00900d240f060b9503c1c0030b859050402806444000500007101c40d60042c10002144010b40c10440c60081d200c0000f10b0200309a0f0a592030304200303244e101e048a45c296690303114120b80740d40171031011421306008030298018409440401000384052075851400f5248910b4054085e05c042140744401d020b03c1d034590f03001c2c00d80c09060000301e600f0b85681700c00381000030300d60031569406058000c0c244480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836748147 1250 836746897 836746913
    0x3030b060c0a02060c03090a1203120509030d0b040f060602010b040e0a02030a0803130b161e140708041a04140603042103110309070e0a06080c0d030c0618 68
    0x4120a942491a005144044680b100c01d841c41c024801c03040030864a505403010826100410809889034800c0f40d101c900080300c0301c5100340114001482800e58100c204594040ca6001d54031510065042000251840c000307443c0040c00d80d90030666519420f10ba5444038000c0400900c65500005800003040090100791001340c110f8101c0361f07020414010040e10001707500c40c000383e000080b0a88030f07121140483c850001101380a028034100c40d0601c8000703018000b0100318205291641101c162040d40307281280c3c038040c5801c401203070000302080d40384846240140b9009209090b0307107191548900010020540400c084800d440d404601032215034401300d003d00c084a0120344660651030a6561100010200d41020001e1802e40300340310b6141e4025080109088640c41507280c0b2454001002950380301c0610603001000094000b04000d07002600c2900183c48000014081c3c00304a02d040c041c03c0c51600b0412000c01840840c030001188552061149085c04011b0005020040b4240100d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836749397 1250 836748147 836748161
    0x1d160906090902030d0807090f180e010b01021b010302130e180109080414030319080a0b09010b0703050307230a11030a08010311060c1009061b05030417190801030303 73
    0x6403852900c0c10b0403000d650b0004161481e0300039850003590302c1e51041e20480700c20045602105040c1e1500e040850038101854a01440d07441ea80020481c002491949500b651851810140582c2000b00801c0319540c40d160903032600501030402514214200584c1302c1201d4696202031181440c1d44280b01601100300800149400000c0003400002c403da12443c825100307501c1a1221805010481603180d2401c1c002e43d1404c81d2402c8059104c1c1801400142c5000e5048920043c4035143c551031844a2910049841c10785141c0060a410071003150380030f9410b54009030000062114800444220403081d407605450041d811071116220201c44502805a2a0a0102a040750020b2101404807544084614110b07038120300c415490301240c5000c140248a02c3c0f403070950b20b01071000e4103050306266801031803109100300001c014240301090034100d1b6090b0001c184001500400100d804030300503200c8000780e107201e51820391802d04a80d40d0302c040454021541404180507000400c01c0c59003501c10700c0c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836750647 1250 836749397 836749409
    0x40b031c02120f030c0306040b0310240f05060304060914101a010806102f0706020601060c03030e120301180b03030f161104020f03090f030703121d160906 68
    0x160420f400c071000140603000c0201001c49007440440000c469a031141c100312003a02020707064645800303103c403100d8040c0c041c10380c01f048a0415882020510031110807020b007107840c1301c00403052041c101010001e15034400341c001e540480e1501d03c51001308882a1071458a02c0304500204030486824002600b50348003507110265400140007000a182d802ca6003d90340002d00720b580b421070f600032800030b070b9070307a0007080306010450b10300c420141032041d038202c6060030710303c3d510201d42d6542d0b5102412070382c0c2c0d4424054400047c1c1c10007210b20000307001e80c10841c800d00450302950360302c60a40c1101031494200368481203d940924002680c00c00981c4203488000c0d10503000755207081600769801400c1e1080900c010500c410040000c000c0c00500c88050601440040095540301502104020581c009075182e05075802100898046c8410000c1211942645901c0c0c008030180c4000690004100b4144243d5855100000808000300c1c140003c0140c1c2014190101625040c464003208482158101c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836751897 1250 836750647 836750683
    0x40b0a0504110d020a2d0e090a140a0b040305191e05180a030303150906180f1404120f0c020307170f01061211010804020915040b031c02 60
    0x200022403404500e58403242c0003580d0700120007040d880032030444120341e130010b85c5110b0035242c201c0f4009900f022049811000c0ea8181c1c15043c0c440c62a14503401c0b0941d000c1c2040c0d4007245801002518035403071040760410300802d94480c000360b070b200c2c0c00c1074801c02c1702d045000807000240b90440754521030240a8400716443c1040750a00248030a110f0b8000d241c0400c420320801182c1c0141d51601e1781c01e2402110f801400e9210060b9403890090050250540c0100481e03540ba5004528503425110340c20446091104060710200c0d2400300c0801013000d03018100d4550b0b21802111a841d01d01da0319103000b0b44c400e40303100301c4145070702d18000c1900314241108002c00000d0003104026940015081054403204a05d1007e00d0381d4860750a840c080b00240c0c01240c550800a000031404050070108030100c1c0a84011b2005412500c0112120202240c00950101e0048003243e902601e4082e4919032840c05080045d03076040c902e00007440c1c801202c80140a022442c008280203643c14004140c212004040c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836753147 1250 836751897 836751901
    0x906050a021603030f0e1e060c0c0706030218030a0f0c06030c050f0a02010902030601060f0f0305070c03081b2a0c0a0603050910050f0f15012a0209010e040b0a05 71
    0xa410766034075500541095205c0411841680056104510f0001c02404503504000320a00390100da00078840d5062036401a4800101c043c444031045681c40c83c64800640b010500b4a8003da0003500304020f02070302c4075180921100e540c0c0341046442a0710b40610301c0c2000c10011840c1024044039260003417000c241c10b20000403c3d86070040c2c1558203c2043d003001c10f8880c60944012401000c070a00701940c9131007407000000d066034009140c042c081c005907a80a101c400008000e80642e9400d80c1c9080018000055480c04603105054050f0056500c18036812181c1001003541603907088888409060301c10014003154144036400c0d842d15040e0302c040a417480d0900701c0300141080d44140300b5034050540316030000328004001d01c241414590400010812401c07d0700c0428068142103c8950b02c0e4003280e400304001441c054401c1c0da00580594516550b020490404000f050040424841810720b407100e400050303840c0c1c0c41060103414040c0d502c01c00d914090030840180702c40030f42007540c01e51420007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836754397 1250 836753147 836753167
    0x62d06080705060706020d110c15010f031407081e010f06061b060603080a0309020319051c0c02040908070b1302090c0a020c04142d2e08010906050a02 66
    0x303400d07080721800c580880c0c46001608000c00a8400e80e00c1d107652592501c0b464071101001c11014107030080030901100c0100c90142c0f24525a80420b00900780c1079003c2038410000a1f82c039035a218100810201034641203562010746a1030038102e01c1603021028010002c2603041c0b0024460300106d1407003828203105c40c602d414005801100304800c1f90041c00410070054082c048643c20500003550310405156403515060001801001d00540407403003409240000d1461000e0440700c00f0b5042e030800003a2200d07200c03503807007001800c030162062000c0c003590209880250380d440c0714034808075004840d03c680d11840c9291603841c101c070003000c100800316104a400051f03107540310480c0e40003514520203a50f820352010117a1070030814040c00360b403107820b0950000c072641ca88800240035000c042c0c2900000100c840300340c100c4641201e064000c100c1c62000107014410b1300c2ca41c416a440803080c84080180c24588001d5540040b50026042e81e0344070b6666100f003101030710030303035600c6000d00b03000f1420802d00e0704c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836755647 1250 836754397 836754403
    0x301080f1c0f0c080301230d2d15021809070c1e02271e0f041b080607090501090302030604030f09150c021807140a020a062d0608 57
    0x12120000304841c890920051500a4685810f0550042c0c5020348961703592080c4041c5030302c940c121b40c0015041c0c03a5540841d040407458001c0c12540a1500b40411884803610a10004004098001d02010f40c100d000856127940501e1440c0507400b038050781c1c8448403004a0002464002c1482c0906601003c1080b801e074081400d585207948900d850200c01001c83e0000c0203020500c0001e5071110440e9500c094080303035402841102020312048074a1555400174014100e80c0004421824980000000f1141c5002c841e1042c0d200b84560109c0507161555001480c203042c03150088081a4450402d00c1409030308494150000c090919091406d40c0c10f65012a0f100c14011300024240700361104a8421a40103050b12006068000f0b21000107898142d4018042074030598164010801c1d080b01030b04013031081694034404c1109440740c1d0744d04d000c428404c1545a01c10441d0750300714051010648000f45040c06024202e482924405110340804000b642c403c4c01c0d0040700141c000c0c80c00780c0c1084150404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836756897 1250 836755647 836755693
    0x2090618070c082505010c0e0a030b040c090207030c03180b071e021c06050c03102603030109051e1504090501150603021c1e11120c0301080f 62
    0x91400c1c0c0b2041200c0c0c90600214054083d006181c0304800c0d152000c5104018108042940901d00900038107050030019111340340c01d08606034200c40d142d002400403c8901d10000d40140c413079100815000e507181000e50898102d80000c0b000030306415802e000303055102120241000b50050b41444052401c9241d00551264140042801e0242030312000c500144e81c1c04415480d80203000546c003c2d00f01c400c2c0d044445204d650480d034031882d00e404600004030300c02c04d60340700700c89546050b140d031070501d0052401010b4100380c14450040d80d1b6050b00c0300310310030300c044c1d4024600c459011a01d03040c243c0425202d520300201d6041c003490346c6010008200fa020b00c41092159080da00040c2c2022241005400340144807030203840c80040000000c0e546a055004240307881c003c414810650413580008402e03110f1000f000640d460710f24070002c203004840da000007941e8050181031480c0c00303e00329480c03645901c100c90005482802200404c0104000d114804101c000707080501340740422516001007011706 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836758147 1250 836756897 836756911
    0x8060f1e06031c0201091205190908070509062e081f03110a24020c150304060f0b090403090302040e0c15310513020c0316050115090902090618 63
    0xb0300d07410910710307001b94044000d40360803540c031040407c10524041c20580c4500c40f102213014074035162440c0b0340c1c80b400600060b9810503001d0f240c00c926142c2000b44061000e005158840d5100000d000440e0041c0ca025441e05400d11820305449251ba8000d0f20790b400092011641c010a2001d501103852440c0f80e07a0240c0e58400741c8612240250b802040600c00c540e04129441ca001700207071100c0401d1032100400c0c2c81003a0b402c4900c8400940b0074131001880c004148551480c0500109000510a0308004c0c922914040f00013012107080000034181c00090f141600401c408003028401d5041901802100d440d842c0b00a10504460b2000300e0564191b5014040c00904049201c0b04211b0f07043c1c038000f0681045d0740c0e681ea07400712000b41c0e07148a000c041c0724442c0b0038084c001400c180d1a000e030080d201d00390300ca1006107003840098502c2500b0300c004c402044070103542e40c59506410700320400d00741001c2c00030403000149050311441401448200035095620035080e0b900b001d25400d10b511038065000d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836759397 1250 836758147 836758183
    0x207210b0f130f1e030305010801050108030c0a03080a0209041a031005130201050921070e0f01150315080d09050111060c0f1312150f0605010203040b0a0908060f1e0603 74
    0x3410511a02400c0722001303003076400301d000d0140a0580c10f4100381d040c3ca01341d0000704910390340c0b4004a50f5030b22806415100e039401c6860f030030021902901c603807a03014040c0c40000d80782800c1c0e8000942101c003502103080041c040ca88058200d41000c000c0c40000d290512010041410004003181903c0b02110000b810400000754404141e00c0f60031075080c66940d00841e681902003000c0c0d45c1c645a4491313016502901c0100000103900000d0401498126605040c1c84031002d066a1400c501522840d1303480b41d103041c1c03000301c0014068403c004030340015000380e175401d90706800c010005260502c0503601c207031240c0c8039900303010740000540d088071040e481030200c2c5c6075076000c050582c0c1c1d8284c1035035000c0203208c005242c1c00000d0007510022400c20754804101000801404c1e030110048500700d004007170050340180300602c2410324600062501c122241005903082d59100590341ca000300480c3d01001d842c045006100c89406881c105510070200604901d499180007004260355804040c45212001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836760647 1250 836759397 836759423
    0xd0b0a150303121503020909010605100c03050306150712120e0a0519030c0503030702010605010e06070c060503130b240303210606070803130b0a090803160207210b0f13 74
    0x10003131030f02c540300941d40600804a9440d0081c40c0758024902846482d0107038a141885e40ca14a10075aa20300b6940e52580320701e41180c55100901284503201d404505009400b04140804603150070042286440309503240d180003100002c01600369000149180034035800070031400000350001c140c10070303c0c19007488001294116810201e9648189038006030040c0000414041c0080d410340051060329000c3e21802d45207441c20041c04000e01c165540604050341c586010f100c0c1a21a07802140c001265034078a0303410310080d445510145100b03581903c40d1480a00120848030888000160040400c60142d400c1000ea00c01108040c0420004c940c48810340c103000030b0180e61464180e070252a04007282644a00d05031031007243c80d1054900a640b031000700800608500c0702d07401400901c0d40d2001015040da00c5500c00d14000341040140e68095001c0c056010402c00c20400c01001401034106022407061802c1c180304820300009813010769a0000c4104201c40515a80d540354038455002c036905140b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836761897 1250 836760647 836760671
    0xc040c1b14160605030103030e012f0f16050312040605041a040905040b07090819020d11040509100e01050c04030f0303110423030c0906010804030207050d0b0a15030312 74
    0x86509800811202c11004101007040b0342e2210185050320b100351900d0030701000d2440199a1640c207a0b4100f1988480a58644890340b21052190040c6800500b01d4901c41c1c481007074242070481c4600312005041b0308a404115914040202403441d00a04440034a0030f410244010654400e50080142c0f842070411b80310307400303408002214024400c00800300150306207031800020035082a0391f00d80000e0450700000c170741c605001c10f07051038400d00302105c042c40098030b50910140750100482a9000700c862031041c90541c4490003558412559403010b054001003101e16282203c01d040201d100707981c5042e04010841c007a810450782a42c1c1c011560056480241c40c048000d05583e030704110f075000000c6000144526840c0b00d012174101341740442540d40c041481455620040000129803203080080803c2c41c650140d8213058000d40a0f106a80c000f0b030b2a10042042c0c0c0100d103c0860303030040282c0c10005410483e111b40441c2c26103000e00031000d1352030741e203004000c4031440b200c4440325907030b4607003120032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836763147 1250 836761897 836761903
    0x603040f031b06050117060a1b0c060f02041d1f030f080d06080d030605150a03020705070812030a0b01030e0c190f03111206010b1602040b0607050c040c1b14 69
    0x100d98426000e00c420740c0c641036032a01e0074006400b40e42413485080c0c045800c000c014012a00940c127551281d0300c1802c1c01400888950201c0042501d50960b100c2c11001d00c8002800200054400c0f0000f0801c030300b00310b4121140c9210014402d0074036000411b40514410024068881101d030085040324110710305040c200c042d1b00c81d803210750324038601c2c01c0000100040e0100e03821014541c9901c5c200460f41d070750800d000c030103032040065402d014410840030b00b10601a41c040d012840c000c2d0110780185860320003d514190325244140842d11021007000806000750041e4043c986080ca014002002003030455a0f0703681140302000c0c07080c0f01002c60304d00b203118220b0301c810052000d0307100e42c152140c0d2810301c0159140b5254a15000348440144001c42c4c8600044983c102c03082c0b501203a18059860241c440364070582c01d4102e0713115444100c11442c69442e80003424990f40031303902a2003c032100b4803c00044402c1d070780d914014130021000c400030814800b91245d00098009032418518440c04c02c1c4242 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836764397 1250 836763147 836763197
    0x20304060e03030907060e0301020703120c0309020a0305150604090302060a240e100f0f15050d050a022a030d0b0319150606231806030916050603040f03 67
    0x781d144070100c00c1001508002a4000465400e0b440c0d11700e14003d40d505260a0b88112100500450f000710580f80e0f44071080d0703000b007441c54082e180c00617000c140c0345c3c00914812001d90040e00c00d5401181c03200d44459070410390230f800c01c90840d000c105104e040e580194541710018480314225a581c80300d00d480201200c100380310302c110241c04501e52611b8010807c00c4100580e03101300354075503038400490300c3d400031071140094a107000f404440c96031502d1801199040345004800c100401401340f9440744216002d00740c00b035209001d000da203808016044001c4030105920007950050b14809603400d8030408006c841c00e50320800c1d80030404880300d4010918140400b0503841c840d10b4500c41003001d200c030360088550781400d078101c244481e507940e403800c8548540c42e41340c2c9039524180d00c501e0125014400014852205200440700d14004a03400158454004903a0400c0c15003210302c840b825081030050340d901500d011218142182010f0b241c00000040074135000741480440000d4002014900802403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836765647 1250 836764397 836764421
    0x80d021f1a04110d1a0a1a0d0606030506011707080106030f020c060f06031c0509100e0a14040606020a170a110604050d030b1c0b0a150b09030d0504080c0402030406 72
    0x201c040710410060401030ba01c0410382d4042146050f10101d0380c17001d90f0301e80c0d10041900801400320303141440428020076940f80a44404180c017040078100c103c980e4000e100c0100f035251800181407a180c0009070540001ca900100d42c105000204010b0079044410a8107481891500051201440c0c040c034009110302d200c0c40c0c4091140e00308101142004410052042c10306409481d10292540c0c5140785151003101a800814410f0103040002c0c00c0036150290000751900d41869006e0014002c00d84103107141d001074a0030200c00e401c1d480c0b0b45c02d050041c50020142c901c020001080c668450305c2c0058034642087c501828000384449009109507240c0c40d416040c032054920302d00301442d01d250748554080c0711ba00841d003880401e060602c0c02d2510601d04090402000204c52500d42c0c407101c00c0c100007014000e91982da10707a00c0b11002e00040d14440580120a003007552014810b08061500c071109a104040040c104000c0c041030740085480c081000e000c0c4c0307025032640c0f80d5160520251034051018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836766897 1250 836765647 836765651
    0x1230a090315060f15020601060302071e0f0219121b0b0f0301090c0903050d0809120703080a0f0203010b0d0c0c0609150606110c010c0203100c0801080d021f1a04 71
    0xe040c002d4072580c410b004480039881c2032004184d8405a4951080c0841c48400140e0400c0740100812802034000300201485000d00b803c200c8100d441c102c4484201c0501512000307a00c0340d00900718100340c14440d40c0d900e82b1401002c2610304e05080c0b8200d10320344c820001c103829200030000204440a00d036441c05800a00c80e541c5d2a1581601c4025a0790000d1240645890400c1c641c004000d001c0e40310201920f400401521070071901c41000e5078882000f614011480c452905820f414210482c060001c0034400e540c1c2c00c0c85070a00e16032503801d896080300c1c00707482d1a1040004000d04a81001104c0f9182c15828002c034103000048003e030303445449a1005881942460002002c011079440d480b41e2110069008100c1c1940700c140403103060003824031400181e8000501c030b060b07035801525202c20b490310050855113801011000c241c251607542030002c0c0401c40c00401404480c0052040082d40e4003288001e2002c04200000c4030303c55541400e1902c459076550a481843c81d02020013145072850103070007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836768147 1250 836766897 836766923
    0x60c0412023003030412051c02031005032a090618040611031510030b0108152202030f1806043206060a1205120a1710060e01230a0903 59
    0x2c050345903807040f10200c4400403c074a1001105005105440034002c2404854000340d0700020301d00d0080d84007070a042c48112400c00d00043c0313950b080001005204400c1c201c14030b48a0090103407202c482072681e40c07034440c00c0c0031010010192285045c14517103182844007444543c07a40d0503c003000305000c101440042000208014403000c19159800e90744a0070b90f4000d031424080070301103044600f05022240050380c03c1c400700c1d130303050071030b050218848400806100c01000401c2d0b410b02580d01c00c4400e4200b603600801003040d00030640d40c44a0741300d01500d54a041814921002a481c0ca0340100010f00d4080004210000858141415984c0e5004010182083d40f2400e004c41e03600c1e101201c4440c811044821301195050071b02055404444d0b100c0010f005040c41d142072807441d078014005010410014162012600726803c850301d000d000c104034154589820620020030340303000b10703402d01e040c80922000d4201810760301e648503401c5800142050f03111b00600324225040ca6860344050840000890 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836769397 1250 836768147 836768239
    0x1f11070e0703091e0c0303200601140f06041707060903030c03081e09010516020d05160218010b03040203061e040609080d02071a070309020a060e040902060c010e060c041202 76
    0x1100069a000c1d4981c06555401c8c040180040e444940d0001c40e0354000c070b0010403900c00004e2040c05454002484d585403203050201107a959046130307101d01100d0400d1046184505414400e030000f401d043e00c0c1c603a60607130031030302c0c09000c0f5410b103500101000100b50000720360240c00d411600720140e1461081110303082501400d0f020b0030041c2c85011445c21010041e802603030000401c034070441d003151545070805c11012080d0184d811200340c02e076001004820808880603403c00c40c0303406000c0445000d5103a0605005161416200800c80080405110702c2410310361151042d20750f00c264402d1011501c0405881c0407030250041e4004540c00c0d6001081a1041000300c0800707000d940c000d900510555a1003040840a44541c141d0294110b08000010f00043d84603440c034440c8600081c0c40420204101e9020400355402890300903d10396480c0d40807910740310184030701904a0b016410b01c905003824a0500280b215214030700903c034058800ba401d2141031641070100700080001c4448103e220480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836770647 1250 836769397 836769413
    0x31303110315190e1216050c010c0c0504020d110a260421030e15071803170d0f0507111504120f0e1f11070e0703091e 52
    0x148555200b402010301640c00700b03050315800c0d441018169409400003078054003003030040c840e180148449000d030040ca1200000303c10001c20b01041c0024101c1d0300d040e00f9040560810015210701810041e41d21410804a501c901041007510f01c11100140d0710a540c0200300000c11401c17600500c0010b01240741801c840d00440e2001d00382c400c008001c802042000d100e00c1803600102c400500d41000c1d4030b0385010200140003a004e244295040000312960280d01651170300000048003200040107408100b5140d50000da518a991144120703c8209030541d540c4d030000b0211031182c51150b0901103084241207005801001c031219283c0020400c9050204000700026401c61040e1107902c9940110b51404401d00340e0b40b88210b8009800d52111000314104480a480d203121344000c11010300c0520310b06a990b80301200032000503015007a0020b14801e03002c1d290b031000046244942d003040b00b04120b8400340e00620740d801502c52a00080315403291400350708040302c0503c00c20f00351a4016050081003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836771897 1250 836770647 836770673
    0x80a031506120c030917130308030109090c1512050910060e010f050111030a080408040e0a1d01020f1c1d0f013b010e030a031505060304170c031303 65
    0x8a141440003e0450070250142c460304e250080c40865035a07401c0015040410140c02c0e0703a02c02000c8200c6a5980c1e0316581101d400a070814242e040c0d90b80c4421082002e5155480010441084070407809500348602801c2e9110314806025102c6c0c03581300154005805002c0d2509040c254681009080d03151450a81c0c1c95a09015241c040c07114841d0204296000c3c1c0000d15400c0c9800c03008618003e1441e004580b242c84c0904100c8404400f4400410710919401800d07200300d100c5040020740b01d401c0c070b2804032050303d00b111510550748104880d0788190008802c40700c0b5030020304150080046006581c500501020660b041c00d07008251220201d00c4000c50340c25445681000203000c078840b04a802d4102030180c40912024100d014030807032800d051244210602078040d400004e44542c106100760440c0e00a100503000a540da18901004400000c1901c0c043c0005a5200f415485c0c50f0340c440040001c101410400c1c0c090104000d5603548040003290070103a24440580003650790383c03401e00b0b441895 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836773147 1250 836771897 836771927
    0x406030b0301200409020c100e01050402190b1b03040510021c052a01150f0f0e04050309010c140d0c1109041e060b0d030807080a06060804080a031506 66
    0x7040d064514034680350b00f580081e181450700b00d926003450450703280300940c03080c005040d40c0c0c061060180c1010b0128401c074080c81c80c0d00b200100b1645410300c10849101c0403020003d43c1d060030000144481b5130b416050360100901d42003250084c0c60382c0c150b0f09103140101c4d413015500c0b55001d103a001c003c503804281d0003500e42804058400c03034924080c0658a80c06564000000d2001c4003081881080c0000e8882c1082c1075030b08000111300542c001500d40c0300209400081c1e1600e00008100010400c06c000f450040c094030400662a041c103036240c07610f900c15640d0b214100300307400541c0014800c00380343d00101054080b007160054440408003521100d61102c05803221105040f0711159410410b80b110b03c80e9503c0301d681102180300c030360a03c0f900025220165010b0390780e8450300388244c4403010108069400794542c08050315240720010600000104840c041600b003400c2006495082124203030480e60108801e03440d41d1a101046006186116038000344040002e00040c1e45174001d515075020440d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836774397 1250 836773147 836773151
    0x302091e1302030a060504020103020d05150f01080c03130309180605010e0f0d020411090301060b12100807060f21050103050717071a1b010b0102010501091416090b0406030b0301 78
    0x40c403150180505040e5241c06901904409010350016055600881d0701030700c14140142041a260b502008443e81100c5407201c03400c0b483c030714400b00d24050700c210501d9042441c1c210500c1c90281c00f100900c0c000903194030f20915078000e0117010140200c0507140a05600c8501c11001940b10021340040c01d030501c00e4074040b07198420302d2a041e0900070424040f002000d0303d02c0d50b40758166402e0000500c1c2e21552020340d480c0500050b140d40c1c0d82805458018100d00808585840004071030046120000d4442d8000e070750100070421040d400800c62100300c03502420000c1c101d000c84041507030b0324603504070800090b80542034980700780300c0e140d804503050700d001c0d0f0219032006449403040d400751301841031024000c0d481582c003000484003960005001d00440e82034181055590701c41610802c5402c4040900d41e5100c650090440d6824800c00780101b0290a06000300ba00311055440c0302040070300603e01c01c2d0000c0d41044d900c01d00944a070780081c0b0300566600d940da5925138000300100b0701c4200f02c51083d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836775647 1250 836774397 836774401
    0x1e07090c09050d1401180f1104230c07020402300712051003080723070b0702060901020c034905160c06030e011407021b0103060302091e 60
    0x15208030400d5080e2440500700f8620550281c0303c003680c1d0f91000c104402150740b60101c880c04404041c2600c0a80d034840c0007034001d07107c0103103051050b08015190362402180b0b800b80248044001c0d0020301c240010040ca8000a501c8145d060789583c4141c00010750094000110340d0070103820340181c20120581080c00703e04403600801d0490b0340141c00e0715004001907500071420802e4107980d0110340c000b401b00c074142d6036813941d9580380c28580d001200169244000306101006500401d240303000300040d00400341c81c80c01d040011400090082c08806400b402012540388150b900800ca1121400c20090850b000c25041d540c06000780d491880e4917091401e00c805460744070b01a40c4070044c80b455064150409211117117102151181c100301240a00c2d40d03005a90320740400c0e41e009011000d40360b1603802040841d0321502407400d40721031001e44114a168a410400c8555000c40c9a82186000d204078003454110f40004a0181c020f0380c00181d40000d03e43c0c01d00c1040919100703e151203800c54490132000c1d0f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836776897 1250 836775647 836775671
    0x270e04060e0a03091703041a1e040b0d0207140a0506090c030105041e020d060c050a14120106110a050303011d01060801030503030f0403031b030608012f09031e0709 72
    0x2c0c0700c180400401090455200744200c007941072411601480c000c0c01c071703810700303503034190003c0500c02c0c010031840460400107203440d02101c403040d25011208104242440c0515185001c1704501c54043c07403e0203164040b60f032108101c85506034810602501c1c0c00c44030391001750308025840c2d040981d8556410b216166031100d1504042c040c5e64400c5400c444100d0100081580314803084014030000c0741d0001c3d10454440c0001e049115445820700503560351a00c40040d12000760030b185442140c180c2d410b80a10198180749000c00c2c2040c1951800d1410003a00107005074210f24000b10003000404901010001180c0c80000450710822a402ca070004081a641c1e200207840d1600c007800041e240790400c20025082c480c0c6503e601d03070098820301d00060848a001182d41c41c095800c00081c000944842c0c040000314401d004a01250802c01c0c00c058090042d02c0c070201800c0c00050101c02d016902085503140c070382d003d008200007840802c0c0e0031221224640b000d280c80d40e0150141c0f01040345408041080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836778147 1250 836776897 836776903
    0x14071a1603140402240c010c080a091e0213062306040503060c0a0c0f030c030314060d030c06020904064502180a091409160303270e04060e 61
    0x102c200001d10901d40c680360f980034000003252a0070000c1d03210400d404081c1405030040000e0200c2040c103000011325054030080240580c0010344003140c81d909110150000c04c40e1b03c3c0400307188210b0003144008144d00303440801c1214113580d140c6030710705142c40c00c001081180403000d800601510451710701c10040f001304024840c0124081c0e42e03019805000050780c00c0c0101c00c01007150105500f880500111107645641e012880d08008030300040e0b03007801036010950940103003400c070500107440e0511460300e5804100342a04180020782001480e00c101410300c21107038100d80e01404003030001d2100b65100c0e01d1540750307600415410b0710454610304c9501c10355620552031040c08030300d1034902145c1e644039100100180d00113600c10402101c0c3c2c100d581d00035a0b1000d03d00c20040c14420008908440b0100701460045002041c0211035080800b40c00840c1c080050800181e90707141c10409108102803490340c401101c1c82d109080380201100010076100588010f20748142c0c0301700002d116000744102c110351 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836779397 1250 836778147 836778161
    0x10b180424150906061b150903032304110f0d0b0a0902010f020a08040b22030302010c17090c060f040e0103110a08210d09050102030a021905040e0714071a1603 70
    0x49450010750034a0204071507401c4040e000d0b84440c2c1c5085e03c0c2607000401c40d4144d208c100c0104c1c0c0d0b02d8400e44203030001000ca4482d10712000e07058408900c0c0644034a55200e00c078034000c81c410010306848468039511080020546500b081c1030081c00c0c60840c510400504200c8800d03801304024180022103640300190400e15140d01c06c0c042070610b4500704820885411200342da580005d80f00045918488441d040000114013a0b400420046403071341001c0c0c1404006440e280e0090408c404000c1d00003030008141c140408280e8103c0c0e40d505444940c0c4c45a4000c642150ba50b0462240002061040d01c0003078501d8101c00710741200300c1c80c0e680c2e00d04960b41e803400012a200148501e61300da0041960902400080440c10400301d5009042e680309801c91b44111071181145038007084a4090180e480d2a039000c46c5200d041c040d180c00d082c01d1201c410000010400c8081081d8091a402d014038010b00751254142c1c8495010501c141d40000754034804003c40b0400711070030100d04090016407080c00340c61 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836780647 1250 836779397 836779409
    0x90f0b0f01030c050907031d0a021504050d1518080c1e2d1222080a260712110106050a051302130803120108010b180424150906 56
    0x1511003132034641841a030100052859090643c1c40d86003c0c0034000b407014142c201e10a03080a860181a20310421441c20b01241081400002c00e00045c00b5940b1855000034445d40c0281a000f42180c80c0d486002c00303010030b1075003c0030344410100410100184000a00281000708080c1e03050740100c44203180c007403511052415035903806455540c02c0707034107032404000502004045c02c4002065407807400d4034000a00681d41200200010900d45100d600d00015040d031072049200038100c0d250450f09a541c041c000d90207884011002c040b8048610484284e0000031061500c0503101d90307060514102030705440c1c42c00800f15942c908120b0748000103200d40c00507100c00900d03408899040c0f4040c043e400319010041086203600f0019849003602c01320074075004144181c010760391002c500302c600c440d040044e480715443c3e80c10044e02c2000c541d01d100248000c0d01c681454440256100d01b010700011a01400c010490450030207118072036822a04a040309010414403041480d98859001085034040d100304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836781897 1250 836780647 836780663
    0xe2b020118080a14030c0a030e0c03030304170405031903031a1c17070c0f060206250c02090405061b130b0f040b0d020307030b04020702180910090f0b0f0103 69
    0x80000555154040e10b80c1c0000c41c074201001c65520300400000ba03009a0f03000d9040e0501148110080b07505000d030340c0c4100c0302c2750040c0800c910010b0119680e4000604002c1181a0481d8800b20543c140c0042d1030003054003c0442d4200c94a44d04548030f460940350099000030708140d2030100506501d60b812141c810b010f407000e400841038440040725140e2240d130844030420403581c2e121480101201500740c507805540105009450000c088421030406e0b0322202c02c0d50440f00c200f0601c4c0140c520403140800800320101c0302d8032410181100e80c5d00d0030210080d4400480303c00d0000744038000452610810fa000801744519030711400c1c1c0c500e140541051045c80043c2154184540740c5494003828000d00419035081c102030325400c010040ba0003210392a070a040e800700410042c0c6505015222519400390b03001c515241650700410980380800d45012400c1085501054140f40d04000829206042c96030400554a0600c3c0c107900d040c09d8410305807109542080441c420f50944040141240d51061003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836783147 1250 836781897 836781941
    0x50402100509030102040e010e0105091807030201050d06031b1a0c1b010903020a030302031305092203090b070507050a051807080c070f03020309091005060d020d0e2b0201 75
    0x841e060303440b040420760555000c1c0300010b07071842c0365103105000e07101d2031241c00341540c1000140605c01c80010040c1e05108202203414403000408502c040607244c080c680107a4070140030f000b40000d000e0550009000b44c4400384110504400b001c1032a05480207141d00da901407007001b004050502441c0074004403508000d21400c0741b041d4040f400e03000e01106060481c240f5940380c001400c4105603034010390268000150918101140400b81c9000d40720071944560170742403240c40c0e4080d00c5642002e0031140141c80b10b1100c103040c0151014002858040d81c9141d03950700501c1c003d622880e07a482000c0c060091160042030714544200510359090000036080c160780d4441104852402000d0035141c1107400c104000d50116424110005245c1d001c2e0b0001c640e100307401c109201c05140c00408150044451003001e000554034202180c0b100d1005020146e2613120340c2e1403420050a00a80c408528810301c49001c90700690b0f1048134000c0c103100080003244c413640030000d07800d2311642c14400f00c070b80141d514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836784397 1250 836783147 836783179
    0x300302090a0608011508041b08030c01290d05010b04050702010609060503010b0607021509030312061206040b0a0c091e05100801050303030403030f09120905030d1404150507060c05040315050402 85
    0x41b1080d40b00d8010b150740c100440c80c80b60803851400a0382c100400c55000026105000603003400780c00141d0342024030510351119010243c1000c000c02480c0c03a4071600349001d88105210094229800c207440c001c00402060401303c40183c024507030f600c00c6541f51420142c00103098601803003052440d02000e00094504170099080054030490140d082403c40d6052041e448a80ca04001a0110b03203074030340d201d06841c00d0000400050301a100480802ca5100100b00310002d45064985600521810000701c0e80300121403003500c03010a1904103c0f06c880c44091520311402e5250004422288107507004a90808881406c030b0b03141d4070074068150503038400c00116000038401c0d817080302404501500000c1c00c03a001d41c0d4a00075003d0a007003100003e07000800500c1030b440d0078010030104080c507041500601e850308000304801c0c0114444d0b4882005048038842203e0b0080d01112400b0b81d00110030405030032019405007075900b0600082c1c030018601f944503003510302c50344505402950001c2c2440d094981d00c007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836785647 1250 836784397 836784407
    0x509061303050f03040c030b0603030306010c0305090a18020d0b010c050d08130b09011b0e09010e130503040906060f050421020406050d0b04020f01080f04300302090a06080115 77
    0x5001c508200c1e040202d0100009400041c5014a1280c04c10b055030b20302c0d604048200301005001c9501c00c2d0410018000180e8011040750060756150402585a12041c400256a80300361350240706440038110002034880115801413010040310032040001040c3c0c50300440b05501403440080052b0b1081d41100005270260411661140c04011100203100044e9940440404152815061a1744800300101460b6031010080214141454000c6181c00c0c480c00141620f24181b003032600c2414030760003041c076250070359191001c10754200c003c0740e640b030790b82d9100c2400500fa14451400080e0586501c40c1002d0311840840303003112004402c0410103c2d05030912010700b140114201d0b44641da84400181f0342d12a030a07019000780c055400000c0500c0d10b401801359156034003242c4c504102035130040080c045001061940c005403c081c110304120b050b51031580044043c806030303a001d0080c0c2c89460710722640c50f0300286440e400c00c0d43c10709545070342c541060b10035180a028807000c0700042425040e84c24810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836786897 1250 836785647 836785681
    0x402130908040317040906080f0d021b0618033301050901030b06010c150b0a0b1303140a0506011203020f120d0f0f020c2119030207050102070203120c010c03050906 72
    0x1100e03e242030b5903100d46c18201d0700203030b000410607001040243c02926050003254050015400948818280c130000c1d0158606000c16051203000041004e0360740c030b85a00f0291590f08400b07422070700c4400e0341c1c0da48041c401038004407840e080780c500600f04902134203050583d41203c0e0042c0003147c2c03036400c4d55102140710100070039507070400c120840380201007680745400a1001140c6980065209891801c2c0984c54407142c0000049000030481d008800d000403811804036500901c00e146c07400e012142c0b0310f080402c1280e000d0f201c2c2c410040007107803002008162070901d074400e808813500e2400c42460b054481c202401c002807941800d000d10510f01e002c940107150804200c10300064421028000c41d0221703005003c060329580d02c5150325195603c2510086507103960300044050030180c820841d607012a00e07c004500c00c040c0c000ca01c0324104102501950002039000f030039910070707410b110040710b0180c114840700c01c50b5600300b0081d40b880e10301902c11140a0040e010244c038003645c41000041101c074070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836788147 1250 836786897 836786933
    0x703180f06090209040305030a060b0304050c151c0f051e0403030b030f0708030310120f0615050d0308040b071d0f0105070b091f110702220c030504021309080403 71
    0x1540c40242c01a030340c0b018543e104510a03107542e6102c3c18001940750403200c040c1c120164011007082880045000005e5070a0100c20850740c00d6503660510140e121240641490030b03030044840d031545a0070341c015030045e50280e00101c030b0070815a44c50140b003042111170801001c51040f092808a800704c0e00c80d801103000c4200140c1100c40820322030200501d0080c0c280d10110590300080207104150900200076401001d02c40742c10601c480d0306444910b542d082c1c810000b003031240e41b0241d908100c0304c4280701d80014040200b451005080c03908000d070890b00304541c12036904010200190b1a640507001c02120042d03040d20010603e03c2260a02c501ca074030000c50141400070510071071002031510000ca071f00c582030381c102800e0828110380d4903000e504c917010315600705141800c640c46821101041070310411501103420710540200118045010f842170700e03d00c4e0002d81091a25510780b901904a02d000b907100756087c0c403000c1402010340d0201c0e032102400030260a0104400c00c007150395200c0c18108400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836789397 1250 836788147 836788151
    0x60e0409051c02030309060106140a050a0e1203070303061a39070303141c050411030d020a0c1d0622060f05030f010c0906120b0a17060703180f06 64
    0x242c100803204003070400d09001d8005030310010800c601d0754000e106d124010002ca00f0100100c01200325030300d0040c0221038400c42000004134511700e010f84210350507011810040c0c0007030f4900c005c4800c46520b90707000e81c80540119040800008960140c41c18241d804507080c44500c0c1400c0f81031098215400291050166410705801118041410b007007008070207121103402065000c0c43c61902400320f014503292890804801e00c49003c480c00c0002c0300ca03040350700e0b20000007416070303440c50600140310600000a4141c8201c03140c1c9044250002680b04283e0b020300c100143c810f0b683d6002c2c89a206140185041010400010034090304082e40200340010344504c400301d00e43e000480b40ca00311111a030080450094a0f0340401050400740314119041c1404030090021168980010b0081100741c4614020003d1308000c00300740071003d82c0310550b0b82c0740042504844c250340e40a0400800e2a84044a10794054407001c03841c00750091095456410410402d1440c0c5912911079072940010550199440d50b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836790647 1250 836789397 836789413
    0x9050f040207080706020c0705031b030c0f030f0a0b0727060305060d0602070c14090906010b0a0210062c09060c07060f02030a1d010608060f370f06060e040905 70
    0x85c00303a0001e0300c5a0010000103145403858203080500c0c01e4607140c0000901244505035600d80c0d1030210b4240765100054643e0f0380c20300318030701c0440d1501500901940c0c0d14081d11900b00c0401c001404070900aa03034a0fa03518081800d03030a02490120b40c88840741d075050b41e000340c040000390302907004a540000010100300f180581034172003105913400482c003140c44111294041c09540c2e0100301c003880201091341c94816502d055458556190b2041c00303000c0d084000401c3c0800320520820460fa041d051f204010b01000342e8414448800013108400f046a200800d8407488403a4030b5045024800c00f8814000c105a403224501084135030b002c24010340700183c40b9103848001000c50300003035024583c14000002c0c010110103414031100a406483c40142c0d040c600100a03804002038070076007150011007400d105441d03000c1c5031050144020604d0746040400303000b0085042c0008102064030501c80341c24003035101c0a4403940103d80c658000c3c040401e605a0200480e400c0560141c1030507403282c81110611 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836791897 1250 836790647 836790653
    0x8071703070f0b010303020706030b030309010309060b06040905044206050a0806061503100e180d05030a14070c03030e0c04020d0902130911010804031b0309060e0109050f0402070807 80
    0x60040a2810740e4401c0f40030004204066040000301c006007054030782003103c89114030000b03440303100d0218540d040545640411041c01010b80c400c0498600080c040f9641c1c9641c0d5540101030310781281d0a6541d10082656000d03ea003202115410403d201c028050040704c01100d901d000c0100d5140c19080c0d95510300000c02c07a07484421141003c0c1000c000182a249442d1003003145055114841d0b0360403407024010b0280400d541804141a40e4402c2c403e49800d9980c0050031803c008140e01405030340c4100c0103130300c0c0800d400400444c06440c2085040c0070406107299901c0102d0000e483c4a40000c440d440b1728404684298800c003240500e40b030a40e0300341d1041c00c00140aa80003023036550283c41c0c1c0c40030301100310701d01501015414040240d00740b0507e800b0703403140c20700855054400d034144062200043c2c2050300c00c00c4100c4030707407805203941e007464941d07418001c3c070b000c5281c040c94010501002d070311081036018841942c01c03103100601e00d841c40442039090001a4000401c221018403050001d4400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836793147 1250 836791897 836791913
    0x2306010503061e03011d19080307140f04031208160f0c14100203150a0308071e0501020327010528141806130c14060f030703090303060f0807170307 65
    0x40e11110f00700c440135680c81e10091f00f8111144101424074143d41450000140c00c030040c0c2c1d9100a4904240c0d4941302c5941c0380c54050721031800c11031801440000e0120410840c40c82043ca5603030207a88401e030300c0e80d372107a031020304030509424003012034180c002c0e5107c164400c09a01c030a04e84500032110fa807800e0005014a4500d0064171115855000b104010841d071807050a410442000c41c2c1a40456140d0f032a4001203124a0390003070402844c036140000d8950100e0fa0b60b03110540d120008656078035210a00030b50000c80c408001e0180a03912100351542201401140c0c007a1401c005404090881d108401000e000319180149010f929900000d11359403a4403a0217101d0864525048a060880d091950a100300140a0305000f00300c0b114000100b060030070030780e082e60456507800125000d21000100f85002d80c00d401c0141141c000104402c082c0e06420411545120751014404142c0383c2c0940c080c00b04080c02019516444104200102c4080341c80c01000404e43e20281c0b80780070b002d6110905 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836794397 1250 836793147 836793161
    0x9020313060c0f020d1722080703090306050a0209010e10110d020c10091503020c191b09020301060c0318080703030801081005010f140109182306010503061e0301 71
    0x20104903c0009182e101c1d8060103601400d0b0f0703541c5040d5004911181c40e41c0200171000d0442d00e0f45481500140d91120010b0a0004c1c946412040c00b545491180c540100f2200701070008840c0c060034100411150f028a00135a11503407816140c0002c44840d000600040b102c1b4040d696081084c402d850704000d010500070814101c0c0d40c4d038060004c070174096050010114896400c1c4040090141c0c0411a2000c440361070026a031040c60096501e03200b01040920304411018450328100864a280f001c00102b80d00034400301c4c00300c1c0e40e1005640c4c0d45401050480c0000d10511340842d4004441c800080e120382e001c407501d6907008001c55051512102070f00d00e000000e400c1180415545001801360352010408280040c3c1c81800078446507040600c120913441c190320609400b005e12100c081d420342e005402c900041c0c10303841c0e440080c40310a50141c0020384440c0c40c19019114a060401800100021440d4850f80040c1c4529141d0340710300d0140040510501c25100d800013074883c000816a03802c1c019a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836795647 1250 836794397 836794421
    0xd0c08010903080f01260304030818040c0807020c0d020d0506040605061207030203070e0a0216051e0303041707021507120e0603160f110f0708010605190902031306 72
    0x14018400d15014040400c060840070030381d004c050042002c050b0520708055602c50300110850754003226241a450b40c011900300800001e000b107040d50b17494444208940c5500c0080f1010302800c074902e5070a4460b58000e8a9210050300418007030806414031841c840c039610707c06018a0a10405038031103500b0003805640c11a074140d1907000384091442d01d01500c00714201280b002e40039241c41c3d036000941c0c56059214290b1004007a1000481c010a00e81c152000102e1807510055101900d20384251100f00b03090541042054070b41c96a0410f1100000f600d200e20761100381c0070b01800c5d001d110b2042d035400c0018100d03030004010700f0780c51840042c140a080518454014401c02c8000d01e4006440c1d0850006114015142401088521038000780c01e100d5141e0b250400201110020500300c542c803112051024151095a20704005a02d000911404076001d24000304051922002080761031507100c0c149607804001c0c003005004144641d4000d6800c8403e602013884842031540d0741c00d0a42e03603501401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836796897 1250 836795647 836795651
    0x150b182403010e0a050105031605130902100e030706021f09170f03040b0105060a050a0e030f2b09050a3605070f02190b040503070f14071a07020d020d0c0801 69
    0x1300486488038018907014040c114041c1c2030054800380306124400040c4582446808050310341e5a44a68640c004200590060503409100070030400190000b00c41968041c041e01c142000018071520100380110260041800240142205918a805000d012605443d9100304c60190305070302c0c00713104c01040340c2988015010307107034585810680c0841405070b215500500c8104400303441aa80b20086461200040c206004000d4100ac0032074640560402c000505110f0401041031050200d40a0340e0100d250450350106e8650168049440a04510420740c01c8101018180402e20391030349071003101450410075403404452804001e8141c99007043c40e46505546500740103065a02c111048921741c0f03540010300004c0c44121042883c510302c00400b40c6104d07050030128040080034012a02001d401101d50741a58041381806902d03002d09440342d0b52184115600090041001e040031301100d442c0ca203855042280d15002c3c07043c82d9048900882e0301c8002c0191000000e14850200d20141c0360315000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836798147 1250 836796897 836796901
    0xc12160b0c0d0c0f030606030903050304140c27150306010b0f090a09090302010506040c08180a08030903130e040f14030d09201c060c17070201150b182403010e 70
    0x5e41110030f9078201078100350401800c103000c01c9c1c00c14100c1c0c0c3c01c0781d40404506910140545524100803695068036404002c040c1e000d41c08620920b00401c00d12410425058107446480500070103218000c901501908800010400d0307a011a0240010850b1b1030720651801e021500001d003154600d0300980d00e010f95070181d480c103140d424410507500c61001d40b42001041c0c1071040192400f98010726008400d080380f040003030070000c24000c00d0295980504580e40f2414140b403255100c0c0c1180ca400d4401c0042c400001491601c17801c8414095504262508504c1c442038582c20f21011202030307004450300c0100175490500c2e50500c00c00781c0c3c041c080c20b08034440180c0400b0002e0120500043d0343d200310f52060820403161024800b17110600d920940c001421712010009645038181d02022032440d0007808100021a901034020029604242c0c00c060302c0369480340022104c1d40290510f0b001070702d0f04e50034610340d00d09040d18565128161402c0480080d030040b03004070280c0d03200b41c12610042d01002d003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836799397 1250 836798147 836798177
    0x311031e13080312010312110115050f03030423040612140118050709020c01060b04030614061203090f0f040c030b10050a081513110c12160b0c0d0c 65
    0x1c8070141c440c11015500c0c084000111086182043c08094124050310304103c1003103000d04070800080300c0310f2009004d00b0046100b031410040041c450540610000700c10300c0380d80c0c60f001c030446098519170001141d8240400c1c580003017190003010703460703040381d5540d001040340002080d07000c114510032140200c450340e031141102c1c292400050850300c1403080c0744040000034000b1403c00280c8403003060068552283c91481c9001d424076038000c00300f0100c0003601009005c81034001e946081e89405407480640c0b103003400c0c0504106070b051001e0321601f09000c0c4804519001c92519400300c4000e1403030031802182d00004080720f06112030a0080303603840085030320714101b01c0c2c0c0b00342554401b42000c60610070328800c0078020038002403084400c2105503001c1d5101d036442103820840b643d031109081020644480702a2a55070094140b08140d11039200c40700710329a219412034811524100c18000840c0c2d003a0303101c403400d82001c2c10115101409011521105149219000f03d1090b5591004030241c1806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836800647 1250 836799397 836799427
    0x27090e010c02010b0d0803041704062706080f0a09060f06080f030702010906322106100507060207020d060606080c2506090501050901020a11010b09040311031e 70
    0x2007014019a4104580f003425a41c624100003070b8284c00514085ea43e5969140a03440240002c620b804910f2010501145c415800f0301118860410721032448500784614400c1d20101c2440e200d018002404040041d951503080c80300190407a8103c040400c0c3c1a065036149000e94140600641e101e0303640310000c02501d00e0070404410b00c00c5815000e540303850240c0c3c0000b010403455008400522540c102c03200d101140c502c0a80401745034400510100d034118000203030709039022509c0c14101ba05011052f141c00e07256510260b010b031100401c5000034101c0c464003070300c0715006080d050340d28070340c28084400981c560285c1604e000f0b00c00d4000180c0c40307040000190628101403c1910b01410a01601c1c50240d0b11199140d020960117030ba88181c0e240c28a04280a0480604010015400c0005001c011513054026240317500b09030700c8e6003e90340d9101c46c616007280c2e0b501c51003960080400010402181c060510643c552001c0f1080c0e900d040100e49001012440181035030f441000d00160a013050941e107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836801897 1250 836800647 836800661
    0x313030809181509040201020f160303030c030e0703030f0216090f050f040f060b1c12031a010503011e080303010b09102c040f06080705041a0306010627090e01 70
    0x160100c074401c3d003048810404040342c4825014020b01301c0c00301041c25a8004c00c6181e040400c40000c41d200c102442c024101c5000385444100c0110741040200c100040c007078040c07601c40044030402495180c3c42c3d0340301101c901c190903903007005500a10b00340a003030361505050200a0150001f000c038008008841c584100d40c0004c040ca0613800c5114280300002d504240481c1c0100d0300254042003d5407400001081c18091000c1c91602010940c0c00404001e251001100b01d84140e46080084400e80003600c40c40d5103408240360300040040006002d140e81941c44220315500981d451100f4070740b034507000c500d0b5a00a811012000e0004942c0eaa0349181181890b0000d200c0d5190a034601d00303804036002c0030b1045589102d0380314548000030300401c0c2c030360750b110180500390b203c010710100d6601d401a41d02e46030107010b0540a14102a00c074548100350307001c003010100018005044503881c181e4120760b41c007002c248410101da1080040b02e000500d940b9030001910b040c0d08001146800000000e08544c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836803147 1250 836801897 836801929
    0x109020301051e0117040b090f0303090d113a05040e0a020903011401120203070b0c06071d151c0504020a06050702010215040b010e10081b01020313030809 68
    0x4200620281d10741c1142c01e9100401c2c1505049002501c50058410780001005d80382e000800c4020081441090340c40d81d8081d03900130080d5070b49520407812440c2c8900c400c82c3d0040b00c540c0601030640a0b0380c880d40222060280640035105092444422121006081406000071a030150303a00c25900f004407042c060100d6240c1000c52030685009030020000070001c2070300c7c02c56603000c10041c2c82501c00f9044080480e0704948884101e6071900f11140180302210003d901900c200030001c0b41700c1142008594103110420020310550b030b0b4585088400908619105404c0100580c00030030984070f003048445140e12110721142c4070044e00441340042e2811030902e070405424082440090b85410041c0d800382d0388180b420503030301e10305400140e00c0c02d40103a08008807004000c080006201420b1f01c50b605803044006a080716840305a00c46013403000750700800c0b4840d003003007081c500c800c25031541a281410060040c0c84c1010210007003510002c003507520940b03050000060000107441d03c4014942c003448 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836804397 1250 836803147 836803151
    0x6120a0b0106031e230c1204050718111801021009211b02060307050f04030605011406120c1315020705040f0606080f0c0906030a230f13061b11060109 66
    0x1a009400410108083d40e810804005c00c0030940c9201d41e0004c4038802003a19190001c40d0070540303001c0e40e030341c3c003103100e1080340e21200c0901c3c0341421201c0c002da820b403090382100e441c1825440d2006400c070b49800034440c0e05500c10411200c052202c140a019003150184545020441d5401c0100f151480345400540800c0740e40d40d50742c9130610f28038030b2480900d42c0540b91181c50b0303500e6880c245c070a4800c0442a06100d000840c1c008108402e0350403140c1a2000804a050301050800c01c1c403809010b50070401006801e0a0300144850303000e80c020300b40030906a080030310020b07500c1c001d1401e10161035140c040160403400061015007060b018a14241c110414100956032030b0100c01060b60308080e20075407256034040049065140c0d20419140510300050840d40c0c1c9041c0051200300070020490f03541c01511205241d04241042454843d108101c6001d030701100f80c1d2a42000700300300c608403201710748041e56034013400724080c054003007a6110501d0751240c1548950540e01036241840c16444070b14694 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836805647 1250 836804397 836804411
    0x90b010915080906010f05010c0b0601020f07180f02190302071b0801140711030901030b0f0a260a02010c020f04090c0f05010306080c1f1112090907090b0306120a0b0106031e 76
    0x1980c810b901c803441503000310395222b498882c200106d09201d200c15001c1c8043c0b0a2040c00300d02d402401c00f0156820702126001c001d682d8014514200b42e0091004880e0305502847c0d4807011030b0300030340042c02540e205a03083c20802c00c0c0b0740d59500c2c0301000394005140e9a0754500001000d600c0c50340e200350704645141045d910024034040600da80e44199010641010f07180c820701e05880c0c444440c2010f25010043c10400010307192405c40800081417014481851400144641003610114002c030401e901a507444c404902c10b83c0a114102c0302400807203070420f41c0d88050710003043c4183d0310000589080c0215040040c078101c001815180f41d40c20210240c4c00c0084214240d98901c594000300e4a0700300c3c0300a0300044a8981564140144038001f0068003901c1042e1580c2c58131745004001d4104222208407a507202d925085849003504e021340d090045081000c64540d03d424900c1168154040302226420030f01c03541d4002c030700072083e840304012a85800c06800030910200e00c40c505610040000c01c410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836806897 1250 836805647 836805649
    0x6050406030b01030b06120c046501080c0c0a0b09100510030209090703080d0c2a030513030804030506071b0b060409080f210619090b010915080906010f05 68
    0x9450081e020b13a100326a580c0303040100700d440750f24401103c207a0742c012b2140545107a1181c1c0340e0080c90802c20b10b01e5101c000e03030000d00705510024551031000340f0525107101d91030040103444030725020f030000c001000188200368000d0810400d60282512800740c20b01e0504101300c035980340415401c000900141040100000f1100c60401d4038200c80d011500000c10f83c0358070400c5800c0210a400c09000c4c1540001d002580900e070340c0041490810665442c2c01156100d603024a83e5090503070b088486101114000d40030900c110041c05407403034078464031801d20390340b603031501c5003a80300f0342c01100d603500200b0400c114903400121340410140d02c5036900750784203401c6c0d817101c40648008040504c6076540d0f075480801d001d8000c0507144000c91205000e981c5280400980c01c20b00185180300ea032403e8440b0003e110743c00c0529814800000507000b4040c01c50410a0300702c05401203410306030420113074030800586140d282d0b20286004910751608500d905154010394100070781604030a0b0221418a81082a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836808147 1250 836806897 836806903
    0x311040902071b12080d23130b0703021809040c0506041404050c07020a18060509071e09080c2427011d0120032215140a020106050406030b01030b0612 66
    0x129006c012000202c64807038807840320110701503520a01301c0f0725a600c20440c9020b039400102d401203003c0c9441c09a40d40d00d506044040c0d03c2032824000c0c4c626074010280e0300f1410325a0500783c003d0300c0381c0c0d05801c009448401040680d0842e5110070b800c65000758580100742401c1c441d003500041c11544c0c1c14075004064010900c0c111151140c82d120480d0340c103032412400703015844a009040300030300c0f089203400d0a540051400c6e43c424107049050415541e404050341c001c0503003600701c0c0c0d03c0c50060300c940c3c0e800c8010400b1802d090b12907a21a1656812003108032214040100650b80c88416120300901d900c1024698804070860b155043c402c00000300004c1a00c240101041e881091800804022030020022414851388002d0444c51002240da41008102810100b00385400f0014058a60755240e10b41541c03e07100b1000e940c007040e030798401c4030400d0160764001d00c207001c111300000c00e0380c030b0f0740e4004a0100e07500e0303038015203100500c040140308001030382c20515041a0100c030a50785640444030450340f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836809397 1250 836808147 836808157
    0xf082b09021c0804080607030e0606030d0905062206050705070801091104090f05070b031f0308040b0a1e02030712030207020a090216020d05030c0c0607080a0311040902071b1208 78
    0x180c0000a449000400521030f0448002c2d02421040d1002418450400780251513807108404060243c84000380d00d07410000340a28510203a65116907003146070501b4840c555129903403184018240c0d11072800807903c40c40341403006103074580e0761690f11445414058200b280a0304104956410072100c3c0c4003041419800221403c1c00f203030000350b2444245029140703d26480801410390183e180001411640c2c140a144200101c040040e4a40342004e4501c05084050000900341d407014031040c485064000e0142c044044503003052148045a203480640c02056601e0040060788005261400c201ea0242c1004a4000c03d040c1542402182c1d0300040c2a032a0a000722102c299011420b224421081c503020b4000a030003602d2601c03e0095400c00f25100d9124038058031640c400c2c154120b0043c20b0010895580580105a540c14602806000c80143c0072035101c003840d9800500020944071110310003031500d07038460110703814200250403445003605925841650111183c000000214075600100c40d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836810647 1250 836809397 836809429
    0xa050f030c0903150a06050f010507290c040906060807050304031101180b18190f11060d020c06090d0f030e070b120907050301150306090f082b0902 65
    0x6622566060072180c090300030346540c65490321400210015804110481c6070007210851030a0000640b60010300085082c0c6030f2001d40055010802200442d0141d09150f42c84441c1d8081c0e1103103a044640704035105282501c0940352010000703002c018402d01071280f0702c000e020742e051014052428541c0509207010050024051005041240d0034148003944010031603d0301c840c00710503868250400b0200350001321a407003034016004019900e0180001540c0808441d0b1340c940000d081e00c0c2e650340b41d03100c080049040303418000881440f242a614100035080d41d90703689000580341c2c0c040c0e144452600c50017078030f604269082800340f610060761182041071000d03154180880c89a00c01c601031840e10006a04c03c020030750001c203049000180c42c40d4401d0103288414211103d55031220109400c8070201c42000314028021042000010801e801c208071480c01603000480d5540161034400c0b0660003101e200c20b0065803280d141c00d8090090790324051217184d528003040b0400313150380440c910003030b000c81072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836811897 1250 836810647 836810677
    0x3280807080a0e06010627050a0303180e0a050402102318040c0201020913050709030f0204090614091234080a12181a0712050405210a05 60
    0x18485407415002200700c000301e401100d8181d03070f545400800b4541c032641f0b01c1c80c4c1c0b0072050449200380c1c20218154030070f81d8002441030320b41e549955401e80d61900b4580b580e41e071003032400d040000d0f91041030903907a1003540e100801040c54500b0380304011808c0d074404040c00600080414215481c450008402049800441c03110780c0c3d5100004420070001440114039401030406031040985a412b401600d641074003603601541e441030521001c000d98000b00c44290002c0ca01d13a204001145102104003801800036000040c00305141d00d0310405d68048046008907100e410003444010507041080300d000805400c401c90401548a01d0080f01c3c52280c3d4240c194002560310340c07154045c0c60482ea000c42c543c0204507540e94a0030b000040c02c0c4502081103013a40d24a072500e44c1d000f140741c41204c4100c1e41d0f40b089084400700d10086907031041e008050706a4041183e1300301144080000c3d0320500c0d005500803801405100441d81103a07254490300321103441c0701c007028410040016000010384544a0101a0b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836813147 1250 836811897 836811901
    0xa0215071209081b06071d060d092f01021009060e1f27030c08090a1205240f0606090a0914060f0102030724020406020328080708 57
    0x21284030082840450000d86402580c208208a0394004c003801c803000324136980c4207260301c544251106403c45001000c51850f0b4040390200c10054104241c3d001c006024a0801c040144548200c4c0c81c440e100b00c490b0362007849111550050304128500308010902c050404683d4500004c1d1201e005102c1c0900c840c0e01d4240e5501081400d411040d007031a24801240d4100c40d1512540c1700d0010f0390a18501c1003450082c0c02c1040d540302448440120307244020208040310250303030440d00c0006000b41070358122818011000c4550780c4946000052041c0303070748944078400d6802d166007440c059040f00005d9248914004140d41440c8004a41c0304843d10041d0141e5507801000c00c00c54855811403070b07071117880c07940c010a9030301c020b03445039640f00c060422012a564992007880036002d40c5c000300d0341c09680709000100000e0b02c90541c0e691086902089030300c1c1c8000c0340100340c0a0360019009203003da000805c248041e07000004105602d5000451115000340c3d410300080c11001c80a05088208803403100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836814397 1250 836813147 836813161
    0xf0a0b030d050d0515040504120e1c0b0702100e0709050c03070912060b1504140306071d030a05120a0f091208090d151d06090303130212070f0306110a0215 68
    0x40d40317405000076200b444035140603d0540040c041d00704a050201301842140280f50404d00350403099220501c01e544c20343e00c40364440d4103043e8400ac01c5e001c11445205208002d11425000d404c58880c8050024504581010707560400e850008100e544200414010061181da1000498040300d0220340c100e900346495003007060140110009840d01b210014140761071403110b102c010001c5074010000f440621800c001099110581038803018000392208641c40940303030252040c07803003c504c000c0480707031502c9060f0f81e51400c1c403290300c41d020040100401d034618060f4120340382c4d4a003181d10345480040d5034140101c0000340395503104094120000800c1240c030544814008600e0315030820707542481040d80490900107085a44c00031915940c60107924489014006401c03070082448501075400d5545080100d0030041e1410000d0f0792040761302c1207884040d03800344180d80141c005045603001980c111b0070060150382c401180900c600760b04001780740c0c0095001c41c401000d0510400441c0c3c054076403034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836815647 1250 836814397 836814421
    0x5030306031203221a0c070c08010c120b041503050109110d0f03080402131401140607080912032a12070302061f05180a0b0102030901081501090e0f0a0b030d050d05 72
    0x2000e5404940d8001840003001e40e840c01f0b01007480c498001101240e89841c074250a0300c0c20400440003080c0341804155500c0010340058042c0c03640a800010b0302203403607403100d1a2800c070358010340d500d9640e8541d0800344622500040380e0241c1c01e80e0b0b01000c41c013503079a0b0401c00c404d004101604100f10702d0089000c6640700d000d61800c1da46500802d0110300311704a12040d1151003032261602c40c0042845031b03071050420006803803560380c221150310704080000091011203040021052894002040507404507500a085c0c840c0ca801c6210680145103140b140052425023040402d41404006010f41400642e00013084e035400326030342d08a5049078101510100c1c0840483c0c0025a12402000c040c0402841d218603040c4204602a81480303454940b0005984174032601d004035000a81c0d080001d1315800901a0b001081030062501c0240340707584002440c4003038015906a920070041d40103018140190b0700488580300411400341c40c24824111001e800351045040d03041d031980d100c00c0011200341c400c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836816897 1250 836815647 836815673
    0xd111c020d08090c130b0f01021f150e13120813150b03030c0c0f06070c05010c1a040606063b0d0c091509020703020601030807140a0503030603120322 66
    0x18080401001c0418030520191180454103401010030511f200d10031362001070000580c0c030740c048440071840d44c1d1411110141280c140441c0e028a001980014020081090a845074030031802d036200e482c885240c020b20580c0e10000040030071003101c040c4510880050f030b0348141036130310226400c207080b04031350320ba400f80a1a10186906010100304030f400d4540101ea1a1056002124142c001d40494010080c01e405018800b80821306174910501880d40107200c038410003406000443e41c0182203610351144503404071030480311a62a0201006904d030800ca18001c02d04400079954a040c400641031126007203c0741d102c1c81d03004c491400a4050343c64442074100710a4203c044007107610b442d5440780001c0d046480a50210004060001511164920030f4490b901d40c107a000d4030160340f943c0c8a0f048250405c0c0e1066070305054001d2000c00300d8004000599109204101171a1249420000c050034401d0489880e040c2100400811048a14440c1e00c0c0151100c000c0a045400040e8101000d01d60360b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836818147 1250 836816897 836816899
    0xb03040b220515094c2c010506240d0f0b01110f030301060e060903030d0606020c0f0d1407170f0714130902120d111c020d08090c 57
    0x761190500b01c5210102c000d40c0320300003a008481d8905101410b0b013002d807046079105c1810382c00c510314988401c0c13206040d20440d0f01162a035600d101c03030300062100880d034042d08007241034080000703090851490070244803a143e4000b4002c01092030488080785046d81c0400301c0040c41408505c01c08a5a006107094514105a1544c100880040809080000c15006403400d010810b441d00031010341c60700040c04460154244003450444c4d00c0e000c402d541341907010910030f0303000100780304110658500b0405040d844048081c08541e56241c00c0000c1d052508081805026a240c0080c0d80541e40f512494040c140c4d910010119a134940d40c034a5a003400402d402000385046480d00032480e5410001700780c980760103600e00b0b030f40709942e07140380150780d4060f5041a945c01c000c40740b0b94083c0e015003581c0211b640f0750014102007080107191072210f040c80da4610035000464440314440d40703004407c02064840b050307402000e080d240d8400700043c0d500c0c0380200940c8204241c010000d019000c1c01e10510640e100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836819397 1250 836818147 836818153
    0xf0109031205014a011d0103030212030907090911040b0613062303070206040302150708180c0a1d0c0a0207180b0d03120e0705061b01060e0c12010b03040b2205 70
    0x900004d5008505020b00c1382061074141c0000a104421507103100504030381e41600140800d81000e40210703c03507040280105200e008020001550191303078000d2850b5544030b40c1c10449194290004c110072545c44030074484c0684000e0043c0e80610080301a500140c034501c1c1005682c80e20619204881d5005034182601407890110501020039000504c1c01d000360304c69021f903420316a92100300c0300d0322801101c14400285e2000041283c3c1d4910304194000c02401c01e00b55141381c2e8403140803070321080e100c0d03018244800828070308600c02c101011040380c101c844185401c0c6010070400d402981c0e420a03001d40d070445a04c072211018164203c0d030180300184000b82882404011900b8007a1a03004407003403400200d810003030ba1007030348040401e034038060381c00007014075080046924191042d100c20542c040229940c0700400709994481411052094251040f01e40d0380d030000003105510440c0690120300e03004024010b1000040d00c0c000002c1c0c1c0264014205001c0e009003084508102002c0b80b00a40240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 836820647 1250 836819397 836819519
    0x1b0c12030703020d02010b061e2106031b0603010302041d0607120e0d1d01110102040905010311030601151b02130905070f03020a0905180f010903120501 67
    0x6000032015200d164080c1d029140e00300ea04e01016803c0e604925095035000350204101e4222400e05a070407540b0148508440d4100421403022840e001c4100b880340c040300c600e0104112007440d007044006081a8901c041407082d401c804041000c5000c103000c02403180d5207a405261b100f1255142c1e04440301504002c039901c5050408003e820b4600400359211003600703102c3c0e2001c06240c0000c00b403185007026554810800740d0fa40c0200d0a4120b00040c440c1041103078040548178643c00d001500261848a02c00035295165141005480c1c0c40c0c511428002c1d04010010414600000c105818250542c20401e94810705503d42214a19402c04000e501860101d01420040e00c079a2201e0300c3c651085045a224688507201004c010105210003507000c00c2016040c012005550862a0410103984d8407900100350035903c0da04207400181c0440c496990340c40184140343c2d001040d0422800d860004014030f50500000080c0750842170f00c460101c90b11a08400859010540b140003ca0702d20200710f80c02c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 836821897 1250 836820647 836820679
    0x809030c150306090c0301140d031115150301050f0a11040b03071733061b060412051303030c0c0b0a030f05090111030f0a060b0f030f15061b0c 63
    0xc0c1c02c1926000d010b640500006420002003008172070582d04406600c0b81c1e04021407041081a01c103040044082015581d49080014070030802494401202c59603208c9500d002108620400c1c20152a03501c20b83c107080612000803030007040103030019906400403a503403103188410180c41c850b55201e0401c6410000c200544c807a40000c140010300c00300090024584c44114014400085600a007480e8030300380e580400003081e0f84c05619580b03803800b0703050608115241030408240c18136802602040e40220041000704004a507201d00002d00504141d4100b03d9145c00020109000d800020180003146149005107c51400507100404006060581e204d000c0076004014185044424011505001c040350003082c3c1802107000324000400014115a560900b07005d4040e00902075070b080d40d50b40c0c413010a24150010013003045001900c2c00660f00d00781b000003038000c50301c001d050619001017109001000d81c0c81c10100c4038007071142c44a482d0112296850181001561341000c0c0d44611403540b94511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 836823147 1250 836821897 836821939
    0x33903080f0714090616140f150114010c051f020408120705030f1e0309010902010e0f010e01120b120c0907050703080c131e1712070809030c 62
    0x4601ca10030000060794840d44002e07602c003044031502c10008a0203003c00c0c2910704140c000740211000030315000d1000c0340d558540d01c0c9040d410001ea01c641d0f030410307810020981c1e001c004e038580380d6404d401030700400c0d80740c42c0101036100c2da440b0b409810070034200103409c140507041182c001900310425000d1034640d503908202c0001e621501c1039010b64020020f081403105100c41c02d807214150040c02942c0752414000c0400540d500181d03c1d03151809840c020054060015005148100c2c031007800014503038980d00015007258945425144180d011100104140c5d90150b280080240282403440106d10342c4442c40000d052104600354000950a0713140303031003400015854109003000e4401c801d03682c48185c4211868403400c003000e8086010403010442041c1c0c2d8200919030054001013500c0210344804800d46108103501a6040d2440100030600a80600c0c0d100804900311600080106681c450000c01507401034403000785c05103030003043e400e0507600c05000c1c2d030421010007055504659580c40458031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 836824397 1250 836823147 836823151
    0xe0f03100b01110129031603050a031404060c030e060c240a0b1005130317070b010e1b031503070807030303050106080103032001290f030a03390308 65
    0x2001450743c5010f40fa1203001842800300b00c1903181c50003104d26070b40c80c004a52640341003003820307014401c080044c0d5560311102d4552010390720900103043c00d000c42e410000c01e4182b0458120b085038404000401c030203038001142a105136890306105650343e82c41d0000400a021b0640702407100d004240e2590a840003c2c6605402c0b4500e00c074480c02c81742c48954054040310004144950408840c080f040459402003020748040040340035901161912560b03156078424110072214603404010803543c04104281d2051703809851059580142441d040703440d03d01d00036400b01d070b400492000101255161703c3c1e0403801702c0c0c259400380448141e140c0d280e0855560701d943d44400c4d000a407805001040b86032040c021981284d0b01981c580c0609490300348107901400303445284262666840e403403c084a01d5034a03103400d550320030421000c180c240e41000e00c8030001d50001c0341c83c030a402071501d040000e900188404080154241c201c404e07818129455029000c1c00300100c8038001840510000301a80310b25824 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 836825647 1250 836824397 836824399
    0x501080c030103030f08101d06030f0d0801050f131b021011030601052511010906020106031721090703031d030601180b040f0c0212190e0f03100b 64
    0x80466440c0c0461140c5800203010040000f880c001c0b004212920540c0b50b1900101d800f0240c2c421a582c6080000f8000d0100d00070400d4148640d080160a207000c3c03200034104001c220207003200f1512028020b00e024014011640b0a404450302d03c00b103620b0380c071400300440c400f8401c100200c040c9000904010510190440010300c2402e003041260a50b501500c848c4142c040b0045055880352001500c1d10340060f111480340c1c070740560b4502d66200c003041e44010098001d2a02401007d50030000401c130100d9600070405583c14280c003040084c034125811740001d084840e03150303155106562810500f4203482200d0074080403840521070006c80110701101100e1007522042012342101c1514024108000c003820f5041d080134004000340525141e84d03280c3d0706a44880001d0581c2c07003d000404482d26168421307081503541c3c01d051070aa0b010041d51070b402c030314000b0301810000f1091414241140c1480340070100040003851070b1003a140d102c503503c1011030040a1342d2042d0158401d20307005000240e422 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 836826897 1250 836825647 836825657
    0x50a05010b12160510030207120f0201060f0b030429070504090c0e0904020409022106040c09060f0303050c0102070c0b1c0b01050d0b060f0a09300609110306010f0501 73
    0x10642d07801d00150069140648102c100e071643e2a100401890001070058001815001c12480c0002120a007619418010a465000310701c081c404009086950701d400418914468010500c0414040815254001d61098820318608076081208070344400d010301c0c0c0d042600d2180b0074440081e23000b001800907070b03405071010000c283c2c1241d2701311003016000141030f03081190400481e001d42000c0d000006801e0008d465a405111000d12100010a80d1400d0380030702c0d0885401d0204020f010340510005201c60f070400d000050a02002c0b4100f069581b00c02410b004002034554400c80d001e4054551117a0400c0c070006240d03580e0900384c103840c7e01c800d03007800d810750b6005103800b469611481443d80301e030302c183d548a042182001203000102004a00c00c1d52000c814800b580f40380b0030886c0107280402d91030707860038030152800b800c46003001c1c090110b90b40700d1403000e008409142d20006604070300d0354203c1d20110302a021030500c803402c481e1414482c0d070540036460001c00c00c030341040c1c021b0040340c000380d90b2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 836828147 1250 836826897 836826919
    0xb0c0c0f0304030c06080406090503030a020901110c060a05030a0e1218090f130309030503030a0b0a0e0f07050f0d060e0912040312110f150609010806071707030207050a05010b 77
    0x549901c42d50200504504500304244041407090306903e603c94803981f40000e1407110b40d15803500d10780044445821807900002c6c0000075503070100254915180a100420017683c000000030f03214020382c41081c0401c580400042c4a044094000780140e568003010f49012481803020381104e0344c08181000804600341001d00d00038180b51840900c10182c01758000c60325140c6421181544240b010180e0070003405940c0400401c9080c40251300403244101e00091461040003408038440d401ea01c4510320806031810000940400c56590783d000d451403421594940c950590714046000f0355220080702843c20802040c241090200280101e140200300c0380901c000c0c4100f44150310a5000040074141c00c0c02030000580c3c050f071040030781c0b04800800d943c030800c80c040038140360101461250300c850031103009000041c01c150941d540034224020140009241407200900210403040050803410320400010f052148030b94103645d07400f80c1c050241c0c3c8000305241803043c060210342c80c01c41c0c411441910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 836829397 1250 836828147 836828173
    0x11061308030d06171b01090905010914010e070c080d06031509051e0304090902061c02090f010302120f0414011e0605010203041229010801020a0e0a0f05060d06030b0c0c 74
    0x1401c014502144001c00a070320b0b60600c800d03518000c0117926030601c2641c280104080396103018140c0600140c0a000480c03030300d8042c10b08441e60040e444146031449100074842050f604c04003540750b4540186280b95500141c1d40850000d20f00ea60001c0c204803940317070011820340e01c2c3c0d401c51095180100103c0700e008a80d803804010f2100c1e41e40400c1e003603074801c001c00c102d25903154020a1075a400200320701d0038400c106d00254002158501460001a0f00040c566100c0c0b804c06000348046038280707421410641d0505050034103281c003601442112030004001020004020028080101410020722005c00041d4100a01030800b500046000e404c002c0c004c03036103510010581d0200c0703680c2200c0c031002550b01e80360f8400e144101c4c0000700c0ba02c80c50500c0d90542000341d01c8101c0c001d02e5004001a5905003400c1c0084c00703003099280c0607101d803182d8402040030081c00e2081000303650080380c10799507850000f81408010000c0340d100800d040e070b1880c01c000e032a01924010700f020040d0003041c0c4011002e00c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 836830647 1250 836829397 836829419
    0x13060501080c0307032a0b0408011a06030f09011116030201050619061808070b04081504080315060d06030c0512030c100c05160b06010e03010e06010311061308030d06 73
    0x30030780701d4044e40728210400205590760b851941003082d81c1c4030b000c4441c0d4048480100500c01e60072500919100050030050f00c5003d106d00740040081c06080d0f1900104600001c42510001e80605a000e005101050f243d40c000e42c0020801e081c0d0108050761242c0c688016040010208810b0b00594070780400921681440c550402d0300014864008414500b03081051319003121224502e45418072407103011a0082041054034040c5c5080b00c042500e0385d15020701c0364035007c0320313088509096408205000006100b0000c3d00d03080f5035100030080c0141e480310007040450040b02d0fa0010028104030b000814421901003030000d03500d040c0c0d102d8145101c9030340c5040d541d200c1c0300043d452544c07052008903030f11411b0382d0042c00c600420386401c0f4640828007001d0f00d907000c0c0304142915200c400d182030000c40d41c2c02c04951080c04406400a00041c2d00074007010303031103140503c0098201400800348162a60f00d0350219031113000d106089095803a180da080c90313501d800c5101d10228241c5405008141c083c542c0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 836831897 1250 836830647 836830663
    0x906060e13020a020f07230d1101030b060d14060306071409010c0f021002010c0f111213050303040906050f0603090d121b0c02031c1d181306050108 65
    0x40c1c080000c0340144030034003000354442c040e01021130041c2c001d00c800d03450b0203004950050000c507402c80f00c8914180c01c10041c084040641c64800e101c4011400c000072004e00c1d901c07108403401d0800140f0101e00ca40070800c14803071180142c20892400340c06610f545a0741d13042034080c0c0f0080c2c2c111400c86da5281c106458101e01201055103040c0d0a00c1034000c40d6124030100c0e41c400c3e20032180095074140300c0d40170454080c542540e090140c0d4545200c1001f19070700c145140401074182ca4512001c440300c10f6201c0c3c42c1d04040364001e08011000504900041d0004440070060101404482d80d481c0c0e280154001071040f40100c501c500744000c81c0725100d1600209a901070f901401c01b40c000c6041e00718003650102ca0401858040c035407a0343c500310707000b04203008440744450b464451500ca18030910405003402181420a03030801441405c2c5c0041e02e03408883e20020180404400295040d00000175458140d0301b8040c003081c1c1807240801c000045007030000e12003188100820701031640c0300c1201d1500e80b400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 836833147 1250 836831897 836831899
    0x5071706040f0602030c0f0a0302121b07060e070f03050d021b10080402130612110a0b03060d080c120a180b03070513030212030405090f06030309120c190906060e 71
    0x1181d100c440c04609554021a006802c425060307162801c40001f6100c01d0300201000401300b0380c04103001ca0110010500d0561000d5055500c588041c496180030965001d1100c024002540e2044400c0a070541000310780054004030915002c51540c070325000f03959807551081c040060144840c3e13102182801c00b0401440080107200120407014418116078500f00140140e900140c09001c805d03548015214280c003410b9081c010005008031828032007241d4420096460141e010500304010801c0c01d18140c84d00034904880ca411810000d00300150240150310200c0d20501038005920010850341004140700d4102e034442c00c402d00012100c03184958218803800a06e40c00400004180c107200320000c1020504009410b4441600c1350042021034018142403015030780700103801e0015103000100070740d00112010080800e807922801181e16806492000d40c096081c03495044403001c010b100038482e81c100907200c50a4a6800002c07100701154034811041c400f40f4000020030344511601041c504504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 836834397 1250 836833147 836833163
    0x708011803030903030f0e030c07050609132c0c0a050f0a0302090601030207172206090509040305040306050a0f0b0301091a04020f0a03060c120b0f01180803070507170604 75
    0x40c651400d0b00034118241c4110101607490405101c0c0404a10410200400c45c00007180c6400c12000030380d1400c81240c00041c450242808084499561850342c1100c88aa0001c041050b5110340749a0b03140e4950030b5103a42e110030986d0039101c0e900c440040c5842da8080122040040c866403141030007014a0070b40c00040e00300d03890040500240c1013081d0140d82004041c50010b140006a86a00e00f0506006c0a81c40705040002100c0b41200b48800c2003003c80c04000e215003003013074600b0070701030700310b40d024031465006081b00c0e0f000406043c0558141d40c0110740102042c850b03490309900c00d4008100c103429a016003442d203041d035103031418148104900c060740000624441ea0080b03540c14411480204202c3e8450100c0c1480e2501e51900c882440046100d040c0203e85805d500c2e00241c65005d10f80411070fa000d180c020141c0203131790b0b00038950441e00402c2c28580c020030850801f0a000c0d550940040c002c07840300082130300800c03d0004184045882890a403968840d02d218000d840d00426a03001d41202 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 836835647 1250 836834397 836834441
    0x10030b04140c0a0b030406060e06090406090f06051806070f05041a0d020f040e010b0711040509010b040c020c09160c140c031614010e1c0c26070801 65
    0x14071010340c88003101c901c2000c41c1e071a4030345180040d00a4101350003001e110030001c801d020400132103014000140c080c0c0d8502c4c001030300d40030010a6507903900910242000c0d4460b64010184038021280c0244590441c41c203001d2850119a107203525040d000a481082c41201c0018800310301c141007040710a00c882d40c9041c5020b103001e4520301503503401c50100c46550070400c0015400b174500d100911804140c4081035468a241240d8800c03d0703041640f010b4568502002900001000705882ca250001c0840e400a029203031081101c1c01040740340816600170345400700d0200b400360001500c1d21850320882c0c80ca03041e9968001d85e0494603003585c0c200004204a060b0107400110140a0041c101890301c04031000e8003100300000f89000e8132a000140d4444103520188030350a900b40903040125400e090888403081c510020480c441030b914550b146000d1280480d0081100c006544c000920030340d00f030305170500c40c0d0921040c1d248466802d0070560f8803540400141d20078040c0159400d9505034045c00d0484 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 836836897 1250 836835647 836835653
    0x50f012303071401020f061015020c010e060f070c141003140c161a01170105040b061903050f0c030d0216051e1e19050a05060705030f160b10030b04 65
    0xf4108800900e41940580400e030790500300c0811585100f0120302c1c0c11801000d141c601c0842e50301801a10b11000c54004040e80c5480d82d802980f05000894151741ca02d81d900100c21382d40c40103014029005000082c0c200e00002c1032014004282240319045844452120401c801074040754007500080c1068500e03040091141101c280280c84190b003280c05100842501c0e5440c2d501400e0320041401c21b08188a00503c21010403091052800445200030001c6061a0321511070403030b0020070440c86075840c401038100301c8081004080086500c0300131075000b41c014006458403a4403240c61140070b8400d003c030350f0014600c006540c0c154002007081036100182404180080c030410228181549601c141c40341c00781791141040b030210030f007940742d0040c0e0640b20764040000d0840c041d801c04807a0a8008024050741d5110020f61080f504100d8100395640d4103480c01905501a008015495140103e1410f50025294845010640c0b0880c61482181d55000800044d600c0b903010141c03000042c24005000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 836838147 1250 836836897 836836919
    0x7120207050a0f1703010e040b0109050106051611030a0503030a0e03030609181c050304210906031802100c0b0c031504020c1f091e020d0206130504050f01230307 71
    0x40f00e40500c400d4480c004031056085550760082c1c1c02000e4081c0284200300601c46142c1c4018098400e01c1c5042c011940b40500080140c02180d408000d501803a0344d121082280c01c10008516801c060141e402e12174890800c55240e81040320121101340c1840072009050001208491040400400b5002b10784c441d051140408240c400d607080b014422480058551900d1040441e6280d0150740c415999141c54a00200b0349440001c20b1501d035002000181009500800c4600035104285000070f108413410350008009074103031001a400c0350000011706640c1c0d03402500c240300c150052030011080c3c0c50301001c1c3d913800c1c841120140301540c0b030302d4245546860681c00502c1501394050858040002c16986c140700c000c00701c4403404500e90344851150030840c0b80c1d021040b0034a4042c0654030085455004103c2400c0c0764440244103042c00261000c201c250341600401800c400f4004100601e0803100402d0004000e004444140d4000c8070712651140505007003845c80c1d60701801901c8050b14080c0c942071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 836839397 1250 836838147 836838173
    0x90203120d020706060f06170403080714070c080109140a0302070315023703050f0412170c180607230106032f09070c0305160203100507120207050a 65
    0x601e5800f04807002c08500140690f01c0506001d080e040703d020310700f480181ca002115049031119907105020007002c2608a495180e2203807450800c0e01c80002c0e5504540d626202c3e0100050100c008000b0105910405600c80100c90b0b202e4908030382c40703800302104295180080382c2c0080060b4059002440040d42c280c5480d4050f206c12840036082004080002e07440d00e5001c01e04030341030b96000c3c043c194030040d40c4c0a20310400403d800d0402c003c0c100010191003000c401070016040f80800641154558414001107882010080071010740b4188940303c50038549c13025411110840a0120880052405000b1140d840b58065840c1c0b5401d280f00c0c840d1000780405400c0c1c841255a00d1800001052003004903465404040d0f0149510210000c0f1442e07203400c000c0d0543d07005000c090100121543c02c402514051909130801a84505e0b400c90850003d42800c0c0000750076001c0d40d114403801e0010358105078000c21464584545080000d44100103c0c014403001400c960301c020a07072400310310203240c400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 836840647 1250 836839397 836839417
    0x20a1202310b220f06050d080f0322050d0816120b0a0f06050903060a0207080a080a090f061d030915160807050f010606030b09151f05091309020312 65
    0x210f0300c0101d00200c851007a030307180e0300036102c07925101c40452440304c601c40e03400901822135950301420f045485001c083d001d1080c00007015403001012072100c440e91070808040b142c80700146461500c541ca03013070b621040f00388061008982c01da804076549042da00c12060410301c01d03642c3c042c10800c0c510301c01409001ca2841c00781c3c02400e03400000c254808160041805480300e1344661b90b807805480149850090018021007030644140300f55800558180102c1e2030000f11481c0c0301c0c400e611200440301c020010320b0740040c007120002e169001000456040701414620746a40d1441794410124015140e204100300340d81c0c003011040d5424440c0400724044c2c90450000800c2040c00074143da1040141d40c4a41d000b40d41503030114509200ba12001d004100c0582190300d010702000340c81b10007090f400107010307210307210803c612402d19120f0307100c4201d0403100d08540f0040020341949480060700c2588807500141c000c40650944401306442c90003580581c55010f00146156000303ca08905560000c00f111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 836841897 1250 836840647 836840659
    0x13020304141b3f0f1e0c1509030304090e0f011b260109150f0302091923060307080a1a0612071d0708150103020a0c020a1202310b 57
    0x1494590803c10980b070005119100107040014024a189203044004200140681c8100780b10305000d0002090410031110207444800348074018800440e180e005001c01140c05100c0460002509441a0003420541d40c40e1001d480b01120800340081c242c4421107600022001081d00c0780c1d450500c04c04100c000c128040c1440c0012504102c0c5044032500203034495004143ca0f00d07d05860024001e0441008040b54205036a800789160f01141400d00c001b001c030300c0d1001c2040c01080702c84d8500c0d0012a001c400c3c800c2c4410084484108076080303590250b80442c0a44034074038004c0303140d500000740b035401140c0100b0346c8100100908040219000c00070000ca030401e00c010145c100d03910f0100440005066480141340c940d40020003103a4215500610b520100031726601809032280654420b000c00d002c0078a00583d55441806069a205c540c1c2c0b60000e40145a401e0000b0342450380c800100b100910803244141000700d60b040c140280401c4103500c00d216030003003844083e4600942d0103d500c1303a4016020b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 836843147 1250 836841897 836841979
    0x40212040209150d0804240e062104030804350a090503060a0603030e0913030c0201020c060c0a060b1f0c0312020315090a06150e13020304141b 63
    0x41444c00641d440c040759030500105050100342c0707000c440020000f50046c80d9040c00380144100411a40c02c00c5000b601614001601181c14100200c0d00c1c413200d169007404c54001d05251070300511000c1c040307409440b014103031601d0388070b1a01c1c030450004a80341103001c484402140319801d44403580c0302d0b40010003403103c501e4001665440034400680300340c9548000080c56031035030901030724000309104101d2081d00c2d07000802c0b011039601c0c0520b40d4001c1d05484c182034424841c2c80141e11303007000044010760112000c1645000d002001035100400c078451001803115220f000c0078806580c08128407001012001100d102d0041e100f4a6010b40c0036000c0c0c6840d0781c01a001980b403c1c1246c0c000d89011090842413800d044079403c084031090340140010b0380c10401f5a10b0103c034000841080009441004a18001861551341e103208441c0c07468500c0b501150340e4200351414ad0040c56030841d14001900800c003141c1c8901c0404191160a140301400c0004000000800401c1402500300d451700c55414007c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 836844397 1250 836843147 836843149
    0x5091203070b0c18041e02030a06210620030609070c0b070323041716020307060c050706050c03090103050c070507060905030709051b0c2109010e04021204020915 71
    0xa03030140030303100c0c0c0d203c01c543e00d0442003415200c0e1032400360414043c508044544001410340541040c1d83c80416400507142d44429000802614069005100e0358585414541000b800c0d080c04d2810103100325820002d01d400700c0a01650815480440700c0074200900c00181503050240c100b0368011203a140c10070840041d590703050340646064a00743c000a039580703a045214a80009515183c01c0c2c150143c5401e46440d90f034018031500071642d45803103140e0108800d541c0e00c89008883c0111540241610000c580700e810090a4641d00e410584945c800c61500140030360086003202d0468100e400607528040c1440c0041d0041d001c044d00407030039942c041000d140810801c1c840324025020725a00e8080c4213183c041094035000450304440301c1e407484c100500c080c405150b02c1546442c031814100a45030490071680314249200030200c0e2011443c83d0719555243d6450030028034290708240c07030b20710302d036800c0c075080c04224058121108044406003010602603c1d040d9030450380840701d0b440200071504804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 836845647 1250 836844397 836844413
    0x6011403070f03030306090c030e0a080a0e03060a0e070b030c041514160210030b0a030204090206090d0b0f010b040e0f060f21061f0b0904090c06081609060509120307 73
    0xf074400c0e80040d64030b01c0c090004590602035a01c010060386000c0c80b281c41001ca9140d00d403038980d0340041582a000462131042c070f000e2145034810f10001016291249400c40c10340014100300015024207018604001c1030017031911003540d0281d18005c4505e42040d0414419a08400d48400742000b440246800d9600d9031030f400c80104440c0848070900b011414407031052040c030350100c2500c90700303060800036840d4094580e10751a81c11071f50121400701d00c00c82039002241c007912417032032030f250070018041c0c0d80c0003881b00300001c503400356010b04030036041d0780e90326020001e9074000c50082104000d8500041566000d01c00012500403000400300038036503081e5030010742e215101c462620350b040034003083d010f030748082400015404808290711541c03100c414406142104080e00410740382c090046840011503e840e4495040564012494800d0644900c406004494204d40d0807800c4207100da02e046005100d850380c201100e44d02c2e1240d0b41014008400c010244518130020000d81c40107001800101d2000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 836846897 1250 836845647 836845649
    0x4230604060f080a0605131a1804030e09040201090605220618090b09040b09010e100615030603080405040c0302120c0703110607092112020f0f06010806011403070f 72
    0x158803605050009002c01070b00a060090640c400107145c00300401168842d10581c01003203c000400040001c1640003150100c101c4040c580d821480741ca1061a020000c41c0c0554042c1e4040d40714081c015801c0750420050800445000340062070b603070002c00c4070901030000380031824900900e0680c5021040360341d10b04000c2d1703940700c2c00010300400b03885040b1507880e005442c060042603d091010502d4080030032540c29001c2c0c4002c160040f0390001403003c40d001c0d4403000441031100d003a1164038903454003c40140c1950b00900d940d450f06856101c80b59030007032050400b2aa40218010304042c0360504000017060030740021000d1540070007008000c07003c5030131040e120b08941072001340c0b200a5418024000300c1c0b400180e42d82540020301b032024640d00210312034111f40f81c0301301cbc210254a2451042d0304e481590f2500030141860b004000f40076a8022820308200c400c0101140c8503c3e4080c06810b5a800c801e00c100c0425403c8000184141d001810034803c0d1f40c00c1c082c1c00c80b00e81c1a540d012491600d00b207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 836848147 1250 836846897 836846909
    0x2d061724181c0f020313052b050606100302030601091a0f0706020c0f03040e01271b0e0d02010c080c070f080f01150308090f0301111b07060801080304230604 69
    0x800700300b8141d2508190f01010a1031076100641c04d00b804201da032042c4138414044c3c2da01c9840d01c1c4066070b080030300c4400c1340900200c050345869140b4042d40350442e9a213205440780344c0301700c0b08007070700c211304611070300c01e0701d200c0e800582d00c015450303141002503080010b80d13001d048400d5400300100807d1784006c07001048070600c0340800507136440c1c0c5048200d090004032090211aa00100410491403440c01300c594195505100808566407400d01e0885050401c890a075500305d0500d04503000302003600d00115081043e0b0f80702c40280410781f00800041c1400c141d402408204040d17a0038010480750b41c047d0400b100080e0480340681d45410003402c0e540c0c1c1980c0080e0310350344004140c2002080c01e010b412003000032100d000c4816400c60340c540d0780c1c500a40105a014640d48103d4a0040d5000d421503c05146103840d81035550040c102d0100d070f5040115044006480303000000100c1910410f4142d040301c00b500003440c2407030700b441d1000c0d0b86e0300308170310100248040c01401074100350340e41402800140f80f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 836849397 1250 836848147 836848183
    0x50112200a0b0c0c1e0d080c160303050703020c0603100e06040b120f100207030905010e13050a020403020a050307030305120403020c040515010329042d06172418 71
    0xd1042003000511a050916078281c0354083e00c5c0790107031070300321282c10444e601807215911040c2809415151050b03280540b100071900007400814150401d0041607858080c0c0c0c00d80748000c5003d42031066901c002c0c0d44c8202c405412030300070003000114850054110b403005001040004011000400e24690704815411541100303902140300f0b034041060702600d0001e21025400c020f070988002e00f4410b10b52003080e051101d41e08000a003565030941d81041340341d814a0402460800500301c030000c1d0041e00003240605540740003c1002e240c000380110441c2da140c0c0d2000d141c82440e917400d15000f80013510840643c85034a02d032010710703659400f0740c0d842030000c5481401c4401842000409486144187d400c002c004428401203080c0101c0c1603d20220040d20042040d100c1c120900c080c0c200c0c150500e0040ac000ae4089420b501029003205007100e40001c044150421480010790702c80d043c0c03148269401d52880b1016012000c481c6080d40d2060258505180d028001c800c01800d1204200300094021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 836850647 1250 836849397 836849413
    0x10f05121609022820150f090c01020f07091508010504050309010e0f1807050f0f0307030b0a0e040f06020405040e0606090a0c08060d0c05030d03090303050112200a0b0c 74
    0x8401c0100500707030303041412401c440d404000403010344aa071400700c8504010360300ba420003040017001c0040800d200d05210400303440d40f41041d0481c2c3c51002c01e0fa103140c0c01d402069280101507100042c0d44023014059806000c1080c5083d805000911691070404011550000002580309007842039030300c9907000da40510381c2c80e461000014001a0440201445003409001c6d041590325084a4121006003a0001400c103840744801503d09000310070216451a10000340c004000c90300101840c0034184c2501c0c10310011408504211180c40103014405070703803010301c00090104034007403280180c01e80240f4005140c02d40305c4000c107081c4e80981100c1403d55014206000182c01c1c2000c110303610100f0708808202c00518408020040c0c0d9015000b51320410915000c401404001d0b94404010071008003118601c0c180c54001401515070076100b900402d03d49000080c1c80b48604407081a659404080081c031103009159840d202d810703110009400c402c5603440812203401e00741c0103100e100450f1004200700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 836851897 1250 836850647 836850667
    0x801050703050c040b0304260d06030c0509040816030e1008041406060f0910091d060901060e04410f0f15070c240b0108010f0512160902 60
    0x502c50180c214042070700d00704810820a401501030300d4000794012550b5604039500c0020070010780d9003030b602451003407002850002d200d9090b800682100c0c0b294003aa800360b0380d20800c2040a5a003114040c10b0074404000201c1d0b02d4150805605060348681800110103513020049441003148401c03800100b10300d4404d21050040810907a55948844801000e0a11784040425684500452558060503074000891001641d1030b00c8034000e4000980b0410808040c050b895140c0046010504030500448000c120b40400600605040d11180c508507001e6441d10758610209202c01d01410504040100d0344c424001100c1040440c2032818000c3c15428565042116081404914450302c656101c142c40c00345c240710115540d848440d41c2e5800144a40c1d036008141c902202030368008204280301c821068001a0b000e800b9842c48280c40303000c0000f01c03070486c01540c41c00e00a008003058010005810000c524009001960b00501c54041c1c6050780f10050064030f08040941200d40301980106d80d503c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 836853147 1250 836851897 836851901
    0x17060603010c050901031a04090f020915030c060a03021b0c01021002042108160308071205070c0b150618010e0a062111070c1e050a0e060103150801050703 68
    0x105104400802040c0c802d100064820311404c11910305154031400400207030404c0450680f0754940161003030000c02000c3c9441c0a040c181d03100224461180f90340401c0911481d641c00421600b405401401c0b4112040100241350f0402c0d40488105502000101003d060750a254001905a10010841c000c1100c002905106554080d40748103031041c0010880c2480f840c0e03070b45400840858008400d000b050070500e1039803180c01c00d1884110191220740c8100350340302c101c0a124084c3c1d56680782030707400d01d4030407030b003e0b12800d0710b032103000030884010500030402011101d5001003070310000d00070f000c8106010030008d4100d10014100d5001e40c0c031030a44503503000f030808545541c003115604041410248084c0011101103000c0c44020008034440c403800d40654032030011489982c00481c1c0326003203481c100a01e44c0781d6001c1c110309c84080000e843d1a1422281140c802e568004110501d41800c0498001209000402c03c40c1090b40ba180c40000709039a41080c1405040b04800100d002c0c6410040581 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 836854397 1250 836853147 836853151
    0xf13080c011a28050f010e060c161409070f09090c0203070b01060503060123090a0e0a0605010207060e04090f1205030414030405130c0c061113090515101101061706 72
    0x20b000b9000f1200106a90012141c0c50165402280e05103415020040101c8403c4141000740c6c1e0040c0380024004402240010b84c0401c1c412070740c803500c05d440c1e1a00201c84000a08041c2c1c590442a580f0100780840d0080100083c01040c130324020491541d07914903041500c5040c5101000f5800003d000c0f0107006041003498003400460600d60b01c0e600780b41c40000d0160020003041441c50300b81200c1e5145040e413110440d09a46002040011420f8407a86618400002514480c1000c1d00d17090300000c0701d50010650808546c070f1030702c4110040c3c042c0070600000c0c01c180c0c541280c031011450300e890002400600d0003883c504030345d0350390f90300d901c0c0501e4034030529202000865884d91040c03000300b0040e40c5041c5040300d19411404003107031482001c2401d60b04800124801003400e800e0840000c9400c400c10080e0588c0b2003000748006480d0740d02c07003a810407606c00750380e88900200031080e0391466080c5140c003141001c62600e0042d070030401e44540d440c01c4070342d00e401c4405484520982507411086c20400d039a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 836855647 1250 836854397 836854429
    0x1116030e090c0403410a12050c10052e031e050d080f0103080a02100501030302030d1512060b03100906050403081e041124031e0f13080c011a 62
    0x290484030902c400c14a210750041781a071340d17030354200f240e900c00c1d450611420100c150301103d840960700000c040580243c00c40c3d40da1586030f1080d040946010311040c001d660086000111209100b0681042c43e850f50150842c601c60100d90900c0000000301408054407c0401d56102002001d5040c80e00500781088039201d4010441c0c01c5052010b22003100d900e5504403079100401907a201c40303a0a041e42061b8503940702048103403400c2e00000905401000030007c110b00c03080708001561f4031101c3c00e080d0b690343d40500e00c92207003a48030420024465a0008107401d0004003100c0a87c640882640207950016400b11401519202030004142d08440303480d41010032026020888140c84410740f1925100400c0078200010a100d2403c140e102c00035007205c0650401c601344130b84031041e81010000e40c001d13500c0d2550903011040000101103800364050107510380c4800d829107511900840001e0403a01c3c5000c0d1068042000702d503401c00b000348030f42c640b1010420100010214484108401900450822 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 836856897 1250 836855647 836855693
    0x3040c0e0c1c0e010e060a0e0d020601090b030a150b150f0a180803040626070507080304020a05130902010305091903140d02070c17011116030e090c0403 67
    0x8808404101400e0719100800b0202600400101d41c4020740503046541c060102940780804140e50f002010a41c42d204180c03900d02840041103034510196180c1c008044200160050301c010302601c006074010040c4241d00400311550a201e41d200c2000002000d840800010b82d9800c03601145c2c1800c200c407020042076105042d0411803078101032851840f03010440010840705d0030310080070f107a140c070300c500103081100d080301c0d212500c078800517160720213540d600910300e1075007031900c0d07207070000c80799102d100c0c04039070b9101410b0182a658081050300054800c99210555071008551901e0f265048054134003500da0203d0100010300014044a4000d4108001c50300700701c0a40328212140682101c6150341850041c4090400c02038102c8203000305860403046500000d000c0040c8148500c1d12000e0b60401d00c1ca88601000e60701c440303800c80d4114603440302c402c4001c0c0104c0c40003103852a6224550380c000d090240106828000180c0ca050045a4a0f1403a13800840c05200f0b1144070000142c0e805004200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 836858147 1250 836856897 836856901
    0x301031109060a0306020d11043309030210050405060a0e12070302220605030102120603071e090b060904140702190203030306060a0216030f11010804031202220b03040c0e 75
    0x4146103e40c00e000207400c0350b03000100b4004260107680310903030107c00a2099501c031500e64085460070a000c500300c900004d400300064500d03640f5460040c81c01030864945803452440c0d42d080c0b20b20038035244100800d0160a0200042c10744407207005200803001640c8150101e0491070401c2405681700f482d400060744030403001e00041e110030035860b10a86034860031001c221906007030f4201420450700100c0d09540086078100065800062050046000721309442005803110740020190440c600501d10491200303004020b03000f038a40c000c458001002c0c0c42c00746454040400308096540d0403607039100058042d000c110b4803a5040c0b01e948442550095081c3c00080380c0e07000207a5a000c041c001d02c3c40b5040000d0180f2a0078001c001c0092030740804200c814403613550b8100007080c50211a001d81d1540e40035102040d8030340c8201080c1d8840c0e0b80c96107aa494048600d84182e00940284200266004400c10075a030084400390000c4010f01c244d0b078105d0760302e01c0c0914000701c5d00846580480812101001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 836859397 1250 836858147 836858149
    0xc190f4a010609052b240f0509010c020d0804110127031b05010e090c210f060108190c09081f1113090203130602030a0203250c08130e0c030103110906 66
    0x82449031098006a40c4180d840003410a00182c010b00306031a04518600501300b4500c1c00340e6000180b04040c9c0100800420b02608416030303e58984040d000009500000000c0024052101001c440141032620400f001c2c804d0956280c440b8000082c01000350040310100b04009000b8020700281c2e201103282c882251509001a01242e1014a218450f0b094000050f840e980104141c44000420b048403040e0081c00780004952840c059403840c500440da600011410750003400a00e0041c0c103003a81d60078111070912041d8006007002c400b81010031402d2000040c3e400c034100b008601f10589040b0b8040a40a00c2c1e0000c4112600044070350b12104044c80b40d03040054100600d038084070303041000583d403913031541381c14003000c289070340c00510461001c000d04c1030800c450703400f0714132684075400001c00141b48108040c500d802c0402080f800110804400d41c0042d0032800070785458035101d50751101c601c0d129800100c203807004442a1b00c00140200042060190110041c401f0f648252130740100b83c03e20034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 836860647 1250 836859397 836859469
    0x51c02362134080c090402060d06050310060806010806060a180e010c0e040b010e0a05010f110a03020d0807050406021e0c190f4a01060905 61
    0x1d8080142240d601424060094144510b401800034202c102000c1445031801d8000030390315001c1d5580701000c440b0041800740001492480b0280c004101c41d0040d1380316420000b1503401040007412107501c0b0343d00000c980d00d00300400c4410526610003c18810300f000080c41c07408a05034007107981a44000240301040d1640d80c4114155420000c00071840304a140e04103010f44004e02e1034400342d620f40840c100c041640302010b040840c0c0200c4013449805c0f0700500450b202c1c100090340c40e0380000d80b00b000304650341c02020f00403070400c024104002180c80c0841075605141140d841940581c1064600710a0f11b5030140650781d02407210b040c03132401e06081030b40003560b072040b000150401c003031156040b65030840100011050780c44002c01110880c81e4100a03110102410311513070740b0210f9600400300d0a0030000111510a114041028a548078004c0355500d0303140035410002450313985202d200c4241c0400c0d0b0310040c06443c25840303c0034014900000c1c4085100c40701d2103941c980500441d40c0c52005011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 836861897 1250 836860647 836860669
    0x1814160308090609031e061608060a0b1303060203010308090306130b0103030c03091511010f2912100507080609041a1015090320030607051c0236 64
    0x1e80743d0a4a0300316040209207800f030b61780c440c0910604018001000a40009410352041820584c181895080000103a40c1d0380c8080d2a00c0c0d45c09604000306002c002c08000140400b90801c0071303207540c0300d542c130f886100413680203070415243c0c4000001d040d80035040401880c1d4021202000410200300c00d0b480e244c001040600000f0200803844201405241c452640b02e40600460601c0d44d01c48094014007a2441141c2c16540d030f199400c0c5010002c080c90700b8414480211202d40d841c0e0000411208090b1800484120050f8440b242002403040d0200030450201c2e881440103002905081038003001d025070800a090780d106491010400c00003a40a1070120494014902809140d8071111490f0342d04010310382042405041d80305640d80215405010704c1c003103a00a8040d066a001301d20300045182444000d00d07501076002d50b02160b5164840c0c0c00410100c2060325200e16440d2030103500c001680c5c040d01000407064020a0315070700724424101260142036102c03000c282412041d10100c0c441c0c1d110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 836863147 1250 836861897 836861899
    0x70203070b0114060405092d09070b0904020d0207050601062d050c0f060901091b06051209010204050604030c1403010c020d030c091d040b071103030604020c01181416030809 76
    0x5003842c14003c0d6200c01081d20301030701d001020301006140000d410107a080e100d891085021207100b0f0001184031150312024041c40380c000103071442a0038041f001c0540d611480b4a1500142d0821881000b1a8075101400c001c510a0011700034079450680010001c0611140642c101581c0240c5042a0507403061552000c81c62820916103402c041840d4904001e910150000c150144400300728403003006510602009120303844050303103558543c04c00c14020649000b6078020540c00c00c00c0c00010a22000600d6104400c400054a4503407a0400300f00b03950040c0d4401c03103011080030310a208040040e402100640c10aa008020301000082e000b5600ea5280306040141a80c176042001c68502c14010080034260794000d41802c0f141041006025000442e001c1d0303000f031500c00104400c04c3c801c81501e010f00b983d200046065440300810080203522088442000350b42e9800080c6403520b00c9d404201c5014000c181c140d6980200d60406403d00944003581c0710708181810302400004d01e02c4054884800c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 836864397 1250 836863147 836863169
    0x70f081e041104090c0807080c0d0311031318050115021f0b04020310031a010e0f10031505160504050315092e1506050316020319030b0306070203070b01 67
    0xa690500b003210100103044240c120b41441880e0701480180c13611403040b18104030171195040c1e40d4840b01ca890b060380d180300d01e901404909041020900c01c0e440f83d003401d100c07a02aa460031508a200070994005580800415414005010043e150900c14180102400038042004500c100d200a446003100032801441140c480500403c092280d4440d15a500c1b02a000b1503480c10080c40103801a4010b00c0201d46881e4000c1c040c0e007901800111171412189000304055207500c0e40900c400368503000034030314420000880b0b80000460140174a00800b88000080040d05091503031701c3d800303030090144003c001d0000401042046490000c1c2001080445940261081e20b403829010706100d03a040d1a80d070308221403801501c81c0c045050002190300319026042042a140e01642150b030281c601c10400880e5060001844006e444c965120843c03007544103691400000d40340e0309800000b01d032103003000039a542101844500341000700c0794020400340000c0d401e200c025031f035100c2c4a5005000c0c1500840f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 836865647 1250 836864397 836864401
    0x50105090c1c05100510080604060b0c0601090b030a080a0c0506060405010b0d09020616031d0f0105030403050a0c0b0c0c0f07080a08070c0b0f0904150513090c03140303070f081e 78
    0x1800304c1c51003030094007000b0400c0781c5140311400e00400d26407050710001c5c0710b04c2c50090f0009410f02c900c0c044503080a02c0001a00840c1c0c43d00c86070400030003000b003000d134050040c070b0301d2200041c02500c001c1c6001d010a480c0c8650300349050a1861a04000904280c041c5182030010f0240c8142c00058030b1000d8410000411500500d2000c181c0b1405030406401841e403101d100101015041001807482102d8203440c00c15941a0004002c0c0302c0f9004001240410b508102040220b8450401811240320707506108080303a40d1a900c00003486400c4910391072000010840b010300c5241402200b001c41058401428050300b84500c490b180e12814900814036032000400c0d40401610b1403a0000408c551404542c54480302c031072405d5140d01c0340c040c4521851502024181c0e403441407500e581a500c02800d80c122941c00c0036100d4009050481d825110804a6030001001810680f007032003c0e0f0f581200503513240d0500e01d002414540c488038842c81806405000c018000540d206c00d141c6d04c4402d011305000319 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 836866897 1250 836865647 836865661
    0x2030c3a1107020d05061909020a0509070516031e0c11010f1416210c0b0a0f050411010219260d0207050a170a0527030a0303050105090c1c05 62
    0x648038100c80250005113031403090050150200d0003503c5144030000d511500714242da0040c0071642001ca0003940180c400109000c2030400d505c08582c4a00c4506042d403030f12701c07501540952080d2903501200000c3c01102914181c5650509400800c001400e280c501e40c0c0035565000c10140b100202c1d00c0c10000c240c00d0b0401d07414407500340c4403466440c00342c10755561203081d84600c194078218041a83c8003040c0000940241ca00140301d10345d21203240d6030b0b80d0507440c1c0c0da0b514019030303800c040c2c40505241e4039140ba419000d09180304085c001d40c41511a940c91482c03400c0060300300b490005c00c0445070b82d10441d42d80040b680c69000380809485c115079440e4100340010031103003913018141808094910104400f0100940042d078031003c68000d201d1a0010280300b08500c000c0c2c450b4501e13000003d00e0a008200c58682104203090041c41c5c500304020b8101c5038200420710300381e001c00060f00003136100d0004102c94106020720580154120740054900307520b14a54154150726800c110120a580790300007071803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 836868147 1250 836866897 836866931
    0x203041b03050a03090506040b19111902041a03030d02070c17060f0a05150d02030a1b0f0f030b0f06040b060c01020d06080a0507052202030c3a 63
    0x3412609066542916424900da4030005108100d002c102590404101860711409031000c40740200e0a803468502600c0d101e00390304540401e040180414160036494545c81880000695007800e025103403000400d004100544080b0540300e1f08080340034010420070f0320040125620400701250140c0d460999192a65248200d039024040c0070341c40400c810881c03400421114081c100b440a07580c240e03105d0f04081400c0310701c10341e000841c40002e00b070b020044d41840088850742e140010305070342e1155415210180120290103003400203880c6d0803824001c0407014035010b80544500030105c00c1d03141c00d6540c0c641080c4c5000d025199030a09010002324155120b80103000d83d00700141502c0c0e12038070944803840c084d400424441d454030782413110105104d0741c0010300810b01508040101921483c1c0300900181c56000640e940901031400da415081411900056010b8141024403990b180c0c10300000c568a030641801d0f50010340f0311201c40b041001007031041c0a1803111036103c000b58001200302c401c90 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 836869397 1250 836868147 836868173
    0x124051f05210109050601020f01050106230d020d0c020d0e06030c0913060902130e090607050a140304051b0f0f12010b090c0d0513030f120b060c0d090f18020304 71
    0x350b404000701d9054102d801c00c50180c2402c1e0200e880301005d004030542665400d001d084002104030407840e1154035441c0104103843c00c1c80500b1403030903100d12000010b990007a0b0601c00550f8481c0c00a1564541c1042181245101c91a04490400c56500000c255201c06803070480200001f18500b4000c2e510752107030340c0355085141c104108150340c03a0000c501940000001c0b00d000d107a564400039403515040b00861003014110007030b200319664804207540c1a041580d88208120000c118003168013105070003140614002d000400c541c40c0c998408920380703041844000d001c1d14045c41c0040c40798942c90b40d031402c120400c55121322080c0c444801c00b401440981c0711254000d030040140a5000d20007001802c0003820300005004903034030424182c0300c5198030380004000a0280d50103090491140007040b0303902035450008070b03007014510000380700d6412002c0e440155401480e83c0e17903c4190010441e40003003140c0d59031454502d1402d41c8818003401d0600600451603000070000c0d081000c110513a003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 836870503 1106 836869397 836869447
    0x11220e0d02120c0c03060403021609020c0a020d02150a0306050f061e0a090f030b070306050f030c0922050f0f0105060a05010c0309080124051f05 64
    0x30b0281d80705888103800c44c0101a0300f4682c40d5424003005000b00e0007030740107260b00139030b00c03240482041269000b804d202d0320401c141e0142c1180890ba0103090390b0100c5602c01c1481c243d0000c01c0b01c9808c2042d981c032106000182c030401480c3c05622030400d881007500c1c0c141d1089503c0b024042c03184502d5280001d030013121280d0904a5203100c000700402e1280d454940c080c150782d0415031030014469082128021107602c01c00100d07a51521400d8000c100480d0070400d150440004241c80304d07030319955103000d8400d15001400808110100045d03c6402d2010340c41140c4841c2405910740d80500c100145c00e0089180d0350940700c0b4140101030207944c00800200d041da141c45c0054811954442085003409425100010003c07821b21460a03018450789a841003402c6141800c0c4d205451030300082c2c4a600a2101a2081104014618401302c0d0f01d081142e0396020684a01c640200050019 = true := by decide +kernel

theorem cover : BRFrame.Cov 836690647 836870503 := by
  have h0 := BRFrame.cov_init 836690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 836690647 ≤ n) (h2 : n < 836870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
