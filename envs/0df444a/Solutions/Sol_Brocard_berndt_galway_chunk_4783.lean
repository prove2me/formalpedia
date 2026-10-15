-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4783
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:57.74599+00:00
-- url     : https://prove2.me/submissions/ba5bdd8b-8ca3-4083-b666-3516db35e498

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860071942 ≤ n < 860251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860073192 1250 860071942 860071951
    0x150305030f1c05010e090d2a0812010b090f04020301080309060c03040f0f091112010312140f0304050609030c0c0108061c050604060b0f0604050f0d0f0c0303020601060512 75
    0x403040059021141c50001221180c040d030020010001585e5850205c084c0900655002d1114000c801c030fa01c080743d124103146206041c09580c40d504000e1099403243d0300c0c500403402180e190205020501a150003884072078020014401c9140d5503034006030401c401750340342c02000f51080b41f0600052000c4640001a900d910200b55102a0b640310088c03921072441c0a283c0c01106c82c01c60144010407107407000c200403002c5900318001448020349405c4005918080d42406c00f0680c2213030801000452000303e81c08070403001c0340c1800c803001400e100c51100103078410001c0c0d85422070000207000801004012b0a98003665640156040c040d600101c81d4480742814122410020344001149103652050140d03202c3c02e60b0b40407104a46950b80c589a5180d1748111402d48196141520400807410581d8006244210081841e13140600700f40801c90100181d15802d82c0002c200c1c01824005074688000100c4a4042d00122209500e5454002d1070004c050700038404120041c4280c5202c18030300000260407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860074442 1250 860073192 860073217
    0x32010f0f06121a0a0b1806090f090c0d0c0201021c060821040f140a0e06061c14010815010506070803010e0925050102120313121e110115030503 63
    0x414030044a108101c0f8405804030740d000e07100c01d10004002c09184000d1103c24290101000c0300340320b00d02006924001e5002c01500a40f03100f5010442c2d00e801d1401c1640302c031078860400d00300000d5102480803207044584400c0542c0d800103070b03a10b660300c04145004820110880c01d01c0070506003c085911801040344020303807030901c2d0b000e043d01106440250303005071100c1196400266a5036140e40030141059183d1401003541d01c0d030200c0d90810111049110b114068121458040000800c1d02840000b8074000c3c689030b0366140385c2c0a0811b00103200d5008194450041907001c941545002d0580410780c4114840c0e4001c012040000c3c05000031350341100c218000e9283c480c0e5810400d2400d10080d111150003080200e0368500c100a9000084416a0802c0e401c54405c0043c0012a10441c4001c6d142840f242116800d100001000c4075180e441d00b05d26032600c1000d00403800c842d0b20581ea4100c00c50b40105107030641c5000e02000900c40c500c140d540b5880084a15491500c5058507481000a074010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860075692 1250 860074442 860074451
    0x6060a260703060906020a08061008071107081501030201140313290406060f230d020307080a08120606480105010e0c030f01050432010f0f0612 63
    0xd80c14080c06904000c40d0070040c14030407400d01e850001e000303502440070b840101d110721000c2000b5080140b00d08407514200e88a043d8103403030341e80741a0f03881e8200b1000400ca41c0b02c1c2d00d8011a03412001e101902000a82031070700005541544005449800701480c03070f46592000f40204036108032464903107103c0780c1c0c0150351080c451446045040e0742d00a44007145040143c0c06041c0005c10030103034402e2080310301a480e0411013544071210340c3c450a0100180c1d0000031912101a0090303d042200240e040b0300c01400c0f25400ba5840103402d007000300c0c03540c0942d200b120100f0268840140000195407101084548500c2c20006003c122100e01001d46000700e403600c9180d404492a5000241180301e6400c0a43c03007581841403041640038041c01d01440c040e020b02e80340421070000d10501982c1c080e25405445600d180c0c00d1406000c002d00e103070303160130b80d0440003c1c0004000c8006000e602419414580031240a581050100c01d8503070f074954001d000300000c0a10812016900c8442081c3c80481da010105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860076942 1250 860075692 860075759
    0xa0806010c151802280302040f0b1804020f091909110607210923010207030204090f1106030630010c0c0b100510030b03100e0a030206060a 61
    0x140e004642c1000c04000740380c00703140c0f07946101151105040d03d10880d6400c40c080b48a101c003c814248480714861407070031400c402d00044c905504202c64409449000240111001c4c0001d40a0804202c45803c1803020f0300a0009500b00003146243d002e5050300c0c00e0415040040c401c0280010561051001580c1d0b5002e09007002030b020b17282252201e00906e0f10b529000030381040b6494140c0741090401440300d8980d07807000e643c0101640000c843d020f15802e2140c000000910108a0f0500e00250442c025104040010780d603501c2071001c01405540305a9003240585400105605d81440303080c03040d5010300407c03891707030344100c40c0800008500200c681c0d40c0d161a0301c04031a030090f82412109550800e048000403da10408036003109000b942c50601c96211140227020080f505c1c007a540d000b2031002104420140250081c0f08032075070150031640c4001a000d40f1504450811000b885c00d50040310703041c0e0074150704020858102404465100b6858030300030040380d0481d210041c642c41c0030090002807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860078192 1250 860076942 860076953
    0xf0d06020313020a0b13080105010b032701060b121e07110109170703080c0f0a0323040804050324010e070c17040e011202010e061c090b06040e030a0806010c 69
    0x602e00c0c00c0e40903000140391030301c40c10701440715082075860360281d000050b80095100014024181251701000d81249075466036100704018002c0c8020f0b402c0011611005c00781e64070700910840006000407681030703450311400788440e400d010024041c3d01002807515401c006420005032448e07040105814803000440c8804d1142d4058a401800a040b00f00c0520903201118107580040c07401c984295500d034107030354509580b04e00034050120401a100360601c0031600917402540720031652500c000c0000c110302c2042c8005900c54808031000c44851001190030400b600b0104050b10030325140707d034204c03120721040305446181c49052040400d41040100483c040c50b00421012010b190403011174400704070010b038070a80c01e0b8014400c0100740d04200c000000c0d03090600d90102e100e140e05035220024100f0410800c0000d4000c0300c1c04102c9008501e42400300400680700741074402c1d2103100d4a01492a015040204a0703030010360081403600100510803106900a036070390303403200003420616003030512400c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860079442 1250 860078192 860078221
    0x13120308181f0b010207080601030b0406020327150603010b280b07030201090201020d2d05130609290a03050a0b0402030405060412050c0c0607050a0b04080d05060f0d060203 76
    0x340d8040c1d000b5002d042c501c1240e0b5004280005020b0f002c0303034513641e560103216550315001d1201400d840d0f1010081800124260000d54000d04007171240070f03000c11000e00064644090729150300d034651001100521005030207038125400f61040b0000c000d942c01e5100410800c440d088604a2030b60b41031400b802ca043c04644222019154101c01d0075240c1d880740c0b41c0640200340440c000c0e805449035001000207540300742c0c42d600720f4210b000800c4002d2169035003500101600802107806004040c40345030003501c000c43c1e86800800b1305580300910207140607800035180e00b40340c0e10020304550340040c1920082907001191401e004500d0000382642e5180d070f1080050255552031580280000700303000c144100003820b14002c0d0b008460607139240141600a0700c25205255201e4441e0f00b00c4003a002d0285800b901900195000340305403441c2d0500f0303035607000155100700da0480311a00040b80580a91500344505a4424016204a6050030551002868060b03503680d00600070754001000907442c03d000e001c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860080692 1250 860079442 860079463
    0x622020c0106030c0828031d03030d0c090803030c040b03040609081602121b040c09150906081012080f160b06192d03120201021312030818 61
    0xc00005850b031810b1130031000c0c3c41c41441c54034406e401c016000c3e60700000d000107116907608010511320800f42d500382c03101070714001ca071640c0d840814007545490302c06000402459070080b10008040c41004009003132603642d41c010140550041c41004011a0319004441c00d0303990544165489030351310f141aa02802a50070010b1400001141140a0003061219005030368401c8800241e40710618164990303a803000380307aa021564149661007072604081d8400090500f261070181c4480c0d0700c48150142481100c54814001051200208900e0303a00208d15a080900b074031706502c13403602d8001c0c0c50900340711891028002140004804009040c580c0c121050174041c0684240b60107120f00700320580c0305084500c02d000c0c0d001801c0226246d003089140500b610040c111180c0a02c40041f0b602c0c5488200d8402200c0314a03054001101185808507014140741803a400503a4501465000d24007400881d0b00048000001c10380c0200041e402131a140d6104442140c4074584d0404099460b180045052 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860081942 1250 860080692 860080717
    0x41b1b110121020c0a020a0b0703090302040b01031d0c0a0503030f040306020a09120c0305011802060d0203060402211609080c2206030f14190b0603280204060b03062202 74
    0xd04c00340d11803004140385044038021915000c680ea600e10484145218801c40203001840184040c030041c9071a83c00408400418075000490440d050b0f149400e9651340248140154044c4d4802011450460700b0707400035080c01da0246080c49951010001140214040100495008600642c0081c81001c1040040620b4a01849406540e0814184807003050105450319400c0140008504c0d444801070000e0650203882e85240954540d6a64000d410141c0081d074019001c1206403000c500040303140c0c04104454543c0c040604207649025001400301c1c440c00d09104820004103c0890040b030000410901903e210718071603542d8a0f0450700203210034070840e10038a49000131081c003420b4a6484003481c4034014010301e19003002045999440341403261413814080001c1c4000180011038643c0c1c00501c050700701c404100c440c003070301c041c00440c1c0044600c2500048140501303501c0d090007031100904411840e0361075800d01c08041140d0700b102c1c5800010038070200001c03003006c41855045600e1110001e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860083192 1250 860081942 860081947
    0xb01030c0c26030c07031205070e0d0218041a0f040819090312020304080601170601030f03090e13020103050a090c150519050a021c0e041a041b1b11012102 68
    0x50944e031409821508042c3c00184d88030b482c900086415224441c003a1850744c66003640c01c40032104004000b031315074030304a800041c1d000941110721140c0114601a03440303040c00c440400210207080c607440000402c281c4161105001f40310201c0d0f28082100e81c82c2110054003c041d203080c030710603240c40b159079000415181c82120041407156000c4050000e4980780307030075075007a030b40c0c0d50558409007042e000e9802c0290708080c0c01040010409040680381c0744c8641080f00826560300903143c2c44440885542816141000750f990443d03134188200c690180303c541c401c01503050b42d502c80b060740141e54011000c41c100920311103070805001d02c00351241c140c01d4000b00c160b2482031000c0288580c00c14504400940b14410059002e0800c00c008108025090f5590b003400000400412000c0c204070610580320044942601846441e240030f101001c0000031078140074103152460040c24295240d51022324403d81003629000144c0340c04580350100800d1a0480702d0061280c1d94402c0c000d510a400402103100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860084442 1250 860083192 860083201
    0x3020f01030b0d06020c070519061818050709291c02030a09020f0a0b190c0b070206061207030206040513020c070303020708070905061f051c0f0b01030c0c2603 70
    0x21900201489541c4a040e87c1039280e4890a100f1801c0741418a11344400c14100240612442005007040c21b00307111404201d030355070340c0328100000403e0301c40c4410038039116401c00078a6600062104020090f0f10000e111281122180d04180c101c0e8039020748160400184202e0713001d04003900341e0000e40280d0130455480c200b0080c41d000a00d00100200d01074100c1c4051800e00740f52411240c2d04a400d0003030100c0c54070320040c43c241c526000c841024824050342c0c1c24140040fa03000c003000d40c07180700c0c26001001c007802d11500700415418441d008522a40c010707076040c00180c96860542d01256802e881b901402401a107894020f40140840d145040c826480d000091550004880044642d450165070500d81c070b802ca40410758100b107501e15000003810104046004020f40c0341d54622803d490003a003801002d60500510048280e50103544c00c5d02d55440650300f640d540304042c4c02100074241000f880d07482031301c0034080140c2c9000141c001c0e013244400300c100403000900c00280942c0c008003035680b8540b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860085692 1250 860084442 860084453
    0x30807060b031f0b09070804030c1205070b0403030209030705030313060e2b030806010201051e060102070f0f060e090f010b18041d0607020f121b0d020c01180f03020f01030b0d 77
    0xc04d9404503c42c40000021466640c0103c0340c650140350503688058088034140c90b1000074020040c10441005810400a008500c08202c0c45000314403030381e00135a4803d540c5081614144440c0c000522039001000091680e01004a032030f41260f00034102490a240c3e4003001440014403500c0c240d05010220400c1c00d2100720a515225400b84261a000030617154103004900701c8a080316400c007003c000c3e009032210381c034070b800b80640e200c0d2051045468607601c4080c03100320951740c1d50011540c000001018046260000131020a45405035032002051a126403040c03140501031080307424581d4009040c1d9411308401507000a00c0d00041c100b8000005078884822000200245e444164020a000325103940d102040140c0c581c14400c0050080403840c0f0389244030340e40004452805401c02c8044140206005d01490400791a01c0d00640300d002c403178800140c843c80340201121068145644240958082403244d5020340740c0540d10949004070090058008150320106c40780c4c8050039500d0346c0d00b0041e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860086942 1250 860085692 860085701
    0xa030e0c0307080114180604111f0305011503270c0308160b0105040e060106200f0c12030f0307030209012708071d0a021615021305060301030807060b031f 68
    0x121036844c41c1e249503542007100028080d8218000b110f80c000d60080307400303c0c00074116501030420042044501c0c440302c1c00e03091202b444644040010035125001001000e03a801c40c03018101905d400c0a01c55444e07803925107860041000c0301c541e0500020044030051110008a28014642c00766042d942c802884540e000b0b20034030b508003281d41e86070aa0020913541018000c91804140d104010001079007000415511101000e41daa80c1c50309001807051101c80081000c400701c6004071002d0112840c25600f0f00600801031410702010341c2c0100440b0764080c0040d011642d01c8002440d0040c0c40e18400d81c0101c5d4a041d04c900070700e02e00b00c039186040e651040c0e0300f2843c01c2103807010000c43d00016581c00b481003004002c503040310484e10f07440e0300040d1002c16903001003103504500310302d401c8008080d17541e6240d100c07840b41c07000e584035a0100340c80052620290000b80904800c071501d505644c51680c904110b4815a0030003402c098403034516103440d0720200855449031350b00040050312032124500610041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860088192 1250 860086942 860086961
    0x6040c180b04140f060304060504060b041a040b04060302030d11030d0c05090a140a0e130f080a090603060e0a09060609050c1c0c05040b0f19050406170106050a030e0c03070801 77
    0x3c04154491040792400ea8000407041e40c002d0700c12429a5a1038440e034000b0319000b40160780380d40d1643c4076000300b81d945104003469038042c40c480d26850381003c0180000c54120315501070040740313801014000b594000035070088200440c6440c124010704030361801c0c294040c610580002500304241400c2c115005030142c181c49800744c4408912503a145600d0010a111421090300000300400900000081d0b00c11164818005d407400710b01510540c1d2240300d07901c4600d8081c1c7d100f15003c034080d4646940310203c140180382520301840300b107090080411342240c000d4001d030011950307002000d040051a800250081c24010000c20031490001d0382c0e58202c0e07100b44c01501c4050581c00c000d200000300c611521000050543c1c84605240c24420040782651081d00c5034042c0c24414800c000c806803d09410800b421010b556440c1c60320310b4141c3c064190071410b074900140e00c2004005004155000040c0c840383c4855107408960500d100c80098140341c01d8030f0b00683c2500807100c0211340404150000200c1303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860089442 1250 860088192 860088209
    0x1090b0a06030b06010c170c0708060901061d0105210c0409030509040f1802010e01180f050405070503130602180a150f1112070c05121605031506040c180b04 69
    0x56640394801100c500c0d86e45280104001c0100d00c08400042e005005403540c8420038080364030301d60b02c0f04225458071a0845070200d0030381d100d079010b201c2001c06510368a0900c0d040740740d01c02c0550400c0700080c01c04903500d0001401390412800b10841480410824440c98009001003002140c0ea0130003d22a1b8010b1200034040c0d030a1012100c1440441e00c40c25041403800c40000309103805e681e00459180d10003242c00b0381041118072401050748075034030f503001c010400c800c44120401d1504050105450f002085c4500744041401042407071000c402403552240e90180005903140c2d041c0d0f00c060b10b0a4000e41c1526009401a400402c09030359074407803580440c0701522002e82c0c441d5030280440702001c0d1040100f00316080007842c41e034001c0c03407880500020340c0304180200701c032a103c45c042106203450401001c4150700816200c0815041c155101000e444180c003d000b51051014090b80b80302c01c01341c81140a1036859901c01002842100412038468005070080d070711030750790001154160402d0249156 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860090692 1250 860089442 860089463
    0x271302040e03040617091615090605192001060611010b0a031e17031f08010501050d0b09010209041e1a1f030902120a06050a05061804030201090b0a0603 67
    0xc6418000240c4080b50101d966980e20390b0781194a08005ca00b010302421040d200340f041c16140d16208801903805040850300d450b5241e501c1c4180142001480d034407010030f1203400c10003c8480e0b0307080402102465a9414404460b1444000c00d03440620f46807040c074600d52a251003c00c040ea070242910303040c0d41d51200288034001d5104100701c006540c511008261220f408616040190302c0004c0b12200c3d401220642c07100c090000c1e050f00130b40d000321860700380707049042030034403002c0e200344100c0300034100b910f008020544c10310300410040c0161010190007080b01c100004c1e83c40c6000d40484060520152090142120b005030769071245e00c0d04d0f00b00f079038800d040064003040c140c80c01c035010f00440f40c010700f2106480401035600760403040a0003560205926610303140056100c155030088241d0242e030040104030f84c02d05100040b1000a001504401c1c04c01080c0001c40d512202c0f1182c00f2a8841c0100d131407070301d45180581c0100302c603400c01044501c1c6030040043c42040e95200800f101d003d00c0c01e0b0070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860091942 1250 860090692 860090711
    0xc040504050c0f030f0702010204030b0f06031b010504050409080c01110c070b0711010c030c0f031214011a0c1f0506040506030c032d010e011b0c1127130204 69
    0xc280d03010f103441c01401c0324030900001d207583c80d1407242d16070400028000140780c980c40b41c65400d03100c001265000801c00b01074082c0406401e0400c40498000ca032401d08005410305140000d2580c803851150511a81c1c0b100d2a1105009000302241c0c00140560001c02a96002e140b0801241e0000c0800160b203005484000034076210b44401c0342c81d099405600020441c1200c40151040204108242c041000e000f8800d0b0000b500c17001c08121483c02600e80030b220a00900a1100f42c41601503c0c4240030a82c000400004504080e601d01800d12918050344445110a90b00c1c030384503a030304500b01072650341070b0b2420814903207074005402860142c8042c0442c2e6242341c18180d69160500040b0b8259121130340b201e1010145900400310720504808000901456211160a440e07102d000499144d555030044401031900401d001c1007420542858084000141c40f00c80208440501090044440545006040b60024101c2c00c40c40c1404280403424140300803003a011b2259500202e004920302035084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860093192 1250 860091942 860091961
    0x30c0604031b03020a060f2309060907080c06031807120204110403150b0103020d020a030e0f19060c120e0f07050a0b07080f0c0d020a05160e0609100308030c04050405 73
    0x5006843d0140c000f0000380045a07600c1000305840e240071103540d55602000002e600c1c410708079204400802d06520700d01d0800701c0c034003401d140011f400c039919980038403004c005907400814540c1500d0390490300a0740fa99980b0319410a140102c4d840407110b4011180081068806a000140858000d850401440004080c140c03c80d00c100e000207403551400c0003082680c0007080d004079030156410314026090100076002c0310140e030000b50054010949603603040080200402452007500e1100000303100c5088079130301035001c0071844000580700d15203501484040601500b0f1800c074031110000204120b80f00c0400454942d400214142418001d00000185034500b000020041da484000c0740c82c40d003041503a500d411680725241d000da032070b00c041c401020700c0310007400b6104004060750080c19089030507107065070400d140b9a201c00b101080c009000d20581050381c02c281d600c138130182c0d1a840b2135243c0040000803801c00c0e5100402c40c0d00c0001c10061140000c40140c421100107407800e00940e29124142c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860094442 1250 860093192 860093237
    0x6080604060615050f0a0309170711030604080304030804110910060f18060e04060f0f0f0801020f0409091a09071502010204051f18031a090303100e06040e030c060403 73
    0x7214005a024400f181700d07081c0e00001400c600040c0e040c0040d043c44280d5545444a6042200c551018404100d007410302050240c04201e00d0f100301d029220a14041d5202015804054005010861380300001802c015640862414a400c010896625441d0bd0096510006071700e018020001c0c0c002c81484180303501071400c40d82a2100034441200303441c20000c044030380c01404031032142c0c401d0300d070b00c000035040040f80440d2020f808403e50558803103003040c2c2c0c0b0390180e240c140d002c002e075603104001d1201088201b906440594104820106001c007083c1071440d14100f401d1080c0c200e1405c4881808240040000c0b02400c03260500c0305480141c0a10200340c2c200d00035441001c0d004003c1d1a10030f0b20000554803911601c06103414059031145005089900c100c01580040f50300c0544c000e0707404513005d49410210b41c84881c4500443c5145026500d20420b417242d8410041414502c00c00706503640c3c0c0d1500010403800c0b682d005c0760740724100c010300719940e0b401c1550160045107d40324014200b200302c420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860095692 1250 860094442 860094479
    0x1303031803020709020f040b070c14031519060e0a05041e08030f09120a090311060c0c01230d1509051b030402190b090103050f060d02130b0301060806040606 69
    0x1902d2002c0c44c0c401514080d501031200c00b41705810801000c9583c100a00203418028041c2c0c00c1d10600030f08060640f0810111912036038420350084400c000c401e135000d06441d510980e00344140201110540c41071014001c1ca40050034400c66401c1082500d8a4a6001c0ca11481c0106540724030310f07106421224414803000c8014140086c208001034583d244a02665040902c0f841210648110034602c4802d40d049180c0240000700c030310301c0400c288001e400010501c040c0486015203000d4a030110569101c00d490010350600000381000301e2440c40c02004412007c4ca40c0d020b480e034480300700a816008041c4107068802980f000ac0e0b003c12005581c0c803e25200300314403101d5481034150040c003161385030030041c4102e9111620701802c0114001e0314400000800d0004403250720f8410600014041e6140206014100c03034040040001946d20742d00c00050854040d18120030303c02c40c81912a001d014002c0015405608100c000a8001c000140c0c45200358044c4e20101b041545400141003407614045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860096942 1250 860095692 860095697
    0xc060604051b071e03170a1b0f090e101d0403200f0109060c021b01020615040e061503150f07050d091a150a080d05130801051303031803 60
    0x110b00200b607040c0000500b52103004ea114514181d078090b80000000458010032070009100000340e2005240244995401c490040d0003130089884100b01065065951485441049030361508000e42034011103088011f0001c00540e00305c02d203881428440181e07090300c039100781d62419144410b2142c0310f0850080c040c83c0e1564800070400c101c2e45412520034504c0288541501a41000360400d007424492038520707034410080032130321079100d400183c20284000290610488440d030a2005070380c1c0451030340d0707100c002100c100c16455207a101240040c04241600c0c0258400c034814007a02c00d6402d1004040d05a048007210202541c19100484014050300d260311040401c0c4040b40c1031500400207005446031800c00001c44108a03102d40c2c0d01640b12810031141820030005105025600c004506104003090710100c2c5400d02c0c041c00b05954900b80301000f81000004500ca00d41d010301038150130000c0402100a01c100d080070701211080b01040c8804801180c03629412420340003500034290350482d0580c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860098192 1250 860096942 860096971
    0xb030f0102090a0e040c0b030403020106060e030309030601090e0f03180405061203030703052e05120109080d32071d0f0904020102010b1801050a0801140a0f090b0a020c06060405 78
    0x110000104c060090f00807101003c0d00c0d800492050b00b0700d809548181e010780c0c00030518a01e010005084221010059800303a0010030184041e9100080e9081c11120702040028456440e401418180241500c4041140c000000c0e00c1c8602002c0642d4418504070444003040540c507413008004414102c410a60840c0d001800012482e42c0a5441564010041c01701044030b0424201ca940c0700650081c074519034948010014881070074081402c0c96a24107030402008070ba1140e4507000c0c0a4000c010490044980b669281c000c8000155200e05c0c0220304040034030000d0b8007111302d444010074210391410004c0c80c9254105400101494114101e00700a04130042e5641658184815043c0c000c005034159900c400c507000b4144c90b5050041d0158030b0b03c1d040400154140010003110851560007031441703a0411404d100c19032240301005402c1301e044e07040080c10780c10080c0300002a02183d40c003e000440000c0030401b01512030f4009103020303c015020340f442595080100000c464040d24880742c83d0000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860099442 1250 860098192 860098199
    0x8090f01180803070207031703070807080705040e150a0602100515060a2f15060d030807180b0406270f050d020d060504060212090c06191803060b030f0102090a 70
    0x200001144c1011240c4103464403152652191121001221288906600c00104201142d984048001d070460a5841c051405003000c00c0000c180e030081e030040d40b070b11130003820110b0b2a00c0e0780309454400c0881d015098112195548001035103c0c2025060202800c0c1454000740301311912406d500c44000006210a0800920890895040c840480401ca418901001680080c02c840140c0c0030020742400c02041500c07040309107083e0512002d0402c90043c0c0d483d09102d40040d82040c2041e5200c00c0030701d083d07042d4003060765200c0038401180d840040314203c000740c00710f590303039201c03400c2c0101e00b52402d4a050071000301c101c240a94000d512500303071101c2e2406401e22140c81c02044105241e0700081209100c407001c1c0e21164110f4401b5601203582c254001445403032070120742451903001c0c0001000e040d61000c40380c003066040c0310300c400100c820700c1c039206110380700e80c003c140c980b01445c086542c40b11625100e1401100070091040582d1092140030700c03114440c601402190070f821405484818154507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860100692 1250 860099442 860099453
    0x70e070509030a0b0619030c091a09070e031509010911030d0f0509010203091810150c02210d0207030314040609120f0f0812151806120d08090f0118 65
    0x10080d11086c1d02c5000d48943c002e001100c1d03949000614003907692040102d142510f10707003c881a0050384100300305130740f800b42c2c074030b503520b4865a900c90703902d00b400405a049080000d00700b0400011000c0c1581c0540705009003a0380560204002600c12050b940c0202802020142c0e210215209640020405009594528030940c0600940b031018012242001c039010005146801840304032241c03650003900304220847c0100f261401080c818961010100d440c1100422a008411000e4000d801b081604604111008414050304034454103444403902090402503d4290a10061300016200300b19481c01d990700c4002c031000ca8503144c40700e80e201ca14001c214142883c040d10f058442c04c80103040d24010442c1603d0b2030780350901c1954004e584d1008c003812a0a11f040181100a035141444203100f00e83c0c588002030040785040d11b04001c2c0300d54520300003c6180c0e2483c0d40720b00081c05001c901d031154035000303e400383c080c1240100359035004410848280c220703090039025000345106400048003254 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 860101942 1250 860100692 860100713
    0x8070c110f030f0a14070927020607080409020307120e0d110102040b030c03040311010911060903010b040204180b041107030c17040b1903090c14031e070e070509030a 73
    0x400141c1a80c8100c0442103015007881440c44d001c0c5c1d5412000c05021013804418442d40c006406018020071021100480701110f440f610000b24491031550026042555141400e403118203902031b901590316a2580050b0010750001d40701c40b0045501104c00008402103805041c044410f000010f010012032140b04a800001440c50b20070155801c20000c10070440c40c800a40c86501da6841555603806d0615004001e00b030a500030341d4480c0d2400d007400c000104003c1e8a0b4405980c11255503031545a980c001a00510120038000d0740a4400100003941c80031902c01600580c3c010501007010030440f4040c442914000c40d805480c0760303c1040b519000074055400d444c0d03001c0c0102e001c80c2201000311112012503015401c040d220a0f8007080300280090340c498031070034000440ca0240300c101010740d41e200c07004065005140030220300d02c42000b2a070700d0820503184000c82c1d01e0000c1104180d40e07502d003034941b0214002c500041c0701907800202081d008108945580f14041d0081419040c107488804104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 860103192 1250 860101942 860101969
    0x38010317250f02011814040207050f01140a0f020f03010621090c03060e0d1409060f1305090907031505370507030c09030807020a051201050708070c11 66
    0x801c40c9146210854009892145102d00c00100d8840700e10700000d080007208034407034000b9003d030700e80501100e1002080c1003c2e4803020b1380d0260b00c40081d80303003060802c2411091552598030740000105100324810203a8007804560008100951108442009a114030b07050004003010410040010602c00c1c0360035010040b00c0c03620230380100d0441c10f03030b032085c0c4203000000e41d00b581c208002071051024910403503018000342001441d0b0003259000140ca252013103100707001c0440c800304210426880c0d00c4100c904c9030b200c201e2055518482c0c0320002c400070f40035000c0c0d14001e10107200080d0304840300048a1060b642c03c11888032404aa1841e03030005048002c11078400000000c040c000801d80703540c0e00a0040c01c618900e1702084030110f05081c1117400040c00364041600740002200901d400201c01310030759420101540d520700c0c032070000c140040344039070286d0340003541c061040012240662006003c1c07503542da1582e1749515990b80403500f80c00e5010001e0405d01c00e119121074686000f0000b100390 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 860104442 1250 860103192 860103217
    0xc0803150a030203060a0212070503010806040b0a0615030915020c060f060d151e1109060706061505040f1203050f0c010e16050102070f030309170a38010317 69
    0x4042e142e501003400e001c01a60305118554011400e00e006800c10422035510140610f04a4155171501011947d10307480504084c2031640c91f0001300b48200b40341d4100710060600050700c0d14000e80d000400500818084105a40b07446210242944040e007600072107101c005994010456a1031b488260080e600000e446039501080f50640e16000410950010420148240300080d0700040101c00c48050950800020007540c60b000074203110001d610159100100242d844540f102c00c40e1800c00000c003c070743c1040c064800480c94620302640e0000c0204142c680130000d4014665680038071080c0c00b000140024003044050088014003026000940011041c01c00003080031400000114100080451b0b204406270f0780180a04c6196010084e040082200c40141038030a440c60b14000c02000103030182610242449036a0038103040e041200f0942a07030040000d94103c03510380450140725405511141004031812981640e00b0008807041c0e040306c3d089940e5243c155580030103215a03500101c4440d29 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 860105692 1250 860104442 860104459
    0x1112090309041e14060102030a2a0503070c060914270109020910080105030c01180b0a0215061002251710180804090b06070212100b010c080315 63
    0x1a41e41c43c0124001c00c80140214184540b00150f04001ea0701c410398180c000110040500860707176400401c07542280c000f441e011445460211207608658100c0038001030030500401c490040c480701000424500340304032600006640d8409050314051302c0c600c43e04020300020560340f02c49080041022080700c905003002c2c038a414110005030043d00c82a08007034046980862800f0407420308002c3c0c00311b0080c26080070015985400002903032521800b14160400040c0f0344224500c010300c086580140c4219009a5103581c10960020341d94201000016004a04040440c0c501d044c14138020241c83c4055014100041c02c01314551100241c40100110304034803000001403003400c1215055400304040013510340d55100a1042041d0342440c3c48040000000410038400034005404460842e80340d00f1001c00c145034418005241d5001c4d01e5800ba42210074615440d103c1400400c82c81c0002034800010403c410350f00c001160300d0044070500920f00581000807a081181e408000c0400c400014075044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 860106942 1250 860105692 860105707
    0x1b091a0c0303090705041802061c09080c0105070f26150a03060e010e010c05160809100807110304050105070b0c04030804030506070f0c0816050c031e060a11120903 72
    0x307195500844103512541c1144505000d280760500900c1c40032440603000c2c42041d03649070009101c9208603402c40402c10004800c5001d494490f8220500c000d421041d583d0712a0700c02003186010340700446034000041c00e400f0030303010301c2400703402e000c1203466090002070404178003c271035040140701c00303043c400d0481080780c452085a5a55110b000c0a10300c03036000440c90403d584074590964810790b0300c611403641403481c0b02c2d03441d07a480000d844030040c005d905140e80f50105c0c00d01d056903114000c0388a8015195a100d441c18a400625050080c2030a54600e0415503000780c140f601c9004602846000807030400c2050045070000400d9600405241700e494a09580d998800703020307906c20f44c81119560010010000301c540c1105207010034002e40c1c00e003450302218a59408410b88291071400744950429400f0406010301045800d8960501908542441e503c030042c04030070b000c101d103400b2207600c074030130002c4c0b05111140500750b00c0d11040c1c20b0850400c4c0c0c1c06130303600d040c0c803100400602d0140700600446 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 860108192 1250 860106942 860106967
    0x40602130806070c15181e02030d030e100501081e19050d11030a020a0b0a020702220e0c030606040b030f0304180608010c0c060c050405060c060a1b091a 67
    0x40c00f80215484010340742034030b0302d481c44442c1c40010110952516110304c40301c005182d0807182402a60010510025850300350131001c1001982c60065050b100701c580110104c0c3d0554040c0300d61000c48401c4696881d480100481a12024016100d85403c40d6808000303d0145a8100c0e040b050a001624540802003e48002000c801c100640d95544841004056541c20442103405c0804100145140080551010b5912401880001d1004e6480380000b05081c507158103460342291700414145c1604607102d02125013000280c400100c075407410803016000000025043da41102c080d014003200c0d50b0340020400204101020b10390140101e01c007014000405100800180ca01244503c4000140c4080e4a045511540007024540e2501991841d8660041c4d04006816404180400d8515140c01e04640e02e024a40c40300c1d0b084038000c61503020b03d50020174040e22512600000700031102916101c012002c81c07498424004c19141e84e010302c4040e0001c1e41030340101c4261514180340071140300d8031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 860109442 1250 860108192 860108203
    0x703110405060d02011421062407020105070c0e07030606080109091709011b03030c0221030f06150d0b0f06040b0a050f071a06031002030108030f07021504080304031412030406021308 80
    0x5141c6d0a420042c10040741e0301c1c00b4410403120322009100041d081c10b0740840b4270120701c20084007038188000419800704100c000c50250000e0f04050038550b201d07041441016020702a64007c05004c84e49081c00483c4002d40c40c0702d18600e150f0800039a100842446695003c0c0c2e522419440d0704000103007c42c01c4080302c0c0100e000d120184a40e800203291000300b40001d042c040d15541e0080e80c0c0c1c1c1b244c0840311603903040c1c00030303650010010782031002180c80e0b29000a10800d80800e00d01301c3c01c940400c69080040c01544101000304040c3e444180c42d510401c2041482e10071f0340100701180b4428400c01e44914803c0700504110640308503003519210042d2a12442d440038185250b91007100d0b1020818030341014418541c5100c1c40d060700b58219410801010344a00411440000101022403210295500d030344d0400d2035030b011303004036555a0f40c968203103a44980c0b140c0428cc071801c400e0b030043c450000e40050110070108801402c141161504d5840030040d44c8101600d1115885481c80401d805505004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 860110692 1250 860109442 860109487
    0x60a0324180501120b070503060f150c070f030c12240f0b191e090e0322050609060921010b10020a020a050f01020f010e0703110405060d020114 63
    0x40c40c0c4944481c07114000240ca605030030081c401c210801020000030b030a8508140c0020013418030030b0b103ea4500d800f0900006400310480c1c0d0110141c4542c20901e22884000c202600318002521103181e1600b03916a51520f0b5407000602d0f031415180d00b040b20518142a0304580380c80ba248000c0d42c030b202c11741c8251840d070302c09a0b00032505075101072480e4550542d2103000c801e450207588408040c4170f000008078000c07a0764420010b840307841202c0c41411b6200036003c58041c001a070420400d6440003c0e403c2c0d40e80d0013000f080400f20a0021000707e40c002010b52603c121900142624036144070341d018800310382c02555400f604180d00100305094540b81545043c0d00c50110000081c50014003030400030502d254011283c00e5400c01d180c0a0090b0721004004415200280e400d20071030158500100d140520110039864107500e0882038500240000c2140d0040700e003d00c030482d28110300401007000311207040d503d2551101e908a56100154040d04183c00d64101c65064541051a031152107140c5043c0ca40303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 860111942 1250 860110692 860110709
    0x415081006060305241314130605010b1c0b01050c0102070b0a0f0209030604020409050a020603010f08070501050406120507090b0406200a1e050c270114060a0324 71
    0x40c082c0510303507061045641c000c019040c8240d92101400e09100000380c5100840e0080c0d0848040c08013020058000a400c054804070700d10b864a00300c0c21000c1c5500c2440ca00316080303401c00000041e411b184005413244624a6900030540c2038201151200901032040124103108050101841000080c4040c205590081c8202c4084d840d003100000c0840d800b101c2120701251041c0844080c83d100011038981c05070341943c0029680c0c0050815a19020702000002d510820000021500030301c014a41e808840c6c5c1c500440d0b5002d900c0320015255401140500b80c00548010031380c0c0020720083c0c1089820200e103052124032103440e007034071121991044d08610003003130510300f210b410a205e0540c0d0441442143c0085c0a40680740d989000005008a1890301031040e0b041283d001c1c0b00d42402a0001007400500b407203540c6100544508980004500894138076400e2000040d010040801c1e9280310400141920301d44041410154000c1c02e030603000140c000c044084c4280300c1d03079030560710740054203004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 860113192 1250 860111942 860111951
    0x90b090f06071110050a0204030816060f1a0f0a050603091e0109210306090204060c030e01080103030806060d1b02031b0a120c08070507151106130204150810 69
    0x410640d0300d00680070708407004000daa801e07058200c0300045540203129801480102d01e82c2c03140700d018400b901441e00060144100014400d200a10340010024800c0c0320303210502c800080c004030030701111000f014108206020440c0d51042e40342000d0309840084008214006803074031940480c01341e03041210060700c2031f805080a102c100c003516048403d0803407000c1c000e100f0040d0361703a40c070142c4828a1811b105070341c0f8440b01164506009400c18009054000320440d2115a5080d00900c0c0e40002c52059000c0741c0450104407155210702c08841c1a2600b58951403059203850061000a610122008000b2035540541080780180001d41c1c040081c0703542e000750b031070b02c05049005900310624010007255620880184000480303840e030004800fa11801d200342d04802506100135140f065000040031400381c00da0200f07800f48410030544150035995038410000703801c800c040d5660041a20320185c104030703104a140062506070032124401090303201d03a0800310380c0d6003d4907240c030280c0c0d1181c1c901aa00d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 860114442 1250 860113192 860113213
    0x30c0a080315120d080711011817181302120412020601150e01030506040230060307030818060c0d0903030f0504050f1e060d0207051207080a0e0103090b09 68
    0x451039502c078602c100d4004059548500380180e9646004010409000e8a60000707030089004182190106002d04002e10035000002130303215103a02007590465010490040b0344403915100300c150340c0b0001400306003040e42c5010004114034480c1c900c49001410740c08000340b41c030141034013140e68003961051699489802c80704001a0812105070040b0300c0c2140322450342e20381503511102158640c00203080029481c3c640c031001c5806403044081c40540c102034000c0c3d98030746180c48001e56032100c210f02e02d801c2c180d1705c5907020107442e8a603612000d4903004040c4070b810180d40c03488003040c286d01001032140349400b11011280d414030042e8424040402d0107140b00300207141d00400d00c0351414405140181c601814040050340700380f03500b040d1343d000368074044071f1040480305e40c000b4081c0044010081c507240e052044c0c40d903000e0740c00004101c0310313402881851984683d8150503140d0fa02d60160a841c1040b207501012507014000d50610b82c101601c8030042c0c404101c0c4600c8031405451581c028003001d241 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 860115692 1250 860114442 860114461
    0x1050a05030607020a0b101205030a0f031a19030204060b0a030c0c0f1101020a0501050a0b0a0504060302220b0a0b19021f36120e061b030c0a0803 64
    0x665910240c042c0d0410700400001d10760100c1c81c1d21055900652025154031171000d5011200038a410010080c10911040302c00d014000028045040d03865803800407944410304210151203044203211b0082d1350000303503030b0354502c0d214841c00b01001029002e40700c1c0d140d40340c0000342550741c20345c4400d80c001c030001694141160305002e01c3d181c2501c07034202035400c1029a542d59140c059011340241c0322049002c03189109a2007400a00c0480b078020000303004600346100d13140001e006c0401641e12480c0002e50001e554282030241d0401c1703d0300101a001e0080e4012107080180845880045c560f075a00d451060b41c940d100100c13500039181c201c901c6034403005c00304015848400340c4c031407020556020b12024195580d40c480072403c6208500c1c40410a000031800358401000c0020700c804103110716000d91041902e404e0600181c45010365001d00400c01000c00030340307610301c21192968000c2d1042040c2d480280c03100c16103800c6950700c002203918140708003041c0c6040200002003100d8001c0000b040c05140790 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 860116942 1250 860115692 860115709
    0x6070302161e0507090e060106050c01091b05030f0a12030203060604030507030b151903020f190314060f0c030c16021003050907170c091e0c0705011a210102040b040e0105 75
    0x65103c40c1003246c41e0403100703007555400d0148244003c0110014a4042c03001c402c1d0448140d1b540d004121425248051007110204142030045902a10440855000780600090744021084c0c000f0300b085102c2940c158102c000c5d601c000c100c0c640241c0308000c0000010810070142e00110b01400300310f810781c00d124001c81940300040070564800c002162003147c8100744c07441c0313840845c0d44c111406095900d0b1440800d00045001c0d11260178200440c80000500584581c40042011042d042d02c04a9035503c20855801d1002d540b49140d1220074800599a042500005e05c02c507803100c4003040d01c480d030550028801e5003030380000d40000713600c2c0d0b410710491300c1c01040340002400400360384401000141c05001e640e903c03c2030500e40b10705102d5001c03510000e00c1c0c50004014100072481c5101d9460602c190203810b622800301211603601e07041c000d9900d6030300903150748000413000304a1400082c03035114040740d05403c82140c4e0a80d540c02c0000040c003400900050004000d40750314402190b14120400c1140c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 860118192 1250 860116942 860116949
    0x40302010e0c100f1206090212090d030e07030f02030106090203010602010c0908071805130f050a0b0f0402090c0c072402060108071a160203060a0207050c100206070302161e0507 78
    0xc3d5042040007000390b0f0450728000c0c861041d450058801180401e0303c0000d007150340e2090014510000b02c80c003c25080d248128400d22412003243c0401c40c5411013281100c08000010741c60390411300091000030f00509800701000c0c0010004113580392182d070a1000c03a44280e0140c4003603075442c06c80ca0065a0082c0901005004948c05040300342e14003141407100c18150680110842c3e40c800c00a14200000106d5000301a0402400c0000c0b0b0081e103000c1d88d8075041075030f069604007089000204001d41440000d072045a0281502242d9201e005401c41c8582103101d0202c601c3c010780b04041061114a0385c480011400d080341d82d42885410480641054810380065500e500310200500c113110003020000701c00c01da40320650381d4425090984280b05081560002d6041c01118188400341030150058030340580550b003520102800f040070410021860290180980c00c804001088540264040d105e6030040c03034600c5c40b4010076640e030300a009804004180032511184618414000d00300480c0e00903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 860119442 1250 860118192 860118199
    0xc060f1101050907090c0504030b13150506030d030c050d1e140c04140102100c0302030a0b06030f1f03020d06020a02010c05032206060e1501020c3003040e040302010e0c 74
    0x3241401e0400340e03102c02d0304d4081e040f600c540b43c000da40700140c49441154000d64011442240d9424400c20442d2582e405c10000d030b0311490310a451854403a11846004d0040074010010548900c010303605074040e02c00443c5803000d201091082e40e05000341401200030b0096007035402c1c40035401e0403825200311039004400b40d00000f01e00b1704000d2014192001c0314159a004203949070656408070040b0718107000f44a032040c01c54204031801d034103507030140c000d180a402c4200c02401034144400c1408100e01080301d4140c0907058100c0450540e408a0182c02d02c1e014905401050039903d80d0007013002da5022200440b803040c2d0004071500295428400c9001c00783e160701d811071460070400e400c2c03607480b03240540903008000c03005075000400001c2c0d88404000d04101c0941840c604e8601d0b500210b0315443c003411030160140b403124202510344000d00e000a1100c1e040b0419105841c80040c1102041a40a031141c91004204c0820040c4018620701e1144e031080c0c0c000306807041c616582074241640503c0c420f01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 860120692 1250 860119442 860119451
    0xc02091303020703022808211204060b0a0b0f074214130624030605040203150f100e1b0d200d05010e0c0405060a0c0c060f1101 56
    0x2030b8041100d10840c0d4048825480d044401303030031559001c682c501100381c483e0441c00000b0340c2e03420108100c6c99070100381001c02c0034618010070100242c802e045032982c81040303078800078000500310b60000d0f00d101c05c003a2414541c25100c425113512540801c280b1240b24801182c02002c102c1504010380300d021407a0714018a0701c082100d400c00401c01440d00550b4102441c0b400d2100940d16071000050802650701440d90381040d02480108203220b80c0d0960750702d8101080c0140d40c1000401000140b00320765240a8900d15580700d800040c14040c0007203074940604409c1c0143c0100c07241e2064050341250f0050701c03040c20030745654002405c0c29440007c0301c032607280400c0350042140da0011007505010540390f984000584440e00201041c2c00200d9503d600e10840c41d8101c3d000d00050910900902002c04c5a66210400c03544120812103501840c14010807043c80b4608115014100300b020a0030a0003075170b07003140d80c0c1e0a8a0599900080c00094610a0510700c20360700000780e00e1003c103148001c22 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 860121942 1250 860120692 860120731
    0x4020a21110f0d0b0d030e010225051c0b0c090a06020f120705010b0901030803090c0603460b0a150f081b070803011a0c0304060c02120d0c0209 63
    0x1490740c0038108a4210302c4502203440352010312070790465180401c0c02890342c117100000e89006000740c0f040203544c500503c56020306d007010035545648032403100c1d001c404200005240c0005c001c540c0b9242401c58030800c803100c040d03000180c0c4260000c2c5c01002110140390321031009900b48140c000340c1d507000d4011940802100c43c081280031400e050081c0c01040105e079607803824140b190251201003a200c5e000220400000148092040514007818645003920300342003415041084a0000b5116058200c82103401c0c485020b00414090701a240002045111035101415048030b813041c014603501030079210380309040c0d18030b880c600074000780010301e091110602000000070084142202c0c5e580500c0b0310803001c20500500c45414011240480b4000766039492075241c40f8004e80c1080c811118202220b400861032400761100380c80302d40381c00900950070b280c03070500f04a0b48000c1520050340c02c00700010340c0700540a024040c8035480840760b220224052a607106002000d14010690081502401410f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 860123192 1250 860121942 860121971
    0x4091a010504030b010e060d14061f033c0c06020712110f0f030a0503090a0f0308030c0a090518090c0f061e1209151b0d02070c0504020a21 61
    0xb1070546c0d001d454400050358803040030402d00c03c9600005044500e08101701c8210701d00000f1003a04c01c40030340e80907070240c9600480070090b586181c0030003002070250005000c00650a0844552044040842c0b904e4020030b0b801c900d8450b00c14100141c48000b0800c00a02041c0c0e010000300c8005c003ca0b07070f02d8180190035500e440c510a0348034400b02e4810501c00c0700045003581c4050180c05810402810389201c5205494201e0b5280d102c0f03450240241c02903140020310441d8407640750101c0c0c1e0060700c502c1c03441d641c0d03103070400f150350003011640d052204980011030180c0341c0038400401400001c004402508001b44424a0280f2002800f4494282409140440c0e111141980d80002085507030003401601d5107514100e50241003428841030b60308800b0018031180c00555018031546171842102e1300d40700d03020030b4040c0d100c46040d1034140460410005450302050782c01007510a003e0070800c89002d444800080070307030b804a480079000419203840300140307801071064040b2220308290304104200135442c0342c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 860124442 1250 860123192 860123213
    0x170f012304030f120c05040e0603030a0819090c0306380f03120f0322050312130515101d01030f030908010903120c02031602090a0603060204091a01050403 68
    0x10b0400000141c1241c441380542c42c0004802020081800005901c480080c010f40180c0300d13000a68405001060030340c2004400c9801d00001c42c0c0d1044200da80740e00c0c0c122005924244900e00c1e040c0e0b00c1d446200444d41280240018600c9084081840b49844120886034043c082d51225403030f030034060742183d0042d05141c03030720207400589101030704050800021381081d0003010700104018002400803010402c60000318400e101280144845900c10488240c0d46029410020031a80c810892036840340c01e45019540d201c0d0801013049414001507072407505100744a1000038084020105020300e2011101c0860098a44045501c000e44503100c044501b0600610000d04142500a6010180b6104244401c0a042840002d2007000100d20f001003a56103020703070350b008103440d009451896503c08401c451b842414200f45440450f200d400b04101c0060282030310101e940e503a00d001001501c0717400076200820400c01c00040107402c00c1140c0620034090002181004000c1105000040c00001d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 860125692 1250 860124442 860124451
    0x3030605042a02030c030412141513080415030902040b010e0307030809030111180108010e252703050f03030f07050d02130e0a111e0c07170f0123 64
    0x482e00d8000b8800264154807031300d102c0b401c1501000034003281c000e034422524001284078030750003005040c1817041c2e540c84031410912580300440d03181c085500e010901152039039250082d40028602030b40d640301511003804a8280c0d601103030726065010258903061055017082c00d401e080c0740d4002d034407050001c0d0315548140002004520702180c00c030740e00c1c2c83c2584041100c59600c4001036881d01000c4014480303900c480700090015103004000700d51000b014410f24054120005681030030190150241041c0c8582c180c400300b04500b1901c0440e0002041c803004d0030b01c161f000400e91606007075060445c1000b1032000400c113507a0080013445007000009403140d90002092420a41f220550b2203140041d100302144804c142101000102e01c030105495600e0007104940b50030000d03040c0b507800702011030081c8840f8100150003030360880d41000781c040042220010b0300d0180c40f0000c0c0c42d5258100040f100b034202418a40c8428403590b0645003d100381c090518044484440d5080d258840044101c0001d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 860126942 1250 860125692 860125751
    0xd0c1709010209330301120c05040c1d0112150603140c0306012001060e0105041a100f05091f18121103010e060f07091205070504091505040602070303060504 69
    0x1c442962200e40003002020340d903031003982980d2942d440e00a040720b03168030305050312303080542e0000049034a0140301b002c3d111411600d40003c58078603c40e240b9803008004400ca410300821203d40c082243e0640b1460000f0303111100740c206400e0404400030300b201e0440e010130100c040b2120a01403c002c88400b901c0d8025024600718440c8003007080003e100301c01c000c003940165800c020010412200b1404c42074140d403000e540800409000c00e4085c03100d40403540f46c00f034020910041c14000c440c4a515111722000c41d500b44240f40c0050308010032003031715036041e0403410500080241002c190b48a00190610f1100402d0111101d013003c2245880007600c600c014000602840c09980a1b1401c0d00320044800000b01520361911b4400c48403924640200d60380c000260601402181c00400b1199003034810390044001c0240701e00b4030f8280401450500010389813001d4811441c03103900300074061107220354415000035848020600d0082c0a9400c242c004c503200e42d050141c803100d002d8545038504100b81c242b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 860128192 1250 860126942 860126989
    0x6080601050609040b012010110a080703021317010e010b2719021306020c0109081c0912061401170c04050a060510170c090a060f02030d0c1709010209 66
    0x4900503288181c0740c6030a124500718090301c00f4007c000c08036416004c40c060340018401d00040104140b11403054982c4100800c2801002c11803440c8298003420119210076680b0f6412130b00c9110820354500783c0156428103a4440400707031081e00b02030050304074509091702d1107802c044d40e0001c00c1d0302c03040b40b14094203a000c5a41c000280713041e10a9406594a001c0721408650380c00b104146107907100c0090080c83c015100700401013025510031203c40c800c0710610005030003400380204030044d0400c0f41c446c2c43c034100080350b00e010554a80036040c0c00612032140704001036400c6902c20203401c100f0142e014259075403d02c070030001813071700104500c52003450032600010300e40c1c0c40218100050819801117074005c0d0100c2e481c48800707a0820034140090128000e1042c0a50f03d14858003c14403400c54056000602030404100e803c1c001c43c50700d030a004285c01034a003024905a121003c5078801442000050684020300d84081b40032410660000320a400030352a01e4000004107014071003100024804180c2c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 860129442 1250 860128192 860128211
    0x403091a070807080c0c030f0a060509031216030c09050108072601140906030319050703021c050d0e0109030906120f020703020a02011e0c030305070e030717010608060105060904 78
    0x100c1048400c61a40200d04076110811402d11000e5a0480660b2210a210751356042c491460002035451001c072699004185655040d941c1d5000713041c01400e0049140b03c28800c0500442c800120b40d8031525118220f409844c0107080000c0c26921030108082c14441c00450601c0603903800303000603074044a6404d002c940700114124036904a5000101f01e940350010b24004240410900004d40c00e1140407194120780340c642008041e101d03c03a1140f91070803c6500405104494084c0025200460281c010344895503007085010f040458690780303c900047e00010646091110f40c0301d1885540d00240081001c1c200941c0d020f00210224041c640a010350001d02f40c0c100d50b4650800031000e001c13660155200d02e41446d0281d074900000c4c00403404119480007501c201c2800e03828222100d003840da04d07141d020000e500c1c00d070014130000c0d1520081100510500159031010400500100040f4548030891245200003600316401508555010381220700100000d035250b0b020354159001c05c542c0000c20105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 860130692 1250 860129442 860129489
    0x31806080f0c031f0312120b030c09090f190b09030a1d0f0307120309290d0605030a031701080d020309190305120d0609020a08070c050c03030d02130608040309 70
    0x4c03d02421580c00078100000310030040e042d60300f00704600303240c0c1341c0b0f03240741022035255015107400318506901540a55600c400501e05410002e420401e0507080d200a44010101281044280d074015005080358024440400010f04983e036407000302c02018605105054400806504000c00090000c107401c40114000e662121483d45140d20001c003140c3d0314507511607038065189852141134011841c0144000f9440c0141510b1003030b2500c217601e0000c0c102e4114071103e0056003007000005105ca580700f8000c5050b1705d080041e240c015020741c690305a5010384503e1034012050503001800c05410003402c003d9625000803d0310901c840072590340c0c201c0c0d001c1039000d4040036125030005c3c1c114494000f0752050b10b100300004080300c0b0b01844081c0082502c407002a4168030440550500007a40400011041c41c07064a020328803905c5803056a1a60807801d000a1540e0002441c40814541c0050110144c10110401d6001401c5034105048545059140036241425a00c02e409011034076208a419582 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 860131942 1250 860130692 860130721
    0xe0d0609050c1801081908030c0d090f050c330c0a170301060e010804020a050405040c030c1d06040b1008100f0b0a0e0d08180406050d031806080f0c03 66
    0x12003d00f0000c0c4000303a0b1440443c04180c01c3c441e00301a4080c050040402c04030302141481400d420854003071543e01e0b103003000022a484040c0c1c91ba4141d9a900e00c680001d107036081e541d040980598002d100105000040040d040b41007004a06074018001070581802d4200c0407003440b605140d505141c8400810400908001c0e0a00000b480a0703600c1071803020641c0c161010310b041e0344017541c0e40781e0891104001510540d400f618041c3d448600c1c04d104200e41d00e0a904060740c014030400145c001070743d5a94030103030070b0400b1390070651104d0040d00320700f4820007145c800b0329403014084805200300c003464008a010f01180203040d0041001100000b01190300b840038101c01400c0710600d5407415039480052400303581041c03006000203800810041158038224840ac40102d03040000f0750f24103910900308181c494042d0048540282d110040011507903190342e41660704500a4480b031544698003039484a140807950025000e00400b001071000318107600140305d5200803600b0480d65680c480c46441061803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 860133192 1250 860131942 860131963
    0x41515030209030601081c02010504050c0d05030702040903030515030303152b050a0b01090203090d050a14040306050f0c030c07150603020306040c0905090a08070f020a0f150f0e0d060905 82
    0x1813150303000000e44444006102160032400c25030405170340d150f510040f4240c03001510042d005522650000031030313141441c03d0031001341c400c2c0c041780c2c905a925400304094907000301c03082d40030035500c10800861070403a0540005e000001c40146d4a076180101c04c858000c81d401034542d02030b04035480401020403014600c4030300d1804400342540400030502d00304d41d0302c2c8007500e000c03106030480c1e5000046003140c83c002d403800344c1c0401000d841c07c5c4940940855054004441351000c005140a080501c0c0100b04001d10243d0f000311004203061400321003038840742801401032129003c04104001030142c488054908540d0f0103520b02d00c443c41d414260101a14090f04017035032500800c0300340020400700303025110403a4404401408030740c2c0d444034001d03155240c4110190905504000300341c001180307400ea181056200a10803103505442c2e510101620000b60880040700d0303440034069500b0740e085100301d0007a07045031901c40c1844c0510404181502911100200520707100e503070f201e0402000380001e0081317 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 860134442 1250 860133192 860133199
    0xb03030304062406020615040204091a100e01173d0503011104030b0a14010303091a0319091103160603051008060711010e031204060506041515030209 66
    0x507401c060a0803002858400314603560344041181c0102d0200c8400c41e01e408a428079000b5201c942c1c0e4140301010183c81c4003000960080d03003000041180040d40c80f4001440118030328404403152800188071381e00400c0000c0d00e060005000305101d41d43c0c0c0c081e98454210b82d0401000d2519114541f289506441c030b0950780040d1641843c04102c59540b5109040481100038204c0e00141c5e941c0c001c0c903003202d80c0940c045102c2c0c0300421003840401c1241205940020551000085046100302a106000020b030030031000a40c1c0203104104c1d40da0346020200500c4042c400ca2499400c000302000382c070804200b410b006181c3c9800c8048140700480e512900d00c2c0e030f40501070322510140c0340e440300d03240300b5540103120110380341c0008075000c042c03c4506101680c41c1c0c00d009140949031310300251107004404050021540d00c0d011840224101032011b0220180c00050032a91801c15182010540d000280145d000720300d86414642e055501207441403c5811070524803c0b109403d230b4044020b4841c000d40303a5003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 860135692 1250 860134442 860134447
    0x100201060e010311180420060702030a05030918131101020309221416030b0d0c0b07030806040b0f01050c01240f150e100507120305010e011e09050402040b0303 70
    0x1d109040400304d10268084403807100d590f80c444900384402a084d10b01a0440600440c01544101241d24032a00401d00170b00f428202215035000a182c4a006c00d4103c0b031030780011035504245e050200342c0e4040c07a981c00d8042001440c1c40703141c5286540c12a000a4080300410761000c00c107034000d00848804045c003901121071205a4840074088914003040c0688007880c1c1640d071080d80a180500314040e070443d030b40703420f140507000300128082c00602c08591b070700911071880c0c5030010700e4040000004050554071252221311504001e400c852006103181e00681c00c00700140f2031a56101c41d06d021506c82420000c0d203400140c0c11242c014000f0000f009100100d801081008440e142c02c01e104544800d00ba55030555280c0c1d114095003c9615045008289030000c240801d107460728050018182620b01182804030540f02c0011140940407403a0129550b9001072050024400307400f40500340c41128500c00000301c90000c1c2c00e19016110310381d451545d41c408101190b640b070f0003804d00e650005081740d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 860136942 1250 860135692 860135699
    0x121e06021314010203071e1b06080907050d08120c0405040207200301060b071113021603080708070903140f031224090f090a0615030b01091a100201060e01 68
    0x39003202941c003824150b865154090141c07588004100d030350f1306a10200000949030f4015807800c0b0ba0400b084102c0b003260380d102e168810b207075a01e4810b01c020404c2d507650b0806070400c500803c2c01c14407617402260140d44c01c459170380041500d0504a90003021000c002580c5075541c03505040160060340c100035401400001c0c0041400a00702c1c000a008d812070406040340c900380c2081500f02c904520804002c58010300241005c642203102c1804803401c0900f1036035140403910400c0b401c07a0702681400c015414213204860500d83d211a00c17507400001d509001d0641e0030204c0c1d000e85030740d01511005000c0341082c11100c0141600744941c03209200340b402202c1c1c80307000341c48030200340040807a40300700c904051041440042110b66900c4002c3c00003e04215010303101c1a1511700321307070001003248000e0310440740741c900000c1d9103114000d0714500b24603e1607071182c1949072465068006034000c6003100e00342540e03039070036007069038a0000382401241c1d000c4551700007484c16805090540e1280d0143d603d81000003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 860138192 1250 860136942 860136967
    0x10c05030105090907171f140705070c091508060721020c0a020a0f1701020a0c0201110c090c030a0c05071e03180e07030b011805090a06030b01080304030b060901121e0602 75
    0x500304080c2950344247c00300441c5020750101c510700024030200c110720001144a090003a0000e184250181041803919500c44440c0c005843d484040102c034103109540c20850001c080c403029411540510344100c0070250008081180f004040b06101c0c004c0d40040d400350b0441d010030240851550240c8683c5540c0da8540c2441c104801602c5840601c40000f11640705081040c07084408100603501e03485002c841c1034004544003085001486140d01c1210300420b6155200001244261412081513950f0701d0300c0081001619102051002885024056000042c2411640c0c00000441c8412403440c90806d0800300c8115a000c400010050b040f1040810401d8080b00003038452040b90301d00303000d40035080c801100c000000a800074110940300328140010310702242003035040b4103544808030309103449842c0c41100340001c1e801030050340d10000d010004c000c0a50381c0e00d036104000726001003056240ca650900140044c0d81c00801106086a01d0388889250380e001682d4180c00071411500c405000804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 860139442 1250 860138192 860138203
    0x11040b0d050a080a11190f08090306040c090b010203090d060203060102190c0602070b0307120e01060f08061006030e0a0f0f0b070201090b280915090b04060e010c0503010509090717 79
    0x400003c0c0f110f074030550085c08000780d10742c043d17010340200d04e030362003000d445801d6084240e4a08885102c820032200001d560100b00860041b40105410303660207150240520403a00c82070030983c195081840f403126a80e859100610000e904600302503601e960f540d00407810b10b0402110b040f8400d14540d002d00a000c40c0004a0080e035143d5021181c10507120b10004106010880d8001c0002da00101391008060054004c00741c11509a80045181e503118901c0c2d4003007110f030740c11400d6564428010060384a00d1855100001c01c01c2d401c0420080c14008030507070315142d0605000d8117510386150f88a04200d85c0c01c000e003581d01c6c0c01c8561031829050030350009020b050380080c00c0d144000f40380c01058020320842c90200c8168905003645d0141804196110301030040c101043c1c6510b2240e0030448180c10103402103d020034410400654540340030320341442121a90304200e149685030070300032110760750424200c0e41510710880300c0c0d03c5243d440d005650315064031600600c0819213070022545050100041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 860140692 1250 860139442 860139457
    0x1409040203041407122406050a091a060304030e011818021809061e0d021008060a0b040e04080306281409061c03090f06021b0301020711040b0d050a08 66
    0x1d848146584003011503903c440f490000c1d0421b0041a4803a141242d84811007040312907111002c508543d4550000e840892194081c04416442d126546c590303c02d01c1100c0b19040e40e01711001415400c00e81c0b0003d280c1e90b01d41d00404c1c1070241d94401b01c5090701c07141e00090000c0840010021010303015800c0030003e50130400d004030703e00d042c06003584154607040c982030344144000361a58501400307030084e2040d051490540f00c5c0d00702d1416281c401c0540c841102c603549100741780e201d0f0075141c1001700a000c01016298006400d2100034001841080d5125150641042d040f449554407070719501c2c006403c240341403180d480c0024030031041001344030b0959684d4049a810303005c06641d50403043d05001184004454080e40f01c01020103141c0980486820092410b000b40341141e107042c0c40c3d00e180007414800742c100b0f001591000150300e08132982c0c02d01580c042d0000341e0080d4204010b0395900c001c81070001c90054402c0e500e0300544029034a6603008000d002d0b03082001c4484ae0038260521405640c4080f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 860141942 1250 860140692 860140733
    0x81e0d0f021c0b0108042301051e01082e02160f02152109161403070b04030b13031e050909010e06060d0f06120b1602071401140904020304 61
    0x44035a10b20307142d40c45114000801a101d0301c4a40c0d6a650f02d20b0441c80d003071415031305040c00a02c8100c1046809104180c81115040005c1450702142c882c01416072805a0101d489503100444110000c64010b2542e1040ca10003818441a00082c04810019000d0314801c00c882c4420741c0761075003e00904d81249205c103402614205641c0e00d59001c1c2140c07a22940c4840140b002d800480c4090120003008100d134002d0307070752041c0c0d00c0b100101c00020755000d041d540058003008402c2e1a01d03156160900c41c40c40105003250503203250a1a55880d044050f00017007500c03045810490011040c10f0042d515448610400b15892140b61980c070341c007031301da03810000c1f04034003c0c6207000012810f445905a100d004440003040300c0d0418488410800181100c81e0040d01d0072a20751f0000101d031000503805580300e500c2602c5041c114602111104031a1914012a100b1903020580400c01075080f41d44601034841c00f0310346045e4501c82d100c51585180318020440713800c81d200000300001c0c420040c2c16011004800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 860143192 1250 860141942 860141977
    0x21e0703022d0910030b0c040e18010f0902101d030304082802030a0b04031202070b07171006140f040f032a27050412030f09081e0d0f02 60
    0x6052020403081190130794034100008500b44040b0310064030850340084002846841c094135261115580c16041da140c00f82080c609112900a1000b0b005a0901401e048001c21074040e440c0c001800b6080d0007142d02092020078402e200000d0080200012074007805011250349aa03290040f035a102d808941c450362000780310304100c2502d4084602540c2c170304d40040091005510680300d179100700201501c11801d208040c03c1d140803e200d40d00241107898002c0e00041003c4c0341c8924040c12800800107148031005c401010044c44803c01080e9200340d07405480c10715200d00c0389004034060343c4103020700c000a080e0042400110a54080c2e007200980384a500c840d002c0d00740145071107140c164075003000704003542c035144188030344800b2080a071500b131310040c0744005480440d100b500868500b07403000d460f82e4041d0011141c0b0103130503009560302e024102e8020000c04031a0b0300c0759041d600aa0640752844000f070b14008041034500c01c2510208030510404200c0c0b078406585100c02076009081a05900302d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 860144442 1250 860143192 860143279
    0xc150106110c150a110f03030103120e10080a0213080c0f0109060203040501050a030f020307020a0c05151c23010608070305010e16022a091006021e070302 68
    0x402c2c6001da16602810003a4014200107400c00d96800800124080007803806510784400342c204100c44ea243c0300200916560350550404e0841916900300003407e1200d007110388080303074a4028860100586510300100c05499031200b01e00648507022010240010000d8049a980e0707000c10301080c0c0c0d1b0012246c20340c1c0c4012210040d6072010b1244143c0e000750304107000820455026200030544508140380000d01c01004010040898100f80ca201c0011380c00f01044804000305005e600d4050102184c0344810120201c0d100e40651040350080ca90480000215030081c607910b8003c41c3c0091003052801e1140c0c60130710703400c0c45400070034807a8030006004400032500d5103010f441054149d40c1c6003d80500d585c0d44002400d40420704580c26807085224210704507180300703000500d0a00602d501c0c26642041c515130020000c9241c0c002d00f4800510060780340400185070002a0030144400e50203440d03103400b00042900f4140003480c0d001942001e800400040e01030303c01d66a80040c0b01109000c02c244440c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 860145692 1250 860144442 860144477
    0xb09031b1e0d020601061d090403030b01540602060f06180105011b05010f0905150903120a09060603060b041416050706060b040308121303170c0c150106 67
    0x1c88902c00c00150704924010300c07925210b1070007100454101c41d10034601001c00340224200e04800c6500b6400255034140c211895030340f00d01100c190140c4110700c1c2101c0480001025040c6003d01208550805680c40700b0809c2580103008140c944040c0c076007800201ea6400019480d481d040717801c1807480c80c0700740004600780f401000c102070072212018030004903801c02d00191401da581140e05400c0c4280740143c100051002d0165190002c050800450048413520f4003a1034080c4850000c081b01c1061001c000cbc010b01d0010568049284a9400c0b4150340c4403101c5102c000d03d41c07642d01811807420720b10301009020b903c0e0001c8801c004240c500300b00005030304007101082e480c00e031030240294845100c6221068403643c040c00c040790280b0000918a90307290124010780d40a58001c44440030302003a2102e2403c52210755544c450300c0012001c6181410340d50050801040c1c880a01542e86090045800440391100752130074503584400f0ac0d4502d0032000c03869041d07020b092081c5130010707101c100701801c030b00c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 860146942 1250 860145692 860145703
    0x2815150b0f0415050c0d09050310140f060604030609060203010e01140a09020c07080a2a0e06010507060216150b03070308030f07180303050301032303070b09031b1e 72
    0x18040d040c1d050074241041000b28403603601e40c40c0c0e0020803000344010303001c1c400148120300d40c44071207485020000380b07482c0034507040031184a4440b49442c80c001d100d08980c6075141d50303d5030002d280541d40010780d0b18000050703c603005a4001034400c03498690310340204034480d4020350580c2c0c600c41c20074910340c1eaa1243c2191110b0f965080980040110f02c04100b42180c58010780484000a02540c4030305498482242c80c2c020f00d401c0c155850442140110380c0556888440c3c0701ca1381e00e0440705030740a03040030010a120003000d00558100b00d000580d2101381b001a9040da188080b0300a000c0740704105506054130600060561150850b25140d2415040e1400060032030449601c8800303207007141e0715511012424440181540240003080600001c4c1c0f241036654480510f12a448030340d107950444c2000c0e00020000712169908203924462091050000000d96130120741c03003c00f545807603694061250840c0641c4e030f039108460540309404a542c8101281c4034010742080e0303041400d00d024138546941e440303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 860148192 1250 860146942 860146957
    0x1b09030309090a0b06070c180506030706050304030207090e030a02120901020c04091406042301140c0c0c040e0f0f0a0308040b09010b060a0f0201050f06032815150b 72
    0x6038800c108141050a01c1c5070055440a01d030399000807000591800310301c16500100040f10740d000011700c20f000c040c080381389a20910b0351a80d400c20440c580320000c283e90325840d000d4070381802030100c009020140308020103805407180c039600340710904601d4840c51b501d40242912001600804807005480400381c001c0e5070605105038020300c440007105c411300c4001c0a0680c0240c40f900446a146406480c00300710003070041d0712481d1b004c28a6004915034954030000c1e50fa100d109039041c402c00d03452a100d00e114994104407230101550380c1d502d10b100d03220300d484031096800d50820308003590302400748000b00b140c000600500044d5015456640251a110b1925403001400304d9842000320f808248403640403980700320b40300300004580321444000340340364004603030b64030000d800150320851855080c0503164108100000c010f41c50b00b01100081d450301307000b0041c011842c42031028840400c070106200858640c0102000e842c05840461000103004d0650091054030310301c0f1000600d8015600071582e89 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 860149442 1250 860148192 860148199
    0x4022107060c080405031203011730092806020106051e010203160b1509130308070216080a0c05011b020f0d02060c060a0c03021204110a0e010b031b09 66
    0x311400c0240c161951403441c441a1400d4900780030105968404010740b001003100926aa80c69600d8110029907840314204101030a40094444449041440f0f1210061546840442600702c10500366810640180b403103050303000070180441d05450329000009412154440e0b130080c4040e44841080e03080c0c0e8054880d058121840c00100407402c6020340b56440c20301c1e0144103503071418035202c2800b4015120341c4015161040e801d01403000130b614a5a0008240308141c514013602e140140c1441c4035601059400340a00c80d1510005d81050700c00d202c80004840e030004490f0f1307060b8480c451960f6a901c0d01c1002c450010640d1000306003907004030410300145801503080a0390b241554248107003a8011002d854202d413402070000c0049c2e8a82000d0480000d600f4001d280c20300e01002c9540030f07110035100c10410b15104001200005100b958400d07070044d0000017510f6403050842c00710b040600c090348140ca00301000c000100d2102d02d0903001310b00422544918055181c00182c00003894032441075a680e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 860150692 1250 860149442 860149453
    0x12060306070320031b0a020d02010f060e0f0c09030f0a1214030106050c0102131d01060509180c0409140114300109021003060602100203040b04140f0114040221 70
    0x4215601c0000b164080303817003501c9042c240e081c001031291941101e900c034070158004c1100320110550901c00c1500c4181440c0062194600e850245014640090071800100c5280c0c0001020f0010341400c40d92500c1c0060120303008405200d000fa603e4903900d0a048410f074840360743e03184c24603114462843e521a20100c07034925692074840280da443d8000f4600b22802d54081c40000061402100280c004008545d100e003100f81010381c42c000d054505030861000c0c04400d02200820361941c0c034403152641c0030f1203000f01007500c84002d03100e914060385d8404840340341020410b041402052158604a4144850521203580003504000c180e1143d61520304180c9082443c0007c071030780d0230544c440c0d03006480000065005d0142c0204071403d446a83c1d03031000c46d8585100300301035070781045081842c1081100440c00d500340746d581c0001400c0040c001502c00702c0e603403c0c0d8501002c0280441510040740b40001c1148103030b88084010207201c201c80a920990f4500c1d001d10315803203903944000f41c1202074000b419 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 860151942 1250 860150692 860150741
    0x613050a08071d1e04150c0305070e04020f04080d200a05030909041b0807150c0f0206220e07030b060702030604330218060a02071202010e06120603060703 68
    0x8a1000d80106103440740000e600c4644000c2546182d4240a02d0003811b0001c400e800259148099403014900307401054a062304112072242d002c90030381e0b4900d02c121400b40c0e85821020307000e00c040c081d40d00501a02c0c0958244402110703040280d10000500003041200d520007048613964660007110406021030f0401c102158052520081d507640c0b281c42401800c0c62851203a024690312105501300361140da01c0303c102403050821400424105803403d00e4240100b42159880301900d5003c1800240519408901640a00c4454405440445c0401c4407060100d540700640b40c03000806440c07000c04030386403a00046081c2025421213088540182c01009a0b44850765400c01190b650320310310910001a061628481001c1c07440071035460741004d00075841d0941c103c2e05d0060000860f4803544501c40c00c000c1e0306540c5802044413003c4400c6810401c3c490042400103a035681380d140a034945c0018001805010380088480003030148105404841c890703500c00600760115806c030030042c07421451299861 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 860153192 1250 860151942 860151989
    0x14070b04030503060a091410080109081e22051302040b1606180309090506010c020d1502071203051501030608070e04050a02060c1b0603010f14010306050613050a0807 73
    0x450700808050310306444199248486c0c01141c4996070480d030344c91100ca05001140e40d00b002d0300005840e41800800c12210155101500b9108240d4452504a0405219040100300f074040e142c500c801c41000c004070000c0d41e01d05030b800d401076005040c440c00030303884914514485032090303d040d981121a2a031400480503140400e07681904c608944494950501c540360b4148220110111407194035442c142d5030420300151b0580750010640360400c01c10483c3e400160b0390700c28004190759004a946862100d0180003000603100e901000307030204c40c0f0801400c0b9040d9041c0d00c0203100740c2c03018002400200c10407004606951701886130030f10039480018288401440ca800a580140c46002196a0f02d0b005501068083e002400741981d00d80003008440700304500b481e24032036940c4084540518541c140004c050f41e20b4014000e0040c2e10050020300399443c0d0003a4003040241c03000a052944074070071743d00039102610150181500980c110040000d44920025895003900c11642104c0c480752060500c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 860154442 1250 860153192 860153197
    0x9060a1b030b04110f0903010605030f03090607061b170f1b091815030f03030c03010311030a020a0b13062d05121311010c0c03080a0c0c08010c14070b040305 69
    0x30341e58404d94a00389590300549400c004c10701c00e82d503400220317101d1b96164101801c41d00c2551080d8041c0d0885211044510b0000c812591034a1045a5540e141e0546d0300740310000308125030f12881004018040010aa9081640038001d0608204268055504d2103045000c020041d90111414075050040c4001d6070455409040501c4015013129881c10710800301c2030756440203403200b0580b141981c00e5805036017001e102d82103050091500542c0396092010b40e10b03103903100511000d0308443c189040044941e40c14003040e081550000c120300b400c95107491100002c0da1103402900010424071800040881c050440003500c28041540e80c0d8200300c11660b8183c41d803138041c81850030000c0070440000101614008203000d000c480c1c2110307003800c6042c039080c0002500d090361241400b451940050010702500244030035281c1c880f11280d2240320411043e40c102d80c03e40c80051000703030b240d2000300350014158001450345005540d1a22014040312070030340c0c10700c07940c40040c0074168080c00040110303024000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 860155692 1250 860154442 860154461
    0x2010210020a03150b04051503070e0904021c03030e0d0e0102150a0213060c0203011107050319020f03040e0907091b030b0310050a090311010c050a18030b0f09060a1b03 74
    0x43c00b2400c0a840512160000020b8000c41800140801c041c4420f0a05940c0d40881040c4101c0341441e60404801c01340c140015005d6603441103007408005030440d120509004114080880882c2e40486140f030090064000400030060724483c003d45009800d01c01c001d08500800c0603000303840c8a001156000c20039a00081c852a842502041246190660b4120f104000c118582d1400b101070207d204243c2035403801c0c044484018414401d03000810004401c640c010f410b03001010202280e04d50007641001c0b2034018030b00190001040024524020900151098505006880001fa203e411410440380d1340c14129000c80d0204000b21070140c0240c1c0447d040d546c00408031a1000710560901058910489030600b21a40741c2d00060b0402d07801074205140490302100034000c2c000325406c0289107000b07803540001049204180c04088041c2c0040311000341d608000709038803c1ca0700c003620700d14641e0241c0303c6118500c16000043c10b0034074144610301150502840788951541a030204130081c001081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 860156942 1250 860155692 860155697
    0x902030a09114e030a0806040207110105030a0f0f021c2a0203070c03110f030f0d030b0406171e03070b0601050d15092906040306022802030909070c02010210020a 71
    0x2040900d62001c000105034860f0228000e50b5a03d65600d4006e00400d00540b44501960061080e200010b400e0400c20030000b00a01e0078903200d5488440d4100030303001d00390f14000d0300c1d860300342922440d41c0d1503001806082031801c45040603403502071011040703803200a0200c54a0070f86210070014292076075001c010040441c41128244240740c0c641440055241d881111100d0070504a101e450822519681e070004040b00940380740d14201807215200d44d20b1488010405559506d84a041e6446911000c060702040715203c50340b80c1082d03101640d405011000c0e62241c41d10705070521074000c00104980100b41e0000015a0b6501d401006450a4112011402040d174588240964601c000d408201c02050407210201e00140c644a81865415118480403542810036075181010386a00e812030302101d0b03000d100140d45540850302d00a011140032500e21040e280010200d80e1f056001010340b06002c0201d55022443e1960601904c040c80c1102c030003070141c1c222041c0c4003400c040e264054076000602d070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 860158192 1250 860156942 860157049
    0x1e0703020307060e1b0303160303050c04080a05030301030314030408040b0d0f0207050c090109020c071a0702030604121b1a04081e030a0c05090a090207020a0902030a0911 75
    0x960f1400c00340c0d401101d41c0e441543c86854004001d4002254808900b4000d6003d145480222010a4805000402c1c0030302415250008240002c141c5401c030340041011405403a00008503150035902c9038801e1000b680001d8401d18440300500440045900032a03005407000d2806160280b4000c0c9504a440c030f18004d00e58030414400100058001413904600c1940500754095603201004680e5006811064500340b050102e00c1400000094181c2503800303424036054814060000e0008a01c980400250580a10b000348410008042c6072b003480d019070354440c05040160340c3c80e59002e6425a12000d05419000700c2c0784800c3c030540301e00e000c0d0040c7c060044207181c0034000e0408081d5242c060410415214000f00300074400f04188550004030149103400307440c040d100f10003d50f41420303038007550b4a81c6500046100c1156209041038004210081040d512842c1001c5680c2c010311100b03c05484416103501c41540520349800b26210400030f01102130000ca82820f00315000c2a9444803401300542031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 860159442 1250 860158192 860158207
    0x7051c09080711040507080907060311071a0709120309030f020d020307180b0f1f050c060708091e030f1b03120403021c080c0c1501090b040c02031e07030203 69
    0x2541c0042501074060403103040884944014041210401403504040003c01341c03d02000200100d40780c4125012841e001c940070014580e1125181b003004001443c2055951291003002c0c80c02c10094403c2400d61142c00289666003091a07041000100090005100301020b1001508110030016240d001a021410b5420580c1c0400d10f00000c540000610822298110f1210300c4540511000c014060b55030a003036a0240c000b00d100c11981501c283d02c9001040600010640310b103060b02c0c1003085c0a0201d5007503040002c0081c12115054915007905c0c003440c52103004a0301c03070700c01c41c001d00841003005600d40b5010b0107004442ea0080c5136424040034032488025044181040a042d4540c01c07210300303094a06281c6406490728202007590002c11100445201c903da412000c0b02d5131000820160070f03910080500c900341890569403210450300600c02c00464810320320342c4aa9503881080d02c042040407120802030b6521f0090040480f6a404400c00e0f0303071846161a00500959071190045900f01001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 860160692 1250 860159442 860159453
    0x7090f1a300604060f03020d0201140c0307030905120d090b16060f0c2601030b060f12070312020723033a030e060406052a120108010507051c09 63
    0x3008691511040701d00900002c1d00c2d00d48540002070612001403001c240c5103070301080b038840800c00040c0c140141a40000c101c0d11505040300c04000b03102055030394402c0503160241481040f030107a54055003010904072588080000c0c040c4000100f038a4184105190101191181e441200c0620f035a126003070185000030f1040c018254268061040440d5101088200405212100f070310b003031480121005c0700c100c0c40000140300707041d40c2c0c2108120510390b55010224000c00704492079150031881c0040312009000e00481c52105480c440d4400380140f6540e00d00c201e0f60303200d86000d5880310241d2203100da0388090702c50800c41e610744000341c2501c81d0840808505107480c03c4884890346140209800e4020382503400d81c070200441124201003040703070315100205a945800810017443c141d82d603008628541108075400c41d50358494140081e8440740362806400790340245000c6000010030380000314886806001c2e41d80701d4841c699520b4105040030075101c03551417140c0340c000c3c0380d9a42d581d81d0001290 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 860161942 1250 860160692 860160757
    0x2330705010209100c021e06040b0313050d050306030c130905010c1206090204142e020c04050f061f030b09070309030e040908221d07090f1a 62
    0x3400340c0001a01c030035000b400e02410603d245004403c1214299400d0016920394181440b1320484503075004e0551000f4002c1015482103421104d07407050007000f008602000745410364002d03485001550038403024600c081e40e40d0301003035901da517160300240b26500003070070710aa0100002e40180303404030340c00007140c49503030031160324800450018034480346192881906029107070041244140451a0518040003c030411401c41d111314032a50581c03a43d00411444200c124100500c2c1c05440388601c0301c07440d0702039a14907120a81600450030840020100420002401e11901c00a00034845031091070b001010199803411f90201803581c3c40c5032111850716804c110900c100a152000192050355017000340001190035006e0f0f104a003001034010002c0d41070015a1600340c40c5810810511004030303044c10000740070340c100300a242401c00c11071405080303c0360b0f02c44c0281c0d49510b40000c0b02e5224000d510440e1003600950b00d26111507403446942c1c3e05014000c06001c203110b801d042e1a94420103010300c2d40c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 860163192 1250 860161942 860161957
    0x4020f04170d11060f040510050c180a0b1e160503030a2910090b030f100812071b0305030309010c0e010521100302090f0406050a0203040233 62
    0x107000845980a1001e04204064407800c41d800d062000200c140e50a035a2088020b260b0004c19105501060410900f0080039016100031a001e01c407501e82141d03d01d00c26048086824071000b1641549006810416168801d4540c00703c900e0380303010b28040720540c040e130341a20007a24044003000070100c040c60458110308003e12844c00346a41c0d08001c02c0c0b00064620482d10113052081d030b1074484030b23090301c0b1204902460400703592075007048054800c281c501140540c4000700541000003048140d45068030300c584103900b901401002607440d808041e517504140c050b00b0300140c408020001c0400c90f8140c08612070002c40140f10078840d00d90365801c0c110742044e00d03c582669110318129103019042500c00c41c4040081c41d01e5410321a03080e107080030080341d2400800342d500300d107008600d1800d5420035850144d80c01500b03200b081e041142c06148144012035040c0c078114a0000072503003881007402181e001d1a0020050382c429154840c44e08030407045803007021124014000020103009091000e808403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 860164442 1250 860163192 860163209
    0x10c02043314041b08040303110d061d060901090f0b06070f03030e0105060d0201030e0c0d0503070b070504030f0210020a051b1504030f1b09110406271404020f04 71
    0x21580b4001009000401032002a4070850402c00c001000210130704107a0032221051400d0803030b03919241021303001880302c20254002031000103004090341c0300301d801548c1258040c3c0003140341c18901d11003098413128180caa859010009100400c03401619400520141d00d00020008207032210350000354040d8005141129041c1c0313142c0c10389041c150903109055080b40c4a100921803890990f0015842e441c560b40000e041c1540c0315030700c0c003010008011441c2d00e0000504a004803a641c0d04105540b80c011344401c441c117a0407040050440c61080042c0e90840f0341c0104503104102050b4200200c410504005a00f14490216001d020440800c154824801303001c984842d049a440103204038500b00e000f103440030020401c0200006422030072a450440d40007000d541448001c0307102e407035400c04203500a050f0542000c242c580c00b00380101c000e204030b40c9036494103440000d81d007031503d00800c00310404480680d80000c0405c050040c41c0c0c0c0c042c0200e0b200610052401c6c50500509850ba040754102441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 860165692 1250 860164442 860164541
    0x11d04180218070e0d1a091e010c050403141f0e010b060f0306040c0c050609070e0114030a08131a040608070531030f05012702010c0204 60
    0x29802d0051410380507000c207200041451811400c09000001034505503802610102011000c0c098a0003150400040030300d600d0100381081e10040c0d6461460303c0c00004e5013003030f80d044070104100522400c0d0b040604c90302c0d103904107842d5450b4801e2600b0380c90801d0b07040f4002c08000070700c2c05864481d40c8a07041c0c240240003038481c108103801805c480704100c06500840041000301100018402a268005003c035008502d031084a141110b00c1814504020400e0dc100780c24030484581c082103000540b104900d00200c1b81e0307610390940f10840c0004041a400d90040343c4400041110880240004082c003180c14074556038030384902c00718001d80d0512401c882000b14091103050ba01205107a000070080c9403031410150b10a007079040c0e07801180c40f83c1401c070301c40302c8040600810400b2040d004640028a00c10a41f205051682c00303480304800c10b840c210386840c000c4403180300e450318001e940c40e010f95440710074400c03e6087c4070040002c0310a030100e0503001d1124045030f1403000040c29042840c80003051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 860166942 1250 860165692 860165741
    0xf071e0e070f11010c05040302060d0e1504021008060105030402010c11030d0c051c08010902090406030609080c120a140c070312050c060105010e06160204090606090603140703030e011d04 82
    0x2040c0d0b51040c0c4180b00140d045c00d0500c40316075802000d641c00c0c2d9404540362076840e551100c9144c02400d00e01005c004500501003c08144000c800ca481d10440c003c0c1d440b0984540c40660840fa414012981b00e4003064051002c00e015510440b15004c0c4184680e6180e070005660704002841d00c2202e484207000901c482448504101c01400105840428004d40000080746800050480785050050b03080311640032443d0400c507a203030381101c3d00071904050100b14001d8141040140b90780701490504552064000e07003100118050119a0047c1c22540c9500034202c0c3e0841c0c20105074009400d4040300d209484022001c900d00340511000303201203844e043c0c1da42c04c000031080d08080c0c0c1640028180300f0300101e0000c3c0d82d203451044480d40c00c88802c040c1e91803491440060000d01caa881c0144c446450810301140500701c40e800081030741d0040e44206231740d1000c100a01c0d540c205c103000003800100d1805004600754021903402000c000030300e202e0f588065256000c10111400b41d0007103c0003c45c1080d152 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 860168192 1250 860166942 860166947
    0x90e0a05070f060207170604080c03120112060e0606031009050111030c040602121c0f0f050c130e060f0405060a0308070302011505060a0807050f040302130f0c020f071e0e070f 77
    0x685c014203902039881950712103c0794054482c00000c101900038070780058040714a1500b402121341400000442d10407558440b007006161401c01c010440f02ca914010b010305c50808006405c2c0e100394401801081c0a1514801000c0546520f0400701c0315036486044003a0030300c5064024620528030254407540301c0345050402407a10f11070107184611440300b0032000361000d041029091030984400400b250080490503040000c1542c2c1a80240311890141802254203420f80245840d100540c0e030f42781c41d50380b528071100030b510040c0d800951000c00c0059440e040d040940010385d00c010020030b250801a0761f0707120450305512020080700140d641d002012516544102d5442c040c12050314090306103c1c405a003d0181c1c0b20283c40350040c494040741200c0041e40a00413940a1940581201c1c801940058040d001d000710050200c1c0d10303410301a00480b82480018145840c1000c0740c000d15800b07151072550794041c2108021000c00e05180d40003c503809907070340d8050f8052103090b82e80a80c034141c6560300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 860169442 1250 860168192 860168203
    0x110a170702030703082503020c040c051909030302011a0f1e150919080a060b0604051203040305010f0531381902160609030c0614010f090e0a05070f0602 67
    0x41d5206c0c0980306a400c08241d0005d04500c052105072000120210301c884103581c58040c3e400d9645800f00607922000245903c40e03012811a8071130f40003400400c065941c3d2070f45404420016030340050148100351480d2418082f00d40c000482554105403d0b01000c001c08e01ca425240d03000034240d5000108100d031810500c211244000c0c010f00404a03041c14074241c0d6448400a0802412407601c405c1130000c01d503148000c40380104401400c40090303034400380e001038598010303102c2900e0715440d190b1090a000c03464001c0510400210490040b00400c2d82000310320345e08400400c1100c8091340000340009030014400d070074002d0000c031381e14024289000c0c02148140c1120101c1501c586800c1c14072668080000b80075440440e000c0000d0784072820a040a1300e080c481c000c01415550500349244140368008000c407003014001c0c0740501c0b0107581e00ca01014850420310a4600641911204128510055200301428820007007660003000890311703071506c1d090744c0350001241300050303a00c10403216404010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 860170692 1250 860169442 860169487
    0x20a0b1b1f02181915080c0d0515061605100605010c0b0a200c0607020f07120807050a140d0512060108070309020916020f010e0601051207240906110a17070203070308 73
    0x7003910790740c035200700380e1501c9005034503504040031380300c80114902000040350403032b02c5040500810b07111590285000030314540341400340ea550180742c6488042107018040e803c19107006031a55141d8080c00c2d51442d40e0b13070705e0092002c80da41d80d40e050700c0c201d500101080f03694401189102e00d03403150310b050341190072310308042c0c942e1040d503020000d4101c840340c0c007040d107904580c58640d2403800e224072401c00760b6107072044210081403400791001d0001007101c2a0300c0d20388003140700c1c03048560aa074000800d0781c3c40d110794100441d20451440000b0020344c030030010507600010501d80441c1440c010b901042c2500c3c016980f40040140800b8041000c42c0d04000f80524103004900a00546c20707a80f800c19200d107018040c0d103006802d64152480e81c21010040039000700051011a0000e03108440e6113088180a01944e00005940c504001081840744d0580c10122a480020300405021680c1c0c00b0803a0a070112100c40940040c0201300c0542d5050042c2c1c401140510302603540c81c10b41080c0e100c0c4020b030a03407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 860171942 1250 860170692 860170697
    0x70606050616061d030c070602060c0304030c1e081602090703060506040506220f0f0512100b0f031501050910060906110a020a0b1b1f02181915 63
    0x11200c1100d084082e03001c1d40d412000000b40c0c5684241000a0203c0700c2150709a40d110014200e1b2802c08001414800c540c115400d0300c0c0641c480342d0301d90b407480c40255005000030f480c0001240c040380d010b001c03140e00d426034080c86031710500030b90b0b540ca1055001845a0559080c0c0711591030250f0410000940d0b202c80c052a00300522810040010064041c9005890140700c0100b0311500e07140300001200c050b0070340301108800713450341c688804d04090f51a0090181041020000090600b0249004081e45c0d0540c8060141290b64180b900010090319140c1c950105000044c1c000f180c609111070f491032100318807a4078042d03040c00c043c06401c02c00500101c04015024404010140e0300071900402d5400c02c0c50f00b2081711150015082c85c0c41460100654022460038000844a0340000240b0081c80e0007444c00001d103907521002ca8881e4401c95030100c60801c0c041d009100030942d0f0740144103021a04202c091810760307034004103070300b0710058a041c0007000d01e001050080c2e42c49807416085821451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 860173192 1250 860171942 860171947
    0x50f221517060402032206110f040819020f011d09010b0901020609030f0319020f040b0318070807061101061701090510020910032307050316110c01110712080706060506 74
    0x1803500d0020383d80682410800c01d01c81b40d01c100c204030f85a00020a00321041d00102c0c3c071415544030301c1030071754014400c1005902c18141004a034502000e9940600d40e0010320460051701881c00640320445106500803c60600c200c0054096403000c170428083c0100361516601c1317072528000641307802d00103010265a54401e10401c800c22003600e0803258042d102411400c1c040c03445c5c0e50094041c1c000e40603e610f80001c04200424802d41d210b026620460946444020415800301c0d403075114041809409a6600040360500400340030b4810340403070040d0300b000050340c26a41c0400c4142c4d45190814016165140d80d170f0030043c40404c100194008100c0b120443c81d2108007070001c1c4541d91034401c82001d154841e02030110002c044810175482482e2402072400360700d41504020003913402102c81d06060244180041c0304288a0081b511000c86490002c1944581c44801035030302000d10200707004107205020000c24041144031003807805520862040d512802c252515406403007898214a010784002d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 860174442 1250 860173192 860173201
    0x105040c14030c09010c0507121e0b06040b06120f060f10120f0e0a24060b0403060209030f16090507031815110a0e0a06050f22151706040203 62
    0x6410031203422800703514043e95618503090060755902c0358208094400d010f409400507009400390000ea1f8000c0c40358001030005240680d244000380754041002c0d089241440020390f4604107584103000c1c440c801024141014110000340d031325060700f01d0b0041c81417a80c0c0c005004031400e002c00c2c10300445c68101c8200041200c01000108810241d48100e0b07115511440f403203080100aa01c080500c1c4480b07001e5840000c0281000d2400020707450300c0795145841c00d0041054144e551142c00259070344480058901440e54454001a410076883d81d60715000790050400412410008581d9594031441301240c0949041c00350012920b0052004060500b0300702180141e041d810070030143c0991090000b00c1d6200c0e45107501000f80200030720705070700c14800030314045003a4000c41d5040b6126001c0b20f51400782a02e0f11804c607868003c0903d02e1500c1d400c00e01c105080c080222000b80070401c2d9840f445c0d0400741c0c2c3d402d02e0001d407412200482d404900303441090350b50740341e08078a296401582a03801394694140f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 860175692 1250 860174442 860174477
    0xa050d050a0308060112050114030601080f07030f020406080f0d02150f0103030c030908120d0e0705010f05070812040f02030105130c1206020c070311011b02010c0809041e050105040c 80
    0xc81d800d0003001c000c034560008116078000d1056514400040724204010f6031104110180d220901d60614441e2048500000da40800082d10f6841140e0308400b400e405032031540c0d40141e48010b1402283e02c030b0788813940070a503082d003040032141201059005024080b80000c0180c145a2070201c9101c1030410030007042070140000050a0440c0d900d8500a400b41c611420210398460a40c2c000c140d5602031514000350801c3d082004d0041462400c0c41000403107003c3c00e40c1d40d0713100e1440c42910b01180c1e01c0a1034490450180e000b5040c1c090090320b80d0342c6050748514541210350713401c03102140e44003094081c003001e508091080d5a48441544d04c829164500707901d44800c521580e119101e00c1c035000541100070031007950103840c102e8003c0c2c4202c501c0703282c480c07400749011005401030f0707400038218416440700070a40c030751114222a010303180d2040028054503030900941c0126001c5030400cbc0c8840c01d0480442140001d180ca1103140030001a095040c00c0c10081a541181b05110806c15460241488481c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 860176942 1250 860175692 860175703
    0x12050604030507030c0b2401020a0b060634150e1c0e041503143009030a06090c050109050f0f120312092b0f02010b040e0c0a050d05 58
    0x150141442d54580d09545400c40f03800b07a101034010310030001c0c00140005200310011041200c0c504041110325200a2401280c5c0c4200d00034014180c1c17401c05012844ca41442c030003c08c1c0b400485203240b1444041e48903411848800c00140710050705560a80324240803404a8240e420040c1d80800d100501e0948403941e980d0118101c034014030791908011402c1e05001d0549000c9800c0302800c24880c05002c801c1c2d044802d0342c00e101c00c3c1c4040c0f04008501e45e0325000810140e00740c1c803920409103013242020325100d40022210030031541240d000c212201d000d54040007840070081c898030f40810b1281c060f20b025038000300140d000c0380c10b00100043c00d00840d0f0325800c4180140c28103a0b004500909902c00041c0c4056001c01c02a40c40d010000e00626503901c2c1c11201485050a10100c0f08009070780c0b0441f40300e01c1862005c2c207080801c100402d080b4036200b16801c118041c2980300119201d000540010f08450345400d40b2141d035807151040480385c1c00c20011100003000e08035248070b151b40603074444a0b120b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 860178192 1250 860176942 860176951
    0x60d0b0703110903010e01051e074a0f010305010f03020f031504031806020c0d12120f060e0603060c07080a05070f1103210f0c0a050f0c0901120506 65
    0x50300c400c0041d0000c44140180c0f0a90712000f0003d000d0b016100d80325500904050707400c409000300c2e040c00c40311001c0000c04480e00904541e0b4845414910b801e1091200122800300028102c402101c1145034500c441c81d00145550344554416000e8108000c10181d504000900d505050400300100908006c045900f802c894065070010f50407078582000904191032008540f41100e2040284001d05600560901100302c403401c650100c541c60b07410a99030b07408285032941d44403a0030b484440c00559100310b8038142180c1030034103504c074950400c64101030341d502c104405a62560341c0c60412400344218099a000142074002d000e25040149000311340d8810014082c181210014020550074410401c555070540c01847d03c0030030044503d040710b070110b05200068070910a00c08040180a40220b00504545600e103559240040007013104040307800000d40090b590080140000c0401c2d0305002628544d80c513400030b420500414000c0010303250042c1c00c100302c03c000451960700010700004a60385c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 860179442 1250 860178192 860178197
    0x30504030e040b0a170d0909090b1801090b0103030f021b0d0f0c0b040e1e072c15120106020f10270606060f020c010e090402011407050601050405060d0b07 68
    0x6030783c05440414003003541a40071a0800c204042c00300d43c00d56000ca41c10301c0c000d495a5695881c40d984906100a40e800c902d005003003034060002207a01c405050700548482c0c2da4540000c1401c980985410840d50426031065010031000c070b04d43d642c010b605010305a54400d4806201ea41e11044002244440c6103103480240050040c0e41c0702c000340700c2000a03c600401c80d8484070790356a070311804421280a41901c041424540703415030440c84181980e0070500c644029512000d20310712040724440140398408040d0f5090310498407003215501c0e48021109812b02d4080d010750340781c03500590034000f140140c0c888001c5401031024028513040114034000610002c038004502748001d05541c0100341c0c080c80e034103103024008201d501304000158000008503489130b15141c480040010099845103001e0050500040c811841c68180b850403038186a0407074010300d4900d12110300d035000094070340d20062041c0c4065021600400c124546401501e0340290140c50380041d1000f981d50740802c40c000582034500317 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860180692 1250 860179442 860179451
    0x9130506042918101a0108060f0301020705062e090f0b0907030f060602061009020309010605121606090e0c0d090203030f0a17010b031605070602031e07030504030e04 73
    0x8190b5400700400140751070851010803401c0510f42a07000c06501c208415050290b1008244ea054491043d52070841c103490591402400040045421910084c85640d010300d80031082484c544091010301050b500c22b070000e013007034140310f6620904a419414403214131f011090328200410001e41541c0c08490140b2008900c4c522111400d0700500000c0c0545a003110015081210499248d000800003e0011404125071511404120388504040700d1400481c048c0390410041c0d10015401180d004696800000f00c882d21040050001030f043c85041d40c140e40007040e40501c00c050100b80307200801c868285241514a4844113006050008021411005012800302c0d000ba1082d04a0f415840e40107056070ba903645d41c5a1482c1458104070381307e40c00188405018011409003010b62410780d842c04980c0d0f41103680703c0c2210140340219186040c00c0200a1142a0000d0698006940504410311a501502000a058000d58800246031700100350a040501c804203030031189a6000080a031400304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860181942 1250 860180692 860180723
    0x30906052809030308090c0114071502070c0305190f0f230106141504090216080c0102030402040c020318011412010b130807080c010503070311030f01050913050604 72
    0x40002454902001501c0c4020200144841e80080c200e41a24841d484242c041e880b2080055901c0caa640c10301070102c0e02e000c01c0780025621100240c18401d10508882d071100b500000054240d1700a00011035458090b42c43c28010440103100242d071011804442c07955406807030302c8040b03200241010141403007000c4100c4405104c10f004001d503a11000e081c090f0620302072400c080c3c2c024400c41c17059580950310070350390620790319200240304000503030300d10076508003810801c0d650000d511040281c0d080b125280c0281e27000460020191104204805c00180c403072034180188000e03100d4550b0b08034115042007040d44490001c68a03010011042032800104450340c01015242901c0342500d800d0032101103000014180701080000c082841240f41800a030301d56980d07c40b941d6103528001c1900d140c010320100d481d1f0303511a8010310b034444a9450003083d09624800012980c0e401038908400d80070881e401444a400d200d210031f038015002c880c021002105544405c2c0d241c19001d00000d00c3c020070f564004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860183192 1250 860181942 860181967
    0x60a09080c01022106010207030c0e100510020a0201031a2805030a0501061d060d03080703021c0905011103090c0d060b0405011205070506040605180103061a09010806060703090605 79
    0x41d600d00541c00001c55071008000000c4002c40c29081c1c0c0714140d03100700400030b03d095202184c4541102d80c0900b0700080760741820600c4490650041c20380380c000600c0380d8000341c0365803900819212072180d03401401c031f04031702390000406503842c04120351086105600150390300e4664031001003242080f42d106218080d66454503a00c104100c0c0d20840c0c0c90b2140c0700180d01071040652040c1c0490b100003004c82480c10b15a5801c6801620842e503065006280000443c046400b1b19039596204d600c40c917005240405c0ba00c00c5080745134805042e0001d050b500d90352481000024803170200741901c6114440c0c29840d0038031000c1e07603440003e040c090145a071498260100820341d003045c40c3d01e4400601c2804150785440032100da01d62903110a070f40f41d21030340300c0c0090b250500c481110182e034080ea48440c42c00700740303d9a614043c910846180d040668400000440c07440280340412000300c812074103a552900c0b240010040d80004d465035200301c00c208203880001ea04880000120303089400c6c00740c2c6618441155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860184442 1250 860183192 860183197
    0xc0f010612050d093203010c030f0b0d02030307020105130b030a06090524010f0c020a091b0e06090f0f090907080106171c0c0c0b0307110d0806241201140603040302060a0908 76
    0x4031703609507080c031311560440ca8060300084580c0c889102c08000688005080000300c01030f200000e9059001003043c007015511442c000d0030303078038200040c8105150380c1c1d81446809510880b0720b00840d542e035080c10b0101003e5030044680210030101c48000720070241000b0105081c000f481c450501050f40ca1780d0040c20b004e6500084029001031020389265a41c0540d031000d486805070550182c8545c80044004500885007800903503400381c80366041036411401c4c49607046100c200b1035801040c400b24003010ba5070b205030040c42141520081c0207010b05d054451425514a40c001814241411020703c070102c000169104002405c40b0b803000c0f0072101c0d140291030300d812010001e051040940d80106810b80042c2c000c0d03001e0f8030503030b803205442a500f44605488041301d000c1c1100040e11040800d0325464021a103c2d103200d410014001511440203007108213074404080b060319810403100400540307000841030742444d80190380c07070fa1940ca8590340080d110b07440206441c04071980c5104000c00d02150505 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860185692 1250 860184442 860184539
    0x90504050907170703020a15080402101106150a210b07031b0e0f1c0209060f13050108191a09011d010207021201020a090302060c0f010612050d09 64
    0x100603c0ca4100c07000c55a180c4000b404182e00802c0b0300400000c64041000404000100d00d680f01c0c1d042d500c4550800003418a4600c00000300514440d403c84052021303c60715006e41c494260480c040c40791a410300c207055007a40d204110301c404045480c0161403142040a01c0c807540044541e60a40d603114042e130041241c1480c54040030881109604005c0d00321140030609482214840384282c11141041011100344400c4926401c40351108070042c01c03c50b901030f0304003000030f1030381c189840c0c84030214002c0c104940711075801a840d08010400c2420512603031074481c83c658003840c11110780740c032000c24503007000d80c801c0c40c01109a0f0004179040001e60000c41e54004005c02c40c1c80343da000e600594040e4200d0715003071384148001c0400c00010501442203400901598a8034240d0500e19000c00105400c51069464140960140c0703c2c0420028441c140107455600d0030654045000e003041d5180c42c3c4581210001e02440280c00c0c040b90a4200000e00d80c0104403104450044403005100c1c0082100f82 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860186942 1250 860185692 860185709
    0x30c0612130516090f02070c1e0b3f1f080d03020406120905070504090f060f20042102032d150c030604050c16080a091401090504050907 60
    0x1c10b903140d20500240700022107240c018144045800c0c44803000891060b0500208007160070b023400c000708000006101c100201c1c0c05029071000755100348201466002142203043e54500103199455034004451138031040054400081401c1030f00c499002c800000a4030b5800d03450110308600c2c861500c41104c84000d003404505171494106500b0026002c1d40080c0030f14008102e442e0f802980780c500b03502c50602c801c1d4002d401089034926000c1880020401144203443c0740010034001c101084041c050f51101131050714001a100c00080c03800ca60b41480008075031341c40c40040108200c0e03040d4218560500f0041407401c1c0e1480b912501c00603107441c448920240010b4101c408410060440c030010000c00140101030340c1d501403d0300141444080f08803080013080c001070010035030302c0c10309910441e40b02d0f418444017454480320807402c00704540c08100c1159410400580400e0a56010180d41e00900c800341c5022602c0002100181000d20b040c0101406a9074900024003a50010801e001c020900c18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860188192 1250 860186942 860186953
    0xd0e070612060e0a0e0a1203020703080105190924030822080c041a18090d030221040201030e030c06041b080c040f06050411041a030105030d0c05030d1406030705030c06121305 77
    0x107c40c081c029410101066021602c618000901810321524801004000b40b181e00d01050800e800308004050200c1500c81854000035a042d0760990368030032001560040340c20b1b54803020048001100180442c029114400034143c04000c4c00c00005124140c0403011900030915210301c0048078181481107011651022851411110304100451003501941900043da6106110f01c40141c06a100350440d02c1c405d00030002c0c0035240d8003030345202c05400c03d20515020071107406001c281c0d480c40c0c03c0500b401e05070760801824042001101c902c90030358103209848040c03a541c0340850303080c0c0350751560781c000d8080c80d2103810705492200740390701090240200400400407841c2154074126250064055800340c0801d9400b00c1071428842001d80c0c2c100c0704010002e1104030f81401084440703250300e03841255a48000c0c0221605084a070107600c032002000300b8446850701e40503040500d404a6640828041d41211528460316210003080f80c1c0300510a002c40021341d03c1d400c0320070080c0e00110001030038500a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860189442 1250 860188192 860188223
    0x61a10050d0b1c110405090102131e0503030a02070602060105031b010c11130c17010e06120102040f06030516090812071505070302030f0a1806110d0e070612060e0a0e0a 74
    0x100c0d088002081005d850400403a075824082030f08030311498106114800350024200148070160706601d10100700200f00c5481556034001081c40c60304135801750300c00341e00700ba2414041160304000140c0104811002000c00c1c10500c43d0901c100101c0c070040604004c0900440d02c14020300ca40200062200581074203184001210034100400c82000b810f00021140c41c21041e0100f411806103041c1c40e5604020f041d0380d120354007081680c9030300010022080d50280000607511144900314002054151004901c515110000e0806422444000b00c14885444c900740040000010900903119065441554428480c00c0540002c071185500c0203c040c100030410982680c941c02440c041e882001011500c3d880343c1c20300c80165086680d90000d01400212410042645178000390f0342c00020048061130149411182410390b41101e03080345040e4000c01d010084903a0080e24000c40d06084182086064244174104565140213052108103c4e15168074281403407080c811412041e82c440c81c4e040c6800300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860190692 1250 860189442 860189453
    0x290316030e07081c1e03021c0608060126250b131403030f0909070909050f0f1e0a1d030703030603050c06030f190b0d061a10050d0b1c 59
    0x641300481c10342d01c0c21400800000714040c5250614504044800c1c0818030740214040b002500102124080e90138290001c40a0030504e1150401030100e40015280030340c103041d5207041d41803400f007803a400c103010b0307800814841030b01181400b1640d2008080c84070002c1c4071a00411904201c2d0041c8031040c80010b40000b1300c1481290380400c4402d003074040603920800c201010340724028a8060b80320143c0400100b050b13441c0501d84a940000076080000459490b5502c0030304845013110340041003031300741c014030103441401c0202580c00f404241181c005908403403c080100d03013010b805404103d40311600c0300b043d401c01c20b010580300800d080450340c0390041802c00802030041440151101d0055040303900003818080122131084410004180d0740ba06e86070292400d02c901c80b81c0d4200010350722051200c3c596074255060b02c51074001c660110700e07540b003140842c002c40182ca069510500040380300072003040d00f000540d00700e00768401c0700140384d11580020500100090600b0b406506211001394200308 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860191942 1250 860190692 860190703
    0x2010c080d14090f073605040b07020c090106020c0d06020d02131d1e06040e010606030209120705180702010605030102160b0708070503011505040503010510290316030e0708 76
    0x503240307002c0700d0b80d041d4084074150b2924540d0054002142103002010f10005154506e612801c89890300b4aa10b445001d010000301c032800d83e0110742e08038000e4244110190304010100c90800219030016041d45010000395546e0b800d1940c65000d40c1c0030001c4007003030110700e50559000641e0f40006540d20a00b403584114100540d000d28540c085000001c0305000303145402e00c501c10512000810315038a04200307070b0003001c0c0d0002c0040754011340301c0041d001e092500b0300490f40142071076100036856841360010420310320580c5000c01e519500c061070401c01a981c005c0001000c0c0c0300c60866031015198460704074098103d40e04400e07059800022090b024100300440312001d00d014170301c00085500d52070300486400704107071241c2d00011030600050000e610204284d5003c2a540c0c140646000d5461000c0390075900222041444070b10320a5040085464143c98403030140c3c000c0d0301e040074451110890119601014091080c07004869800d036500c180650b208494130420a070490708100da0355414207aa90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860193192 1250 860191942 860191951
    0x19050a080a0f110a0b13060e0d0906030605030f03090105030c1308030406090b0c0c06160b01031103300d0b03030d0e0d2f070f0f060206060f0102060402010c080d14 72
    0x500d41c900d00f1543e41038049040b00110350300800c848181c0d201d50500007800600c0400507500c039580e4941c00d203052001007014840d001116118600c000b40340000180c04c585507648598040e800c20341000301e4440000c0225900e410003420f04507144d448041040400d070142c01418204c40c04031f0312001c07403a203038000040c0084070407a54502040d11345405601c5054042e00d0f6403118103078004a170356079040c9000d02c0034008031084c41006206030003e035150b07503003018000c2c0c1c425600c404080d51412400d040c24050381c10001d500d1129001802011810107000f503c403c2862220b0034404580003509420540022110080007000c480c0c480b00c18280c3c203402003240110406043c4103044541d4190760107280020503040d540c034101c950410285d00c0c1c100031115078500b401010301801c4030204401c1c1d200d48801000d031026040b03c90f05035003481c1019182c0cd001900243c41400c0b0a144420540e0740000d80716440b41d820300c0d10ad07100b0350b454900314403240200c0c0d0050401c5401d1460384940c1c10300018025125 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860194442 1250 860193192 860193197
    0x1103070305060a0f06140d0303150b0309070512030f09060d110a03050906070909020705030f0a05071b14040b040912020a0b221211010612111219050a080a0f 69
    0x44c084c400d407050b0480f5440d124400345140c007500080e50500e0710001d89550301d4000c1c00d000c50000a00341040490ba0103641000781c4564011040c04448802049004041e11007560a016601d0b0540150399a0703014112500841000002d039081668941c60103a4281f503100c40403e01c4140e41c4420070081540211505100081c1b0308400180746c0403001409900829954540721241400c04074100041d501038002503842c0c0c4000c0110304081c0204070020102e072102d60743c42d251501001d1400d11001003410050f101844c20741c40083c80024250140784080e040119000030b18282e8410110f8040c20401c01c010340f1b00301c05045100c0c0125000314108802910550300c035480b07035480710320100000500000948981e00f400e02c01000003440086040703240b202074103220000740c0d180a42c26095580c0760308030b0410b40d007114002c142000f1004044080d048800c2f14034000ba010841545543e9003030007000084803031181c0c0003904c18442c040c4100a222074006150f03564550715103002510304007022508100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860195692 1250 860194442 860194451
    0xf050103060510050f0d020a0f030812010b09010909020d241d01140d020a03050d05071a07022107060e0d0831241a03120f03041103070305060a 63
    0x150543c000c1c0001058030002007500312010030050620020048030001281c00c41074150021501d030b91810700304001940b1a40c032003a90b039102e0314030009207214185d011001844007402403402c1a038212001d030080c0d4884c1c10740140c84525041d4202d014101152140c031815881a42d4a5824003090f402e01e41500c4510120384107850300311032440c1040070309202d02d01c01415075155580e00c914103007808000c200c0c0010032112450f91252100c0f0b00340554100600301003007000400d17604001d61081756040314645542c00301c40d21703e42140c01942320302c1c03010f071008999900201c0340c003c01500c20058612494000c1000c0082040e55111150b4a9071001c1c103000100d88440c0c000f4850700d0340084141840c10900b0b10340c03c05ca01902d013540c2128403100008840340e802ca2203052500c1c0d0203224141203080c026401c0803541d02001d680c000c104041c00c0c0561802500042407141070144080100c9144060307040002d540c0b40e6031802c2903404200c204030103680c1401a060000280100004e40f42d01600780c0400400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860196942 1250 860195692 860195701
    0x1d0c060d0f152405160c0f090e191227091521080a0314040501050402190617060607020a060c0303230103030c210903260909070c05010f0501030605 65
    0x10400f40c6039040310700020300400c1186206040324002614162103051000e0000380c841f55028031000300c54021010301c030b0b51400034002c5102c04024060700c0a031050301940e1104100d46401060f41c42c0c41940303c0c18803000d4020b2015101048d18131024481e4500709007284542c031902d81d4000f903e903480c00408503140c55a804a9078028001d403820100c049c1102c800e61450407596000c1164020364805814541d54031407c0140e2001a64042d00c118801c3c4000510340ca0148104048024283c21551441c0c6402c441800755580003407040840c9550461415820703603e00002400c180304588009420000c000700000740c5580010b1900c010500c69142031010700403c145101d507140403942e000c2d4801c1c2c225001000468001d0308014502405214007074500c0000403c42504210071076034210008590300001c1050003020020048030b03d004000c0b1b55409050b046010f13200b40144c5040074451100c1002246526000d2246030410302c2c2d01c0030003030041c11048403c00f0010b290912060300c0c01c40c1080d0009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860198192 1250 860196942 860196989
    0xb1e0405010801210b010b070510060b340f12053f0c09010f02060c04090b12070608010f05040213150c0206030411041d0c060d0f15 58
    0x2682036800607541c50225a20b80386018403481c40c1191075180c0442106000408641c0800959003c1c1c07160310340f4181c0c0d4030383d9454150300c0e040c0d103c036401602c0c0307240401c07e001c12040b18044620070255a42d041c0011540300d0b014844e14048048084d10041c000c800b00e10401040000a01c482c9000784011515580c12240594051142703048149107681c21a500c2c00803000d01e46e050b0055030f01e4415090405803088034194201f07000540e1907881c840340105484d120782d0b81c0100300c1015042c051003e80301d5820402e80c3ca8400340184c1c0624882c49031605100320320341d00c078992030b1301080584d8405c035a0b6281c2c3d5140040c0420740280a600c03401d011104012805044c11700031218004001840c0d102002d10b80911400c01a031809490310802c42121000c0006d039551402a5028034084c410030404030302030340d003000100c541301c80107000448100440c614440c82e000c659a0185841982c03042e83d035114005481009144400120001c40d161142504050b2642251401a985030001c0482038a003d108075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860199442 1250 860198192 860198197
    0x90103030c08070804051e030105060a0f1a070f0b01050a050f100311040b2722020c01110a02061e0c040504090206070c082103010501090303081e010b1e 67
    0x180104490751070010000b6000002090300d240561503140c20140ca50000075001c0010350004405a400502c0c101801d160a01c200d540000d01180c141101a1400650140015a0741300b8000b6032040310060211500d40001110400d903030100507805210214500b450450400307008113400385011030700c0070695080c079140703130101c00c0030040000c1030120b19404210058502031000030f441e1001480300060418404014020040b2503841680710100000c3d004102a44100302c030b1071062580407108100750ba00e400c0400c2410000e5480569248c214000c0c042c054050400700c880440d1002910001ca140e01164580c0292039108880f5208402812003405994040c1c4030009004001c00c81000b0031b00d030641c4441d42480c4003400700c9052030804d0710b85060894050340400140d400c0a40207000b01100403400381d490103900d024031800d6505003000207081601c9400010140114100404e040801c002240030f0040c9000050302a6903843d0f03c08824190803449145012554042e01c2694103001b400a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860200692 1250 860199442 860199449
    0x60b01050403082502030f0307050c0402030c040b0f0f07061e0e0303070f0e040204090501060f210b011107090e0d0801080a1e0602400603020309010e03190206060901 73
    0x4810382000c0f01002401356208150403c2c480070b0355840b40060050300c05100c1404404c5020020b55111103a80c00c04505103041d9030354080c4030b180b04200700312580100c0c00541e019600300010258a94001d6581549988100000406414004116001004626000f0504a448000d011800d4680c03030000030301920706803043d0387c403d6001400011011031240c05060100380075890182c4649001d100803404983c00703a00403581c100d0b150700040c803d20341c1000c017564010b8920700e00100300c0c05900442c005074042c0010244030300b40c0c5600c040001d907840352a50014240c00c100546407003569074031041c1d00402510b00a500c090107540c030701c04900c9000f00d40749412210b0aa0103840c030352410340d9940a00c0151243c01e03040042a410440002ca2000d2000c0e2400c551034400d88050010000c1003c400380d00800c1a15132006124501e413400000d04803005002c940445c2005604c90325200156800b42200011807103040c440070075480c5c2e4100f55818098030300080d603001c0d11025240d640034081c2c0c2c01824007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860201942 1250 860200692 860200703
    0xa0209040b0901180602071101020d0210051308161511160807120905090a0501081f0209060c16050603010506430c08060106020c0f0d02150403060b01050403 69
    0x10046049142082d5005a0500c0006a10b800241900468603200d0f40e05984281e40840d404040010440c0041c4001c5403d00007030143c1980c4400003503990004691f06120700e61200045014495810b001c1810310381c2c019203032503c1d00303015441c08070b482208240c10703210046046200c0812141c2c42c8643c48203030ec0400c02c41c0323140510800007110303508401c2c941191010000c12024000c603125255001d982549a507551700e120380307032000b00030011502174000d5240c1441c1c4001080240000207400b598640c15540d03e400c4a0b11450940e03009014084109420100001d0242e4101c04082044000068400095210700d6240c0f01031202c280402d00070290800301c1008240386000403041180b0042118943c3e52081c500700810190800c1e142c86150202c04903289580b80411039010500700c080c02507a40104140d61418600035a10185d001d401030050f181d4074a003940c61780712402140754858000e04000841012200c0e280000d5005210544a161920040b4000d540c03140e8200e2b4110ba4001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860203192 1250 860201942 860201959
    0x20306010c0303020c12041212051303060e0703210305090c030c190506070b1501020f06011a07060e0606120a030203030a0518060c2203020603010e04142b020a02 71
    0x140d030b0a03002135101c504c10a00d544101d00000c1c991045000040025003e544800301102d242032078003196841040b00e01d401800018000c20a5604081d00c0500c102c80c4c00140c0440d05000109a00341004915040901501d01c1060300d4110240703c6a00b402c503130101c5a404100c143d903101a19911401128030b019816004140c03044c0543c034105000068040d00c1c000c040c4000c0c2c1c0d036080000d21590092130b00301c0b10610f1000400a06902084101d160a002070002c0c1012400c41140142c4440050054450000c80320203195001c100082c02e607120380740d1028007040720708006142580d642d01c04649007481a21040d00b680c107801008516250003991540007142161901d0b00488003800c0010480c140c1c00701c0b007031108080040208149030043d004c900e24540d031880481341d00034a00c1524540c0401d00e4a00c184200b00607200e003021641128440e0707480a400392503038940700c1c0d0320b04038140d40c28800d403189041d44d49216040700300100c40c05a40b2142441002c5041900381e803244010039020f54480c001c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860204442 1250 860203192 860203217
    0xa0608070506044a01050907030911011101020909010314061008070b0a0c0f0303090c0504020a121805060f0708010e07020c0f01090f0f051801120809030c06042702030601 75
    0x203041606291004115404c440981450320008510ba02540b1150004a41401000a0f042518220341c00040c503250500120410303455554480041d040090304010204d813040301d11400a42c15100b001e240204161260759481c280400a6070980f10206a540100c9010640c40b24601400c001242c15403c00f400d88140b03016406011070b002001d244040c8844e45014038005002480080000c1c2c0c840c0e140002e61101608012540304415008140500d1040107120402e03500706201116060101c040418480c2c071226005a160f11010b40050251003400180310203d81f01c80703041c80c82050180d0300d01c819aa69052951441a42030382c01c1009a08152020320380760a00d1190342d04068010304140040030350301d414203c0d040d242c0b075011350811003044e0401d1140b440d06451604840e040c1c81411107165040c01e001c1d000d07418041c58020407a11001602500540b41440240380100004114035115640c1e041050002103410030300184200003d002c03062511130a00c251f0f0b00034030f81a07440d200c41d03590 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860205692 1250 860204442 860204489
    0x10e09010e09071502210f04030b041e030c1e0b0f1b1305180609071803050d0507120c0b06220203011508010b160222050a060807050604 60
    0x24148202c28083c050011543c10386010409242e0700145d4010083c42c0641c3c00c0c03443e801960050140800601080540c4002d008101070390300f600e410201800864446140c806944403101c01d20008403c0152098018942c00405180b0342500561003901c5491028891070015860300c8002000c0611a4002c2072135001440645a40b03c01c42034024003034445200b0160302550841303500301d10044140d0006011a0038070740c4007143c100e00d110740c80c9a0141000c800003600e10400800d00d100b00700e5100c0c500c0a1402841d8507503001150804160f500e00405154024810760250000f030305d00155002c070580c00c51b80b01d4140c00c1c102d690043c841d600c150700c4074410081d40b5541c1401c48400b107512501305c600b14a0140c07000354028884640b103c0d0805a03100c8024040b0748050340402c001e40028080310090301401c580306000c20358112040440000e00700c0214000c80c4050503401001d91420040140400556108030191503c2c03208580da100d07641c100300045803080c1d00030480440031a076002c031150300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860206942 1250 860205692 860205719
    0x1050307030b040807060f0507140f09010c030203040f09020a090e070801060e0d0605090309010305071e0c0f0b0a09110d05102d150e15090402060d0e010218010e0901 73
    0x20320a203211303894003003281c640809540794100c0d40d081455903481071001449d0481483d10070001d00d2198681481100343e28641c00c2d000329048541403000409103a02014401c0c0f00312009040440982443e00d502c42c12010300035004814032001080070550042000c800e01e00b92184102e1b210340e181600d5a00380982210b200422659440d04105440003130400516603028192189002000460311124a84001001d9540103071a00003030088000c00c1540c11341c40321011a112550307608103044614003d2400302a001c0c8403e1001e41110440d40500c0010602600110082e90140b142c803280184810f0401507540c548030801441c070303401070b0300c1e0240701d814641001c0041c50350032000505030114820f000c507001e18984408824181e2302d44101300703000421201e07a00500601c100d030340081d19000600c0c500300001d414055200d0000d58000404542c0c5810480320001ea000d1418007012000100c0341d03010750481d00a01e19064030010607400294030900c1c110550341c800400c2d0100d940d00c1c0501c0100a139 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860208192 1250 860206942 860206951
    0x8071a0423060d0c0314100609060c0804150203070c050a0b120612060403111605010818330f041e030309060c09061803241b03050601080106050301050307030b 70
    0x7040501c00607264040760302c650304c43c00510380c81c041524600805100b0203a02d00920360a40c01034100703018001d070361b4031a1007001a50002d0824041800319410f1200c2079010725130001c0502000c820000301201d03804806002900d11031091010156150030400c01610128020100c1c48002480b140d2182d203044d4000c1604140d0280c2b000d010102000240d9080c030b04102c0d026404900c50407070f480c810f040104154607041f03000e000c0c0b1b850b1060a060000305418000b40031082c500d4410420310094001c10b100128250050000c0000c030480c4000000060038071070700540310345240050000e58004050f01205104561010f2100a041105541010f02080f03411041d010540d48118000014480303218894041040b03032640058540761050040c00c416104640c60342c9140a40000c0000031001440211232494001c4210003010001d0808001001074902d80003417088500c0c1c1905103030390540e01c0b0a0041100f030781c030083c9580c0c8808050b12180300a10038150107510100341000070400341c0c0c030100d401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860209442 1250 860208192 860208199
    0x308090f06090d1b09090506070f05090d03090501120e0a030c03110106120b0601031422020607060509191119091406040e0d2705090108071a0423 64
    0x3805121000f00390b111100c0d02040702c085001c44030b0035050448002480c0001c0c243e0800a00c81c0c54802e40ea20394460344040c001074148441904200003041c0144e042d5200c404001d41b145420701500d00340100406518801c1501040041c42400700c203000300c1c0900907030002c0e22001400e0300c1d10507690881e14583e034004180c0422006040601c4403000a01941707004015500204100704d40a050601440300080d04580c14940780a000109215804c0c0c562507004501800a540301c902c0041c801d1500c95094070002d41c000e4001a003e000c00400e03a00c090b0050402d6011110040050074145011b4805000094030300411031000c985503240182d046000b007281345035491000c0c0d03540c0d012b020603910082c0070702c02200d084c0800c0080c81d04041c800c03107021082d5007004122108021601410045039050700402c141d00c1d5030808905074070109580e03401808040c007211155a51290346549a0007a0301400c5000c440010300c10b81d120400b082981c003174410b010583c3c6602110000358a1200300403c044682 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860210692 1250 860209442 860209447
    0xc0a020f0111062d070210200c100515060f0703050405130903030f02042d12050607020f071a090307030204020c0106260c01080a021204120e0405010308090f06 70
    0x1800010301c07075503024060681c802d100c00c0b1440c00c0c607a00d4071310b803100c440e5030101341c4402000259540090b0103103003200040c40019402641c00c0014004100300c1b041b418801c0c80c0081c3e40c0107200400a21f00e0640d0b8181d240c20080354480c4541e410554041c082407551045080c44112401d11a150040081c1c0384242000f5107404c0e62040441c0b040d501070101413511a07698030214041c9600b60141813464190340004529290500f8420f840404002c00d00030a440e40108241c0007503541d1051900240902c41400003004d0303044c0c81c01384d5070b40c0c3d001c989103401405655880030202c84006088000d40c0c8142d0300310212207000c14250003594001080080e45440f4000c800000742c0c9461009024016003140040344160030700ea121101808080d0400805002d42040f2162b1842c012400c1d00103480300b460701200a8480301b607640c029009401c103084080b01e20700280820401c0119100203510120786500350400045070400003127810920015095000401c010665860a040c900034544c0c0c00030242c50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860211942 1250 860210692 860210717
    0x30c0b09010e010603151b0f030b040915090512190e04180c0f05150904020703051e040f0b03090d0305060312070606061b080a0f0522090e030c0a020f01 67
    0x1030030749505034001d40c1e00d821103000c1c110520801b405800400d00311020f040913000084c1c0703070060511b80d00c880e10b60105961104008480e65554005c0000c10350010dc030b95520100700c01c003c00040424049c1152288945134200303c00c24515016140c900d00440d4a0848d032840115003518640c040c804141c0c2e005aa03040341001144041c101188014040c0c00580e034401e00303000c40f254168030203030060340c800c817008502c45c600800e003a0125081c0e039005450158941d0701d40d10b02610640904098901c1d0b13a9003000c0524184480e210107401111801341406404030750351715145c0c0c2d052005648840d220b400001c020031099000303411550b000100507080310155800c0d008034500729004903900b110010b80751401080b0130742d886407024400040c60a442d01c00c0480359902d41c032492007800701c1c2d0018800d151400c6003a403070080c4184c4505800c00b12501c08051580480c0d6400c0130480d005840d02030b40703882c000e40e00282c400001d607803003490284014143d50015400304105c1c800c0c40703460a8100a5510381d40c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860213192 1250 860211942 860211971
    0xb0d060b0d0b09090f06010b0c120a0c02040c0e060714250e010b120118110c030717040f0302091302040903020d0e090c04050909070b03010f0603050105030a030c0b0901 74
    0x103005907414040000707100c080c201c04114003401c02400703101c000d074088003c408102c5d1000c0b48072411940c44a114035a641b40002c0c0076401c0002d0305201e4410f141e030103d0318454440d0800d00900c5010310848013045011310400095480c904a20600c40d0011024408074001900c45080c58142c18034110458600d500c1802d040ca41d2401c45441100391f5510542c8100004444040282d01506109041501b003421281940c64040300510440040f005111804006c4ca40c3d60350001c1c0000c40c60410f000d81c0d0704951104995a03030700c6880701b229902c415400c00c40c04007090009650654004c002540310f00d510b160200060301380080d01035402c8441c20600a80164ad451107270400062294014081070342c07070241c010b081500340c0600c060141e09090300700007420002c1e4003210300791141181c0035103190721240e41c010725004058003d110141d000100200e4905004400c20302110b0706543d0038080e0381e0302e940074143c803244081001030108400040c0c0c1c40c00294010f50711070f1b0100b08400000761007200d10059 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860214442 1250 860213192 860213197
    0xf021206070c05011d0a1218150206061e1005090a031a0a0902010e2e0305091e030d0504020d0605070f0f1803030e04140a020301140d0305040b0d060b 66
    0x6000710700110b06080c10030100380210413180800040000c400c400c060501c64680304422002410301882e5002400c440e40160100320303540601050407090b49840340342c0c05800ba841c42d078075180588a01c0c030000350940390420310300d101808140607148400e500101400310b150803a582c054103001c8180301e116a5a11498150002140110019290380e040c2c020540261500a000400b0b600d0924020342d01603600040000002c8130250f5690800510568601c00c4071107480c9000c902000c2d40484a0b03c2031a0303d60041d50247c6810410b071119030110059034500c000c22200c40750740d03a400500040c0004070060b440554018000380c0007440c6840c1d240e6642003251030840300840880e06800f64054940e40c40504141f41034654108035140c201e901c44403d00c12a80c52200404209000003501c0c110b855075080440d242c007800d8694400c41c28001d040344040c4d0000d015800c07107459600e5900c00795181042c491401150107445207494142029a111791a0303202d6107000d201c481e2644400114003d441c0300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860215692 1250 860214442 860214451
    0x1032901030c1b1a06010f051c020403060509060105120708060117030f0408030d0c1d0d031101020a03201312020a050a080307030e060301060f030f0608071805070f0c0f021206 77
    0x107403018240108400e040b04c00e80151886041084040e40b01e40d289030404115498019901c4c5090212842195080d000c0d11960b04010940e50520701030003083d96001542906a0b181241c000b900b52106014ce655141203a114101250f40b1180041020301c07a010074071100c03041c803a0141e0345050224010710340c4961159000032000d60002400d600e18803114400d0424400031458601c02800601031080b60f50003202c8a03051280320510000d8003054007560b200c82d0364681c42c0c8000d40d214803064501030000d042810703030307000c03e011841c40e140708801c80f243c00c458901d0b400340842c544041c280106070103003001c480750132a0000c070903a00101d03d41d075074141a08020000038008540c0c0700540d290082c105018035942ca401564213200620090f030b005030440040d1a541d2400148120090101402520840c0e00600250240d4100400d103402540f101c0c01462100c540280040d4070b41401c110780c015040c100a00c002078007140d00d0400134401481c0c00c00f5050000b40702144910310071803e10f0800d0020364 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860216942 1250 860215692 860215703
    0xa09170417010c050702040e1f060501020708061e04080f0f0309010c0309052e0e060f090d0c080c0f010f02030a0e12030c030615041401032901030c1b 66
    0x10108015400a512441080c03407001c002d00c59020b0554025040f80288a0002c1c03045442c0e60b0395000b81c0c40700b00004845100242440c600140910701c08500a000c280a900d0050081c1000440c5005001a50300d0154805840500104800480011507090050805c852984042054422003a00c03040600540c1401300e149176541d00b02440c0c032500f15080e24610074280341c1840d07452008070f040441e1409000700c81e4100c06601c0703018072403040b81042c494013208084c6850100521007411000071824810100e01c062802983c030f0708015140e459042c83e9107500010f50300780b030000000d00321001812000002074100c40034a0004102e060035070700c2d5842c1080d0364075400300421a000b40140602c070310220582c0080e108030380400d0800d400c944001840c1d603948040c0000401c2003a2184941c1d160804403450700a9280d5444018042800d52410318060020b401c203103100600b100890440e11a1000201c181d80c0e84956040055001d0310207460441e0900a5034180c6801d01c1c400d928102205a1048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860218192 1250 860216942 860216947
    0x13020a09080a0605221713091a0406050613050105091f022d210f0c070e060a15030b0f150702120601120611090d150e0309180a0917 58
    0x4174030b0180030016081180011800c901c1130f003c04100040e807070510000310b120001ea070f42c24200d00c6800c4804680d40c880501245409003107188000e805107820f40c0c40e20121028495169910200581c5000f0850752941740310b42103d080000c1c2d0302420007041440c0c0090074a100c0e029031304540e081506015860100076800188c024079041081d4000f0000d59a013280d516000120039038040c559500c2d605c802541301102da02142d03204140014140c0d80004000c860440e512400300c0515900c41d4550f01c54070401240000115144e494000c03084c009481402400d0b1184511002088018111608010360010412180302407103444a040b5001c04509070b0401c075564a080d44180200c00d100d0031001c2220780c111000601000c0080174403246540e4104401081d02d69050745000c026100e0070500381c0d4040c65244801e42000500071000401c1e800e10082004128603103200d0075105d100f1040110b5112400740c1c00b02505105425130307250809103209000600d0340d036030342c0c514110320f10343c1c0745010107074001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860219442 1250 860218192 860218201
    0xe030306040f15210203010e071401050a080708060406050a1415030f04171201123c080415020303040b011a030a0207060f050a0b1e13020a09080a0605 66
    0x240034814109400c0b0508125031049040d030048815001e009403010403245021072000d03030120a8035901d5040e0024000c018a10342c00c4043d0b03a5588452042c0d010400c0080035000c0b80c1d40c0144141e07540d984003916000901e43e10701008803881440140b8090b0302c5944c4642c0401c0c0e9840b01050100075000240c02c48846039030000801012088001043c41c41c0b1504008100101c4c4071513041d1508158055032400b103070000c00c1986189030007034200949180802e20300029070a18071031001017070540180007050701c1042540808a4000d0125405038503416000807800c004c0e04101c22551805000380500d41c10192036240b1038022524241c26039005134008001d000070b00c51146205401807840a5280060b83c003402000e14a601006004103d0f507540414100e00f8000c07940c004529034417051030104650310748240d550b8020f01c072005103180a05000c0e60001000d0a80305c4414054103002441e807140140000300310300203540109031280400030040c00c005201c200400000d0701180c42450042540c5c0760 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860220692 1250 860219442 860219449
    0x518130f0b040b2409130c030603022e0e03100501091d0607020606090a09050f07030516060801090c0512040b190203010608070f1b05030c0c22020a09090e030306 71
    0x10311189451084860781c0d64101c03107420600441504005040c4d00c0f540394091310740040c0c4082400703244504090704020710624403580c15881401680d108940400e03c44080e03c42e214a1074000484448442f42c0e9101000200340c020200d400d00040000c044407002c4a03040c0c030789419640c0130b074000e40c0e60716121125a190183c1d14446040c160109000802c00d610742100025074980340a0482405800c443e400315205982ca0741040703440c00c0d0404101c402c01d61801007010f0362084c1d140704c180c801d4050f01c5005100301341100c00d20001c59a10b03654142407030b42010030303d100910b081080c80080c007908000305030134003400701d10080c4500d00a01e10040b86183c05a80006001e0864800305039681c41000180010fa411840703c1d504080c41e85800114030364801803d864804a18450b40c0c009084030002e90108000040206001da1025085e00c4256142c1018801c00c40082c03d031000e18240d07108020f205a5403198003800704503a50345050b4400542e281ca13444221060fa5620031355a801c0001000b07107604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860221942 1250 860220692 860220701
    0x7080c0405120f0607031104181107140f0c0f150408011d01060806160c14010e010b0a05090906010b0d1503030302091c02090a09020f1201090201020f060103030518130f0b04 76
    0x45d43c00d00344040c10562010000c5403185004074400c040c8007929842c10140281d211001508040c0503581d41c034121418804440c20f804007081d8043d20030400d00140444000c1001500d9160103480030b01c6480d04201080302100b40c100804200100500000036041d000b40246c0c000c42c405440c4041004054480c2c86d420348201d600a50305690101c01032026514a1040b07105004400c1d02c0c0c800d503004030601d099680c0300700080d04a419503007000400241d02d0300660003d94045422150100c201307a0300d0342031240c03100b0201c3c0c46607120703004200100200060728008010100e030070390001800c44800300c0b01074000354003604142d0000b9408541c1840c541485503030703440c1071094103079904240542a40080c6801500070032200c80151240440c100310b403503c04248001d000010800d14940c0e160701030b01070007040075a505034010300c02d8601000c600500415114145c80d01959203e00d00042c1e00c1c3d0b00140f02c0c19600280b41c1200c5140642d10002740d5601c101c10031402042404604800c1c2802040150b6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860223192 1250 860221942 860221951
    0x38070b0f0a1406040b010e0307060906030f05040b0c0f0d05040302100633020f0109081812030a0e0a1701061a0c070e0a090206030901050f01090207020907080c0405120f06 75
    0x951030001d80000c07040403005240d5102c10104c602080c16040c035401252801c0c01c9003c0319404d840751100100c1c47d160445501c40a440745a542045603156880c46030090b40c0d130648000e03061800310008100e6500b4080001d03c0014442c402d0507140880c01d10340c0307808484049509800580007407800c1210701e0024069940200400c0d04a03405a003021139089843d40740310011000c02c0e4280034407802516000f8230151032203004050081088030014104580c1650240b0000d981518030603c50041502e00840a04001807007940118101241454250740751a8549490396104101940000b9030070400c04a01c40d130502100c0c00402e04c1442c0046172602800c00c0542c1d841c80e2501403010b00700800c0d00088a101316046009000c0c0942c84005150004110b240ca0180d00003000108203c03609805401c0603005604026800c0b0440c0e0360341c6070310002c901038601d0081d8046070880201d0b00091003a21403540211802c020281740564840000d402c100c1d503c582d0700816081841d100d91124030602803107a12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860224442 1250 860223192 860223211
    0x1203060b040314060606031509060a0816090c020703030c1415010b13060905010e0103051b0f07150b011e02010605060319050114090c030703090503040f090f0638070b0f 74
    0xa41c180564065a10070031152301a004141c000b001842d60f90b40d00c104600280102d02c103030b503289005e180484003101e1142c025010703010304211640701e01030300c000341d2a41241d4250366251801010340d610b402115201e603001c44203501c619002d0030622507070f12003454001c104d401842d0b50740b080111200c4101d0085940b10505000e010841001203036005201c045c007808023442c0c001150340c0c85151100080c210701780e80c0500c02038003142800014a4409c01000300fa4040e10842c6000d00c0c100040009449148095a001031140c03042650010034801c81007580c0c900600001c03c04a40f6003005c92141d400c1102c18420b9400c0d0b901101c82c52080360701c1110b002d0f00f00b8403144840c0104c0100401c00c4210301a00d11610b03000d0000c009140c01c0c0c420740c0240699035005007600c0d03440d992256004191040c41c000d9140e1140750664411004180d4800ca4080b145160ba0220314005c0281105801d000c60035106802180c803007400001c02d400100007810b516209a42c90031107828010001411060010428240f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860225692 1250 860224442 860224447
    0x8090f0303070e0310110c2e090204090b0f150114070b071413060e0402071115250317090c09061507050d1e0c1203060b040314060606 59
    0x506080200c100c03544000c05051082e03402c8094400b0030720f031954050b40408094a81010300080c1c0c0b02e00b5000301525102c48040f51501c40c0381e1101c0074a20a6018003c1d01c09495402d01c0c0e105070030140e08856880d5000505c0003e10580320b444d0601880022604100b600c0c164104111078022410301a5560800c207203050900540c3e901d01b811714078403136a48042c1422032480001114240700f1001c0d03503410000c2d44034454581c0f40d02c2901c2d102800c424050310002c90b014149000c12805c0c18420303191019003003120b000c050580d17030b424003a402031240d00002a0701d8040080c40119100d440700c0c10761090004c4000c402a41d65400c0c01010641083d00500d44040361380240039606600040790300300b103001111000c0c49901d035040000c42e20901420203420705400401c42c4011300000bc506001802d00e03d44614600320407601c4014200c409000409021509100e80c80b00440c0c06800c00c02d480d182c0500f0001202038a912501c03440c0d810a0303008039202030002500c5a0450424055650084402d0342c3d800d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860226942 1250 860225692 860225713
    0x12030b04150e012904030f0515040f0210200a15050f0109111204080a110304060c0305030603070911180a03020a0902090117011203090b07080a1103090301050a020a0809 74
    0x9240c48061051011144400d545940390703810722180f2110000300401005c1d6615501d103441000d450340c4134010343c0d0502465100360b04100c2c940d1040b0b48110707800303440720451005036803c211007008002c1a200401403480e140c4a26209051300c009509c4807400c004100c0200356180808a01040003100c1c040d1605040034890034030320512035941552044440880c05001c203140100f1580030b441106000c28070b4a600f0700c030074048030500900600740d1030703600d04260564090343c1d0b90790784c0720350303c107000000e40380c80103120101e48100c0103036030409001025141001d54450760b400c10ba83e590f03400215088000121504209002458600c0b403c200b0740c1c0d1200480d1035900011a0300b9800e10901d0704143e00003403801e901ea84108420882da82100100c4005942c42e11115042c811105100320301080c603844010039000d1445041c1d0741c0c02540301803001d1800d0003d580844441c0b0071641100b026220034442c0c000e16940c01e0294602c9101101c00040c6c5032480100010300c0f140c8040d14083c0181c01140302003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860228192 1250 860226942 860226959
    0x10c170c0f03040206070f0614091905100b03160603021b061b0c1f020c1b06070219090c1e110a110d0f2612040b060d12030b0415 57
    0x803940984c0440341a900e505e660b0410880c0b1101e18a0700400503494803000300015940348440b140140b4040d404c03a2410720007400a500b01400c000409801070780301242c80590420030f50440b4200c0310707014043e201a00645580344084a005402000119030041000c0721107000e00101036020344078401c02072071907007051048000701b01c000406095420000050383c071980340042021110b103000102000060540b46101c600082d0801c110b03042040c05002c405181c0104215820406000c006150500c1d050040d400c010007900c480d12000541403120760001003d10240c403030740481c101c0c26200c000302c2a566480c1c42c01140582c4409074240300038000c00f012070800010305070541c10b5010801842442d00b0a00280346107804120041000808141c22800c0029480e0060105988030200c1c80ba00304411150b07103807601580a030301e009801c039a000140400c241d03800326600181d01402c54840030070141c1b1000301512000c0c1e54003010036211000b4030443c0c10b140c40303019000004507908030b05407420030390b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860229442 1250 860228192 860228197
    0x31503030906030f11070507090506061315020a050a050304290711010504050a1d0609040b040618060212040c06050c070e0c090a0f090b0306060f01031d010c170c0f 72
    0x10601015994008044c80e21a5640031030303080340441d4903c5480384001c6c0390084d0f458031140a890b20282c104404190030b414038409a540c040803c40e03500c84898207100d070b400301103c1c031b0322814811803140c4110040411414002c0740c21040c024000b441d0f841d41080741c80c02c04000103140220b10700041102d400205100003040d2054030303510501e18000a03c014004854900480d04102c2d40041e508400040c6280c1d0100e081c82c050500e503041100329980c49003040f0502204a40141240303400c60f000600041c00b07a403151880940ea10b40c07040380074503581c41d45000c82e0064031120800007072001c103000900c01c000001100424030752415a240030861001c003a141c4000b4071030380c018210340e100440c2d1201700b2403068801e4044040d10800e0141e039100c81d42c0340c443e040362094454082c0b40001c2d03400c150502046144c820700d006800144d405502d10011070090042d4200301c0d034540314502040307400d00c1007030041281c100c04135518902c2d01c140d4024907142103000a4801d40d0a448208a20060055228207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860230692 1250 860229442 860229449
    0xc08131a12011d0a0c022d01240329130303202b0e07050109140f1023090f03010b1c1401050f041a070c020402090604170d0315030309 59
    0xc0109818501070010ba242601d940d0512502c140100310b85013468507241e50701095840480005d0007620b0b00c2c0885007001c000e0003027003c2402c4180450901c0403914140081c08038a08203400040c48204e804203000c5002c0d010703104522030f030140b1072340342081c5039040c000c0f10a51319070090791f92400001d14502440b103204680c500c035004001d5400a01003860100c0e4036a660101000051012180680301d05031103c41c00c0c010036006ca40820004034018110340030a003080c170005030501c10241c2500c1c08000d8605403881e1032030100704204140c100c4404542c003610b03240000d280443c0752514540010030a00200f01c0c0d880b1400b0b0b0303142035003419481d81c510788000c0c13410070995107086402c170803428a1746202c00041101a16036080500780300c400065403032010311403406202805581907001900e000c104006031283c0f000504100d49580152511b50300821072020002e00e01e91601d50346840c3c1c9032004400c00001c0516400805e100d4404640500690b445c1c3c80c030025040b85001c1c00d41e43c01800e82c401900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860231942 1250 860230692 860230711
    0x30804031707092c04170c06040c09060b030c03150f040216030909020c060a0c020a0b28090503090909100f1a0a03020d0303180b0f0402130501060c08131a12011d 71
    0x225200941c4103480440301c80108000030b235042c1e451b141c24440d0740340030305d8403603900100c0c13624100040c40d0300c90500b500e0060780550410351658544e804c16141000000c00842e0348400038502c00704117a540c500c01041c0510300c860500705000131500b00900b02d01403a9110382813003401000050308003c03020800caa442601035000050039051030000b24603182140c60300809140c0d501c0c0c1032140c3d140510f01c0502c8541020b1a02299505034500c40c80182c4070003c4005209900c1880034120a140031154180e002503254200c4103051205a034030020303a0740000303112a10a5a9a1000302c07000960040400100380a48204810526550104403666140c0b103000d0101036890345056400e0343c10341c807a0200305030840c040c1031650134421004150101c0540e401c9102d4240300030300788800d041c1801554101c0b2584c3c2c0301c00c0c80c0e00c00c8030707241c800b0103511602010310340c8206148082004503216201c801080401289207440707070721414034079152040680150024402442d008041c501c810120300c0d51142698 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860233192 1250 860231942 860231963
    0x3010e0a0213060509010f0806070224190f020903010b0a0e0f040c0911040e090f061603091b03050f0309060d0b0d05010c031e0612030804031707092c04 67
    0xc5441030010080303900030540c008001780c0006441b001316060b01c010740b440751040d00c0a58940c40d4003640e44070404005200702e00d022761403441c400036101035426400392a140a4201100704a803095080b9512103140107201c1c0d0b404100302c03006040900c145110304805540d0010441d0a102d526a9039070802000d58a8020894000504210900d01204024074030202c06000c8146010348041c8560464000d00d010402c403240041e0082c1c42c000380d02e600708840309010f00380586803158036007140b00e003500d080c205150700c82e0542000070f42c1440c0d030295074140e01c04000f035101d4210701c2c1c003d0074000055400411540306000001d21070351458102d50105403800c0d0005200004040403030580348070000d0181140d46440ca8908032641c01d508003108a406180c41080d94400004031002195541d0080c4c420b0103020701710b180c000034054011103400c107000e420070a40303014148200920080040307820f2800035542e02000c100c88130310505120b40d40d503074050751071307101010254807015034080c0144044c00c00044da = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860234442 1250 860233192 860233219
    0xe090a0b0c0c010c03090213140c0a030b03030301090c081006050306011206050405131119090f0216050c01090e16140c01020a0c020f01020106050102151f080d0e03010e0a02 76
    0xd150440340b04040800082c0021040e80e94081c0c010030160606901400000304410110303880d5100d007141001088403480140e07140d82500e01c9807600f000d41c9840030b040d0790380c1c02002103030307420005540213212001012071001c200c4030000701010400741000d281c0c403c200303c05001c015009400d5a50002080c03070481e415110302c90628010f05059445039412078540303800c4c002400303031034500b03003424038058180d030204003d00500f8404100d0011041c4189000364600910107400540c0001c0d128100007640503080c00da841c0f071044001206800c003110103034040707404101d465800290364001000e001c41c02440c94a0201070320b002800503944000208030100f40454421811801038030034014000000f15150311680710701505914041d90241d03c9800141c44480096105000d90001e8a2060340500072050400c100310080c804050189800c40031200c0c072040d4004500e00d0079000402260004041e40a1907190140c000e00c1d034400c2c00d5001ea41482540c911160300029806242c0ba0b0540340a4040000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860235692 1250 860234442 860234461
    0x310140117060c19022e061e18021b0a05100212220c090b040b0d030903080f0702270a330b04060c1b1206110c010c03020c070e090a0b 59
    0x704c60340010000300e00c1800802510306c10380340c00d1640b6110210104000c81d06d900000c0740c05400401e0314508500d01160612040804d81307608001c00040d04000b600780150030710340030f03c5100842e800d010140e2150100c001803000c20003034000c403074141000442c0f43c071081c038225080e0308100404400e200020040800080c440030310310f03518280c0e00500c0003211580c0328080301002d44202035203a8462410503450340010703c5e12400c40311400781e16803140b01c8043c2c40d41d45e80702410f4001196500702400300340901e00142c0c47c1c407004a84a0414413081c2c038035410402d8005000c01e00060a4845020f00d0100c003e07008241d020842c072a0010641d8020410030040306a80000c642244c22003125a0004100016015004880c0008e024462143d1a44030320035034605420b07609040c0b24802184409450000202d00181c0c0514400304801f583c040c581000f14000c2806e55107035000c0710000a90004a1402404040c0150006041c3e020701c1c03081030b800c1412142e540c030441d2036000742102984038081130343c060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860236942 1250 860235692 860235703
    0x3020309030d051f0602010e1b0102030d050f040c0803120417040305011802151602040f0f020a120b010e0105030c0c0708160603050609040206070308060310140117060c1902 76
    0x80021010f000615015059802041d407801d01c44458600308040495414010b0042d28082e0220100810001d608401400070b01602c90700c02d0b5040d03002c1008942c00810b007902840e1702c03034118840103541d141064030300384080008a90260556070000c0c490f9803103500340c050f5459040745e0083e6401e89140441507402301c0c41d20513680000c0180d0f00c2c2810380070b40408200580c1c0000ca0084400042400c10307070f800c095513803240b40c000d04080c900c10303a03209006191541c071500c1103141e101c071b001420210240348001260b09c191703105000b01d8012112000410164061a1002c810a00e48008070780e1076480060458040a005401c0004020800c5204001e04000388030050020300c013154440c0c0c01c0d20600160491103406050000f0f41408001460f5040042e00c550046901030000c0785460019141164019409002d903035050050640300c1005500070301601c05424440900094a5490000140b0080344c003502c01d0781243c2c20880c01c00c03a01065003015642061290103c0b004090001c0c2022400c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860238192 1250 860236942 860236957
    0x10080613021809090a02031e1501090e1015030b06030f01050c0307020f0105151207092d050106050301030f0f060504030c1101020609060a0e0a0c0e22050d0302030903 73
    0x118804128881c8000240c400c102c11610250390360050341e154600e450743c40781c101e09806509980704080342c41e010300751810f00c0d85294042609442d442c8108000d8802c50460a0f0301169030b590710790450001140381400500c04845200508101a216580c2103000040c0e0350720000d01003820482c0010780741c0d10705020103260b034400702d0000c1200b03150140c03405025400999901c80107210b610030b69201444144103482c0114542c445901c00380700e5200800c484604214281107141c05084c0300040e5905143c024145003415003050024480d00e0500c03403c051003144544140302c1400d0000401c18181c00000300c9055a80284015060b0017541c14450700d000b40320b04c001008246000304200a06d6803200030240002e1007407089030050080d00c1e0049950390b5003074a03c0301d05900000081849449158003204500300320710150f98001030340d9140c8503030340ac1c1c031944107503154040002085858200703030f000d489038076442015900854216490b80c2c0d03500c03101c3c1903548050640c00808540d5842d403c00548020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860239442 1250 860238192 860238229
    0x1103040f0312140301050310090201020c0d11100905090705160503130e0108010504200a17160b1303020f060d1b020c1e0f06070b09010501150c02100806 67
    0x2800d0303491601c01050702c03840d80c1c80390010f0f100001040042840c002102d04a4100a0042072041c1030100c124009281d0303d0360881c10741c818a07011403005c3e00c99440e00c008a5004484d14035241042100f8014520303915200e0700100300c801c000a000a0342c40030901e0743c004003a440c1140d00c400005a03106050040c115000d45a41700100d610b0b2807042d200c001c480145c800f40313620b01110b0390ba2030224900780c50090700c0c004d200340d400ca01d4185807400c82d11541c0c80c00c581c0045c510402c96a58400361003401205180001c40d0f50020300d407036506414045450002410f013494094034103803804605038411800303804028441c0405205105240d40c8201c152002105440020844102c5900c00f690150f201911540054000e00308031a50501e4020801d48062a48241c07800200303502a0400800506141d140741c0e00642c10700c110f101050700030400300d00c5150300c034000080ca0350400141401c0c00403040b0030502049402c004902c0140c851100c800c02d00400c900709017540c0c0d1102c00010f600c0a01d03041c0284407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860240692 1250 860239442 860239469
    0x3060e01080a030e01090815100b0409050f0105120d030e070f0602010e0d050f0403020918010213030c0e060d030810090f090c1d0f0a0b0d1109060916110304 69
    0x401c40d6000c600410410303c00d4a400c0c2c0000310380c000546580c5400d22510030f2542111000c1500c4032079070708030594046021542c411000e610b42c04100300300e801540010010b90390f108100411025508505409000c048408122407450010101d545aa409104a04150701e0b6140704050580130000c4a0140c210800d10603000798649200900a011a070280c82a0788149460840c01502850494004c94001151503182c141160280424810050082240c1e9203200d10407a07460002071015007401031410000c4000079240d41042d89450040e50040b001c80c101001c18084540c0d10b00761502035490b803504140740315a1f520f00c01401c0c44034559222a0071141801140c41280c082c60340b00b071000922a1882510041d1034440c5000b121b286009079500090300000451a1441e400b41041c2d404951000e01090040440300441c045000d810001c42c2d2045104420002c24600b417003c8903882401655030072040d00d04114042c09404000c0107400512280111401e65a8824800c031406031442001105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860241942 1250 860240692 860240699
    0x50f070f1103011a0906010516080a0314010f06020c0d0221010f0f02040503030405151b060a060b030402030a0210090308120703060b070b0114120d21140f0703060e01 73
    0x705102040c056541c820752030121001482c50441d549a5203801000d05035030916611a401986d06070f115030301e00004a600824144009800b5100070150000240d41c007091030620240301c0d03410014180c10088085505290a001c1141d00040c451f0751036104482807224100f440c008150070a9a00c03519980a4800901c0d4000b0513105400000c840c200d614010000250b10240f51022130050303024265040d0004c220401c0145000c2003460500094094900d10b400616031002070390700408071404401c0e40000041142d15120391054500070426566114523615240d4001b03529a140184002c1c41040c5404000361614800d105c41c4000c0d5500c005403036a52101d40b0220401d00380e040700d01400180c01d01c031002c60201011015a040140c0c0180c411069900b401d84c8411b10684406071150400340c4154520403141c0100000c50b041012a145c41340340183c440105800008e1104004078040d0516071032400c18520b00389107a9108030101402400340d1600e000440103000c160340030160041c6240c0010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860243192 1250 860241942 860241953
    0xc0307060b10020f060402060706060e16030c2f030409021c0b03030702030d031a0a0603050604292e0906111501052205091f060b0a050f070f 62
    0x1866000c01c403103140b18aa01c48404a94401300320070511925001000400d0050070408050407031203100d0300d00803507500c0e110003c0b01c4600d1412501c112103c51400d03c2d0480407034140c0319101c202040c81c5007082003038071349401d0340d0500d540008210100041c0c021003482604010304c1528094221030509542d40d40c1904040354541c00d002c150005200d14011003403086280010440382c86690140240c9100003511400394010304611600300700c813040c003201090391540c030003000740003901540c2c4000411f420100180320455503200300b00500c92460000c0b82c3c0b0030401ca81040f81c50030704100da500c007841c16080003454060880300c44819184110b100300f4001d250700003002d0800c0e190503950742400039120301142541c0349014600d0a2a00698100501450a084030010042c03400400402945107800c20203034200c0308200c6a50080781c10881e808024030608070141c415200c00c406080c00254108924038440384120700302d240c10f1010005140c2c4907403408d1410307a04c4042c1c2140e0030044449107401c00307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860244442 1250 860243192 860243201
    0xc0204050718090c0f081e040f231f020409060306061502060c09010309030e031e160b03131e06060e060910140411040b04080d020609120f0c030706 65
    0x503403802c05081c0340c000c2600460781c800e00700806103590720428140040c02c41a510610302510f855030701a07406c1d040d0003100da65500514082c6204000e481e910740c005046c28007040d02480c000305640202c0030030704000300c2c1e1700180013020b1518110b10410101d400c495103034000d203e1070f8041d4a082c0d08028000060040590241d400c64800e03401d84900c2d4512014100c0c0c5441d4201c9003006196010302021a065101750300c0100114402c1c28400600f41300345002a01d491120018000038030148490b0300300303000044c800c10036102c01a00b000e000b0305090120003252400000c0c42081600686484001800306500d45450520f1040d40e1140b9510242d04101c0081c04050190012420659010a1241c00e254800910612140c0c5121900f14206003518200380052095168000d1310b41e0004080d03030f0140d60080c0002c00e071078005260f4851419807440c0c2807040840d512000e54001c038081007442c850110721403400c0300080007010f9495152904081c0d0343c0c0100c019818032884041100c01c20081150700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860245692 1250 860244442 860244467
    0x5040c0509070c150b130218040e03070305251208100515120a020c07060804020f04090b010b0702031002040801050f180c0904152a0504060e060a0c02040507 69
    0x4002070305070360340070060303070b40c145072030b0b001451340c44d40101040e9258443c0c5e00c5070007101c1000300b045000c03214240c0900e00743e0b0042c06010650315a5500b036078146103030501c141c2d086145004051820324103076031005000d034010150460b042c3c0d407494000c00c210710f5401c0354082c207196000940c2c03400f0042c3c0c0c0034000c0c0b40403800c8a480241c04c48940340401c852824401d500e07002c5c507241c20780c43d1404501c007141070120000584a000700a400788075030f001410081c0603201c003501080e03950118038a041d0040111640450101c10b020760319000030340000c1814416001d05684c00c469100d540c1da442d51000c00c0c81c10fa100d004400d5814400306020404c4007040d0000f074040c01c41d540b150300040c1c6039407507180c141035030200d84414242d101d034440c50002e0410b0004a60320600501c00307281502c0c42c000d0320703006940c141045403500070962840c0c540c11459200012800c5602c518010341403e09040002c2c281c203602124080c4210004604140454420704441c1c408982c06407040c4814248480301500282c003121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860246942 1250 860245692 860245699
    0x20906032b080a060b07030c0f02062b18140309090414010507031a040902010e060406030b120606010804170c010f33140a080f030a0908010903090603020f0d05040c05 73
    0x3804244140c0b514040c8105035149103e4903442d04005640690f220302440341c046601c0427030f030f5401c0b01c090ba50b0301024104550f641403100466096103081e41c0280c45486540f45030302441c0c07040c0881d5001c3c1c18810740081d581d0200038411280d1001c000d0501c0c40c0507135811903a10203007090400040210000000d01072090000007032101d5100d0020540070b607100348029090591801e50400d10f24038154001003010b03801810401e40c66000d4801141255205070404ad010036250f0f401a5181c1c14080e1040c08007000d004c014043d1810700000081c40c0807c0680003410046481001700800310383c3d901160707000801d22000b000400e00e090b28550160040008810807181804003240c50406078a0b00b98040c00141205601000c1c100014040e1144445c00333016040100d0440101300b48504002c4094040c084400454480c48012002485c414450704010aa6414001036070006604040040b00703840c058240540c0703c102c5610510010300946480311221820300041c0300522507030943c1c20090f2001030f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860248192 1250 860246942 860246957
    0x60c1e010b04110702130b060c0a08031f031104050c09030307200109080309060729040b0c0423040e0d0810083423040605011b020906032b 61
    0x340d074401064010318601071b4001e0258107034008148900c1d800100000c200400940c03c0031080d1801d1440c020b02c03100c00301c8540c1c1000090140c011450f0565010281c000040d50041c20b096a403007040c03980100290324050740c0c031400854000004070082e910b402030301030204d03078844120b402c01e4150b0b130040380766210011950844800855110306400026114a10300840c64078000c2c0d418001107a011540c10380b040c03a94400354000c41c5000d110050720b03051309520401c050b820141450304010a0241030a44925004c0000700603040c140210001c04041d840c1d00c8280001d00d00010402030b00201d140b9400d07a000c0d040d528400310f604240c981e4000e0303040040c010348050b192020141da401aa0bc0740070540c00420b00840d0510f90341140380300518051013041c441c3d5655402130072454202c04460740c00c0038070b030400c42004541032510074a0002c10003480d251041d02d88000072241081c50009000c2c0c0202e1036080000c0580d2020000d40f240201c0080c403c1c414004942d1300b03494180707060402032000070000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860249442 1250 860248192 860248211
    0x2009010b0310060c110901030c1401020a0201090504151809060f14191e1b0804031422030f02032505060a02150c04090c0815060c1e010b04 61
    0x5542a07034400c110075051510610304054068600048041c0308a8160b5500c0104140340d84440031a03500940c4a02c0004c0c841c0d905100590103c001140103480c1150700150792000941e034000040702c02c07200141c80c001084c03281480034030300d0302641c0c3d00042e18101943c2075010420080d41d20075001c0324083c000402410340019030147c1510380c0302c10500061551000402d5400b416600f680c4c86c00c422645000901080d500e0b07a0f11422052180759888059a07601d200500c600c00903050100c0001624000405140070340d40035016012150407000c00d00380106400b40300340300f04030310384c0340f12140c9580d0390b154113580e49415406101c11420407030090007200346100120202c183c025070741c0120000e0b210100c078100002d20500f60803203080b103003c52055900302d80422000240480c05040f010025907615802d05004c0005c0d12501c0f0801c0c02002900003c10603038401310a016404150101c4580b9583c00b901502c0c00c0c40c00d408461444e0166010250a9040c5034055000d400103900030350b003c1c800c4020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860250692 1250 860249442 860249459
    0xe0405040506011403030c0d0e090106170c031503071503060b0f0409110706091203050106020f0c060c0f10050901060e04020d02091f09092105040308031003200901 72
    0x2015900103055900c0200144000d03040b618120000c10380141c1101c1c00e00b10524500d41c13401c2d60010000000c1340030441d03520034500785544a82d025105505200121a6110700071030320440d0001c00c0c0d841108004400b003020840d03413103083d280c84500201110f5a01c0e840b8000303035a5150201b00d40b00042450400001038442044041e640c510f5020100182820f1500102102074241c004602c032980000304030540c0050f40c01d2217840a124000d041c2503c001543c014054100c81c0107800c8902035501000343c1c080420350000c0c98402c6018107462150316034504102035490050381100141e42405984001c80225075180c1c805846611628001d00c401a0303034a03030540040c103054030083d400c101c0e00744040000d82010400725400800441c0300c9042101c0d07100e0f14001242c500e801012040340c0711324103141445462010b140c0b0f1100ca03481c04014040e04020b01411b40c1c0b16900c0000c102c00804000102c809078007100d04002075030484d00c020007940a0300201505034582201452003041404000310f100e01d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860251798 1106 860250692 860250701
    0x3120207060b011101020306032e110a090902120609090f0607020d031505010c0b07020124182702060f0f0a09211e0219060e04 56
    0x2d001030300040c02c10088078000e6101d6801401440460360700490100034401c40d201008690029400c50b91040041541c2d948a84624003424009160310002c0100961001580c902c480079440c3c04c6500c00300d004110355040008111800100c036420000c01141c1c01003102401c81c4d442c0e044a103490780c50000101da0f140c00580100d0f4101c02940e03050b01910003d1192284061074490070000003d10040c00348502810300482d80011a1429000390b201c2030702c2d9600390719800403004002e002d820090026110318021341c0d02040030040c141016108481382c491525001030341b103200c42c08004810504100d03007a030380a441000310036074a442100043c000071403408d400e41c0d20340059240c003034481ca41c80e40c0070688042040190000c500c490511601d14070360b100d080340d01c03201c0046208804200300e40c00d00030340051001c0f0344d52450784403520000c0100c0e2910f40d181b801c81040102440700b40c0703 = true := by decide +kernel

theorem cover : BRFrame.Cov 860071942 860251798 := by
  have h0 := BRFrame.cov_init 860071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860071942 ≤ n) (h2 : n < 860251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
