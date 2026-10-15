-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:28:46.922001+00:00
-- url     : https://prove2.me/submissions/b8b7193b-0a1a-410d-a0fc-fa7f948821b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 790287769 ≤ n < 790467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 790289019 1250 790287769 790287781
    0xa330b120304060e1e090106030b1305130b06030607120e0309030d090e090613020409060e0d02032106060403031103270405070c0b0a02211602100e030a050711040e06 73
    0x1404041c45c20368114121801e00c900e840305007107039041d20514100022040240400520400005151003102d40d00300301c200520f25216070301c84040544141c10388544c0d81c4400c0c08060329520111088000070b03000340304d2040794003400d4100b52005101345098a20f00110300c40400c1c1000c0e0b426005501088501004000c5621a03200c4954400f00000c0507210504001e9180304100319140000ba1260b5203a0701005c05004290780301c0d410514a080440e501884188c034013a40320b4220000aa03903a0180c035003c00d0103110f404c0866445048010403040ca0320341581c0d02910401e80d07448180c041c500c814003e004051240011590642c982d0556004044641000300b20560384001c10000c10004590821800106400000e6030801005007001d81c541c20078640203150306020030480c2078410001e105204600003000380c0c001314a6402d9090710300300d2451608201c01d036010700020351419030040004e601c440b80f080b000b4280e19440340d10601c0f284422080010251010349444054682040c1c0074001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 790290269 1250 790289019 790289029
    0x1b010c020a090c0210060506040b07080d14011806030215070305040b0f030a060b09010e2809051608011d1902030a0c03060f0e0a1a09090a330b120304060e 68
    0x1103060341605c040c4100380c10300e004102036005612030402d1141011840b4400c01802d0400d8400b00007000c0010054007101d1041031003403e10a11800549518180c5400c0c12594203014070070613250050410788020391160038540441d40f02070425010440c05200105070100320000400c1c940e61000026512402d000b06640c04454040d844418030580c10052000e45903008155132500d0501210030315003030b4a98455640b101d84d04030a4407810242d0707a580c0800d0140f0719030b20460142004d05030b0902035150361b1a0a0350111028050b03140d2400607809640f18080d000d96525a11813041c01c010a59196802103000582c0c20561342000c1031500d541004049583c184201801000300052030a22036241004614107088050040c02c4144d440307000c001c2c4501802c00c40394521010140c1141000c1c0340001009407984440107044941030b081800c2e59501c00f4465005016a00d03040c01c07035290042010315000000c000c0b40084a0304254a94140008680c0a00140000300059150034103031741403c0382000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 790291519 1250 790290269 790290283
    0x1050414121504030c0b061f0c05101404110a03020a09051012080c151003031b0b0f0a110901080c0a0908031c05010911070213061a09030d111b010c020a090c02 70
    0x58018810804002d0019203d03a40100e1108e01c1c03803c0000c0701c3e00b928103081d81814020041c4418640c01c00c40c02101110301d0f0a031880c4910f010340344180f00b0b814800c08102901c6594400030354030025003001070203000543d505c075940111411a504040035a102a20004c1d40403e007400d940400c0301140e02d900d041018400c41100060a10980403145400104038801c4615408068200180d400800300c4010510001d810a80d030003115901031031610014100c0c084070304403664505a400d01058940042c45041a501d00c000c0c161640301d060b0f501c40042e14a075070045807040c010030007511000101103c081c002495540c0b40074131540305506113005d0f154240d81e07040c2d2188502a02c0c2c0042062407004071400d83c1c612507030444014020074508402c9002034400c136040f41220384584102d4440341c104038002400c107080283c00b0390300020745035070090702d0719001d90700701c104540c0042c890b40d066420740b0100b00c26101414140324402d040d8907004a40258203a80190b00c800356590440341032150100444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 790292769 1250 790291519 790291531
    0xc0105101403010b1e0409081201031202011401090216021509030f06060d0204110d0e01140f041505060114220e01060f0815060d09020f01050414121504030c0b 70
    0x1c0c0850600d070000700314211302a00341c2c1c034450b07034072045ca121050381d803600b00f109019000115507885116100030210003000c20710080301c03049000400d40344c100380180920800c8180400b42c1d00f040e607103000c58480207076002c2103035458052038620184005075500c60703003500c4138aa914043c03603e88288000b4107140100c8664503c41c40d82c00482002026a1581d644011095040d1004250b088048110301c0c19402580395aa02c2d090a02d010300c4c07000c001c154051584403244000c011556255400c64009101041e10043d007140001c50140070048519001103030030040c18501400700c40d548952100d402c3d0818085482c200e442c2071020b85904084841c802c02824020500300d219500d40040549804182d208034001d00643c00000340c00307400c800b0b441c5103840d60301416155641a4015101c4002c04400d43c0c04ca1158034929445403a6501c40c0041c2c0d01503036036018840a482c0c0c558030801c000c0022030035866070306200d00c900c1c00398142c1901c440c4070301a9120391a282500459880c11110f0700c0f030700500b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 790294019 1250 790292769 790292771
    0x411040f0209032d0703111806030606191a03062b031b021507030801060e06090f0d02120a0c08010c08040210020a080c034b0c010510140301 62
    0x61070380349950220f040c002d61130a0680743d05a0008400540b801000c0080640e003144c021420000180441c143e5200311043d4100d40000301900c88107040c2004071000d580450b0580d101400264071410f040c3c50040d40c1100d80044d88603043d6484000044000d550140034541840200030b01280b0308101241c2d2404c030306808100d0041c0c56290702142c0005d160038001804100d01062031140c500021218820403980282c80b1043d00911240c8100c0a64010401140002d118100025001e4443c1304801c052000007031859140c441c2d0350b003c2118400d011040164060060800d2100690307402080d010901c122201600d40d4400609003109207440c1c035413000742ca90741001c40d21301c80780382d200e103c040d4455130460340c01d002c541001c00d04a01d00b01c2c00c42c074010862240040d4031000c042000018062045010000c1a050800c401c446000c80800131240c0c01c4001141c0d402c1004e82c4240105048449500c4e041141090a0b0709c20080c290f4000b0b44002782580c4c540c0c042401a41040200c0c068002e800b600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 790295269 1250 790294019 790294027
    0x309140a0c08121e04050406090b0f0a0b34030207081605061b010f0504110a060c05071a0f07030e04110319020a0509130e06011505030f07170411040f02 67
    0xd0911241d210703042c8030003130302500c1489040b1201e900c40d05641c090300d80070700100b060b5601c2e541e03840010a1003109240c41203031203140d44500340c50146441d1041d02c20700948107041001c409400030b1243c0d101d0005010300382c00d40c1e8404040c01c00c0207412154281c02030303004114440c900209181018882e01a070300c140700702c20390300380415100d000c220350012458001c500145003050b0080c1d401000d000c55602d400c0380c1010140401d1100304c82200c4104a0103c1e20741b292150b60301c0b4195600416484001c00c51740205a08201c0324080349040c811410b00c0361901403030102c4009140d509688154402c502042c0401c02510403130401d0310408655003500c0c42843c2c03440c141882c0c10310072000c2c031008014000d0b400140307140b50a0b02c941c00f0303554960009403d444603403048200200c0a89103200c41901244244000052201e890003035a010075602034032114956100c0d0364544040c0000100a0303070034013083c6018403001d0001a90070600c82c50003019142008140d0384100320913206160400b152480c0184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 790296519 1250 790295269 790295293
    0xb04061e0f11030c060f180f0a170f03100503070b091f02010914060108100b0d200a030803040b0f160c0804120303050f010b04050307091a0d050d03050c0406080601050a0309140a0c08 80
    0x103030700f005940c0004a0b42b100c1200141050164440d004034146400b8000c02401220317444408c012003070701c80c200c0a0322005a1503049180141c0aa1440580c1c051075000d2068602000f01001d0300e1070210510020400e0340d2103450344003161282d0b0380c42d2423103548007100400c00b003542030001082c0440004024010701c40c0800c001017000181c1500501102c2401c1c0c2c0d0905810b8003a0504022014041d00c414140c503501d08050010b900b007100c09540150040001445210594844910659626103a01445000428120313150710600354100e491503410400030070104e40725202c0b030034410310940d800304103441c0004074120710120681c01280e40c69024041406182c1c2c02180d10002e42c1e11650001034030010903008280221050381c001a0841000c40512050040200c1d0b451020401c60b01c00340890746840914603018442d034450700c40000e1440d00850301c9588901300801466100f45004110521143c4031410f4010050142c1d0707540d5401078140404000c4007240c140010038008001d40b00c1d481e081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 790297769 1250 790296519 790296523
    0x180c0d0e010917030a0b03120a03060b09060f0d060306090606051c0201091a040510080f1302060f030c070c0905070906020f100e030d05010b04061e0f11030c060f180f 73
    0x14003d910f16500400081c0c1282c60f41e0b4031900141400500700c0d5400114851000c480e03031b1009118000107418200c005c54059403900482c1d41c103480243c060b0340f402e1010211409150081041044c040780c07500d40c00004210b260103250a401c0c01480d0001e5400d15090030044144003080d03a01020020940640300580c1c2c00a240300c08035240400646108101e143d64400c0a100d00d40100d82d00a441551000e0703159440340720948101d458100050840d21103082c1c80480c0300042d10001d601110800401c0341201154001e5908012031014240c101419a96107104582681d08210a0580d1340d8040114180e4407000701002000c0c240040c00301c0c0f4590741c14107622803000c01e07416030701241c6a15400349803460030811240000340c544000c104650b1107003000e0003244c1c05131203204000b0300e005000b401326a00582c501481001240c40760705400c94056000d0b20034050030803024445000500c20000240000c1c0a190300c0751a07a9403035410107190041030605800070850034111194401c0c80100e118840c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 790299019 1250 790297769 790297793
    0xf0e011a0405060121020d0506150d020a2021090117040503040f0303050a0806041802040b040609090f050f0c0a0311030703120521090309010509180c0d0e0109 70
    0xd441c08a202e035200070058406652814070040300e41e240d56000c0304029480d901812640e5240c11092001d03403106810890313122031440a503001502d0411007484030006039070081014800d2410010088001c0b80743e0180c400c20070720025aa503420034641c450710581c003403074042c40c05900d50700e455044c135030510300080090884031003102200d0700f50f801280611004209480c0200740908140c2002901c0e440c1c0185941c001c8030044000c10070341c001055541c54075019240c8845079449614110326519001c01c03001d044040c9045030080d541d5940450b80c802e20340500401c850090080c00b10140842c5031291409083d5100100c0382c2d0000c0038060380d142c0da25664901200e400202511101d0003000c002410540240c3c4006c010040d90341c80070000c203411401501406c030401c2031448038030315001d180918200086501446a4008001043c59580601e01a00c103a010140050110881010201250210079120b20405150100d4140031418060203503503240c0b0003400003070118000c0c5070f84007849195 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 790300269 1250 790299019 790299071
    0x17030c0727050a020705121809061f120204060c030806040e1e0c0a06080f0a050c250b010e06120307080a031109280f05030d0c0312020a030f0e01 64
    0x901c1d0700100300460119010364035030a8100c0c0a8801c44800005414042c1e440781145460180418042c0103140c07400b03880c2188130350000780409101002c0c01c031074403402e0b641c0300c05504144332118200070092100d0b4400703080942601d0700d51814059440c180603040c044003c00503445141400c00010100c0c80210300941c61b41c10354440d140e0b00340c644011060810320006c8542d500300007001e90000700c503a8018600d5000300325605510400d512815070f041c086d140308840340d200154041080940d142c43c1643c91038003001c83c61012400890082c0d0b50381c11500e0302170380710031143c0003c5410f202c1e5500c0d000d100c040c00100d00500852401d9586c4c5ea6001c1c050003200c00f20818103a46000c042070100c4500c044a083c9078000780920480c9040e0301c620010b0b604040d901e814545407c3d200455107015458002e015140020024903001424010031591681e04200880030003465880c001c1c0c15030f515001400c03140c0110703240483d8a40d10f0b80079505c04c0707070341d04041022942c1c10007486102c4a45035000a00d6110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 790301519 1250 790300269 790300271
    0x1608070e060307030b191d0c011d0406090b0108011211040c110d030c0e0d020f0607050307140703060c0c0206070303050a0e12030f06040903050412060617030c0727 72
    0x607a401c030009080421030752024048007016420009940c05007002070301c2940140d0310402000c010304017104481074111025420550140858081540c01980e4507200000c0e50024084110506000f00d41a1502c90340010085500e510030400d144d0f0300a2041e03805417102606041e840000740c2c0b2010117010402143ca0701880d47d64032000481445004180d040c00300032000c41c3c01d40c04070300c1c00050080440c0b84180d000140c035030082404070b2800c0111403018a4004142040340d4041004202075540101d60454542c4403c00a11000566121105100c8640c840140c105140b543c144001a5a07202c4c1c032241c10002725141e41c40050756804145ca0307510b601071400142d541c2d15585124000c040d070403901c039014030510455407440c0100200031489091020401381881c0c46070300a200c19079042e0b110041c0415000d00050000c0c41e54074010460b55401141c1c0440c076035607078030114140b171000c005410f8610707000016019200c0342c041122400801801c0c07600c1803040000000004003004c0c001351501c0c19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 790302769 1250 790301519 790301521
    0xd05011a060313030525031101050c0301140f0d020d0308012c07032414120304050102060c071a0f3403020a120c030b0a060311030a050601030e0f010e1608070e 70
    0x4030040300441a43d00203900c0216030032985414003502c410504400d48c40c2c80c1d82008001742401c9803081c03c3d00e040f1b5161510700c083c1c0b8501030042101f1f1100040b038480d004181c40d0039090240e5034007041d07102c03041c3c020f4560040e5541400780030204170010b1800c034003024039501c10045103060b00c0c0300c009a224900340f40019036000c0f850314240f4402d112107040082030555140c0030070f80c0d403042200c0c00440300089071588511000900c1c4580c81703011360300c2040d000d40c000c10000344440480754000c2c18003034031407034503402a81303e40321a010a940090b504016803002c0c001c2009100f21410048840c0c0a14a402c5144015000700d00f00791020745e5000c20008161b0040307103043c4c3c294040c2000d01c90f004202c0c4000c2c84400f448150084c02040341c0c150032803160140c85000104180644900000e41d051103242c14615902e4840d200041e105c064000f5042680c7d81810011415003449020000d0100500104004420124291404160300c82d21042e040402c1d1040091a10004d140c904462895a0100301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 790304019 1250 790302769 790302787
    0xc03030a031802090c0a020c010207031221021c1109030c120f01021b12160602031008061e06010f0c1209080601090903170c270d05011a0603130305 65
    0x1001d0030030300a4000c1184e0080c441034030280c0c400341070800300c59400c0707484950f001001245d03640c0d210300c0088c2c060484281100c0040f40b144448c45420040c0380090040819401c000d0310490380442c01c01d4104511411281007e59064060b030f401c00c02491040d20700f800b54200000740c41d81300e14840305100d81890804551074200a202c43d07007440b00910021921104108141e07084484c44251444c03840c024800e00c081800c50000590319058105500199460f106940f00802903001030940c00c40b1481c1e440c4002090901004018420001d44040b21001c3d82000c60000004401414850520019240010300144d01948070080250020f126858220742048203a03a110903a8000000c0c0f4018400089a0088103403c02603805110740e44420300701044200d000040c3e181528030403c0403504000f034000303003080002c0e0b00d2241502099103082c0c2172142000100e102222503c205d80c544d44990b4058500a0081c25003090302c00191030003071a6203002080103248450450004003441804101420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 790305269 1250 790304019 790304051
    0x6140d051006080f0705040204210203030f030103080a140405010c02190306230109020a08040f020103240512010c140d14040b011701091104020a03140c0910020c03030a03 75
    0x550001010010098183c64044070f9454807000480d1502502c21040c0c00507007420315208450440c1c0e1002d600100a0400c2c140400300e001008105a905200600050315001070501c010740c02903105283c0659610b2210744090040b080c6400f501134001c000380b00030445640c101102407917455049a00c40300b24105005c2d04d079500da071a0b404c094210391030040d400345004000c0440c850181e41c02151104207a0381c17000441c069102e02a01030340025070420109000580607000211803d01c14100811903d1900d2881461516080c04007504a0b484000030003440c1801192013108254083c02071019043c4d5075400b506242005850003008100080c900e9110076080e03020669145c40c228041324141801d040009805400380071300e807a00989108000d504c40c00500c43d44074651707840300e40401c141d90100100700080d041100b00400381525505290306050407416100c0c411406040181c0d128454401842858a03d141c1c42c40e040d540b02041501c115a400010b40b1b4044d0203070b02d00890680030701c0480752 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 790306519 1250 790305269 790305283
    0x1509070c0822081e121b01020706050105031c090e07020f0d032f031305121c050109050906042405010305100c1803150209060d0605010807170f0705040b040305010c021006140d05 78
    0x1011b5500c040b070342c4001c100d11034224030b04130342d002c41c1194400d5020002e550380c02851854180040388940310100401c170001c24503654003100d03a0064881d10512840ca0f5401c01e0003010f8900b0001e40d5405400041c00d0207400b010700610901e0040c845481c1d400b25052a082c84050000382000c000040000c0030040c04000710400d51007071000309610754600c5458809007998104d2807006036801d000002c60044910301c2413620850303c00d4001c20440d05c5a88500c000c5218100e803185142c2d080220ba407030b0762401401814001c1d0300c1000141328001110045004a41e242040c00d02086040350155032a00000070501055a070022890803058030200000c40c024800c04030f00e290817080210340e4000d80d400ea0341c0941c0480d882a20b904046170703900e001c2207801e03101c42c00003034003444214808140040103003010544c0c00502e60a00500d801c3e1640f14001e43c40c0c02581c81160380ba9140c90341c400740e181d0b041c403078070300c1040400b1414480541840c10307103040c1001703107001c25008042405514042c017104020f44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 790307769 1250 790306519 790306567
    0xf06030106031502030a05130807110609040e0709110a1e03020d2903060105030307140a08040803040906060302041a03040204091b08061509070c0822081e12 69
    0x2003d502c021044200081d4200b201c210104c14030f0040020f03d0b0403400c100c8450440d1340100814941001503a801d080b0f00182003410b078101905020000d010340313440c8140300321024420010403e8500c5d129946041d5420f408074003041540602c00980b840c0e130840104142d044480c40707101d920509200c4c08600902801c10400c240500f0410b400c120706841085142252020009410000074072400740b690300c040070300c05c1ea60036030f108001540c00725070000e0790b250794100341d54180c030f042c1845500d0b004041c5c4c006800000d825000001c0c1000072108a100c2c000091040b82002c1d41818504860411244005a42c1d4081100008009402c550340c03070303015003a5160310410b11003a064180c0340300c5242c410a409985a584141d001248400302084184620018000d0544005d5a01e81c44115041d0b503c00e501119a158140035036001d00070800707001c01c044034050152110a43c60007408a00d02400d0074240c0c82e0565556480c0103500b02c010403040000f0411403000e6035925503005940c40e0520500c80c074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 790309019 1250 790307769 790307783
    0x5030702010e01050f15030601140f03010609020a030b030d09060e042f2104020a0506160503070605040c060e031b12010216110111101107080a1701060c0b0f0603010603 74
    0x2042002d104070304960b0700410403c400200d0b002016003c7c0741c0e4418080c0038800c011b004003400c040c0f0303628240c00310740701c40c0700060004201c00f80e4860044050ba004120400080390b1a02a0b01c21942130801c5040103081d090310381150380c0e9291000c042d0041c404004114002c2d6290384402e0318090f882d804040403401d000c200401020600c0c5020040d58104c40b180d520440c45031034940a0489100450f140110b4004042040441c41c0204200c6a03900c581e2000800203019841c8a002c00c0040c800f0780000c40c00781d940810035107454034040c400c00006402420501801c55854400303a10700154601d0481d0001d5180003485890b800090340c40382e64040c004940d5800054105074850b10024039100c4d1510414052040c0d543c01c1006449504d007046c04010340754005016450518116005000340714039029119107000420b443d440680d034000011400400c040c40c2580c1103802803e441140101044d25100c07088030f1750313542c1e0260560740140c9480607005014002c0380c4a56002e40c44038005640c0220 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 790310269 1250 790309019 790309021
    0x602120412030e0d02250b030106030f0b060a0219050f0f0f060a0c120b0609060c0c2e0305041e050d0f03060506030a090f12270e0705030702010e0105 66
    0x988140e01c0440c41860780d00281c10300c50080003540c00010200c01d11421034028010350f0704100002d086601130000600d44520b40e8090024803c16204000d5010b00180e55001c14a42441f81c03030710059410000b0f0040c0104000c01140320f0300d0b580401d141da1507200040704814214002c2c18603d11b0400c204a26028602403080d880d40107010008840003d407481e03c0945440307a5070100503030219045501884041001086200d031100415403202c0140c8000030f0956081030041030104289400681c6046040c0d4042003004105203880d00b42d240050b005040e8110b103e11050200700d452041c40070f0001d06044d11100814101f216248403203550030080303044910389116604000350742c0c03c540a20311000c01c0400e4801010305100f8041c01e07007560000340c044c500d180c580709905001040602070540390900c00c1500040007900c00c0500c00b400303c80300e595005802c0341580940013030410080800d004511941410880d00804003080e03a032048140c18210303103960720b52200b82d000d0a07188c01c00f84055480c00d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 790311519 1250 790310269 790310273
    0x304090b010801050a05040e161202120f0c0111010e03040308040303080603070609290a03020316020f0601260a0521030115050a021612141f050604020702031515100f050706021204 79
    0x505880748503000311403046001c0cc003220701c10b0720350854107044603407a0000110a056940110b070342400c06046080001000c42d10008101d046411540044441000010b4100203140d803044c0c210341c02c40012006841000e01d08000a0460151403250a120964501d0b800c118401505240c1c282260110001c60341c4000903003004001307501c12a0031600c1c0c401c1c07002c2c031160f060344002280c00d800d643d904010b02c1a83d09003080b440140c0c0d8420148101c0702034240f90014602414010365a0742482400104002d01c004140c03003192440a00e11150000310a0004100a001010700301c450f014240c14240d036100384400d4101d0520599007140481c04154141c00105120b041c0ca80b249a680680e9600d4200652600c00c0c0d0380358086441041030303884a2141175484201244c1c001c54100c2c0c2c00910051030300025a01082c00c0ca10308030040c88050291008010f0070040038072003030209050813502c0000350b410342c810262070000c903101178404100012840c076041100315412900c1102d90481c1c00802442d040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 790312769 1250 790311519 790311539
    0x905010b12332701060e1009090f0b1e0a0b0304051c0504170622020105160c0e040b060f01030203090705090c07060e0304090b010801050a05040e16 65
    0x2000107405000070100004030b440c00340202c40b2200c800301c1c00e0b01d40890340440802c1004640c2500c1d01e142d0040b00201d168a101c00404210b01094a8040c00d0070859031500380090505c115486c056070140c3e076060315504102da070001c452002d440842c040040d003090394128000003048543c059540144210703070040d04000444500322203604007110620b84a070b0300c40146140602040e1001000c4d680804444201008641c2003680d1582c1c10b40f46ca1400c203a0703504080402c1c20809000c16040d60025002d2158803c10045030301d14407074080c5a0a03121403003c3d80000d00d40d114240c003c155440101d281d04c400c0000031b4010000410110318800c840d410310b400c0c0a50019002d94403944100041d01c4000980d5019000790f07441460820064090340303141006000000d00010041280903004200400008030781c0d200c2d094034003e0440042d6180e904042d02a42155002c2d02c1d0a0705100725107004000700c0e03442601100981e001901e01040002c0d2203000d5625040c00c3c4000900030303003036680780030070300c1410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 790314019 1250 790312769 790312777
    0x3040c0506040611100b060301030210030b10030b03010b06090607260f040839040e070e060111070308030a0f09020a080c0f060f040303080903070507030302070e07080f040201030f060905010b 84
    0x7400056841d0505500707844c41c206c1d00000300b070641001003480100054070340040c0600c2d10807128140403602d9082200051010480703c0041000b00342e81707400d481d415003000d03c103494011a0941d1214a088030400000d12280110300d0014a03a01c81e04040c400982103842c0a49900b1051f240742d0740e16406043c1080702d041e002402640098440e4840e160384100c0340403690103542c3c0c09050013040d81000400f82119400c400c03528550095220801c603c420700c01089071074001c00c000000c4204070b003400000103084d038590f0140b140d01a0300c075510503c0403c40020840342c0100d00c4600018803123402159203005000359072000ba50000b1300c46c5000a5101c00401e0240c1420030482d8007075060f180740410003251380100004845030241c00c1c0070a0001900075095250400c800c50116030421115958262410480d5003040300140c008240030800c609140c556640c0164041c10466090b203040ac0b11380240210081c00a410140c0702e80d0988a400850790102d400361a030244103000c0342d0784409525040da40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 790315269 1250 790314019 790314047
    0xc04090201140304230d14162001030b090c090118091401050a1707031502120c0403150513020d02130f021e03010f170c04180606060801080a0803040c05060406 70
    0x1702c41000380602c181c010604280c040c2c0c1c2500d407580882c030301c07020840640d0000100052880042c151030808940b02e000500040c041416005580465082c001426100c2200d2540d0040d40c5290600011603040e42c19222510020710b02440e01c24400c2d00110100b41e40383d44459172241c501040506810018850340e4140c0d00203442c02e152165840f8901c0b00401510040c59441c2d801544044c00000c50360100008a40c0d480d81001d0704008480c81d40e003100700020b480c40100808006400c1003040b18640c011101c028042c80304015030320303001c0c0028a4031150048000e2150225102c9401150f640302001c401c0c840e00003c0400c049001c0d1407030f0300b00944c40390f04140102891002d622a070925020100c0b410f942400000c0d00d03405151000c11000704014907200b07a1280140d0aa1040ea519503200f4101c14082d140074003041c22a66060841c00c584098000c0000c0142890040c82070383d0001030ba60414503407110000f03980e80d4076410010029440358100c0d80e4040030010f00040c40a40c41025141050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 790316519 1250 790315269 790315313
    0x503060f100203040605031017060a060504090803010302060903120315090a0501240e130b040f050c03190b0306040506061003020307020a150e070e09150402030c04090201140304 78
    0x40c5200d41008540780e008280711005a204210504c001d41c421006560003840c61903400505a88409000303040800b08000c0ca20710303502a4041101c07014035400b400c0000d29003079030104038a40103515200f58900c8140006400740700002840409030320b041012180380c14403103d50356103d09149000450500304c06010034401e01c0d000021860100c101c0c400c940c12113800098821858160f055014002800b08005c1002c0c0b05448030082e065440b180800e501c986803285002072140000782c02c010482e1841080300025600d010100049020b110084a0300088401300e10140d2042c00b8003814003030402460125058000c0c44144410000c0026149014090880e070502076109003d404038200c6c0400c903140c40060340809180c02c042105910361440111940c0000704900c0c0b10b5881480c9807424650000001d0b140c610b042044018003885064801701086041000c6c9040580000b0b503103925500001e880b450366040380a0031a03010300b83c500c0700364008004c166100d01e403d081c00722a000039a20401051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 790317769 1250 790316519 790316539
    0x1020d0e030304031118090105060103060803070309141314070e011d0d03050d05070810050d0209010e060d050601060206060109090507080f0a15030f050f0a081206130c050306 77
    0x100340140055000e050016000354180b51a40d12028440c2c02c615250f5904044041082412020688500307407084003030500100b19030408000050803100d19a00c0280c1d10340080c011640020380c0600b00f14125200400c0702101540d1590001d40203611148095082510308944403500d1000ba03450240b0841941d02c07402c4403800003070015116003030010511500d200005c190003c440c0381503420100414080d182080c10580000346c90b400312001070b00c211002c500442d081000380d019075443e100c00340009440184100d03c1e2a070205810b01c20600070024007640d44000103c1c0360711107441c2d080d0740701e4001040f00d85950b502c0f03901039100c0300280c50190019007000d9020070700460700d02400380215a6591201a41c0d510040c650f441604054000001e441e00c0e100e030310394114214000d410195008001e1719010910038901246041082d07014651690084c11513034001c111402c0c207503400010100041c0d801940c40e0702c0007034409841c00c0c0c1185102894007099401c49607010300594401c0c1c6050322401c1c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 790319019 1250 790317769 790317793
    0x50a060206040c0b0301050a0b0a120e0615040c02030a03200708030f06040203060f040504024005060307150203070c0905040501180b160e1f080a0501260c0d0c050102 73
    0x1683c8424000c87d5003200d41017504020a500c4400144849921450700904460071a146001514400044c0c50050b510400a002004007040780c5d807450103a040708e04000324a6843c8001e504e0f401400c0c7e10341305041c1d4400030702201c1072000851041c1140840c10030b07070392001c1e6889d0100c0c090704242e80040100309824001034803401d0a00c00c41e806032030010415410300a40a0030040600001130040341c21100c40071250b0b42c48080031405c2c0000b002d0480c40004040200240918800600d0078121031140c00c240c144090b6071030104042066400102c1c4812165292050584c51407156180c01800044403882c00900740919610050180d44035600030b100300d203201e44900a016200d84005001203c840000c81c0703280320b0340101d4003420030140c241020644100740004900840045141c5004800c080c52400919442080990300c100b0381001000075505080494001e1700301000001f01c00400300c0e407a0303100305004202d011010719004041c1984218a0719020b182e1074128400c0901501c102d580c5103074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 790320269 1250 790319019 790319039
    0x4080f030f040504050403120606080603010c031b180f12060e0d0807080907080a1b060207031203110909070c020f1005250203060901020a023c0106050a060206040c 72
    0x40e100c42498040d0707082c00e041200300001400041c0084083c03040120b40c00c85808043d0060304014061034492440a02e0708501781030030f544d035144400c010146402d00c020781c54620103400c0c01024481e0b01e00604085004d907600350100aaa070042080a80350a00015004003505008400540306040900103c04400344195580c000005200e02049290b0005503100f886041c5842e406580e80c800c8500d03071903a800049003004145101503500c2000364841011411055000c0001000e152004280591550302c13104280d52a16800030201601c481203905030864801c150b4541500c01080762866040c03400001e0040c1e09001c100302e0103540050110034843c90302d9298226044070945500389000226000744141410035981c0100d4480704880710409a1810001d80e80300710544400140d031010600b002900c0c01e2803483e0460b0542c90a40b0050385001024102180161a0000d00c0781c98410018040360160030702c2c1e040682c10220001e000590143d0000d02c07207021f680903e0183d0710f400c1d15001e0b110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 790321519 1250 790320269 790320277
    0xb161206150f0909020d020d2a03020a0203211b03070e010e0315130507050901031e0212030d06030b060f100f020a021903151e09110a0b04080f03 64
    0x1101099400c07a5080aa00541d01c2c0c2e00b07900c41501d0500501a1180001400c03070300f021010fa182a50b011460010040b458403800c0d07420184180c8a0301221360722201380100320344511407001010f8021500f801c2550003001510034a400d5000320700c1c101c07000c000c10994040304c101c40d12824100080c03401003903041c1f014100c86c001c88181d070b41e03402842d140c4801136603505c8210008542501c21a54180c14419071041d929020b001013911142d01d081d1030f030030b00c68036140c8a504000d200305030080c0100000f401014218025201001c0002ca0b10102c9000190034a03000140c140014040011406000445030f030251055900c9070044600644511080c02854003540c030b110f03034100142d40c0060b45e801e40107003c0301410640520460398030070758690120f0058078064170f840301d103140e50340300c2442040741c3d06403015a141d02c4142e040044c219103290032402c02006007003501186a48000c00c40c1070000784405203030f50002c0035001052a139a20b9900c0c4000c1d610611440c0380d50300500c1100e01c07440303030301000725 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 790322769 1250 790321519 790321529
    0x20307050c011a0f06160606080a1b0e01030b060409050703060c1209021c150903050702010e0102011e020906160506070305010b030f010317040914040b0c0909041e0b161206 76
    0x21030454a18502405000da10048403001d00c000c1491b004000161180140005498810090a0252030a280c00e050b800200382d41d211a6071034255041c441084000c14850450b0380000000e0915101c40d004070b801400c00031009090750046407008000d008a903044140700601175a038030030888900d08240f00854282e400c000354056079001e1865925014a218034042c0760107050b60904145150050b101129440c580440210b43c010a94a0956030802c00b20720303d01c0820b0009220001c0401c0501464008022003c5402d03039012440608648030031091b50390942c8440358400d402c1020b8240595190f00032100c1400103420702e0300115200c40400b00790b07030080a40900c40003140c0d003503507101c0c41060400d94075081d10210900c07001411542a0060101204c1d00d081d40031b00505190804640c48030000b041032864074070401168496403102d00b8007a44c001d8106003502c2c0c0f0032411840031161030810b258090001401c60003840f040042502000340009441d84803400e8039104200709a05036940c0e0300ca4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 790324019 1250 790322769 790322779
    0x109031b0213020705012a080a060803070210111002070605091c050c15010e04120201060503030d0e0703082115181803220f0509040f15020307050c011a 67
    0xc0c0da96030441e25006840030500c204000708420000307c00e016440f11075011041c0c0d075031240d002d24085007a0488803c031341258005070140100b50516003690365900c01d2690023070040044802402205118000c8030485840c07030703019900582c21000400020790440c010595103640740201060710084000361008000c03942d011b00c0d45159061400640d20b9401c820210b5440d0f000f0f1860160000040c1d03000207010f84903002c0c542c51581043d040610380e02440d00700d0380080d60300d482424403071590000181c5040c2d908050000c00e40d05c45001e00b6605028150388020410403022800b40c03070100461030440c0340102c500000b8003071652010381e400b0240c1e4040c04101e03080109a000c20003029101002554803112006143c025521034940c0c01c0e1442c0d00001c00108140900d0380b280d011034055407014001040d03100c1c5090a014282000220354076070140c801450034100a640508001603090705002c0c961411104541707074901440d0240c903c1c1e000d8a503941c01c55281c0380c0071100d400c04c112403041c1d2210011388 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 790325269 1250 790324019 790324039
    0x206060120010906020703030e01090b0c0d0b04020304111906050403060905030c100b01031404080a0e010219030c031205040c03080f1c0903020c010504081c1707020109031b02 77
    0x4015101c503090012a085a011000311030001c454003405640c0300c0d244100c0c1c0043e9906483d06000301218960404052181d0404104101040c4041c0105421803a075200d4075039190010402840101130b10340320300b50428000310410007480051040032810040a075910b0f0b0751650403035800c0301c00800b41d00843c004668140414008a420360703024002c0d4502c00c5e41101c2c0390444000300c03145801c0710300000007a926250041c07a000703943e244c0a001100000005184c43c1420325503100c884034011542c01d0010800c1c4010b480030503130710030850052030b000c086410600880250800802e00c0c00c1d042c000b6000f10300950541c01c0300385a1445554421500700514580c481d041d9640e40c1340c207034015902e142d41a081800710107801051494120101e4140c0c0c000020042e002c0d2801030300f07140001c107015060180612041010701004560300d40481c1e4034025502c0410300c1d82a064400081c20b0420310160201c02c001c1259854056200c1030a140c02a01c030354801c0d906130130701080c0501c8140c00080d04800041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 790326519 1250 790325269 790325281
    0x8011407050d02250b10170a120309021008090c060a4109150703120c021006060203030910180809130213030303052a0903010e031603120204060206 65
    0x94040c02400e64940b403913100030725800260202c4410503440a448140b480c90a1020007804d0004440040c010301c1d0f10300c00d5594142c014075031a07402043c0050155203403108140381c103074841c1c0d00200301598000c190103180002e06030000d080c02003ca500449502c40c044d4000303003900e85130055440100391507490954801041c1c03611840000e030801190b088042465241294000783c01886800001c43c1c2d0440c0c5c0c507540d4090800041c84240d0144007030209042240d100882e60011070340d6241e074524a000308100038003643c12850101d9076044020414502038020886560100055001d10400c0c0203d42c40421400400c030304139014101c007042000b112011325000108400c002c2e1075010001094420162307082e140c8001139070b000c00d01590000c40c3c108000c5c010107426120b226000100e1031401c0ea00319080c040b00d1803040880c00c1031404a03040204200d066550250019401c030101e5205030dd4403004242c2650600170308000044000c80d043c00082d85100c1554030a0b18121400b550050000b070f1952 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 790327769 1250 790326519 790326521
    0xf19050705190f14010f1a040b19030803090c0d1406060a23130906020304030f0809030a0509030c0d120207080f06011509120c0f090506090105010305090a14030408011407050d 77
    0x707884404c0543d500c0341140e280c1c41826110b001c0c01b560070320881050310400801000111010034801c80d114201500320301045250001010058a50005107136683c3d45030030300d44a00d0b0403560040c080e8083c0d1071000d00340421202000360002d405000c400c071420740e241c00f010808862040c0c090711824850300c201400070596034100070308000780e02030109400c90030510035003026104050300580d001ca80010038001010b9100c4400c00414015140659450a1400c0296181c3c880c4e82c8058080140200ba0f11205540a02c5280346031200184001200401c524080300c428102130b1b81003025020f2040b00007501500030500801603143d80010b002d00d0307820003054024070010429800704106a4110101d01c010b081007440b8075031400b6240c40002070349492044901100241c000b07110b000d082c0010f2040c11380340d4011440c1918401d00b000300d050b50301e40c0d2010b494224070319006002ea4000000d00310810b10084018000e650740b0a0003401070305201d50002501a00030345180d00062800c1205240c40c04031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 790329019 1250 790327769 790327793
    0x1505070e061b030f07110607110d08040506070c0e07020f0c10020c091509010506120708040822031118010e09070b0f03090c01081504020f19050705190f 67
    0x2d42240642204405401600d590441008032180410006601e4244402002082c40c00c0c0e004407030861030806c0d150b0b03504400200500a05000b044024411420002c20100365000340001800058a41416041c1580301040921409210315400c50200f0321043c0b01194081c00740030584002d0600b9030044040c03010400004003604110b01a82607800c145070756030800280242c1000749911f54441780b10040040095069000344e00c10321041180d0303e0003d0b0210061940014141800350082ea62803e151103148507110704104040c052807100c0c606510a945400e0907a0b0194060f104240d4401050140c0603818410140414004078010010000c1c40c2c0600d55000e81003000ba5005503940d00008100342c1c021494002a5000100401005e41d00800054002510034a0700502500b001e40e460b020801a200c2914012a00041c00598961a85084644603145524211920450041c004149810010003200d582c041c050a01c5465084000014a840d422010026400400b60b440d6031880700b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 790330269 1250 790329019 790329037
    0x1090f0b0c0a12050c0706170f1f080708060c1e210a0504030806010f1e0c0209010b0901090b03070f050c0c040501031226060402070503070605131505070e06 69
    0x328980c03060b4001000e0140b007074810a00ca4440940303510115514034180122900700c00d0800107202c60680b619500400740c00e820030035a85482c0b442d6250800369030307030720140c40383e0107010005100c40c0002c05402c0010544220b03a0702c8415107025880d5001540401d1046407408107c03e0036501c0c0b401355080034130000317240c0c0c0346800c0280401c0031010b0303c50113a440012201080486d556404020500d5041510503501940c246402040042030140141486410505c9038800d191380e00c1210b0840c5000b00444280c180d0014004135456940e040074401a521280441d030009041c0c01c00007646210040540740218081d4642c1c4240201400c82101c058000d1032920700c00d840703a20749400c2075880d2481038501850049450304180f9071070000140004500c10800032800c00e83c03445d1030042e0380d0480001c0783c10520807140966280700f14107009146000f0841c01802c00c40c0303442c0601241918040c0105c0b070440c07240046101180240c40080704403402224608046030309081079041c5450100006c0070019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 790331519 1250 790330269 790330273
    0xe120a050a18260307031223011e120804050d02040914070602010b030d090e0402011e05090102100b0d0b06130207080702041a03030d02030714210601090f0b0c 70
    0xd11038151442e10104250701008600300301c00304889650082c100c00151128403034005610f080c0b8150380052050240c071125402c0d11350703103280d42d1861444200c0540140c0c2e038222000d06513961118401c410a010300e281501c01400f007010009040d81d03183c1ca01b03105031508130000c1d40c01c280c948018000401c0b91800100d9002d9a42c0e03091000050800c450119900d00f802c00814180341450400f90849107101040c900c298000003440041e198030001040999000d0002c200182d2101d20050b100c20220311f41c02d401580c21714050078401c542c404098551031100342c0c00c4500c2000003826030404c48000c9200749400c034844040c0030300810356450750a038200d10060200d61030712411071602400c90300040c004642507079001415a083d444c040c00342c42c4803000d03410741c0381441614040c0020b81c2c1703100d444400b4203800d4000c000900700da0b0042e2003402c05441240c0040355142c2c000b410744504401141000d101c4c50a03020003184143d4400e000c22010b881d0745900e0405003500709068481d60b034001040b404118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 790332769 1250 790331519 790331537
    0x3051c090602160303061a04090905010b0406060c0312020703080123190f08060108070e07030912050706150503030a050f090d060b18070806090403030905150a0e120a050a 75
    0x841c0e9200400081803101610007a4991900d0001c054070b901d07a001000c0004400341d21900d104458007280c040310504c0700d00142c030079207903c0c5c4a8050a08108110791040c030701140020a0b92f002100b011030030380300b41d44200d4140c2202c0010b10032400740c400302500042e681c4005100e2901c0f00786103c400d21847c3c008a00c40d190000d00020741d442408118030050210081c0704020504201c45030402502c2c9000c080c040a40c105020030740d4030841c510660400505841c04502924080d601052900b43c00221001c00314217584000341c02580032440840d6064078100103082201c0400c0031400070b1f558001c015500d007048105044980d41c02c0350601c44a001030403c8420300c9991481100d001051040d80c010a0641e1180300b00034209070151071121101440c102000521035000724030660040017150a410b158030741d41022002003d03841e100030302d907115118101102c9011011078920407803600c4800e00c28608000981c075224002c0d00e0b07040b1000c0340240207800b83c40380502d01a02581403181750600c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 790334019 1250 790332769 790332773
    0x206181e031201030305040810060509070f05040b0408060402092406130b0310080d02060403080103030818010e1b0f300601171b06091003061a1306020a03051c09 71
    0xb02d4442030744110007158000800304044042031041100103400441c041207a00d2030040450341d1800300508103010828500d8981215900a400760783c0940b1a2081c5203840c0d036140c0d10110707902e020546050340700740300d000d00045c000c4440c54451070311000c0d51400800b12235940c0c0c003440407941001e04824058580f8001c0170406845100103144100110980c201e44a8a441d556500300f08004994070111b411040070040400c2e00b008155044a515240052540d40da04046030017411060a081d420795080c0900b02c03ea80030300046080100c00c40c80c00203070028036a50208017410303800409581c1c22a0180e0a84c140f944055202d000c001000b424090030000c2440f10502d04120f0260080d601c2403142030300940b035a5000f00442c1c2003201601500c2d4003c4161100055054002c5802d4140f02c0c95200d10a6203400384650040d00c02030007000d868a244495000c000c1c0002d400c071034030040c071109080c000080c1d40c0d4400585004004e4050700c07020f01c0c120145104110405000f0180c9088540340e590103c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 790335269 1250 790334019 790334047
    0xc0307151d03072d031d27040201030b120a022b02130b280e0f0c0a020f070609032d080c1c120b09100902091c080702010206181e03 58
    0x80d44c5200e5a2980c1003215860344400c00038140111040c001e4102580c2e00380c106a01c10f050509030242c1010610340d594491004074003811030384400541043c0040d007411070100001071a144118801c55000703103008000070203410b00d0040141d106107040b4004942c076001d810b000782d00558051407103501061100c00c80021824152080300318000d103880115a55031001d00e80c924101c040d02c050b82180c152400c002600003103510001c0d05440900200280000b50b942c020001080000360480948075400ea41c0e5401074047c0030f44c0d100540384c4e01800300c080540b00c64a200d05d0306c4001c014032004034803011141c840a0568001c03041c0c0c40e40a10a03800100e03c600182401c00038040e44a5072040c0898007001c40f060140c1d4010f41815010b804d0b00814011003000d0001c0060980d41032440058030b4075644000604c00f00381041803107245520000c407071018480048010400517000b80c003201c0940e01d0308440b94a841700144100c00d420740040c0345540ba10608013440800c107080100c102c9017052030724a0145 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 790336519 1250 790335269 790335353
    0x60a0318020d0524130201050c01090b0a0506040c03020f070602071502030a09120c0f0b0c04091d0d18050618042307020705011409060c0307151d0307 66
    0x502c555014100e100d140340c03108180d9191481d000c0b035040505061084000c0c082c41740b5210b0003410b02030040350408051000f5800b444045420583c1c68035641000c0d88040d0003003c042d036105003c1c07402c18070205c2d4000c0c003134001c031907203a541c2031201c03454009140c82e014020b40010380c00f01d6011240362401026041d42c0c3c0080d40c0100c6008500054120743c500d020a41181d07203008403010b01400b00a42800306141c107404451803900420541030558540d02a60140d02c0f6913000b00780034500c0c00700802d070444440c0b5070000580802004551100004100a60f50b42c0c220f083c0c92405800f0003c81803140e4100170307010740405c100b400210080c03031003000005010350380210680b104c2c42c000722032a680032003030a100440d04020345001402140e1308240009100200c00d04950003c508006088444d40d1100c100b202c094200c880d051700d4480c4881d1900070410004002458040c80c2000c11106210b2000380c4d2030700ba200105030045103481d006e40d44e40041c481016003911a160484540a14200198170100c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 790337769 1250 790336519 790336523
    0x901080607030612081c0e07031109070e090406240e06030c010509010e0616050a050d090905270109060f020a0909020906161110030608010b010e060a0318020d 70
    0x3410303151800d948001d00b01c07005580038804003600e4801450102d8509811500003400c12100ca18101481c4403202028180e406030002092107603c1c0d001061020642209a84040403501d114440d19854011500903650b480a0741d0300c124004041400940b4070340c4810302408002c091040018001442c820310441958080740f40318100d20100034592400303101c4e10b0001002420460b007081c421100082c1085c02d403204d518000d840004540100380400d14200f56001d510070111400f0406910f001d0707442d4841d21501001242440b00d02140d21580c0707001c0d40380305507103841d650054440300121030418000101140440c6542c0ea8407403c000c0f46e1907004801494440e844003594030722841c032000b042d40b25035611000c0e6140c4140070081440d500c00080b079800400351054000030003240e0800b4100c50990510166012913540302c0c070b4180b03e07019000300b402c075001c4000800c5201409001594406c2a06000503880002007040f520345d1402035000d0f4650f907400c0d8208511280c490703070120f02900200c20003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 790339019 1250 790337769 790337773
    0xe040f0b010f051014031f1a09090a180f03030e161a030105180c0d0905011406030d080711160308040915120f030c0b040c050306090706050f0d0605090108 68
    0x203005909007092a101c0010940c07034200c0140c5d880c42030103100c0c1d0102a00c42201c5010800b20410404002201800500100d03224006c0100d0100040c8040340d100b0601140110001000034071130385120b01ca0550345c008407841141040e42d4a0381c80c150b44030501c04c4210f05056451111804d02c480420049440200a11007603000500b0300030501c11080c01800c0c101a6810100010700a50b211850402c00000c008001d50386aa01e5905641d800c901900d149001000d281c550000140711054019000b4081240d42804003a02c411060640310400b10740c1d1030003c90703d8000411381d407510461908003410b081070150742c010002c5005034561130f00e81394020340e601302c00810705000e50803040c8100495061a003505001e01031801d10881140c076410000600002d468090300800c1c10702920303181401503032000c2d2700110751a1a251440021a00d0b0183c00c0c028030071100018400b9000203900d03826a886030321a9030074410341035a00d5003aa884a03050403106502d501c400034880d21200702a034060000c0c0700c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 790340269 1250 790339019 790339049
    0x13050a0b040204110f090d061b050403060b090402010818070b07050709050a0c140f040b0408060406060806150f12011b0e060702130b0d1e0302060c030601090e040f0b01 74
    0x4201c1550441d41c507080348a10304020011303842ca0220122221b0503015240714030400101c1c00d0040050000c00c0c0c1841c000701c54143d007500480e5000d00148152441010700304500c07560102071101c07a080c100c8000303010401030700104240010700c10034001c0180b440d00455803490b44a0300000d01a13080b8190840303840d8031400d4188105005070050550110b50081c04001c260504c12008040008070703000c5440d0745200155101513800100103da000d406c04a0099079520783c0c80301d40540c1c43c0c108980548906141a40106c2e00700008101607009001c060000c4060018440400180c0300e01301c0440c86d80200360190081000c002801100010040303078111f0180c1c144c3e0706401401032003000b449907101d260100074000061761340030080c0e0542409142c00089040710040030481c030f02703003a40002e801101c04c504060804805100c412407102e200398242d03001a25404200d4020b80800d50740c140c08100a800301307014105108204507070080c081c49100003034142640380c01c02c600d81300385c03c1600300d008640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 790341519 1250 790340269 790340273
    0x1819060518100902010809010b060909040c09021809090c0a051c0b070c12080709090c030b030a0503190e030705090603160801060608090a052a090c07021f0e060313050a0b04 76
    0x801b85030340400321038002d11070f212800700029070510500b110305105d06000c0780854188420501264080d01501030110340d500400e4054084082c071890040344524514800150000000300320007540d03c0380a071183e00140c0c18030003001a0302c0d05070b40030958050820010100800ca11449181c090907040d141c910360f0041506000b0384985051803908140321501c030622443c02e5003c6584411520160b400144444a0039000c4015220080b00243e140c407640b000c54050002c0880245640c0520340510764030202300f0313407041d40c803140c5541c0c0c1c80303915401c030490812113418104030f00d41e44280000c0c15204180c0300305140381300b11080e41e08143c00707580d0340f644240500340e002040d040d0884c0c1100c004014101c0c20340c1c0c850b80e503102444024400052405001c44601e04203441242d040d4a0042036021a85407082c01006035130459001a4414100d1148000c142c0c0c0545a14601011303c5a45407510942d05a0502c822a8400b801c11502c0380300e064034401c0400c5c000d0241ea0f416a2084105040760b003414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 790342769 1250 790341519 790341527
    0x604060b0a0b0a1407060e030310080105090f070308030c090d0602040906060c021c03020f0114060406060e031009021f030b0f030727060b0a08181906051810090201 72
    0x60380007440400b400700a445801900150640c582c980c08207007003650b6071428a02400079080021080072640300100621510740b075440d80340820380369002c00801103651040c12056407004184414041030300184010700204001d100256401090041403a1034542c0702000700e002071103008404c1e14403a90202d002d00882050780500d20040c2160310300200400c44a40002e03040380760200540c11160002440e04003054000c2c8025400c04a00f08001c020445c03080c1809244410110746a610561905002003251401041085801c42c0f010b8010144500a00d45950080c500b01c1000d903401078040c0358000c8079450f0b0820781420f030012550041009030350345080c0200c0e0034a5400052190300161010f000205002802140708003070f038011406a1030050b8805002800b00c1d42052004d80000642000260b8000c0c02103405101d03e4804186c04040d032814207a16441440344201d032008030485030b0000328000e038000540286d1900901c0c0840c0e9000d07005203140144045a446d02d10f034494035036800395a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 790344019 1250 790342769 790342789
    0x6040c080606040b341a150f0a0302100c0611070c0e090109050304030804050405060904210314010905040308090102071101050f091305011d09030d0903020712080d240b1b0604060b 79
    0x4056040030087c2484018046c00c5500c0704102c1340140c090300c02140c0d05030380e413000d601c2c000c2d80c01400000c06440708110083c040c40b54000c060320000e081c030030161440d0f20010304680e41c468200700a103183c0c2c0c4c00e0210055508001a003800601d41d21000e200c0080b4400b4801003000350301c07500c81d8550311440c000c284002d0b2100200301d01e200b1b480352400c00c0f01107000e04a007490400180c002c103040f0745102500c180c3c0103111020b07100b00d0140000c000031403600c2c955444580a240681c88100c841c0c0e8981c5c2046090f40f150120041c4541480340f00482c0650080d0040d000e516440c0750454107228000300820480503015050094050b1940010011301210000c074007008160b214150b000c918084070303003503624411904012042aa148004805e161083c000e00e0058410a1b644003684815400d1a000507004040c80200b45481c090301045400c03012248041b000d46031b05c034403408140c904a6840c0054000814512080c15035250814103810706028482c8118403440e40004d000c0c080740c0038420442c4c0d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 790345269 1250 790344019 790344053
    0x1609090b1303120e03071e0b130c0306050c0f0c010b090c0f03040809060c1204030506060d0f12031e0f14090303012102060304060506040c080606040b34 67
    0x11581900341c04298032020b107908000b42003001064012410302d040f451407054000280100456004490300200d9280c118200f09008551100150f15150040005050400070050015600c8101000021903a402482d40800011f1b0018103000c0300040051040e80038070f090303902ca80d5603961f0703001c00c030720340000d0301c40d00700174030324071840c2032400c00c0940302c02c1031002500c054841e4501088040c040d581b16000c80d070200c009813041d00d09040001f4010010358001c1e00080714203010701310010b0a94100019075992090700080c2c01541d58a064036a20b00c08400b828400302055100c1c0c414480d6141c0c2160304480412001a00194002c81c4404001c1255440b403508000b1090007030034031071070010000541e0f0644074103064000400e100b02c10f1281039402540340094200c14040100012b005459010318401c0714290b6040c8094981c02070200d40b5103204030340c1950711883c02d000c24000126040050b05402d085c50800342e10200a5103c0500c1520f0144c984e100c000d44503a11403402c111008032000f00d180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 790346519 1250 790345269 790345291
    0xe030a081503070e0c04030609050f01050105180114150a0c0c08150f070e0409080d0f0b06191214040327090c0c1b0503070b0405090402121609090b 65
    0x1e0201d000094481c50244210011142c0c950b002c42e42480403a0304540040d54010800c12101410f0315055407503083c121040300a03946044000950340c10f042c9510507107603002c0305190307100d81c1c00c2c4003c50114240242e00350380c004194000051b400c8c200341008020866094850300122007451a110080750081e8000c64a00e03081500160403880b2078031043d903000715a40071a01040d503681e88041b2003080d00301448617030190900400c48184407079180149403626a0f07400c1800340c0700c4190290800d0303600d2401403c2d08440104500d0f04021480a081c141101d80c914041c200c3c3c40d460f5450006941c074203c0c0d41850304240d00248010940c001c0460359580980c10030400d143c14082c800d541c628900d500c1900d000d0341d151107800036804d120742c42080401d03500c0955000740d11045060b4500c600710a0003003600078810342c81c1c00f0130192040b409540031200014115182a62076500b80854200020045107039842204003c407049540caa1f605405000400c10001c0c001417a0f09000d414240090307c81e003001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 790347769 1250 790346519 790346551
    0x11030d090804321c080706050f010909030c170d090501060501020d230a03020d0507120b0303040b0f0d14040b040303060501091232030d050a02120411040f0e030a08 72
    0x440f021400c114514100301c446040380d4075070b012100d00309a01550020080c540c00504841084450f601107070103020202040c0c003a980c0c07a019000200c5100503030140205000510140004000d48101400800c56401032410210266018000d030b905c0808103d942d44d4548405110030b50303040114003240705d07591412003000c0c01e040405521031b515000d42d49190385d90000302d12000034000d804603040181ca40008004604d0000001000703a04a001c03040056428061090042d00c0c0c0007095409a0f00b540350550720309914a840e6000076801a10704200c403640780c06009140d40f04000d40d01d88942e0143c10190b5603864186070007070807180641c0246043c0404441e00f032045581161101c060690300284001d5400e250184010302040962000030b046c6ca01500071185048012000d00b43c02241c4560074003068542240034800d034000e542c1005103010386400080c010030400311681c140d4000c0600700080904600c03002000b07486418a040c400d6034130001d84410307103a501840e140c0d4000d40140549442d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 790349019 1250 790347769 790347839
    0x20603010e060102030921070f1406031306150915030b04030c1a07050703180528080706080411040605030303060d0c0b1b16030201020d11030d090804 66
    0x1800103024601205161400240440e4020012500c51010041400d8804104010450209050185240002e010301c040000f0040034038896201036698885070f0890303210714842805015000100840740c00500c440403c0c0104030644118010441c880046242c05801c5c40c2f01c1806441d142c007012856404038010410201d005255896005a494900000b807500c4c0c508210030368095820f4140c554040c0710043c0556944c02100900e000342c0700703466185d0128480c090010b0104650b10503940c00c40f0840000d0fa640c4280244010785190f81f503071440c0301c1c080c3c0341e8070180d1802d07405411180200c6e40703000a10061000c02010f4040446044600b030100320f0809001c240c50b4013000d04541d0040c62005601010080c10388001000703000c4144040c3c3d20b603051740c158001c0103001d15039000403078010b84204900c514906034104050b83d806800600b140b44401c03004840723400b040c80311034010b4001401031480205150091106460094034020385030350411180368010403905002c0310b8140d42d41901809 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 790350269 1250 790349019 790349029
    0xb040501080103060515031f0c1e051b1c090e090a060b120a120e030607022e050a1b02030a090312030605150a09120b1b090406090e0c060702 62
    0x1064076880303540881e40382c4406c02120001000c07080159070602606503c40004403c480c01190310401c00700f400d020310481c0d55010780340c4411000c40c440e001100c403c05890614002d00080059555081904000c5480c6da0031080c10f0211162a60301040341d1918a03201c0306030312000050140801c40c1c0d0002c094102440401e03698042290010a8561107a140000580d20078605044480b4000b0998408101d2032400e030785090300c00b454100110702c1100341c0d011141800a641403242269070000e0003002c881407151306d241d440c4204081c0054107040d2102d205491030380a510700807480001d0100e03a01200141e801c625a4030184918210760080c005480c1d03d603408101c80c011640c203c1c80f4005190381d07041048010f8240b50b001140c0080d0345d000b0424000f80a40d0060641da8440daa508840a0b19100303a11408a041140501440d9031040400c8a604242c0c89048500041034000e520703252484001c6015140d0a40c00046540d541d18805071f03c0910500134203402c0402254040d00d031088980c0010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 790351519 1250 790350269 790350271
    0xb1b0901080606090406090f1104060f0804050106170f060f0709030609110925140a08090c03061e010e010815090a0f0c14040c0225030611130b04050108 67
    0x604110701040851003c0d102e41044445148000d041804000d88402c01100944510755550082a260000c1648688518004e44044d00c00c0340e42c40341030003203800c1c80448030341401a009072030300e56803004000b81c07803000c03194401543d0071840301800404e90b55000c02402d254000f89202d0341c09006000308910035030f2001c902401d0700d0b400f00b800981c2210608112070404030001c0100d4121194400380a0058900b14582c0c840c4a01c070a0105c09502c2942021a5010041d4124441d2041e060014907841c6024800d215406803031082119030100c801c000103480c0420550b0014085062102d09003606524201d00a0260980d081222125490400426a24245c5a000c00b5407030f40008045240310710306101e10100c140e00001d0081401c0018140124070000d18803400e03004880d120651405e60406000795410016540c0240c100950500400c51160f001030340b035400c0c0a0000350010000940510a011140e4410a1102d44412051045a0740746415820003da0700e1350502040000380e03030150a203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 790352769 1250 790351519 790351537
    0x60103030804021c0506010b07060f020a1809110d1d071503060e2703040f0303090e061e120102090405091b120a03180306020d050709090e0307140f0307050601030b1b 73
    0x8d40d07034a10643c20201d00400144118040d210300020b03110799025482491030704080507210709200c281c2d07619080b260440d4007041801c40d41d074400b44008140c1c58900d500044482c520031050030080d0b15044455410219550444400340085a40c280b960952600c00d5401400c00410300c0d008a040c0000000c04150b811100c02040419148080701142c1040c0140c074018085a203021000640707038038000d8100a01402031240314400d010004000f0310349030541821020140e01ca41443c0c018010503c840c01011401240d001c1d9000c005010b03050f00d071445403a00c150024809003041e2058070b540036141c0503200b41e00a00c10401e03e054184041808901d16400c1c4d07616080c001c0c2034100700b81070042e003c982c0d944050f040b107201140e10031050025030003a600c2400c40c0c1d90f9603c2d00d55282c0182d07401320b40385c86c040c010880d4000c0c002c180000e803000030700307081d19100f2100b124182c2e02c0004045195070320000045925802c00001001004007100c622031300301c450300e050300c0b0243d43c15003100c83c403a018250300b0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 790354019 1250 790352769 790352789
    0x60109020f07050d0206090610141009080d1e03020705280b0a0905062a090f0a030f051c120b0f1005090a051005090d080408060103030804021c050601 66
    0xc1c000090094500301c6182a50000689013400340315000a501c441d402c5412a20501030040010111680c8900c0d00c2c0541e4042c0e0542c44150100c5000d02003030804240250080c880700c0c103000300c0d5103201045440300c40c120a40d01d8000c0115001c845888440300071001c1000e050041c400f02000400128a1800618608000d2001550402c441c030f1900c00344580040e1111001e1420311903c1c21090300107440ba2405901200d0135610350f4040d032000501805001550849802e00d03560302c0500020041c00c02c4c0600608101480503a0b0700012100b01c010783c0708139039a2003006240005c0000c180900205012408011407864420307035000741059400303840203142e2235512003c1017400e0b61642c00f03070085441c0240140d07070101d001d03c202412513404007140e680701d030f5055040040c0500c0d0410404054100580d40c003814906c601d020301c550340341080c404582800e81030001098102d000c0003400e000314040c0d074402d00035003403900601c2400c1d580030000350305521000c450840441c03030010b14241111001c0c6130b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 790355269 1250 790354019 790354027
    0x5090a034803032102030406050f07080c0405060715051f0f0620010e0a03081b0c0a0b060105160b04061a0306061309021e010f050307080609040c0801090b07030b040e06010902 77
    0x4104c621103820104419140380301005000030310046a205a11452a03510811500e4036655010b50715000125441c0c02500d504010520042c18a07401501c070041c45500c5601d0541100d84614098800403103694031400214a000355940250020b440c0080440f040004540b0f800c06000811004200d012442c58281042500c482888254440c100c10140113090f5849a9620f1800400c40355080d0345034038101c1580503e0515620003d4200c1e1083c813411300050844000710795890100440040545052120034891640665004803a00d000b90f0310401c1400200c1c5006d24000d070840791819002c44008006482921943c2ca00041440e00500121901424003030f004604202400b09660001c2d004400301d50b01d0308094040502403504e08200741c0710004100d008807412507050000311907080c000341002c0007083e02802c000c5a10f40e003143c02182071032521902d40c1034280c2510180d00044038585506410401c2591b8035120720301d05070301c04540c140007240c03100f070300107030744100c18050712550a600003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 790356519 1250 790355269 790355297
    0x6050a0e13150f05010521130c03080304300804060f06120c080607120c0507060614040e0318090c041505030a0b010903020a0605090a03480303 63
    0x4080020007000001440080e40784485144101c100f4440d03100d902690a4010450358000c0c070a54074100c5005104504040210a0011140e10003038001d03150400c070a510b200c003094980c6240030145010700c40d8540d8900701440e04081251034040d60010001d08040101e01b65001403540a088199a1416403220344860600d940140140301070785075102c0c60018000b030200e0fa60100d0032085401048001e0f81d80350f58010441d1100c5003181c0e43d2000600105050820001c99409002c1e501d00505c0c1850030500242c0e00c0c1c000721f03035158000429480d5013023451036a6180a018104940c0303000409141071105020704a44041d4807003e6003442241c00c41e0005081e444800107542c002c142c09048c0703150b0080d070050060210b5109844a05010b4103002a170003040d4011200d0800f00c940c0504203a80c60762810100312805e4000032901c1d503000d1040680000410a420200c0c0c00d10030a205180d1150040d8405c600d06852100d820007200d00e0b144441d1003030110075140d40c0d03c1260f070075007480005c0c20300d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 790357769 1250 790356519 790356529
    0x31018050607080f15010509220f0f1a010509150405150c06100b0d0c05090d0c03051002040308030112050c12010b03070816090203072106051c11041505031c090b0406050a0e 76
    0x1270050041d01840c000045174114455080440200c5c00c61b40104119288603990401c0440b0314440e03940401c03420030030f002c19410b20003466410000c4054040e400d03c0c1d103603000203080901e4442c5460090b0000300306811850414002c01c1c3d0400600804020f81d6031038160000c3d4a8083c0c1d4114100e0281d44414801000d03004500b180e98101c4028410904409149030a4020421074001039505204015261901d007031244200e41c21b9a400400e0710b070a5130b10345044c4e0341841ca0480000c03641405541c1c03541041d607c4200c01c5084d04601c1c000003180f1030164070706161500c0703410351003100258880541d40920742c07000c003500c00a4031701544025981c0e0343e40f54416180c1c080c10074440c80510b035a21f00d15115112042c0d001000351740e406c07610f20741102400c5036581007081281002504075200200d50322494580796210a58501e500180b807000700359201c0001e402c00000340460030030034100e90044040e60780d1102400c8060030118400390700302410841d0090142c007039408181c00340150342c00030740802d80d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790359019 1250 790357769 790357819
    0xc3609070908070312111605131d010e010f02070c14190b030a05070c03050319180803180120090411191706031018050607080f15010509 60
    0x601110700f45540c03440c001200c10f0030400010001802210ba0100c03007a0042801c0e03601e90204051809424241000c0165100740c40310740d912840d940d09052103807a514050f604008051010001560903404038905083d6a01c2c8507140ca200b6104010000008419100007810380711107080410040d0100000320f80140c0141c81f0144000c9166500041d002400900951207036800c40000c7c4180c2d115500d043ea0740791610200180440c40600004e03e042c0da4909001011000c1900007103070b000c04881d0800381c00204818140d50080001040006000400000c000c1c5104003400030030418900c44424031268420015840b684140001d00220581d2150040a03645030030140240d580c404a004100010b2503884001c000b00729800e00003070504003c04046840f03100d02070041d106a0f00c072104454028100b0213a80300704200482c58080101e0703001c000c8a03100d416a44c8803d140c50800007403032020040002c0c951998071b9203042c050640c076640441580d41c0a041a00c00d202c10951000b140110040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790360269 1250 790359019 790359029
    0x20622060608120a0f02030f07030503061302040807140a031101080415060f0302030c2d010504090c05040f0902030c0703030e0a0f0c15030e1e0a0b0c36090709 70
    0x81000c0f18001600b2886004080c480210344480d998660700800580c0c0700c2c05001660741b0802024030a030382c00719010f0300096034001e100920040c4102e450599134401c80c0c000f5003000c0d140d6030199406114012001b030343c111000104a500d14505442d640e0f030140c0190001d071a1504000155020074100291041c1105105440c13100520046c3c0d10340e0380d4070745104114402a031182c4155a41c0d107416051200780c610700244c620849030310300c0500d030a4461400a520321310f1070411004001c0042c0c2a181751083c0c0003413104594804d0340c0e40745485c503200d40c407544507003120354064070400502601d012840d003140c0c0e14643c5820040340f0651480312040c01e0231b01120001d042007502050101c20442e015000500392648540701c4803c032403002c4c40071800c81d5a49081c500007680a100200c1c0d0312425980480c2c1003900841c12030340000304aa0721241403c5041d112207000c81800b0171040380d01260892611062060107a84504100c880d0384800031400405070101c1c021980031000c64801c500c40c01d0420090a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790361519 1250 790360269 790360273
    0x50f040f0803071a190b0a09020408030909010f08030301060c030c120309060e01060303080103020f03030403080d0b03070501080f04110406090c05090306012103031a0919050106020622060608 84
    0x107984100c5141c4980c00000e00b01c0e80c540070140e12844038420650034500621020040703060000032041d9820050003180703104c0b580549400b00c005458069800100041c003a01c0001e1911111400c0c24000c00c1071044e0442d840d80030000105100c9203c001041d2411140286007a41c0a142b0608081d40e8070600c200c00a071070003615070411084560181c111629081c4220002c1280202208000d0b00f00c0303403035001c02800034032044010800346c07410310402c1030320307a6004040c1c0789440d03038941d20080c2990149400380d48a60301c4101919182c902440f1000040000b0f0070304c05142c0c0b8200d0b0320254041d0004000628621284031103c02030b80f240c0d400500035040050041140c6079100c8405040350304184d0040c0c2c4640301c3c40c8000706000c080300080c3c0c2c1505070202048460541c09a40a1f0041c010000d100e41c40c0d10340ca417000940d6513881c0c1d20722134051203501101041703c0e0045074014059400581140703003554081400e00c80c201801103000c001d2041d20010840d4410301516040c4054a41c0343d010403214 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790362769 1250 790361519 790361549
    0x10020403050f07272c06060105090d150e0105040b04051c1b0c0b040b120a02071e0609120806281221170a05070e0f210d020d020f030a050f04 62
    0x15192800381e0880000c5e01e1011a00291340301b00044441744035480046402401c424034180c001010560f0840c0411500b200115010580400d81800c44000f10740554516260f403003800140701c1d0600011841260000303101c4402110004054881d02101e410446480079a2020354207021807110705102420030748881c1e03941c581d80c0d00c186c0702503a00216404181c08030a8008514002100d01c2290721542d0b02c20144c0702440c0380e4001051070711031001070690b401900c0b0100305001810070210740b140c12001e51202d126900b440800c0c1300d0700c20789410b0f032000551200f050681840d0329a105103800c42d00c140d400020020314501e803201c668112031840c01c46c940d410020001e130554000d015031181509018101d012a55062201e00070340d4401e461480200d0700c88480d04040b0f040810903035050302030180211010b00c0155411550310580481c00345200d40104031001400d0b070781440b04182003452407000b41a0880d11507003250b1203204000c504c205008001815034109010101960002e0440e40d40074054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790364019 1250 790362769 790362821
    0x290f1e0c072a05030a050c010318080d0207060f09240212090a0204140103030e010e0f060d09050c0a26010b0303070501140f191a0310020403050f0727 66
    0x29284050b1034066800e04858000b24007402c0c00104040520381010040c01c1e05034031900198000c241d00d0b403490032103058208403000400c0415000304005400a0001650b484090800f4000c6071480000c032801d01d1f08103074011000c00c0194402640e01800c1540302c02c0791b400a42031040083c400c0000d01140d100031502002180040881c0b680d200310b0083d202030049142d501c440d4031602c2000d000c01004151007203e0050715511031310020a9101000c0d1409890381c80000000e100780d003200d0102c8151684a6050700c04101c41801820400001a1032113031116040a28440c2c9400052400d03000c00403d850014650200035048075004031f0001e025030780c0d0342c40c90b824414041d01d030841c070346203040c0d070054007140400000395082807181100740b01d0340001c404c0d462041c2010300540c180c009000c8000342806a410341d0288807040c2000714800d0300590744c40c910315100381440020030030000c484d0004602041003040d03141c8207810b070200c0901c03841120741d00103500f03a0080c0041c5001e007070741140050803010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790365269 1250 790364019 790364063
    0xb0a02091903110423091509060613020313060b030106050409080703080108032502040608010c030f05060603060d02010f0318061d0c130216290f1e0c07 67
    0x100b40c80c002c403d903d42601036031060205072441403640307030640404c01c5075010911580036882c640003603420007a58030109500103090301540e0b0644440ca000d80191083c0004c0389000d05280c03d004480403815410b40c908a020554075240c05070025208035283c04650f40281c0d003e61000c0082c03c0010400c020f0798501e42403001c1282c00201c2d007140403505040c00450500400010788200c0c2400141071011860141104400303031354000c0040780c019885440c007054820086c00382507407040039640c00142c10345088940e01d0a0b100d002c0d100706d024110810520485881da0401c8500c659020300b05468502880c4074118010f00004105414035003013a003141c02004115040b01d0b224080e104c00c20300c0e88070740d0303040441c2c1c4654600507059401a40310f13458880c00743c0260090304102e61202c003480c5100078070342c580d1030079a0074051504485c219880300483c40300d600702409a80044405210745910b140c15140004402541820700d04181c418000007011011054111a202548080c06118804020b0800d42c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790366519 1250 790365269 790365319
    0x60f050108071713020619050315040212040b0c0c1219020d091a0903060a0207020324061306150917030906191103040e0a0c08130b0a0209 61
    0x40c00110401c000c00c020a1040e000d614008416420512040d02c8151401d400da030354000c0c040307810070424800d04100d40c80c2400140382da00250b4441d55600d140552402c4403001c0b81e0080c1920031881032003000c503440d4420701040d80c00340d401030301c01255843c3c04525440501a000c14550310744148803103449000d400754060001d045866403103450000c05075009980307a4148112140000c1c100080070004240c00c002c9413840c9076800003c00749005c0e00c0318080307810f14030f08440135850660000781e59021070800300718442e18000154420311040b2440c90103080b074500b018000b14400c060030000d071711106039940d1200c801802c064128004003014100c0160000d84144900c0c6500031980010112218001c01210b015030001000c0c0d500c6e2100000070b07291661020581c2500700310348001129940c000030001000500300100d00d41e6901c0c40c0030b2050f10309030b1740c41404443c2004a45818042640000d00f07a110115500489840031aa01c1c038502c400203000f0300c0071896102c0741c0b041e00c210110008030b0000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790367769 1250 790366519 790366529
    0xc0605090a0e010b160c17061008010c1d041103011d15030a020103020c0f030304050f011811040e0114150102010f020a090e1902070809040c090312030207080d060f 72
    0x501c029030303441a090700c10509204101c00701c0800c21440c14200e08401d101c00705c1d544105104039102e40c1302c140b003180741a0800317181c42540d0302003400e1020a441d1070308400020180f0b04000d0101042026008059078036400401c0180031030125110995502c903001000e11401c01c110702e46d1650f0b0b580309503510600903a03201400024600c008641e000c001d0034804506078001030010058030980d640110020b60010020080c02c0c0140d46a0b0450000d0a000941c0684e029900500101002e00c2c1c1640c2110314850680c41600c01c0c007076840c0300103910100c040c17981010440c1c0006000035055071150241a92031120704803010903000700034182502034890031200100381d000304200b40300108428224403031600d644000c207000250804c03610740c0c912001a8841c10000ca2014036035020740d011400c1c5e0304640070441d00d00c00c000c0b603d0503440c2448d1040800d19a503e107042c2c1070103851074650180d5100c82c8241401016000681c8030203001010f02165018402c01c01c0410105a583c0b00c01c00050203a0301030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790369019 1250 790367769 790367779
    0x207091e0c030c080121120c1203090203100e0f1e010c0503010506071e05010f230403080a0c0c020a08010f0501050909070e1801020a020f07090608030904020a0c0c060509 75
    0x30711529100e071080500546240d02c0e003040503400c042207030306005001d05101015020442000c8002060340e450441800381d261a020800d94076482c060182207040e40320320f420585440340b050051394001950085001031098001010304210907075508107420300d45401c05074070031880c1f100000400c0c000a1110090600000c110300328180c801101e583c40284150760b4494070500403000490714403040c9034003003918503036803000070415540e41d2802d607003080a030030a500f5511003201c108089036192800e69a66810203665881c03426540203004490041c05440203203990b4500341c1c031010f00030300c400f03005c2c40c0d001800d200d40c060b69460a02d0280c51125840c1000380d0034140000f4035810603600343d074020350208001e0708a07031b428018200c0790004000c1100d02800b0305e80c070f01445030810a200520759101c0380c1c0e0103407801000c540c510300e2420038554070555441e0320380201044130304004400c3d22001c660446000da6502180141143e900030000c2c40a0b00c1c05514060019109410800403c030080c3c003610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790370269 1250 790369019 790369031
    0x5060105010906030608060109180b07030f0510121b0512060907050a06120e071d0915060a0504090f02030102033d090f0f0f200403210207091e 63
    0x240071026117007a84124821584104018081d00c00f2a4200e1844481d4624240034180303815100c000b4400015a00d10002c00ea864520602c800b0240c010301e548081c48000340e00340c1c03a2500581c42441001c80320042e010000d20305c001001d464071003480d0802000c0040101510301c2c04c00b00d10b01c0e191401940e90004034032594000007207608114298004a600f25282c0c49140000d000c06031000d88403085a0b04558000c081c40405c44941c0b1b0030f400c5401c41c65540200405142031989a440c151500d525402c040049604110091361850384240030f0b41e50035600464540c64900d044140e0619006000790b00d0750010080080c00803410740e20080c8662011980c08101901c45c1d841c00f80520804030080c044006094103010030106078120303490b01640c0000008020946140e45030407a0b50320707132a0940c6075803a401c14492058001a0011001d4000401c1724035252440d541e200d100e01c1c08100c0c20b00c54018070044c40341c145000b8860000144054802405580b59413254501c03054041440c401280740307052 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790371519 1250 790370269 790370279
    0x1e030c0307141e06040311040509070e13080403080a020105040309140d08030c070507091b030b060a0f200c090c18240c0607080f070912060b030a050601050109 70
    0x10307424212040c050390580405190018031080128051180c0c0c101d0b42d044200ca070498407100c0c01000154055000d014401095034100010303035502822200f91540700e160140703d41040c825016030003100c510080d00d01c505c3c0303515001106009503030001d00140c501040c1c00d1180c0360190000ba00c075034420358800c000303940c5811181c0010323584040c1640d00402c41141020003d460100256007004c034101d072030350500140d50b032441d140c10b005400601150f03444034401703080003038400d03030300b102d02c3c48142020300018070001c0c0822058044c84604a0400449022805c5028021070920310080c01540d1803419400c900c0c90125940c1c0c00b004121402801503000207000c141c448010340351401daa2400c1e05801c2c070409010004c41c950035007601a00c00040b000e280040c0292000103002c0310850340d01624640c50109009004c2846c010b1601c08a40412020405001d510038010700941c1c00501503503000303c040c0d042550042280451140d058401c149410007401000074080c0c0c102c0b0002d0380c03036000a54840f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790372769 1250 790371519 790371523
    0x1030b18060103050a08400503030702031506060f03012405090907081b0a11060a11030703020703050904020f03040b0703480f0306061412090c1e030c03 67
    0x3d11003d002900040c00800c0050070b640001e0031a9a001b00340c8036a11421854964407501f0711103e080140c040b0584542d01000c255240c82c8002c04084001d9401c0002d5500440c2e1510510804020000b2440300000c0031552500150b13150000140780382074407503840720f500035804d0052a5083c11a800d80700c01d03010070b942c0302d0802c0300d0369140041d040050a44030181c040e11030400c090081c1d2070000c224512113401503508000f40006a0b0305956030a180142d0200d0346040c000003a018240c017605000392014089041000c80e50000568500181d84032803c0c181106c160003990b68907507009000050000740d6001da00007941c0078501a01d501c002503126004150300300c0c0c02c100e45401343d00e040c900a0702140310485054501000c1310700502c00c010040d040240000f492001440004904140102e41100d0b0f8076110740303405800c0c0c1d8144080c640c0840000c80500d4015640003640d140b40301e00028a0b0b116061024600c1c1d540c010f0003181c078018550303040d14118815004c0f250700920070f02509038158a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790374019 1250 790372769 790372771
    0xb060604050a09021815130b040806072715032d0915090b0106021608030f030601111501140301090b0604050c0403050d0e13020922090b01030b1806 65
    0x1841d4040181c941803940c00070b034100c5c800e00e4190100265030001e0310b4491030342c040000c8418a0090759650740c071307990b4210540510303000600001000e20041c80766200000e055030708018242414440f18150305109140310700c4442d605082180d15800008103100709941c10811036009484c140041075100340850b910307031800304007103d5600403450700541064a680c46019041d0054150140440a409035001a2106d5001c1100d0ae04010801005400c0d81800480f182c1c4071410180e5860620340388500d59280903100c09582d182c000080416416030103800034041d00340381c2c00240c9900c200032242454000900748210800042e9400c0c22080034641071040c0801d1551044141070b142e110401804010700005102c400c08000402010010800800040070480b9260351158080711840302440500c80300e10003402c607000d006110100342d80d0f844401030120070305044c1d8084040e61426400c107001d05014080034100e21319400c004004d2000c0742200500c140340080407240240f0146a0701c41c0e50f840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790375269 1250 790374019 790374029
    0xf06010917030d11030108010506011106010e15040e0c130c050f031008060a060617090a0f291e1e04050709020c030901030b010806130f110301030f0b060604 69
    0x40000051010040440c00d001000d10741c44112410510200348440440341c001c2161560008040010042d240090041d154048002c0c81c0100003102448011a5501811700603038580c2e0300340b040050f0040181c210030346803c0f82d0041c8103010700c112500e040381d00c414078600186d0181d40301d0003100992004a00410440f130125039030703681c03406071480035618050300050030480c4030944000002900110070003010340940308504000070300d640b6210380641070103242e00084000380203440c20800c1b05040840c13014226500441d451180f03036540d103040e803021038800c0e2040f00c2d41c2c02081c0300c4501c0c40c848005a948204102411a1808507a00410908000c01203c003000344e09041c140408414980d00c8410360420320039011241e602d515900802c1c140d030401c40034510b0b50b502c042020300d52981d050040400c1c000003800c080c101c609010002c04e02c640e48402010382525119580c03401d15801e00e50003000d08a40740480c041d01d039612840d00340303202031710061b056541c9014a000b00380c0f240b40078011a42111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790376519 1250 790375269 790375277
    0x1d09060a0e18010905030406090f1203080a0b131a030303041110031512031704050d03091505010e01062003090111031606150602030304022b140a0b0f0601 68
    0x289407640c0d80071800c0004103962448042d9440c00c52034003100f4041d00c0360480c030800c041e5845d5803d140b0020000c5020703034424011000b246a0400024440c0c0101000094140c034004a080e5902c40f100b0010f48208003206070044c80824924448514a500142141c200c001c03003e6010301240c030400d6503a00041d81c015050001d0001681e042c0d261203c2074400c01d505c01d04011400303203020401001e101c1110392001400c0c03185007841004050348500c00061303032508030120b051141825118540e507502c00349441018107603901010303014000194001c4010004100082c050b6686540c280310a0b00307428070540003c12090700c00e07960201d0302c08a400c05c203a0302c40f00040d810004546c00444034803c2d030340da03c2e4132240030800590b0001010341102420751400762a020616a0742040040303583c49080d801a011904140306002c0141d4442c00f1281c820f4442c407840301103280250001c040000c042d4100103000c43c08102030080720400c0030034202400c85c010351010342256603040119911f0003045130194001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790377769 1250 790376519 790376539
    0x220b0d06141c02120106271505010f05040f080a1406090a030c080417010914070609050d0602040510020f01050a090b1612090c36020c0102090d031d0906 67
    0x210b01c0d21100281801c0c0000c00181c0030b20082c07009039084811907002403080164040300e03500c0c000003810311500320300c1c02c1c0c0ca4100906c110181074901548414001c06040228505064040c60700c0351003594007078a11003480900f1281d44100301951009031120031a624040307424007648508d000b180c21441042500c0281c440b403034450341e04030b40160b0361110807500a0701c2480081400c02128003a07e442183c003400001d940640360500144440010408002e0303980801000c0c84081da00150000440e04151354284400301c8074a4080082d0080e41c110390381007101007107624145075000400045010255000b0000d5840d52800361050382e590b03080240040c50080c0201e1440d9611a40d121000c02d418030b454042119480c00080c01c0d40c55640050b111826010700510644c9442031001c0342d0701044036610694110b100c004000070426000f0b82085495001c15200d200c640213404a40e03e440004044c1c00586007203140291070117048103040e007070303241152400c07802c1414580000ea008000090440040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790379019 1250 790377769 790377799
    0x30604030f03091a10050a260f0109030203040f230d140106080a06060f06091a3610121802100504031a040c0902220b0d0614 55
    0x200c00e00040d0340788105a9900284030100f03202c2c18010140071001410204503090000904074441c80f00d40065210341281c0908124980314071282d4403071240711180104a036921001e0740e9051019159081845508000350714007019808002031003526810001c40c2d200540302d8034100021003007a550508082e409a090165a2800e0406840300e18890f070700141c400800341041e6425500154080c241c240d00083d1010104046030040002420105031700092003440c2280080117a0040e00c5454078681109000c41d070b0740c51158084409115820801c048151800e03602400e250402c103c00300c0c0008507585a581e41031a00e0098590303484d01c55074600e88083e290501d1040146028481d00c0d002040d007000b42001030311040004460712940b52140c6840e0741c95400c0ca603401f40003042140811001600401c4001144100b4400594603502001030f11001d42406160070001284407120054012000001e10101800001c202400c0e40741002d111981c0c0c1e500901c4020954202c8540d0300000f071288480d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790380269 1250 790379019 790379027
    0x604020105250302010605040f0e06070507150c020610092003060f090408030601030509070b03010b0d2405100c0809130b0907020c010e0d0b0a0b01090512071d0603060403 75
    0x9845a00400b86042d024851078102000c203010302001c5016075115441000103150510030710740320540640040c44800d0b00000150f4480000030300d141d06000e00815614240081086034940d1a04101020041c450381d6400281d43c80004641c01e240e2540d4585001c5400c201c140100100180a03c2c99a4541c0d068200303035407400d80001742401d07040301c2c0d100c1900a05070b03282d42c8968069030155a44030355905185000405803031009003100d105510596081160540c00310071a41152150a00f10703403a402c01103d20805481039140c4041c9907844a40f00b0f10741285000c8008045413000c68540111407010181540e99069020025010340820f01904405003403802c01e0b03901ca81c421900005030f046c035a00010f41107946c26110140184d21106038030b0600d50f0000078044035594120f0300d08500c4c0380b0a580728102c00000400321030007aa22547c510305164082e90070138002d458002c0010340392010034001181d56561510480b018900c0c1152015414614252040c3c043c020240103480295180e4500356 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790381519 1250 790380269 790380277
    0xa05060f0d0c110a0602070b090a0201080403050c0c0a080d020106150e060d0f0c18090603120e030724021501121e080412230607140f0f03270604020105 67
    0x15043c400401c1120801c040140801c0c0c000511881c0700603199074050520803401000105603030201e0707101588410250b07801004455101e40d1503c1c105079146e01c280c44035030401001004603500900d444001042e20341c03003c903400035000001d070b008102890340c4003100900700d4807107450000841d41616402c041030402400170312b0810910314000c281d0a038000341c00d004841d812086440001ca80c2c04030540e00000d00030400d0024005000c1c284001c90035919481c00800b840441304c800d001d400c42c015116901c1c1440b03c3c3e40204000f074a200304d00c240c0f40110710200d1f49113240e841c0050041452485401c083c40402e00c0c140e6044400d0700b202e0f404aa0340d41e802c821501d0507100c1044030602c0844000600860083c009003440c5001c00c0395411091502806000750b032110309114090310051302d60000d0b8000b4241d6406a2986003280c0302101e11102c24400344142840148142000186800480c81c90701c011406030881403d8000d229010f4402461181c00807000b01c0b00ea0740007007001c140175600c030b58094 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790382769 1250 790381519 790381541
    0x5011a010f0c061d160b0a091205010f0c05030702071e030f050304080a061a01020c1302030c090411130b0a0f030c0905030a05010c03050a0b030613080f16020a05060f0d 74
    0x18000342890b081e082954002d44000d204d54403002512918980e807501020041892a100c02d081886c101009060a400750242ca080001a048800c0c2804003d41001d02e840d5080c003000c0010180040000b859a40101ea040300988034040b030001c0e20030340030a4408501c110b940c0c0441046800d6550307107803004400704001d0322a840f00323110101d8460014030510300210300c52040040c48070401c4810301100122696042d040d0342001076410901c0c0c448882485990720110801070756aa61014880410702903c10781c10740080c5420700c6d000e51186048028040c0b8905400d44800a03507558850708440c1c424408540005140c00520114060290304003500b00e800c40d04010100945620200380b034070a8090090310315a4442c4020090b40d501840b0f40b0b5045910840140502e5115001090b0382c4c0c02c0140c001d030001d40912120030f0034804120241c8000103c200803a554a00641c80070440b50040300d401a07124056018000403a4035082040780d4842c0082c441c11420308104031180c1c0300030a481e5030740c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790384019 1250 790382769 790382771
    0x70e01030602160519020a0e1312022109030c060720030712051005010608060f0913080331020a09090c0b030a0c0e10141305060a090305011a010f0c06 66
    0x70703d40010718144600d40441952080311001c1101d140104018001950301009104400206010000a060818200c081e03040300281c140d0341003551081b45404400c0100c0018000004144902461414018000c2c0f840480843d10311426400c10040d9a110b154802040c043c2203903616444502941c00d46c8401c0d40d8010203036000076503200484604150928405c4a554005c03401c04118024188035250141140c6e141c220450700e04030010030804500c44036140c2c030810203440043e140e03624242c14641030660002d903060703c904142c1030000c900710140c0b1304505000301f211034084400c00a40881032403c0c2d0010b111040541c0f4090703c10b4028001c0c1c03d01511101e54a17074000c18810441401180104084000080e924030381c80c80042144c0c041000c03280c400c00880c1c6804104903448146026101151540b1582c0c8041c00a040020007005074000e941201011401100003a00240d402048a014400902c1840180c2100e20b0002c0d00300034000b80811814003051003214420022140414400d00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790385269 1250 790384019 790384057
    0x90a12140a14010c02070609120602040f0b09090c03061c03050d05270a2012010606020a0308010b0c0601060e281e03030215040f150f0e070e01030602 66
    0xc00c141060040d034016103800180c258640c01d11542403181c2d1107440c12901c00b030074200341841002040843c0511881c46000000488030051086580c12100142482070408400e40c4e5200b41915080e0008040d544c800d8003644005100100d8440440348540001403840c02d0a0200300c2410245180c1044168200907040c130220303031200c00521031180142e003456034000c82c01d04800c0c018800c1c03542d02c07103800c1010f42150802c08002084c000f840d0b00360000110324015510552000710b00c0c1d0700340d56240580c456090290001d07a4603000b01c0c040c01e2040c002c0d919245075a0725041c44102d0340c42015100e020590003200100705261103030f075901d400c42c003006000c80d030a0074001c0c900280512000c518162404080641040448240a02e03030034880301d80e10000644a1440c2c8010703445400201c11800511402c400007000c02c03640311385514050740e00c0584240909071881e801c0c0003c04182021b010381519181e004078580800007101d030120380811404054607800c44c0e4411000c0d411564540c0c24044a0745c0e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790386519 1250 790385269 790385303
    0xd0c03060b16020a050402040608040f030221040e010605160f05210301080705090606120c09150315061e0d0f05010b0d0c030b1e011e020a060e03090a12 67
    0x51000002c02c140d0310030352400ca8010072a8003503e90b8002480f9600c10801004030a0700404119442034200c0d21304650341095040c181e00b0f01503005440c495a4181580800401f0501e50182081d0741c00101080304980e2299826940c61040301c0351485031100400d0720340005203140c83c08405684c401c80a9400225910340000b407248990f039070b25086440b01000500030424104901c90080004441030001801c180001c42d85910484821f0703d1640c40c10300015004030003030000c44a40010150001031008021226103155810503517408602080c1604114958644001941d9102c1c10b07440000041c4150400c06001940c0208a00c070b81181d112070f20341d01c82c01940d1040600070f001644a0580c0e8000d401503840482301e01d4140c800905103840001d6646071903214401d0070b10441c0b900c510907400c0301800160341c3c00c21000415034865503a071000d40412a03002c2041c6442e240304d001c0610420310104c1543c2d40340d0041c4618140c010020a104203d43c20340d1202103803a80b03000c0c1e194011001c0c1a1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790387769 1250 790386519 790386539
    0x2030703111212151c0b060a0e010e07090806180d0207051509010207080f071802030108030906070204020910110708030304110603040c09020d05040311031303080306011b0507150807050d0c0306 85
    0x1816050309110385c1790b0034000c05d1124020842c0d07441081140e0300c1d2540d9081182e400c54150040c06008040121040001d443d1801501d00c240030f80a545c4c2190003070310b46000810f403040e24001c8100414003c00c040f03ca401c42c00007540d1020f58200601d2041c0c02e08000105d44919008a4429811031050020001b045581803180c25100064940613003e49802c00f02014041e001e00300c03480880a00c100f004000c90b050210a41c3d450407000c0314020b99402c59400060007a0040000c5c156001f01c10211114503507800440812040d18000c040d580322680e6180d61607101e020413a009000142101c0340401c2a19140004603880b92041d0b40387e40003c0e03200c0720b000e8201d810800315160200d03a104c06000c181074100070003520381203055000758500001c03c0c180c80c40c141c200f0312000384070581c04008036001d82e00030381d001c0c001d4219155040c44041400c1c24805e40d14903d520030901c40e10410f01030f44204500c6000070612070301050b2240d6240100b1010b8030b800074210342030005d04056648001080145803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790389019 1250 790387769 790387789
    0x12050a1503060e0609061b0703031415101110050402060c070f0608010b070201022e0905060a0e03040501080106180f06030b01092907020d0c060203070311121215 71
    0x16100c006094a000385000d854101302800301034003607020070204039520040b1001b01e90b120241d510055141c4481c1e19041e006841d00a06c000e04a0f00c4100410140c0f1010b2014404210005c81e00000c00d00c41c0c00d1000ea44012402d450381019400c045d0444184404541106030401d1018114500c0c2801f441c0c3c102d810480d41d50003400300108800710801844c1c0e40918040e000d08510b403080740c07a03c10103500203941c4178410403914400600008284150616072583d941a01f200041c05003c580e0b268138003540c64030b004035210000185008e060042c039400c00000d4400f6100103844140d03141e403d0401c184c4c0d043c58001001316a512054002042132000c80044030014003050310049450720002c0005031030524950000302c4014072250301d000c071014802071003030300381c90350001d01079615003660001c40d0031800700c4400030f0302d100303441000040c44075400401051218042c2e5036007951101020f40d01070311511221250030000310244500320001c901d00519507041225125880c50150b803500c003007500030707031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790390269 1250 790389019 790389023
    0x1020a080108120a20072402161203051b010216022d0f0411221202010806011b0b070806100504080d1407080f1c020a12050a1503 57
    0x4140300400840008208403105114003103049400d01e40350080c01000380918490708009098030110984080b01e0030701c8510050060412070f107061602050500c8080c070a804031140c01885184070003104110005281c1045d103418220000b10188192002c9910360007000343c00e4200c4c050031840c2c1e90a030009200400030106422a40d20165a09004011649644c100c13400342d034803e10003c00180b85075085484a80d02001c90b21040100081d0010030014034a00c05861070710b880004180e50040c115039030820300181809440c1c1d14864540444280700e41001c0002404500440c011420703030342c0180810002d041030580c40d6102c100842e150007640e803030701b0381e1990082041c101c2846018248000b201900710b5150405620341458250000c1d5100340700c52418040025254505040e8202002102e2100d9017028070207884072180f4540300040e0784005110100c8440300358110f00342c1105130003900c945003041e496078600003c00c42c03851006480010070b1491400ea4814011044020003524540a18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790391519 1250 790390269 790390277
    0xf21040c15020a050d14070b090708010c020304031101140d0c0c050c030a05060c0a1709010f201204050c1e330c070b0a020f01050601211104030501020a 67
    0x1441d200d070780e103000c0310703240d480c0001c540050b615000494800200c401c200c140d13a1502607801100c030360402420340550300000780299080028091a40c50003c0e813041652981c000801400d124044166540d2003540300081c111140c00304210400c1d805400d4992000301d61814541c80c210445103070b0021100d4401e625004208040b6844050150130070042c404004103030020070094030203842e616640c0400400c81c07501100000750801142d4411400c001c90400e00310710100d1030741013000d46940680540346035400030501d0181c1c0440c03001c01c448a034800c05140304500300d10707001048141241040340113009485034860514400280e407030341c00c0031180c00c1040290714170260a0030300402450901d522041c0181d030581e0401d001c210242207a179404104061050107540e07031050300038141044850b9102c460f00c20303000700340341030082d03000308440c0883d00d5800700801a96031004010340f841c00f500c4140e941d14408012010710311010a2740007403005d1350310ba400103040c19500e6403680d007a0781c42200388600003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790392769 1250 790391519 790391543
    0x5130209010909111903020c0304090207050a0804170d081e040611031609080a120815100e03010c1707031a0307060903020306090c010f050706090f06020310050301020f0f2104 77
    0x10081c0c034a0010b401c0c2c4003502e0190f1030514403248e0707681d5a008a00500058650000c1d0040421600308020701005a00507135003a11a43d69034072001900700c4100c080841030045120203094244200759030b91090744050111250982000041c804070600208100c5180381c0e10b0018111251707107a4003651040380041035590480c2400c40c4020085902da0748190060f40c0241c202000103000401d413415180d11605c5c001d24547e071190007407800d00000d615440d400c180b491002e143ca0982c407000c10380780d240064000b800380e500520310845242e1160280310907a001000041414035109030800581c400b41404030003075081c00b1900090801030507900c500081410100c0c10800c60406100c40c0307074003001c548050004a0352001c0060311000d120005c01c01080400a101c00804c0582e0340414207682e0404420503403021245400700080d0700540305551340003044100000e0620f014000c44500c0045c80140c0c07820501600c401c245250401402c6044100e4240c1d40103c1e110341daa0080c40c851401081c1039022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790394019 1250 790392769 790392787
    0x1b010b0d0f050f1506040c05040b03040605130f03050315101e03060e0c0d11031b07170c0a0b10051c1115040f0f03111306080f030702040c0206010513020901090911 72
    0x81f2006940c108062200908c010001c0150311020f5a41c03043d0003180108042d602c42c4c000038181030071024001d000004c0c2c42c1c408000d0560007006103200b038406004480390441c0311000c00510914140030750f070005207440b00454501102c0d02061411140b107040104001d915034407040307010402100c411b40710303a50100d0308511121160250030040d1001c50035051844c02c01007040800c007a92a41ca45400c0a40001e03044100b00b00448075481c003030040c140c6035403101d100000d541c0c7c450803444025038440c00e925001c2140007060900c03903801c580c1c000f040d03070013000ca100c01c00d65410b448254084e10350f07850021740d00409840d40251f20609401003007200b903842c4e0500c41e60140001103508020030030415039a05100040e00d852000c42d10007012589100700124469201c8094003580d009100203000d0307540300752a401c01c008050b20110348201e805010030f01d400780d0120382d20082485003503440182800140003110b069401010340d000103141c0340d04c51507100c141b06803e560034403400003114100041d00701a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790395269 1250 790394019 790394021
    0x2090310050f06060319020a0504030f0303020d0e031c270b0714090d060e280c0e040203030304080a0309080313050d0305012301051606021b010b0d0f050f150604 71
    0x241c040d004941607421810a0b84920048a0201000d510090f9000071031312341c15409030b010b6500841c2c0c880c460350500705481ca4010023070740188012881180c00e0804422070070001205903031600900c035150a4541a982e00c03c080034200380e4034098500214402c01001441c2c00071002220340d806607a074000c441c107280200501144e40c00140480c0280700340600c02c82680c071000300550310740c0c01c96004900e05000c20b20307841c28846004040031559806100600110f20350b9045100818090301c00c84107800e0351899841c0304a071003194001c3d8103070020000100000c50740c01c09009401d069150010340d07620955a40d40c0d00754025278001c0403103a83e45c4184410880700300002c08004449290500031949800c80c42e003100560206038050382c0c946180c0c01d0021364415025030390795948060000720204030310300b451030003075004892142422030140984902541705015507803c101c4040d00c0f100300c40c00e40361130710002c10b00b804d00e040300d882c010052907a10503542042401c1c3d400000c001040d11a09185003008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790396519 1250 790395269 790395271
    0x31f090504060c123b1006050f01020321040c0b030708190e10050711070b0403050118080904020a03020d05040b0901060f0608161e0201140f062202090310050f 70
    0x1d02e0143c1404c0ea0405113070005c1580b010b02c2c400e6a03084006407003451707a658201030304400c920f00c1c0e0b920400c81d0301306682e40d040e0000021224140e469051014140d00120384911403e24080d51008407901951100f1140c002d13410b900a01903880c0c1440251512040c00c9581e009036101400540748205203e1070300c13030020f1540f1700d034102034004208850040c00c910703440b0311020111000c09681c07a0b002a04c03890143c6203452044092034140da207419201c07001c0e181d01d0780103400261095840d200c1c20034000a0b074a41201240c1e40c00100f442c0c2819a10002c101c041d5015440d0001010380a21450403100300741c1c0682402603200d40519201850225840c07800c40f98903a11607002050000801c000c52600030350030582102c0c11044031031010307a04207019603480201d940719400002201030340b01c80040d410361102091040f4820245203507200c80018142c204015226a94000380c500384000102040a00006490708454009814160941c0019007400070f2002300c004659210010030034091801c3c0451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790397769 1250 790396519 790396547
    0x12080c0d0224090a151803021606021203191107060f0c0e060f070c0515071403040b1b1509100b0301140402191802190212031f090504060c 61
    0x2c0350540703045000c2c0c3c2d07030750b10b0446806004450a0780020408412a400603e1040603180f8480b44900003460020340c3c90056a0f02d1005101661a01040f0300e840841d00c4040c1c80428002e03241592180c042480d590390101e00c4003110180d490001c803200f49281d00181010718042e0391b0014240740c0d405114020364118070040000c04c580105c03400180d50b2208251103e40d1509904c0e251681d41901e0148c080040e5134204c164801340c26640035200110940050070041d10a903a4009950b0b0398000e0140d030381c0158014141d09020501619002c0134050480c5030400301400215020040180108215810309841c4005240c0080d10344020070b40300d50280c02144e4009034001c2143c3c02e00600522852040a0002849031491426144201c0108040003004c1c0041c404103480f000902e40d0608000c2d441500301404130342d4110b8501c4074050000c00c00810315803407022454510744e52107e180b01c0603070281610407824013441c94007113001c041030b1181c07510072841140001101c003050880a404420080a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790399019 1250 790397769 790397833
    0x608011505010807050f04030f21031e0207050c091005010201140609010b090d0b070507062711040e010e01330303080406020909100f0b0c03030112080c0d02 69
    0x8000da43d9109007415845482032410944031103200b03000340c201d0710070b81e071003d00110b401c29840d00600804144000b0f4852140c030f42c401904070200016003e44001e0400444440c42c00322152090748010b07001400240d202c3d0080d601d03051682030000360a620705544103201604548010302035940c091050703807542c2090b0b10442e511071401d5400030300c0c801814010300601d04800304600d00320392900465215000e6018040071403031b03c0d1000303004140760803d0409964503820041100c09440196040d0042c0408944032000e08213015152503e07c12200640617800540d40d00c0c00300300040003881241000c100c01c000200368180d00182c0e1141900c071601550f07860b1100702a900c010040c1600144044940c9414400d60940e51814000001d0045088042e04400b101041105a110340303510902961900d007900015144c84084240b028029804100c0d40c0350302c2000103000c0b4a9800c080032540c10b101d65005442d2201d120811400e0400c08109032015038400c0d1051000b18502075000484c0a00b07982c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790400269 1250 790399019 790399061
    0xb0907021f0e0c0d1a0f040605100b07140715090320010507031119060c02150c181309080d18021e0103060906080a03202815060801 58
    0x203659500c40700907400080c4512088100c1c0c20800245c0c02c204511018480520041c61500c03502c3d60800a10844003240d02500c5c010020340f41418100c000019142114500d5040100e030ba0b859081182624004a2003846104000102d95446070300c1003000b000c00ea0740341c0b101c0a1441ca4604034007070b094500709a2019070091070100c3c90f6130000646504a4040c070b00802034007114220103081005020074070b8034440c0700722907840a00c034854125420010107036003111803042004500310035681081d01c2019400c00100050b107030349101c00a034601c0c80c00004007400c16414000204004071100948115586200843d402070b410b81d0b280710300140c200703400e044014921401c0d0b000501f854181c0e801107a5007070314405610541e901c00d40c07016000d082a150104480d58507480c4169462281042c210002241417400c0a401080c8060115540c80d03154010f11000c5002402c21131594419100315640b00c6140b070307100002c6224101c1c444558000600001007490814030001c2c207443c500b5201d000001e039890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790401519 1250 790400269 790400291
    0xb070c060e060123122e0504030e0112050105011407062703020f0a02060d1107020310050901060b1206040c0512070c020906090403080a051e09010221040803190b0907021f 75
    0x1003400106c40700c2c18241d88440001402120514609040c00d40241c546480c4c100400c00d6009400140910f400b40c0701c0594040480e08510291002405a0703400941c800300c800340008521405025024847d140201e065011150203584180307500c080904007e400161007004d00d030701407240551081ca818080d04040c103003900800c8480c82055000260766550300740c03001c0401200000c0d0780300315900409581c00c0c050040740c04030291030141c4030181d10b9483e2510010340d904030301c030444184c1d05824075030010996400040000a009841402d801d00c8000c009104c0001c03c0c141d6654815807064444034245d00300d07070041c80a03903034006103010b0140f20700c0303030501c004a078200c9982940300760351100218196413554160b00c4103c11140400103014405000c0c0100104103401030b0807020003506605909501c6e40c2c11803849020107880140004000b00085101000c009100818030380c3c0105001c215030342004042184450101e50400050f0002c044041c101f0080000c10184240542d4061003102001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790402769 1250 790401519 790401523
    0x304080310230d0609020d030c1707030c060504170f0307030f09051504021c030305010510031b1d06030705070302010b0604082805070b041409040b070c060e06012312 73
    0x2503102c0c1d8458a002101d4508008181e00803d0080e42d001d842d50140300580c1c640034003030451200c4102da0040f4000e11101d038150740c05068511840c0c0560b280030001c1e2407510340303800800000d4400e4a07541680101c515606801d500100204d14a000d050355480c42d000100030211181140f2804190f814500303ea804110005010344205203042c4541105407036a00c005500341c8800e80b4a44184018601c0c2d400c02e06030540c0c080303412540180c0342480c1d17628504504074226055100714110b030105e880da0404102e4410301c140800805200c001c442044540350014100d03400455190700090800601d07107040580c280107a800e40a020342d503031400d00d4100320b10b80b074545803004100d030a084104036001c10f681c1514031155003119080001c1d03c40085d2034040240a5038001c3c002ea02607410f040d20343c03001da0306111070039510841d04405503018644036680e0032290841d40c50403e480745900d50130380c0000204140000b5008240c1c442401d03550000660f4009241114800418481c0c68800f103140610b03500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790404019 1250 790402769 790402829
    0x40605060d020904060504110a1b02030a17070f11010e090411060901030212012408071428080a0e12090922080a03111603230304080310 60
    0x1c1010003586403000d1001007401410b00d40d0060354801c3c03c00003030040303a03030405d4020100021155102101d62004542020007203041c40d600a40640c010001c4d00041100345090200700c0001110b040c0c0340c0812600d5240c58025042001d896901d19034054402030360b000b54040600c21070a0314a40030701d24081d20f0340d40ca0902091000b40c002e060010f00618141c0c400d904070ba043c4220b07030103a1101c44d40c40b10003203c20f00da01203800c02040590052480c4000e4000c02d00640704000076661042203408200c0c01c1000750b00600c40285050404408040c00d81c2086000c190b10025140c1d2518400e280091072036080c0d03001d000440e1842d80150002c0c0306010314480440781da034403040e2588040341e1220700209014091180c5030b11005598003502800300f00616008260484484d0340520107122000803800b5a40b09141c4050003c860040c60500000c0c00b4004032100c02d07140790700e4040300804403519446a035108030340444481200104014440c0407150441c0c002e0700429040600f4806203a03411304041413 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790405269 1250 790404019 790404037
    0x905060a090302061303020405060607080306010c0c05040903030f050705040e04021c050f0307150209010819150b040f0609030201080f1314030310050f030a060908130f1404060506 79
    0x200020021034860050201900555002d00016614466030a01c440c2284145c04101c0c0b140d030501010951034540403080d035801075000320080e403441c2ca61074015101400b800750110381101041c24006010355651141e00e074824065280400c60089101090040b0b840003403048023807160512013800042c02513081d25170f105905440c0f04215881c040700006102419040082040c403817030b00c44c2059520040050500a4411048045124111040d0406034050000141d00145040002920b00c611141210f1032420034940e0004070000043ea001e400e0b00c40700e07001240b41c098001410400414401d245400414243c039001e842507040d1f5000138151072024100c0000030b090040841c00c002d011101c0360308655401040054000b00f0284c40701d85a400441b02c0341547c0051300c83c00501801c00407040b445086e0000c2c090501b54450340c0c1c0b40c1d0000d000c614804c3d02c0b488014010040c442c020800c001c1c020b8014001038180e40d0f441d0090580b190661582c02d9802141052010080b40d102c4100b030301c6000c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790406519 1250 790405269 790405279
    0x51803040b0c01110705070602060601080112080d0b31050f130c05040f270320070504110403050f120d09020316030b091b091519060203042102010905 66
    0x41c20b02d40d200780580011070803100355004c000b8011003000400100c2e441182c42d140c00741c03180c55070380b040151070020f800d10440c0d6034400d14501600018040100808002034215400220f600e2884003190780082c964040700c2402051769508c00900322403c0d2071f100c810085260078001d82c50048903900b2034850240440d440045001007002c00c200c0100c409070003400c0d014004006050000030301101070640703014500d101c0146114001210745841c1c2c0c00e00d010540548a0030b1580e400d40d40c511103041001c80014226024103400410103955600074140507000e40e500ea40e032203d055040003401d00742c54026250050741700d415242050141c0311301340c650400b1a144002008001800802d04000959100c802100040d440204c100318018040500401c15903040b2400d62280c0601c075a02100307038190856002c2840400102500780b010916200784102501c9600c000b000e0351100400d030a201d42090016070004a8148411003040201c0d0100702d001c241d443c502d02482d0380028002260780c1c011503000d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790407769 1250 790406519 790406527
    0x191203020711130207210e1c0f020a030b0c09010306051207030305130504050f040501050708070f080c04090513060b12101a03030714010b1f08360d0302030c030a0c02120f0a03051803040b 82
    0xad591a19140c03001103030000f4882c4403d20b0700f50a680e0040c3c0c89100e019002c04d140240204144c10031008201c10311512000401079203083d5102030700c0941100c59049032800f9400c101080d9a110703400380900031260301c000000300d0b003010300d4000e080d120001c0201c1c0130480310504011038158064500126002142030a200d9500c8030807007a5598031031500000340070f90900c2d041c440d2070100c081402110a008920800c80b04801408000c90034002c0001d402059000400000d5082c2e8660b0050703914403402c990645a0b02042c402180c01c5400010090f82c40c0c1c0ca1801381d03555107280a008650075070204882000c0c42c18001c41c0d5061400c504009031504000c1010300144810440c003140e040487c4c0c4015480d111002e41000c050070ba864600f04101c100d02403194441c40701ca0081c001e1300d000300150100d0600b5552250450380082903c0042e08086106a250a4075240d1800004001a200c9410b00656403054036001038241c91001e413084000000c000c00241c90100007001f0384d802e4800b104000d071b90ba = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790409019 1250 790407769 790407773
    0x120b010e0a09141b010906050406032c03040f0b07080a0305040c030b1602010f060503060103020d03031b1d010f0203032205191203020711130207210e1c0f 68
    0x78070710507200501200d03100f811051000302c000780c103107401c4142c0715803401d51918980044507110b00c40d11501001c03c1060200384441d5029410001d20210b00c200d101020311500364803111050340c181c5000149400000d028000004004a560060401c0f10340760b514010966640321f403588100407804040644d1400414100300780003080da00119081f22540c9003d081031000c03030a50b1505501200091361a080311f6411345041d0b4041d000c111040107014004c241c0c41c0d5001c0c40a0940c5c255011000c01d0b1b5200390354044100701d1000c91040e2107640c0d41c0e084000400040d101641c80c07554444070b0501c8501c604510026134008100c1e98004c01c00c501c1c0c000542404003a4000c1d441403010b00074147d00484a0500b1900ca21b156140c151070702038030041c4211686284143c00728440c4500281c026002d0040c9900d040c00c10660381c60f2096648080149407045c0d6840b0f0300b140088180094511040d038580040a5940c084650b20b0b400c1e204807000401c1c1912203400d040c074204049001000c200402502c081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790410269 1250 790409019 790409021
    0x11120c0a09020313061406040e06100303080903040b03100906050111060c0c120705060406270204090c15020c0a0506160f08160501060305011103010b22180603020307120b010e0a 78
    0x141143d07001e0700500054074840c01403a42e511b01154881c2c0542d01c1c104504a09480c00501c5602940440070007070b0049041d928220780c486001885000d41b48410000080c0d040e04441c025403007400707480d00d861401400c0c80c070b01c14241d90044c0e002904004003081081020980447d80a410110700781c042983da801c0d09140c142003804106400c1000c41c000304e9604140301003c182c0c0d910503807041408100b011032040064400003442c810342101c0c404064414001030400d640b01000c2d00e070103220140e101e2581d0b03d83e41d818a640b40855880103812204184110f030a18040384006020b040ba840c40c181022410309801d00144100e001d4505500304148400703200d901d2003101d00c908845c0030031440f851158113003d806000c40344002c032442e40c0b8022010700402488410343e81a140c2001d000c07803904610b203a405660000780310800d54921880e040c0022544c514041c2840705203104000410458a180100340c10080315610001050741c40300d01007400a40031011550545403142400413091f00d03503032000e00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790411519 1250 790410269 790410301
    0x1210060e01110c0909010b06070b06041104120305031905041a090705012f010c0816020714040902010306080d090f050f1c03030906020d02183a0b0411120c0a090203 72
    0x1da023000001030540240400d035a0b0261040c80c094030244550045a100002c3ca4851841040c485106603420381000038030403401160403000c444140014074000d012000c00321001a1400c07130786800020088038000c540e000c40f030356001d42014043e1248900d80f038006442c00c2c0020544003000e20300c007100c1c0301d110b05507108000502601c0000802c103100382170402404201059403c0c10a00d00c0014444040f00e10000d0340340c06440701c1448034403580c01500b0600c005840c04200072814591603003008070b9401c204101010307001d5616500e15413950b1624401c0194800d183e04101d004e1a1903c0f0026450703100c00503184001c1e20b01c0d03100c0207020005c50070b0440007046454002044540001188902c1c0c2c005038000d40032540941c00d95958000c40c1c00b00300002c5580441004070848a031070340b5569541c0c2e519084400980c0c03c007110701c03181007095484001e02042101c080f1201020b00d0340b0400d642c185074140702c408010050003000482c00780c4000031000c040d05e108103101c0c02d0300000002c0c04182144812 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790412769 1250 790411519 790411541
    0x619031401090c120807020f0627100804080304020907050c030309280b04140a020603040b07181a16050f010903020d0e0d02060d021210060e01110c090901 68
    0x54120440c46405507400b80100c001d00380c80d2101c1400c004110300b1446030b0340300c216962026a9528000e0079500780305d9a6850841801d50180c41408035500c41da80b80e070829170781d08005205881d0407103241010001010a0044040100280141040000b0b0a42400c907508541c04882100b01307503031a002e045881c2d20840804018500021050040c4000e0009030144803081342c40e2407407140b00c040140d014455401c59001361010400ca40842d0100d80b200c006110700088983c01e0b00c500c90700c00d40202e0040d60003a10701b19100c002490401c240da40d8808402c501c02d1880000c11240140380030311103003042d481072040101486000038001c0b407283d501110109001da1207810350300d02c03440307600c0c1080c000c000b5040c0990150044800c99418a440f80c0707400345002134010030b01d0040d03111580a000d1650003001220410355820000c2007486020204401d20840e04507016a40413070130300d44003e208030b482c1e05000d41880540c1e0400392a25102040c0c2c41c81d22002a02e20402d0381c4e9400d0f0420b40540703540282 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790414019 1250 790412769 790412783
    0x1090e0a02070f030903020406350c06070308100f03021e0406150c050c010f020d030b040b06040b0d1a011e090b0c01060f08070303020c0607080702150a021005040308061903 76
    0x54205034001711804212402154200451940c8182032100c80c803d140740c42500c12215800350500c1c406805601c9610b081000495401103000c0c00894541d50000c001079000c108003a04000c6455030f10003045021740b0018051088152840d4003240c0ea240c211512542c510109018101454a890b8007620090050ac00c401480c0c21a290000d45066404138003a034490146186041c2c0d1540920315404002c0210350042820202c488000c80081c098902465842a10b5119200e0300d983c03007034044c102400640c424240d6030540f0b00d6903482266007004172044131100c0f41c100d20450340c1e0404882000b0314601c8200914403c1c56a1040300e0500c0a03400400a182c070100703444140aa0552001c0c050b0b55002c00007982c9180c075003900c00d60ba04641d100050043e800f9502141c540e052000c040d052840c0b052480c2818a4001e40c00103124402c40d040b107151550380070030003210b1180d0404c4480712014015004000d1414107032402009020020240ca00400700607070f0101d40074104014000c011a00800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790415269 1250 790414019 790414043
    0x4122d0f0524010b0a02010b030102030717010812030402060304020409170901170c0409020a0918020d0c1106280e060609091605042d140c0901090e0a0207 68
    0x350410012100d0380c0d05842600c14000401184480b0410000c440780150418070200e0b0b03c0c01c00030500e01d9100054071000c40d5281c0460303c8d41904c09002550180c4040c0d2105c4042e0081c40c0c3c000300c81ca07101644135003110b5108441c56102810094202da400c180c06a034529036a075114000710740030348442c407001480340151071052045005075801801c0341a03400d99800300300c10b5003160186c03444641603d480e001d401c4204401c01551040ba4000c0078003004c0d509040c4102681c882c031841d20103004a141904098000981c0d8240b00e06030b00c25407071415810309000c1d0010031425030495940070000e10065050210031190800641c06000300c1c5001c2042440c03d220500d41203a40d561140e4003a144140204030301d40104000b40404280b05000841c0141c030070490364a014100270181816421110801030001031440305a0341c005100040440c0000c0b0218031000700b424010110003000f445075514460500c0500c417142c4c0d0000c80d40d801c44822001c00001600c0c1d85005400a1103000001424075500007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790416519 1250 790415269 790415273
    0x302090a1d091b041802211b221503032d0f080709230a05010c050d08040305040302040f1a04180b1b040303090603140f061003090c08030903010b030304122d 69
    0xc0c00c1c8205861890680c2c0420f4886109400303941200154180d0020f04c0d60410403016054020420501049d10000714521403241c00e0080d10b0f00840d0419030010322000d00300c0700140e01865500341d005001d03004020815110310001010000c00d00803060800203040701040c01d1600c50324041000e4080a03e04602802c41040307050f185101240140d4001c6022800c00901503014507401d041c00c54003c0054101d600c070300c00342228040c0000f0403c4003480700034007000c40581c90760310449040010514002610803071204180f600071941810091151f41020f1000d0041c5945642c40c1446942c450002515620b400f02d90b9241640404048000e044010900009240c0d01c94844000c84a0075101002542c54040d150f44200c101118945280c5d114100840e0300c50074806010603c00c0380c41e10b400102e4141c2640d5000c0340d00030560046c4510751010807510a1031800b0301c2214580502100250b2910780b821619040020309518090007614520b807400a45100904882c10000141e4510590b590014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790417769 1250 790416519 790416559
    0x306050405070f12021906081f0b160302010b0d030207270c030501030201090b040b1c1805010b030708070f090506030f06012702030402011409010302090a1d091b041802 74
    0x180c0c0017644210070314800159040107034440f49081d290789642e40c40090b03969150981140400340c901c0d18004084800000c1d0f14003204000d495680c3c560f002803000d2245030304009094031204d902245c46940284160000070340c001608000700e8285001803100c503800c03040f20340311640200300c0e14070741d090074850450300d0240c0c958841e9040e60b100b601d40c0c0c002e19442e200a0000390089005e41451008200b2002503244024001e03145c0204450f030003c03d016030504080851400c0c031b035000320b42603174550103040094601070003410040d1840718010002c0300e203800380c4901d011170701e40310703001d8251b542c3c0303012542035141400300e111201500e10031500302d56542c103600d4482010100200c000c41c01c2c1c1103d4402c243c2814000c482c01190140d4600c100184003100501880d40700c40100b0307051603400c000401039500c070401240000c101200305919000180c1c200302c0d004c104001c000803803039001035510003150f1240c1403140c1d0102c401520001400c403800c240703980345902c001901039845054004400e02da1035203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790419019 1250 790417769 790417799
    0x909031603110a0f21050301120609080d020c010e0d02010c02071715041b060e030a02010807050d060f18020c0613050307171c0216060f0b0621090c0603010306050405070f 75
    0x640135032030b01722445000040314980030a00620824082505c0d03040702140458101d55040390182540368a881030b03100d400404c0741d0100c40000800d9446941d9040b00c5001230180d15150f000f00d00080c0040b8410b0b080007510380c2c000c0e00521580802070fa2401441890411118620341c0103010303812070034100b41c10a9207403c0d000c000040c00741109200701040302c42c4200700200d5484400360007010505015070054500480007032900007003200900051901c03590b6402100010987c28a00f4007006041c080c5001c0418001c80b010300d402d034010010b00603504000117440d684103004c200c0c40c01114420703240403030840c45100b41c080c0026980c21102c1d440224290300424010307811514422500400d480303070806a00030310f50303400c80c0e000c05900d00706e011a0464011542d80c1c074200100042c0c0d5641c140000307565030031000070703030303582d80443c0c2010144a0841c0100310340044003003008000c03001d0400001280c5110501006000a4490022600b000000c000400c0504034480c00c04115136201c480c0ca0080c443c1e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790420269 1250 790419019 790419053
    0xb0702041a150d15030804030803090a1b05032a09280501171c12201b070806071b0605010305210f0901050901091d060909031603110a0f 60
    0x100c0e104515134045842102e000890381d20500340340c24245103407a004215040242604114090307185901c00192080e414240403080000f003445250741408145841c1401004180a604410081c645007e044880c1190300c2820105d0340180140d40c0e600c850311306c0e076103004550348454002440750103054a440d0091816103e80340d0300002b0501c40044107962b26024080440c41003031000032090546480b400540c402d50045030004542103603d00c2d01c81411140d180d58942341c100c0d0101e0003111010714000800b124410340001016264200f0102070b803250340141c4010b0a01c088001902c581c3d5044558032180b0b0390700b105081041d9a500c3c06c00d103845800140c400d800080507080b08032041808d0005549081c0c0303c4c0c10619007400040001900e20b030780400c003a00d06218500760b000408101084146100340400070020280d81841d02c20720000c0742d0050000e1007070307420034010b0302da5101a40c0405483d039501440c1810654030701002050170640b1f0044080c11100d0f010f0903503828010025000c030390b000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790421519 1250 790420269 790420271
    0x6041101021506010324090e0123130c0302030f101107030e0f030319030e010605040c0e0910080d11060112020a0315140a0c090b040b0702041a150d 65
    0x50880004a8881e10300c407a80c400502c10b000c0c089000c42d4402d51001c0d071540d4000307600c43c01825805040801c0c00107154004080c05440c2c0c1c2c0402d4480c002030207460764840c2c5e19001200d030b80354000c1c8080c0034610010002e0b410000c804290400b44050070345154021034010707064906008806030a56101c684a20020101a084c0380f02010102c20304d404481d4969016510600000121001c008400d003455006503403520007440b1000900c61018002041400c85841c0021030703804181c1402c2c251090b9a0000f48124a02100b02e00141c1d044000308407a03010403100004960750300107111143c2e5003c1e8004414a109000e190035806810031407034403480054404541e4160390304d014485505c40b05440080d0400030718202000001d401d03042c1103960f540e081c440810510f00c0442c10002d6840102c840d041c0d170310344a004042e03400c0d41024081d0050710780e40000e14a8181098106482e900c900f1034000d0195a5601800f2a0340b841d012164140c020000c2207040301b04080c814440990304011010710b803c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790422769 1250 790421519 790421543
    0x51306020d020c010c1d01110c0928050424060807150e091b030702071d061002280201050408032a0304050d0f1b06020709060b2503050412050604 64
    0x503e0290500700314442013440440c1450f41c141c0f004499400d050003503000f4509c0755280c080301c56171b0f804407214894610201e8812a8045a001d030b2a262081c581151b40c00d0303403814051001013448082012100c40404a1020f2101d07102c0c00c1c0040144000d502601c1240078401000c103001ca145c0302a06841706247d40c403080004e039160104000c0311000d640da5000c05c90620f085050301c0410303002455006505006030354859507141c1e006803244000c403016801e4a03458604020052402075281001840544003e00913140700c03400c14200e0340f20100c0ca4902701c2a001c0040e03011a0f1203042184c01070580306050b03c0d224107110031016010318000c0000300c408042211000c184d00710010a44048450092402c0c6c8100e1481c1c0701d414220300b034180255a8111003418182c041380f0100001e0300245001d50003021443e2800c85070800f1220300d604540101242040301244c10001c40c80180c0d0200030015420302c1520042c80c5c10740d142c1c032507540100301043c04034280700280800030440d54812800780c03001540d0b17 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790424019 1250 790422769 790422791
    0x200a080405150909060d0201091d040b0f040f0b060d140303041a0702030403240507171503100f150303021b0907081302121006030507060809060703051306020d020c01 73
    0x6010ba1640e140d0000801030014440341740c10714086e49000d0041c1000118241c0ba014001500700040045400c2c403a0302c002031200304030041e240903a01c80000501d0600a0a050783c403100102e80c0140050041107054001c1222591807000410006620400014801002c0100c80f62a50000c44040d207100c15044448105c81000305007143c81076140d9405103107003a0071a500e184146248901130034000d0030721003030724282481c81c1c81000e004081540780c02d90741805400d49440c2c1440e000300226507516010340801120741300040c3c60811003000da100800e9020381c045909008040300424503030316000518000043c5600030403105072070018000c01c260040ca8110902c09900307410b86459000540d0180001d40e404801070110100307034401080030f0003501504050702d24003840d90446000b0681e4614007002084030030080c10300140080c0c184503220345401c024040e11100300620384001e050716500042c185149014081d00107a0740f01300119181c078a0070b25008025003181c415840303070350310f03201002c24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790425269 1250 790424019 790424059
    0x18121401020705150c120903070c30080903120705010c08100303050a1103130819030c0312060305120d0c02120405040e03120c070c120f03200a080405 66
    0x3240c40d040340040100c00200d155601100500510505038901c050040d60101000b100e01c15000d50100401161124214204101241107aa20610440e400e024242040c02140300c01c1c0414bc0501c044415186401c40c1004d03003051099603400c6915001d81080c42c040a08170901600c11345024600801121100d40c0c02580c20070b10543c0c91016902002c80c2c1000024806c20040001e021145080c0b0b02c0f880c0d500c040c2500d59003000078090f2000100d11800c1c8481c182c00c0141c46801c0d107200704500d095108585000d4402185450040d08100030710302900030740308181d0069401194450207da009000e0f1550070a043d07048601040e41c10b90512900300c1c1501e100007560072640302020000ba241a1400c41040b004029241155840b80002c1c031004401c5048000141d1082c190031550b01c0d518400c5103030100c440340450f04660320800c0c04c000500081000001d034a000260305007005c0054000b14042c00b000790041d088205c595105110a420170402c0c60340c040c0c4221001038581c00310400c11400005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790426519 1250 790425269 790425277
    0x51606080c0702130615030e03090f060c070b0c0c04060905150603071404140a050303030408160f06020a1701080708030d0b040b130504110f0607121812140102 70
    0x200100d000c154400018001004410b1008044da181c0ca14501289070030303643c131a8004000c9541c50f1190780e00054041c082c404150008101652a04840d20000380e81c085000341e02a0040c0c401043d0031a00384010480c0d18098401c1e5100c4035107586070710303003520f030390b0755a551525020f503040c60310018544000d80180c0e13000340384842a80312115035800520865400c011b100d031040240241080c6d09104500006202500003000b00300c62030014a4144024400640d011601903401007041001040280d403d95004420419002059031039034201aa40c4640740c1e000541907030b200040440d106500203400312a803110b40c000c58200e50f070703880c1540d58a030f15040c420307502e643d0410000d403100c88050b540320243d1044005d000042c102e00c00c10205080301a00803100c042c4075070702d405100c10300c200003082100c5400111000f0141e01071034004542035020b0303036400900081d4224105143c0b20301a1200002c00700e0310208500d41c140d5180d500c00c80c0c2e80d400303002c1520800c11020000000b0391060080b5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790427769 1250 790426519 790426529
    0x30d05060118060804030c02040b190e1b0406050c01020f0d02031e010803090105130324050a0c09030f0228060e060a051207091d070e012c040f0f090516 67
    0x4c02e6640da81d107055a000000d0700b41242c0c0b166561141034082d07558030f4554009840d03d4502d4000385428400300e403040f4400030b40491070203502e0701148903000041808940c00d80d441468080d4450a61f00c0b210341c0a40a454100d512012010502151116065000d90700c075007030442c511000414190109054040203004808064001300400c0d00b03d540100c1c014044880288000c1d030000d540d0342c8030046002e003e8646c201d9400ac00071030b42d60410702c2c180280340d00803280d81020082842c00d808007074024001403000601c00030304401d000c1c055660b21078044811100c40c444281d01e103149419610310b100050701440000c41d0907001c501c00c0c2c0e810007506485141c82c1d140c0300c0b20300e070082d90400c0c24103c2000034402000c105501d000440c2c000001e03140c454a8051164610445081c00e81001c0c0603c03c0003c5801c0c10080955848489801c03a220103081d080c0c1001081e0540e02061300110307000d4008112a00c58850407c0007810010603c1d500c584500c600440603610810000100e0300c00300c5540740300d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790429019 1250 790427769 790427777
    0x1e051005150f0d080307320c1006060f08070509090405070f0618031e140a0c0510080a0507031112070e0d0b06150c1c0207060c0c09090c0503030d0506011806 69
    0x506c2c464011b03a40c50300c4501c0d0303000701240c40d40280111408900c6078001c0300312100c00042004482c8150811940446042a0005000540c28000002e00708008000c4d0403003002000c10204078218018000c41d060386a0140036040c840c41c003070405540e90781113842001840f00c1e0500c0b0009695115070190307041810800181d5801070b20710388a14807040750003250010000101d8841000151840030111340385c601c0b9101520b08520749081a840800c4a03920a9000303100364800003001c0340c1c1c04107200c0e47c4100c5101000409480d242d001b2002880c80004201c01c03400002031101c0c550003241e003010b12550f0655105000d044005080c000002c000c3e00c00107201c2e070b076504007080c0c0b103140071843c5422000000c441e80e405c05e075000e002c0070f00e884041c80b461441640010031baa030392980d042c0001800b6050714200580f646034550390f0700c113004600d4810741031b101da511800c090800c42d40406100040000034116510390503c408044001d02003510f90361701280190b4504c2085110b0b4850b280c044440a0721 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790430269 1250 790429019 790429021
    0x60315090c0203090607141002030613051f0b0c06100b040e0402030c041a090c270a050301020a120605010e0907050d06050307180f06031e051005150f0d0803 69
    0x10300e40c4041c00c2075140380e20543c0070a101008040c1c0380d90010348070060091481c0c00800c820024140c0c20207000c3c01c65039000398010410048151a102c104480851540784001008c0d07441d0310f4074007a18000c0300750010501e1000c00001940c1010b44001d081034040300c8007a03801783e4550b41d041049041a40c802c11190000500c01040240110081c4e9a881070018090321980b800c0400094101c4e44801c42001865078101d0007951a030801002d4190300c10000c0704858501081140e2043e50140548044910f260341a000d005490b20782c411100d008080150007503490703404541028020b000340e20040c07118617140c003c0000340d962196042a4905c1009442402d00e601c0702d00d0102d40c5580114040210b40e074803940001400e880402001006200c1c002c0e4135600b80140d0550790080e03c4250b07500c2c10180742054018408500d00c0b0b00c01380340c01c102801c1c2035008003995140c440c3c24400d152000d80c803441c0c82c1a04002458542c1070510700c0e1203c0c2143c03005480c80e010310030880310902c102d101401c0541c040c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790431519 1250 790430269 790430279
    0x1d010f15050112110313060c090f1503020708180915010503040b090a050f0d14040f0e060d050607090512150f06151306260601121407020a0c060315 65
    0x407012040c1d560b4541e008204000e9814070403144d50f00582c3e0780794000c0303800c001060600c02c4a110700d5245a855140c582c01c001e14080d1800c40c4416180907094060f0b400700032003001c007800396040b121055401003401d030b1a40d5210009000b62035106e4219809103c401c00000c018140202c100d00100a050310f07001c0c19a202c0d500c814619090080c0050881c0c4210020784000c2001000b0307068042c4145c0d80100324a4526800c007c120780b0810030303600d460182c18803091250b101d050510005030b84495004505681d10200000c0c4650903884001c1d08502450080c0040c559000c1c09400595a055034000c41c01598080c00da030340e80219002d400040d152040118800703820b440812504882c0041088500700314465020701c07035a0144260300e1081403072280803c4002d8114103081c820b00c00c041040c0c06015007694000f00900070083c041d074104004000010910f0489500440000718030980c244d81c1c500d891000a943d403000b810040d1001d2410f1400010414400d01512180030700c0710540f00c44880c542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790432769 1250 790431519 790431527
    0x1e0c05180a02030612060a091515030f0206040b0c1b0108070c0609031e02010204090e0c0603011503060b0a05090f0301021e09041b080403030b01020a031403060f041d010f150501 78
    0x1404e000d03884808000d112480020030060940200803001e00050f0300c294611381441c0091000c01d030034030070038106a62603e004051129410440f0307003222518483c900c242c030016101d441b641d0000000e61a021038140c0704110700003144000d10f030780c044080300d41d4500080196000401100e41c100092542e501440001d00541c00041c03486119003060911511100c186500c003120415000c00107039170100d002c10070f8841034041d1402c415104406414a8024074000c00d505220500600d101421686400c0c0b03503882c442d0740100300408200404586030b901d4040d00400f280e0084144038411070b0002680100c0e40381c18030032504040004501c0040052400c0c441160f1600208040d80c0c0c8079079a11042550280003203d00b080c51101590340050502d000e150203022a10341d03814140c11503009103000170000360441c0e5510219490301001c907450340e40302c20004441041c0001069040f0b414a441c5e0b00d105803010104080071190340d002444112048040350048401c0181621701850301c4034010419540a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790434019 1250 790432769 790432771
    0x90b0412020f011416020a0e040305190216090902181909030201140106080708011e060503060d0204090302100f0902090a0506061b03040306060b190f09031e0c05180a0203 75
    0x2040c10041104e8020300d52100c0c20b6042007a8a95006102c01101404c616012101c0009451001c406075440d062580300203000e80103084c40c0034102c215598055110398000c10000d100502c0b0700080c0151552120000c2c0003a0600ca001203000300f1140b13400c0958681c51030080391003450444145500003240015250190212001c258159540c4800700300d407182a20070024040c1c0f01c1501c07401c44034100540010440501648142da04140b040d110646983c510b000388000c40e10303203280482d00c03529542c0001e0001ea8140e007009621510303000391181095004a00080f82c1d1a1a072810440c070340c60300d000c1606407500071000941c0314041da40000d40c3d440d5158050b0340c0081d00900620309154200c000d580d140c02c0075002070b02c880c0d40702250400c00c020b010300607500500100d9078614203041c1020030418090101d107011005103c80c8500d4030545911030f441c188000c43e00701c00020449001404150400c844a41c801d8680100d8013001092a08008080160340a10700c18101d0407642d41607161002504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790435269 1250 790434019 790434049
    0x120305060a030c0e04021002030a0903120e0d03170c040815070302070c03030c02041a010e01210c03060f09060b0a0302090d121106070221070809100f090b041202 71
    0x1150741d0100118000c9041640a860800000f0460342001d004119034008807129800455104001d18100b080d0302c48042c070304903584507110094508107982d0507518800310541058001344098540800c0c1070b4400c403078151581c1c0300e1114804684840f00401d0051060780903100143d8032051310582c8010741d1000b415800340380c0303140045c2440b100d60740300e00b9070442a074400c4d0000f0f10101000c905505d401d02c074000d1401050807600c0c1c1070070032404c006050741c101040a18184607280c042079605440102603e02101115a07082102c8000c014025004200034043c06405558210740401ea00301c5911812090328446048981009400740046002c2c3d4440911150000c1d10749050000083d01074141c8401851543c0310300c8401c00074514031601c0c10700000c214008650207000c50742c04010009014079441c050303078088203613101c8860810030094403030a568250000f111065001c0c81e580d0103502d5400740061360b40c40c240c1c6a0307030b00c40702d20645005602945101c4c4600351103607001841c21118417a0501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790436519 1250 790435269 790435279
    0x120606220209035803091b060809280c0b191206030210030f060812092d0d110405100504150803070311070308030a200712030506 57
    0x85074500420704010b13111141924040c800031a280f0044482c14805401d140c07202090440e50740d512181e420000c80c4103440e0810208600080c240b0144240c0011007450341220034659010318a071940c0c03080511340d118540c0094091070105900f044007084c45160494640c070f45482201000e00c080d08500d046000844081e00300010000300c28035407901500d0514850002c0c045000700808c400b50103100301b15141101e8038504802400140c1c0d4816801422000918000610f840b00c60290070082c191600306404c9840780360703080f80a0540070b40040071800f90544103241805020714500c8034912416540c2c500c000c0411842e00c1007418100c0c0ca20700a079010f413410000c004003400100341281c1064035405105990441c0500540c1032502500c400760081072343c80d0908910b48280e0350344a001e202c50080421030404174120b2110400c104200142da00020101c0d56824507112040080403a0642008074845103028500c050181e4425982c2d0700360083d149105180228800314010803000301019401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790437769 1250 790436519 790436527
    0x3031806040f0305010b120f060a021c02031017150105060a120e06010f1401050403110a030b010e0709060e06030718080a0f0b0f01120602031312020303061206062202 73
    0x48802d0302420001140038000008500d0840c2c81488028039010b2290800c1e507100d0405e40c4601d01e00000c0055104c3c2c480e081c010f80b6000d00502c0ea0b4006000e40c02440c03202c60012007072215200c00f0003c004111901d410300144001404204243c0b40e0102c0b020002c131441030b4a00401040c02c06030b0080500103c00d1410403004210141c1c05030483c0c1c070400000e1092340c4140300500c03408824240502c051708501031a10700419507000024058420b5010081117a0120f0940000d0b5071202240b06c1e01641c0e000c0420709035580c44200b4184900400c80d049270009059581c000b44041c00b40c0d03203a0301e1008025121510715031390000c041d190b00b1409181da16140328003013400984550305201050b9024814040c80e10884194240415010000361040c612108448010800182c8089104028550001c805610395885030700c55244440305020241100f8030003000d030000c490707020004611840c011924044407400840c540c60350747c80201c07641074002c4115461041c40d4000c000c000880304945d420058a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790439019 1250 790437769 790437779
    0x603020f0708030f0412020318120106030c0b07060624050c0c040c0203070501050c0c0d21050c0d0f050c1611060a02150a0e07030b04050a0219060e0603060303180604 73
    0x281e481110098444c2480d24140800c00c010b44902106c504201c3c8001c60a0005c410111a00b00e8440c0c01618441c080702a812240c0200a40060009680007054261140e80d1004004c949170b00a101c00c56820340391017070210300300382d0500403100400791500710b02102d201712010503101a441030070740b1140b5100d1000c6d417440b150b40324011581d03004140d60180da04c80046207065400d4450160003006404020701c908006a080003460890302c02840c6484240c101c9045520400d61034517821410026041a0400200810849c01800707072010b1000c0030000705406145030b07802c43e8016a1510740000b400c001524445841c0c10071550b00303038041c0c000ba100010960b000610b05600c140c9a00001da0451240e0b0081c82c00c49642c44c5a02201201051180f4810b00c50142c2e00c603130701408020304100f0280046001c1c800d00b042441c0e0480c0c3d020b04a40e0103089100601d03040340d1000d20481000038400030000d6007a090140a99000d048054000c1d410a03162100d07954180000034000c0b034000d00103100c0020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790440269 1250 790439019 790439033
    0x204060e0405040828030b01030501083a020703020f0409120e060405060c06040b091506060a0512090703060b01020d1b02040b0306040f05060709052101290f09100603020f07 76
    0x310070304000c40c0703650145c03250000a01500c2c04022003e040c5460500100107000e40451480b00e1094803007802c55800c075000c400d01e01c0d101c0800b1a0b15600604814031400600d40019112007a64003c583d0141d00480c0481044140c42c52000002c10209c02c0100e07981c0c00da8083ca54070740803868000c00150810352140c01242c80b58100d44210301d441d0f480340040c4000c0c40002c008140e003203417018001d000386040b203640b9182540c20140046024040c000382c0c41119074841d8017a41d0100600c0315183d140d505060788480d58841e1940401c3d50102d00d88504041c6640c0002030070031605003252290320020340744030114484460800c01c01d07a0403d4441c18546101d0340c007405013600c02d9100d07640180078003445044c0185082c1c00101800c01b8008000c2c0244459503503004001000442e130f08505109176040002075016003024103e020001c400415100000000701d0041d0b41d40031002d4844001080c0050308102c8040d00a4400f50ba80003281c60b014002c1921036001041e44108140c2032034a010982d54400e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790441519 1250 790440269 790440307
    0xd14190302040311040207030903111305011707060201060501020d030f090c12050c0102121206010c02210613080a080c04030f0c050108090604121b0b01090e07090204060e04050408 79
    0x10000e6800142441044140503c0303d03180081514110306044030b55402505aa04c00d00025080c0c2c030500010040303e9903140181d00321a01d041d03400f440b09507507031442d0a071410041008100503014010010034007610510401040300c40580c000d00504190501c00e800070b212a0f40046850b640300c040c0c12012519410000004281c040400c101540e0641003e500303000c03540080034110342080e64519102c00105041d07078001000152080c40c182c40b4400107031904d0511100081d00900d4a0f40c0c00e00d80c440e5802c5081081d04551400d8569954441e101c040c403440c481c20006040b480c09010080d551445079100c158050200480d0901e401e80304d482e161003c03851200100d98001c2a10030501044d68001b803869009469500104814207280e9907103a201301c15410b0f10020841e122482d07919070707030189004921081c1c000411400035615400110081c00041200f200303103201c7c0300c0001034259a984215007c41d0304680d941c074007000030002000058a005001030319141028008854002c47c150400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790442769 1250 790441519 790441567
    0xb0c0c01141302130203090601090b27092509150f0b0703270b0322050609010b03071d13020613050108100308070809031603030f0e060a020d14 63
    0x5006084020f20401041c2180c65142042c064014018056981030024905042d500f014101291100151010a00c00700b07031080105102210005110480d0103481f14060041c5d045100741d401d418681e60310580070005080301060307802e041200401c00f02d122644400d0100316806403403100e41d60b80c1e409500b20300c0d03041d4104480310369002070700c281010740040b200c11703600c03007141d204006541d01404500e9800003680725260001100000240c2244011078840215141c40f504d000240280da04149940f400100d400402030340c64420982e2283ca000140d40045039151741c145050301c4048200600c0a0340050000d03400a0101c40b6044010380c1c800c401b40c07403001c0001d8403405005180c01c000411a600180481030a00c2c030b1134074240040795643c42250380701e50b0007054082d40d0f24a030201017071401413070f085100c0c42e02113031070008010140d001151442c2181e090340d072500e5805207102080021310030003210780007603440030010900850043c803000100300071910405041c56000c0300403604214440e081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790444019 1250 790442769 790442791
    0x10605030a0f2706061802190305160f0c020901120c0b0c2a0a18060506031302041e0f06060201050a230a061206090317040b0c0c0114 59
    0x8100d503062040c4075003003180c4441d6000748402092010b50b424543d050725100e40c5400786948a00307040c03003043d4000741700a05205034042d52440481541c2070094002500f103c030070407130480841e40da0521901601d805440300400c040e65140b503480090315008a07541c26030003804040c0001d02c016940c1c501c0424001c000c02000c210315240030740fa110b030014442d130300030101412b000d05c861039140c8400200719410082901c1c0d01c0400008045c2022092040c80c02a580d028a040710089030402041301c4c0c1c00340f10b403041407080c8080c0d034031481045035a01003203901d0013110008841880c054a8142c102aa640c2c1c1c00c00441d444420040700b904040d10201c0245024698907480c041116690901c15140c7c000b035a18801c000d00380c590610484201543c01c2d0300b4a0f0310301c4134000b04803520382562249000300300c0030417446100110351403d4000f40107040001d4003c121304401c500e000311030300c0a89520513070b480341103505996182004112550403850040800c1e65079a42400f0b0440140b41c1d0290007100c030315074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790445269 1250 790444019 790444021
    0x80a021507060b2106070c0c05060a09050301052e030201050313240510050316090203180703060519051501050c0312010306090b01061d090406020c030d060e01080307033501060503 79
    0x4d01c078a843c002800a03001c021140356114007140742c030480c100548504560040d0b82d49940a0110b0b0283c2e040d4104550ad5440e11041c0400c0e0500d40459031280d00410b150038650004811a1003007104907480040e0100344100009020050018002207410b486011522400d42410f9030308801c8001ca2042d540b45942d542c4240240886640d1040300241002c03801412484a8070410708260358042c03082811054000c0085000c2c0c080b102503004882003003030b040b031324a2580ca0601030080e06041c2e0b00221012000311003501840501d0182a10452a442c040c2c00c0c0c4a12400044556034484d80c000380c000d020a000230700c2d440798080b400d07138000d41c091040441c1c4001c003402c0078180300d031041e400002806105203030703454144001d01c8811000e035012184800ca036a0742e0b041c008040c2c852241c0446007070100140d48001200c90340d1140c400d94803010703240f03030b15aa200c0543c2c60381da00c83c98202501050000007842500304552038220000c008126000c0030b09030200080c00320f5044281c000c036000c620044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790446519 1250 790445269 790445329
    0xf11040605040915020a020721110f06070f030324081002210405030906040b12070203040b2215020307060e03070209131a070315080a021507060b 64
    0x1018440c0034090407039040284030fa0303984d00c0c02e66142d5100f0b02401c01c2500031940d040810b000340011401030040920741a9442c030030a00c041070035141ca2808035030051184040c40603a09080800c8081c00704060f084924000c181d460701d0300400c21041e0100c04041d19150b03520762240c4000046013880240c941b00381c6032030f410300c644281061541d1a602101a01c140000d00c0d203007c40000f2100705060040c00880f40761100c0c1040307030540c032a84801c55001180018005103100404004010200327050151803120341b9065001c903100e04c40d901c603507000480103020041d040303218410040e008850f02002641080e9841e210008031000064040f4096000070070800107200c40ca005240d0f1400400c0082c52401869600140c03081c0c1010303040302c4205141039050310070060010301c5204282801c48045100d49490040103014000f51103205c0c112905075940020341e03c00c0002d2a102e0130f42e004242000440c1c50b0b40c64080d103500406425900303103440d10a20850340d22003407404441210000082d110043e001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790447769 1250 790446519 790446521
    0x30020c01030509061e040507052d090f0118060305010c08010f060c08121e04051c0302071208191415090f0103020f06040806010e0702070b250f0f1104 66
    0x1d20641c4103070040800c0042208417040305030713201384401910b00b1442c1c59a0400500d420a140c010640025090107454048200c19020091803002c4440b0140404804018049025400d880300c2c10154481c800502c4010b5080c0003d4001100c5484009034036642d80c0c071800d0950b084001c4c0c0d41c010a48520061001c2441c00c640a0301802d594144514000c00d01e9813611a14880c4031005219614a140821a030010400440d006ea0407a000c000080382080c4c10241d4440e4681c03000b1695203e00c1160304025140240241c801c00e40c2c001710b41c030b8028442d1020a0780c618000808800e1407000c5060103042e02d02c850320404289913000c0c0c0c00303201c0620f822041e0384680222005200c0c07180340c10030104a010f681142d20941565070645058802c80c00c02d2000c909640100c2e0401c0805000b440f0010078017808641410313218048903400c0f20b55480e0b030765007500068032408040c070340c43c90205804108084001c0310706604080c842c2040114403c80d030346070311000d260001011901000304800c480c1c1540b0b0a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790449019 1250 790447769 790447771
    0xa0b0d0c0e011512050406090f050606040b011805040b12060405010c02060705070b0a1a0a121205040f03030f021507020a1401180b13120215101230020c010305 70
    0x1c8403000c42c3d0600540c000141402d201180b01008185c0c0ba000054100a0030307810101ea8960f03c4482c6041500661800c9500c4a0007180e456001d0f901c2c29029802640c440e140c8038100030b06c2d880c14920224242070502c4003a040c03c82c1da05401c0a21380e14403070a484030030001da038411809100001070965000600906241001d07005808220060101e4408152001d52207a0028501c1c1c03000107921b802c5a50540c040362011501c140e05c03941c15500050404d544140c2d103401248109106000010340350001e032094003880c0034030214541150028000603016080f900003002043c01241c400c420025800294485d0496030100141c01030802e480801043d01216142c2840b080000e0040c44008061400d0545503980c01918980300203010501084914000c4d201d0b803a0029440f448110b80c2c010081d5945500d4a45480c00c10085000134988804400c804400d9880707041510354000301d1902d5850311359114001c480000407000181d10301c00105080b25058002c4583c0103049003040c908009011904 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790450269 1250 790449019 790449029
    0x5060702120133082a130c0f09050904050606090405030c1b1807230903160e010801020a0207090c0302120f0115050c0a0f170a0909061401080606030a0b0d0c0e01 71
    0x4001d402c091141c0b400400b0a10170300904050845140000d007001400c000110500060302d00c0c0b808880807000ca6001e00b41c1d54809006845881000e076945051042400c000c0b1070152050701310501007011440c0c8010440e400c140140100d0303041c103498482007810b000c2c0188150302c1c1d071340303011800000318180700001c14040741455281a200307240000c000742c89a81180d150002100c1040c4080071000141b1055030322100c0c01504464800c0ca161401c0f06c8946034034000d102e1440100000019400c0c0140222104144164054001c8500c0c0030820805024904800c02c00c0c147c0910010b80701c891440c40d86c0c6e100750302d58240580e072949481100344051800400341d1003000b0041201d0454880000b802d498542c0e4801000014044542000c00c0c15640c45034a10b080c001e400901740d070049900c000f442041d00d8406001300005651450485141c400321710b002e60104170003a00080880c0742101c080d40d4415041c04012654480d6500000c0000743c4040c02110304054802e8184020b681c00d010a0f03000d80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790451519 1250 790450269 790450273
    0xa05010302070f120215090601081204080703020603100504050a0f050604060503060c0a0c0b070323090d1416031d0102010e1504151a0103150506070212013308 70
    0x2003055202e08403a402243d00181124481802001c0490720800030090750800000e501c80e01c50800c415210f480d07860a1160f04c12510a44c02081341e41c882c0e0b50120360403100004010040c1d64039507424005141c03c0144011030302402141c0016540d00ca41c06024400c0d00c034403000007800c1d2400032030541120006080306015920b050310501c419240010301c650860221891142c0740c000d42d00d0700302c1341c0c9220014010b101c03510040a0012198040e04840282c1301c5410800202280f0ba240301c260000c001c80d00c0100c0f030f45c0100340e08994613014200024158210b444000c0c40c7c6010b003007800e2078a02032444201c002403c0440c040e40141030040208803181310910082c40803107480e0f030a1139a1089029a048039200e4600003040c00c201c00318294050b1403591001c00c1c03002c2c0b0007030450744002600c4641041c2c0468104860a01c50020a003418010b403031000b480c442c14070303040c1d400340501603840c020811565903030f82d2090400f202d001c1d200801e80e100aa580e0301c200340c80400006d03035180119800300d02d607a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790452769 1250 790451519 790451527
    0x1d0d03020123061311070203010c110c061e07050106051009090b0402120601140903070e040201200d140918010512010e0a030305073c0c020303090d0503070602180a05010302 76
    0x1d5a122400d134414442c0082c1d01045021100412051034403c032000290700d5843c0c402d80405003a00111170740d01e07220102041d604118020303024407101c3d20680340807110401401400e1a4090000005003c655000b1000010415126004a040214124210b5000c104901400c105425140c0507040c40c2c2d100c1682c056081489515800020075009405035052204484619801c0c5000e2411b0b1441c5010040403600500ea540c024064407141c00d450036800501741c070000b00402c80103000c00011081c582c0300108141c03002c0000071140703030480301c1c0d050100b1241080321103070030703510b4a9000701c001300e030700e6180e400c0c95150408006052120100c0d01c0285d9040c001519540c2c1008100d40421a8050a001c21950745001c0211401015449042c0c2800c520221141d40383c0d070b2400f414808581780b2003d030280d040c81400c080e9000641841d0013903055104220070380d280c1c100fa500844941d031040c0308403800c00b04266160b0007603802000484100080014030040b00d171600d04a0074004290a003070031464 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790454019 1250 790452769 790452781
    0x31803070e0402010f1103211303020a030806011106090318030f0607180504020c0d110c030a080706020f0a0c03090603051e060303091c02030705010513061d0d03020123 74
    0x3035050001d0001e4140400700c888003600d280142e6880008a40c6c08050f2540c840700c2100300f01d114101c6840780c131410035000380003600400891020045880d0150010038001c0110741d411268410010445d504020300100c025048600400c0005d0040c0181006107440d00c40c090798074400150303080c07090b82c80303039220b29400d100e41c400204089400401c988ae1404514403075213070040d1090844d62005d43c002e0310010b401d031072800c40400c0750241c6e006143c1d14107820194001580d640ca00c96542c0781c59060704510038203000512940000d02c1c086200e2070001d4200340060b18a42d05980089078004045200501008100340c0d00c144000d020f8002c4c1d040400c91b0341020601c0134a0300b6202d0080f0001c034104031010403a1590100255526005d0081aa086a011003442e80c9214104800e0480c0207100d4a01c0106c0e080d0301500c00d07a80f0900b03001036454182441c002c000c460070300d0760350641010142400c1030201180c0351280e81100460184c2c0001c40c0681d045600100e04041c00c40e28000215011014001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790455269 1250 790454019 790454039
    0x20f0f1c080115030509010605090f0a0506060f0d1a040603080a080f0f01051c1e021e09060d060608031308160302060406030e190b0609010602030c060a092303180307 73
    0x200f043d01c5141c001426a40e405403a8010603282d040a81d0105015041000c0e500c08250300d14842c0042000c11f005949490f800d000700d07409110100058000180b0810103010041d900000e01d080a407070300c03615064400804501243d501c3d820a0340c1d14200003413030418658000719420381209107601c26103507604d00000d03482c1601006000302c07446003e006022014082d07403035443d80f684603001413410101c0800fa06012061840c038040032402142003c1c80311882c40e810b81155441001e0151800700241d031800100504030306003c071300701c4200340c2c1d40c0808640800e04202601c080b56001d0201c9441a040c100500d150540105001e052224040c0c0c0510060311a001902c003294964107000c118001e0526000c2d0502c0000d01a611594110050030401d010210015a004003016038041c0121b0743c8410b030407600c910030080c400e000f507404031011031038210032540703c841c10764001c41100b021601102d0035018000c80814641286901c0419076503082420b0046022030624120014400707507103801e03000b907 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790456519 1250 790455269 790455299
    0xb04032d0201080c12010902041d01050d030c05030c01020c010f05150109170c0d051e06151915020a03030b010207440d350601020f0f1c0801 62
    0x2d04001000b00450041004c600c180c03400303108034050118880d03031103680e40c500035001445142e0500c00c07a8407034084150f001000a5040e00c40c00340030740d040c0e0f1042d0386050b1804130309a9000c551a120410821411000a2010b84003080c007400011030b284030400600d10030b07140041e102d0034406000c2d60403c981e030780e0000040f004035800702160f85494008a05030906054543d000d85412616000c40401003240100340d52001151920034261410064035601c1d81d1140102c921212444290300101030601e0200d178041c0380c0d84c0c1190640c5410341d444900400c0c2100d0f01030340e14000760340036a024800b0550180505406c0503403e100400581e4038040642400501c20843d141140c446814610f0070311080810210394011806128140c29000d001015510b640ca0360604000641c00c1410400740206c0910320000140b1860b032078601c0110080c0c0340d00d0b4000028103018154407515582d003506070810311100028003901c0010305008103608060005e04601c103c07143c030400100d036006028196481e0105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790457769 1250 790456519 790456523
    0x3080f0f13110a0f14090a0b1005070203210304050105060907020a0b04140316030908010207080d020307021e010207050f0c0a15050c07031425051009030b010b04032d 73
    0x2a080c0d480700021800d80c2d142d5070400c00540c131080f20701261403901d0b90700d40f2200000559070200640d4914024600f00d4103060f8219611108410460441e50310940117040b400740001c0540b032074a1000c1d003400c4c680038482c0100758285c01d00802000280b01c021f100380c5500c85002d44030392055240c105c0e0000d4803003210a038000c0410b4032204c08601403019404201d82d20880e42c20450f940c0d0902c0010781910051a40d408030b00140c203a80012901c0310060080d541090703440a805801c101c20010014080e41002b0200da04511414202e50384010082c5104180095000300042e610750712402c0c8541070550f40d16040400e98450481c1c02490785503030105204807107032030b4544010181c101e042102c140c400c0f85103498192041728000b00500c64421007c04041c1c001c0340c02c940c90142c90074074501e400c280c040e4021010f68122141001981064010350100c0306040c03030081005a03c950701d40d0301d680400c0c3c001000e10740c00840c2c24010003109014541520b0420300e0380c0c2c9003035804034100d031290314103071800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790459019 1250 790457769 790457783
    0x10c092702071403130f0f060305070e130209030709051005040203041e060c0f0c050a080c240603011104140f1f0f0219050c100e030a03080f0f13 64
    0x1040c5030200035941642d80c0254007100e40000d00e06941d410998a802010003201d102c10506400a5924080c810540407107207007a040c460828a0840700b070b801080000c0004060260b1540c0b8100c0307a5443d01c080141e002c4c1014401030f02c0304641c1c0706142c9444c4040d0400e140580c034003414050042001c040c2c03201102c1d4110b6000d03070b490307841d890400c0c05c0d4a440c802c20810713841c0403041c0901700714458020460b08180b660b501c5040040e60281190401c200e080c3c0a0515002240c804022410720700050800035000c000712201c40000c0c03901075810a4100c5110b1003445007900510050385000c2c01504454034082e400e25040c1030030301c14407642c2036403094001c61056450761842c00581c0c0380d0b0300c1080d1001072000b20845005880e940041c06a540102004006001e400c110002d00d02c50f09003105110744c2c00c8001444880f00401c141300301f85021b20310503001d00c5168a0103c025507000c02c0145031542c402d41ea00c00050070140b03000c0c2280200600104036200c072400400c0196030818104400c100d0300810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790460269 1250 790459019 790459079
    0x307050f030f0d08310201080a0b030a0b09010c020c370909050601090c05070308130c0b0417010c0f0c2604030209240105130915050102010c09 63
    0x20000340740000282c0300380428014109080c580303680100d007140c0b1854130014655142050000040c0c075011a90803006030b04020000902d0155205407903003988100780302d500145a490400c002807400c00b03181c2c011507400b0142404c2180c104401e0207081540919400103101c444d2602c0c0004503400c001d0000c10f444280402446964258a12600c0928061141c6a0743ca080d071107049074006002c100c042a11148248000002c903a4030912810401c1480b950700c031414504156001c884106010341035500d04107813034100802040490b00e0b0000203003540314086507241d1030320700c0190504070401e0812000b64503006e010700440780c205251010406842c079004c0e49e10b02031403400d01006040c0c0412805130070660800301c2030030310f0f2131802041603a00807030b02c55001e03640314440d414080d030400103900c0400071071621806083d401840903021030307440218011102074564050600322a040c1071309040c401420072080119580a11654220340e440e891304086c07140c2420202e40e0008a203222401602203505 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 790461519 1250 790460269 790460299
    0x11e0512031c14040825020f060901030e030c15071e0f052b0f1a12150405150105061201051203040f09141008060106032a0c0b0114030705 61
    0x25120300b26002d10001c1c2840c41341018208031100c0e1304946c410354141290303203d0940d50740424510002c1c00d654018800b65a5409200c1030051940000b022181890744814000200f11400e1028102d4040650000c2400041001c904041c0940141605c0700740100d0888102030501402c0c07907901c50a0303c1c0c0c113084009074003440c41140c0344d01c2151600c0d07030164002190b2121801a070b045d2401d02c0b20705902c041c0088a10810780703204944011000004940405544003180e0404001c5545002d0000c4240e40c51011448104406520211000c8800341c200c40c036015a04910910303a1350151006075011030400c0c802c802290403806060042920440c0c2c04408090441000c0080754041d111780f00200c0c01150b0341c3c001006c00b03040c40f84107803030184420f8000034020440420015080b500c090000300516480c042055005202940925112407000004444d09111162011030f50030700569801e0b98207204e1b405e1406407058180c20200a14802d489800710581d0005503100580340201d07100c5244400b40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 790462769 1250 790461519 790461521
    0xb0d030c030503041e03120b040b010203041418040c15030e0c12120a05090411090303030f06010315031406090c15090a030c06050a020c0901050112021803010203011e0512031c 77
    0x140082138001c6601085c02c0542c000081c41445141d50000e000c124403e00801c810b84030304460303da00681c01440200400c0e400c1002604480c98090180d2a0400e1180c20701c1000410441d0252000004003031308002c12044100034494034071032071500304a80040003041e40c5d20380085010700c910841d4100c0103480c14501c1031000211200f50101c81c00d5443c031103000007400e1a0003001600307204502e8400c1001520b190b07131b81216420a03004024601c0d641c1d56500c4800b0b4108042c00b4a81010307a506840b8481001c0074003410043c6004044040082e100700000525112000b800e40e40e150708035295644091702c0f807008000780c00000d404403503200c150800100b000703174a8590000c0c200f0308a918000505540042c0180200700f0650300761030841100100f4020460402e10400e0300190499040c00303258a4150b01901c0c0710844035034201c002d10041e400003800e9030400c1c3c11801071010344400302d0f8408041c0418100007090147c03140c40f074054104880c1c03a2280149150b41604c08004880d100d240609 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 790464019 1250 790462769 790462793
    0x905150318030c01090303270b071e03390c0305091906110304030506011202220b0f0418020f01050417100c031b0e03030702150304060b0d030c03050304 67
    0x40d1000c0b40c0e11201c41e000158013801050b0f0040e00405c1c40c11844103469505600100810380502801341030f000314682d030b07188800380014410f00400400664035007483e96040c4c002c008080c20340d500403401c408032140c00b4032200e0030321401c150314040400c10113031b58001c1031814030024107090402202010042c00d040c2c2d0345200b040c0394560701001e107500c1d44050414810440041d01d0b21a80d4a252650103160740b1aa00c0c4500e00001d0802d031700a100400c00102145c07009a20544040e0405000040e103500030380262400003030361843e99850381c0c00c90318581812606441610002c85081c052569200070f5522403155588002e401181052803681f8030b40d0044046500070401f0080c64404c032003207048000d840d021980d0760007051908005285104d02c1c400e00034800280e90440e10216000c14018080d1100c01105503d0340c0c05000a000700d5015035641078891503814a4543c00c40e40d2807400746080d404403070700c0400640c81840200000f4010a0780000080350701941170a000381e91f620340f4100150301c801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 790465269 1250 790464019 790464061
    0x13030b06040207150c030e0a080d150e0f06010e0301020f0f0a03090f05060a150509061002100c2001050c0d0b030c1020070b0702090a15060c0b01050109051503 70
    0x41c181264208203509036114101004050b41c2c00c00824007c01101600c80ca8070380c401800d03004042c0802c0d8040143c81d4850300c4980382090880d000699212001d080e99407049400c1036140303922204108103540c1003000c261103400120700851a016582035802860f00801c0f410442c0c0e900c0100ba141d20b498001d90082c00c126410034494890404a89001075446030100c5036030401a0034000022243c40e480c00090003a00d0000b080303201d8035640c1600340150145210f1304542144601d9103035054001252081728912556941c5000c03962079907400400d103c02113640d001103942e243c003080048211f05401035030b5070120f4103a00844e03e60305840000c1d203071030302040758070703520062072110410150f401c5a4900b44549401e1a0000e99466843c1560b0300c40006206031009a50208011001464407124030369121480000c0060b031414108644030303d00c082c9820143c04240d800451000f13206001c1a0503004001c00d01e0720300d0f1100d044c1404107608001d41d961040d521000440070415050700c100100082d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 790466519 1250 790465269 790465283
    0x120a050f1c110a031a18190204080d08010503210c0a060c030209010e100906030b06070f1406011a07080a1e080a110403020f280305010914010213030b06040207 70
    0x3081c00c1e500c41d9802c1d4043c043c507a0200e440c1001000440c01320b00c07041e80704030800a026a09800c2c409003552090000207000710801806446c550400303851910280c0058201f0388003d2440181c0060080d04200c1e041e04200c0c03096106000c40c0c4281c5000c0c054401c2803e0301c11250540740d4013082c40306d624140700c496004000030300303203030054440c60781c554084e01d080c0c2c900743c0e122031400c4101414480150f00c040078135000202041400e00c81a40660003420400b00003500c1c0615000c85912085c00c1030f180b600c4100c540103000c0c00d1000015204001050160403c2c800100c102d40c0c4229031070a0714450480000c0c59007401040b5103154034090108150810040100204c42e02076041c1d00602c00d40e8102c4111001500d4000b0703416840301454281c03000d803a030240c0205803008202007000b94200d01d10344400c0d5181074013107580d890807207100290030080d44280c1c00440e154250b03181a9040c200c0f15030b5070a04a070b00c1403004007481c0b40ca084011044a82041440340d11b83c417010041400784c4035250bc0a0142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 790467625 1106 790466519 790466531
    0x1b0d031b0c1101200706262703180415141203090d05011b0e0d1401110708040e2208030a021c09020102120a050f1c 51
    0x520701410600160000800c40d413240e1968201902a91340040340c01b0000190003a90400d00500e42511503c1540e105e11010600e0003401001c00c5800441c90620300c020342c1ca8400f2820b0600400c0301601e5450103d00580800c92000079403c034080c03890591215003082e100408001942c5c494400088011600f200700400220000445040b9000400c80c1554580c3c0d4104075581c0a48aa0000318026070444088400107081004c45028001070804810413030761851340e0740018a9101a0030001c1c1060300d00e00e18010000304141c03000000d000603c007414008110040d00403260f00000c0304074a903481030b402c141c8561003040c1c0404200c2601e05000001003142c0051a4010121040103040c54400241840d40990044106119560341d03030310b8600f5540d042c41030a9103150a04a0f4a1030020480001003180c82000149440c0c0700740852424070707030102c0e5003891101d540029014880 = true := by decide +kernel

theorem cover : BRFrame.Cov 790287769 790467625 := by
  have h0 := BRFrame.cov_init 790287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 790287769 ≤ n) (h2 : n < 790467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
