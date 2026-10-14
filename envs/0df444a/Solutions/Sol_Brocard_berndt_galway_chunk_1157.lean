-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:30:28.41462+00:00
-- url     : https://prove2.me/submissions/211f13fa-b92c-4a6f-ab3c-0d93f7cbf166

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207913669 ≤ n < 208093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207914919 1250 207913669 207913697
    0x106080f0715020d0507080d06091d0f030c03070b1005040c020a1226090a05030a090e010503060f0105060304050309030a08030a0b040603030219030e030a080304030224010303032307 80
    0x141940500c18498006010b5046111303070020144d1041c42c1001c3d00e181000220300503059050303070000d0000e1005030000c000d0000d02940c101d06510a10403071a440e4070800d10204074104000c800c46015030608c2000b5813828905540d155081c58008145644503403180d800015507031070b14014200307640003c1e4082d0490b2400382c0380c04424042d04480e20420802007803070384080d5032a0034a2801071080c00c01c118002c640d503413031482480c0c034868020041003408081004800d05030400c03241403c1d6002e16088000581e2030b8800e16030340785c0c0200c030201d0030710050b0f00c010081414080c000715001030107002034a2030440d4103002320f46040300365941264509000010007600a240384100c3c0c4582804a4040c4180303403444d20000e5640c83c1440d038001a160a200040f02010b003e21b00b06da409403405030a5030500c200c1c0d410b110704990800c50f015400740c0202c0c0b03c0c0402c001031905460342c411441c069400c1c6c1c0d176425504c1c01c130000c020851a9583d003c00c0a2030700d60502d18140021881481030707503a1110344048817 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207916169 1250 207914919 207914939
    0xa02061902030106020d03091b03140f030f030402090402060f041409070c020f0112091707030f0903050a033911010302070c091802130e060f090303040605090106080f07 74
    0x21000202041c410b000602c107031035010880110041c001c0c41d0118000c0f40c2c030704150801700421254011010015130700081040700c003001e50a10350443c00300703482c03c5c044000d50140c1c80344a000d40400c080740c0d08100140c0140b411400c03440d0010f00241815003080d02441e00c03050140c0c440c4d0440d0380c2642c00d101200c1506c2c5130101b4082c0d4000007900e0101803140c81507002c101c08600d406da580b41800201a070000c080ca100341d0026a489401c81e100b4680c6c402c401034801d070583c0c407644040d000919003515540400e4062119441103946c4200188030340f03050758904039240404050740c960001d59210321210306001844225079465072006009601d0341c01403400101d44015044028145030060041034041000c0a079040212030100c040402c01a8080c0c070f02d03000409a9030002903000c2d00c2c0c90302c241c07060001507011402400340c042c00c841264942c0b641042c859001140c5841c01039000700002030000d42140c00c5645c01642ca02d0000c03c00d0b988811883d818003543c24840d400c035500ca0b0400300720b45010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207917419 1250 207916169 207916201
    0x20106090b12100b1f0909050a060302210111030109050609011512021c0606020615090609042003010507020d080a1808130b04061706030609030324060a0206 69
    0x4542441e02014207804003034682940d02c0c110700005a0b204d10034907107625a0400310000c2d61401003880c100c0780f110b00010b094100b040c0103040c0654a0080000c0340720b040c600c145000c1c1d0350000c00c0a1142d0225200b0700003494640000d00c1c1c1e0035502e91803d042020a500051800b03401440c101080b54503192080c060320b100140d00180c0004c0740d01e1000142c0780d400034882403c0301901f210140e500d5818a0843c925034284c1c102e40c0c4401850b0800c0052001c1c2d0100d40c0c1801400c4107440f006440c04007400300010341c039042e03030b42590104000020600084a05855084210810309112060b44000000a007161802c940100250b08818402e040942c2e10800e4a0b030b1140403410700300191074400e03840700d41101d140000201504000078100d140d841e501c42e888001031042c1c00c03d00c0d80d1640c0320107000f807214000345100110a80340c1d1000c200e641c640843d08a108203081c0008504554511036212201d00300c07a00c0540c960580302c041c0844680712300c0018441c403912a00105500d040414103030019241d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207918669 1250 207917419 207917441
    0xf0207112e0e06030a06060f14090906120a08041406071110021c03021801020c0117130602070b040212070303230910030905100903050301150215040302010609 70
    0x100304940308019114007904801c6034071a110210905501a8500b6a161005148101d41c0400c010080002c00e81d2250005020348420b90788003c07241c4c580b0302041e1507010481141c8140150207000220490802c00d013001d500a40041542d02004140c0d62404d05010980100347c1d04000300040a000304419001e8030343c45510140d03100752400c0250b4035803500f003603081a0710b140301c3c88800c40c1e460750081c4200940c01c61b004210315820460020664090000d6124290581c92046079104401d4998004070303042618007410b03110305000c40c24000310a442014010081400718071201c140b030010a5a42c4041c118440c42101910040c2c00c00340104034006034050103103c0140c3c0171542c1440040d52041d042041d001e074003181141c40550903000e4400a0198400d4140c00480000c0c041081c158160800403d1500440560782e2641d4034001f0311040d204402c00260101d60200010043c44c81c44c03507400b10001020344140c440303a40c4c81340f001c00720240303040e141900141c0d122103044c020ba03401481028040c2c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207919919 1250 207918669 207918679
    0x8030c0d06180917130e0403180807060906030614010c030302210a06050901080a0b07030204120f0b09070b07170f2805090d02040c030b030303090102070c08060c07080a02010b040f020711 82
    0x110703041174146504040c015110a840d003a0f0101d001c1500550b982100516005401540355484460850f41c8145030301c150f00008025190006da034038043c0c40b845040c1d49081080c1d5001e08880c074015600780700003082c00c40415508020004008100400c802d01e9240310340c00001160400610311410340750242c10440c46840f64000400540c40006062480305500c00c1040c4040d6840305826002402070ba0f1010100c03d8012007880300300005182c1c500041440b0b41d60421498685040a1b5942e011038021004a0101002810045460b0b80c200303044480003040440c0c5442504a04100d00c0e07005404900c0d0482d0440082414811141c0701c2101000000d246c9141840c1214001450140039020068040d0f903480781c100c001280719030004036074010301034103c0c0d031740381040042e0714001e600ca00c40c280c42c1010f88030b43c08500140045540d50203442005003440c2048810345807131040d9400101030701c040d0f41d071f03400000707006481e80c0c094204000c0c1e8403d0016150344403410080a00c0410789240c610031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207921169 1250 207919919 207919927
    0x705040e01020c06130311010f2901210f060603020c0d030903090b030c0d061418010e0f1f06090e0114010c2003060903030a1808030c0d06180917 64
    0x3840042c8945e030100c0140d81912038240d260a040d1100920002c1c0103040d942010900d42d24009035402420b5150030100c0c130a0000c1d1040c0c2c0c0403040d031628024600e80095040640740daa003c503040101000078100804c0060302100e03181a600c129903032a40a81c01103500402d141c40c00740c10a0001d181600d80d01c0c00e090080060703590300200a0120382c00350071119103001c0049031b00020301388141c54002041034005c200c0300d5291050f041c1d442040d050030034455900c4041814000400000e800d0489482d03088a0855448a0341c10080e0810018581e05140c030031040d13101240c5001040150051549484d00c0e1280c50030b00601c240c00b220140c01c800703507841031130401c2d803500c0e64000078150b185a0001005240d6a0003039041d0282030503885420b691511454051240341d54010000318011807200c03802304114071042da003060500510303000c0940204014030001c1ca0182d501d50003410300c0c0340701c18070000344c10b501c40050142d928030b4142080382495444080c8400c20105807101c884560100702d0003824 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207922419 1250 207921169 207921187
    0x1020309011a09040b06010810082406060f030f040f120e03010c111b040f0c0305090c010309080d0213050d050604030908071811090d081c0c080402010c030c05030a020705040e0102 79
    0x140105c00b501a90401c501900016224238014010790040e00d0250309503006800c991058a43d040290200070408248020100d40d0078544681124550b2a860003507604555820b5008507400070001d000355000c0c071401c0711450018034401803904807403040703440e84c00c504440b51051500b103540001c0a03805221101c00c0e041c1d00c22030009990000f0400341405c0300303013080300d90b03011801502e030300e0013541c0010b810700f0000320b900b03034141d00203e03c12510f02c800c0b94198200c00004405403190020050300e00201042400c0d802162a0000c0102440001e00407800300d5490020a00c0021245000e0324150450070604c03080540c0000301900614a440c010b20015052881c85400351300701c0300c2d241007015034400c03050a40c0411101500c6414100416001c1c680d881410445040e0b4031610220102ca40d84041100c4481d0451041040c141b03030715035400c415990390b98010350340c000418406405102d5052442000503108100a00c140d034426400350226030f00d010700344000d494441402c1502d5900600ca0090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207923669 1250 207922419 207922433
    0x3140403140703210b0f04060f0b031506031311010e10120f0203130308130b061e090c0d0605030f0d0f050c010e030a09050f030c010e1201020309011a0904 68
    0x29028061181d03440da900c10502d400ea6490f00407586005103603180ea0004140122583d00541c00107609441401201001804000c1202d51a0081c4003c0b420400b8060154440083c09542d011103810100044a00d0920001e03111350003c803400c21810b040078001108000651400a8203a202801c0a6141c6500e0030002207085140b4041181040308907104a4248030041d04a5040c040c0348440841d941c2c104200c4654030340810324000e40c04116854041281c001002d0044204650410b0b01000c0e00e8544508100e0400000300b0842c055400b20380e1b11150315a03a08030f125004405881c4110f540d040030804607415a9503991140d0b00c02d40112a400c0d07000760380802c081e01602054604810800758140040d0b1310703801211462001580f80001001000f20000010142495540c80b030160440d942d000b005001c031070340d881c42901038010103003200c8254060312030280d0b11400108483c0300d400c4c1c940c01c0182260401c840d4038103140e44807943c05040400c1180c480c90b04880c00e980b510518642908d50358 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207924919 1250 207923669 207923687
    0x302041b09140a0f150f090b0702150c0d09181a0603040215040f08010f09030e090a1e020405100806060301060822150c05041203030902060f0a020303010603140403 72
    0x90110700d00c80882d510765a5488420b0740c0075280d8506040d4016888025000c8015006605100400c3d1070700e03200781c5010300907940e100c02c98203405546460020fa507424003d040700416401e0108402c1881043c2c2140c1c000e0081c00741d031301c0d1a9694868054039007445c0501c2c0e00a0103403403c511a161040c0d85200c81c866280300c40050078241c0303d05550351202c1c80451103a0b20b0b2040f0740c813aa032a0101c0c000c907580845500044c11030312204000c0c8800040303c4400b00441d054090003c010500483e107100321810b0240816a00a585600000365208884001811042c424050300795941e030008080c4486c0c0303000806401143d40501d0059081c0c5014404285980300c18040c40341800b582c0d0000900103c0034845114010001400717019260b851807030021200350042e1440c0b000c440c2400d0051003014850700c1590308640c0103483d07009510f0304540b01500140343c00d24040e80c021904110800042d18048010403114200d070303000f59620f601d407410040c12107098040400a101126040c840800d034480080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207926169 1250 207924919 207924929
    0x11070605180f06071205031f0e1f0905070e12010204050616140a0605090c09040201020607140903011410060507080717130f0f0806010e010603020319050109060302041b09 75
    0x80c80b102000000164040c055a00010079000100c13600005c02a4880040c60080000c0641d02222440d13003001c0000c00c105d03d00522247d62140000281c040700500c10391400a402500e942c25126103401c100e40c2030754001c42c0e542000c9403856040551500b0050800c0b620503103031500841c18907080c90005502031040b62003015280500d0524081030041461000e521041c0c401c0c1201d01528403454540094802142d42841030b00400403c2c0c2124142603a145201daa8140d001d040e9940d60b140d02900c4c80c4d50030825242e1103100c28071820322961824840c06401104d10620707400a0b280684000c0304102072a049607042180c20712140300050800780c15070703050319803080000e41c0d640d88500060035a405241e840c08a8030700318035030004426002800d54029200e00301d44125215440f0108196220028442e10f90840340150040003194800c2e4007654001c03420131001900781004030140020b845007a04202140c0740d035001c081007146054822014500c440c0c200308044005101005000c8040902c03035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207927419 1250 207926169 207926179
    0x1080a0f02120d0e0406080616081314153306090d0c0f080a110d08041d090c0a0602032a0a0f0b0705070b1602011401061107060518 58
    0x1050031560794460103a01d4144000c00c032021041c00007001010007800c8a04c1500540ca02400403136603040118600c0d210b46c0b4902820340c144a070184003181e035050010409040029039045900014100f045000122103240c001040520040c01c9000342403030024080c854410005101001c84910031654404031603103981c0d07820541c54112011548600c40e540f44031364450f2075021040100605600b40c1000d50b112410030542c0643c0703074500b069403003401102c0506031103491106000c4515050f40442c018034402e040700c40c109940c8806d61400c4600c4900c8030082900c0e0101080241441000807001c500b034226254403030b1a182c82c6011f03451b80310307940e80c840c100d100d521982006d41500303407211100c40110004440880c18141070040350000300c100c0c200d81c6192000d001c501080d108500307540b8020b4012030404006d8451517415411460080130120555498050004030a200c0810483c0203103541c0d01c03807140032010f0f03460041c280032054000206000c0180042e4150140c00c00540d841100b00b920 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207928669 1250 207927419 207927443
    0xe01051c0314070503070309050f0f090604020d020f070605090a0f030f020a02120d031503050303180a0206031006081b040b0c010e06010f0f0801050403051207030f1a150301080a 78
    0xd04942d41c0c0c00345101052034100001daa00f0401c04004010301c0898003d940b103060941d1641700300080386509564070342d0b200c0f141003800d20b0341d0b25040c1c40325074101c0d6004000501e446600b5a050060b40c1010345000501600441c8140c1484918064642d2014046028000b00740480d5580c132150b44803844080e081110b442c08045050f4002c1000b94080c58008011940c606800040181d41d6400c2c040c48400003070030036410007250841d12141d80280da600902660443e510000508646c1d00b0307460134000740d48511110071000d6125a80154094200c40c040303200c200d4249a0040c0026001401200051030196000c0317030040e0707100003603400380c1d5406045030fa910300910b01114054800c028014810b4000c0400000362404111101c0d011154140d115800c1c5541ea100c140e800c0b0f40741200c024001ca00100106940c0000d4010707000d90051003401c0000b9554000261107003111100d05409501003030304452107085103040003140c2580d1480344030484c559030401c40f8058490364200c0c401041144201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207929919 1250 207928669 207928673
    0xf01060c1104091a071d1f051c020d2405040b0a1e06020106050312040905040204020403050d030509011109031207020303040b3103050d0c02061303030c050105010e01051c 75
    0x380101000a402042d22040f07013000b14014030245000b911030101080d04080034849454581c039600b050010000c04110201c0c00d0311340d1a22610000c0d004800400c1000c000100100c140000b4904d81528911030040c1c0b01c0c109882e14000701d4840c182041441c0082d01c04a0341c03c2081400300d402595420b84000c524600c8600c04a03003400c085410004411141a01c1e000201c12003440140446100d980203006081d40c401c181500c800d40d034a02441038400030041888600103a410040e0014405800149015682e48903d410541c1460013480029101c0040c007541c1c40b001d0050510540780c15441520b090b12b0140025506ca914100c04005421b0220710328040d56024400e8500500d0890304407907072611016140e0310b488824031001509004000b62880e000104901d100056a43c060000c0101d045003032800c1d44e109601c680101c0e403020007005440034107622505540c0040d0f109807180380c0003102a14203203080d0740050300030140104510004200c5555903034411103442c00d002100c10340309000c81c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207931169 1250 207929919 207929921
    0xf060f020405040e010b03010b0603060105030708060d1202150c04050609010813020406060c030f080f01053c0f09071425080d0c020f0303060f04061802120f01060c1104 74
    0xb540501d600510b8401105114803040d0011514454201c0080017000041410817400c0e02043c2c80460010340b05100181420303010300c2180350440d00042c40200256001e07980d541c41e0102c420440c00060300048150b080303c41010741d089800c08411051781c0d05150030b000100d031244c011581650304010f8000040b40c50310b003091140d401d8007038001d00280a101d072940f030301826807000c890040f000103114144981240c2d108091a174011b82220790441826460041081445840c5d03500a40c510307941024900d4034684044048a088400350740c0500986c1c1060081082c003244122219004080b0402002601688041c0500000c04205d02041c1c640c0c1101000000201299002c0f410042d000701825060142401c090704030002034200174008446402c1040362109000d01400b440d0764402c0c804140c0310718040095002c64074000c0c0000804642c0d808400d0404618051036481850340040c0c070144141300501c005900c20000707078050400d541341000040140d42c003090003620b008130503010900c5a9a503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207932419 1250 207931169 207931177
    0x5010e06130f030606030201020d0f080406091a0108010f0609110406030507050c0d0203090405061c1221020414011704030302090d02041a030d03090305030c1e1b0d08040f060f02 78
    0x840c286005800e43c903441d25030300505d42400181d01521411100c0d5a84d6031259001001c440c555071303110030070307070700c41da560344000c0c105485080303d800310303030b9901200100c40000010780201440400464000c0c010507106086440f560021401242017100125002c0c41c02c0d4110303011a110351600103111740d6a258112b8032401a0f20103a5002e000c2c2a0001040640c008068818520111005c001d540c40304020001e00d0a410010071307401a562540301404200308002c0c900035034406042ca445003e60b00800e803080d00c2e4003054807030039143c0d01080611001c800040483c03a00503083c24080440d540080100e4103071040244020101900060880c469840729000355401c2940600140038010032100b100b4400403041e00c02c1c1d0f01a1203210100c0020324804c0c01241c42c250b0b015110310b459a150481d000607150b1140c0c48004d40c0030241c1c05070a1001031000c0040c9444045100011003000c0740100032414007108000203400c0144581c02e12010548170750041006071b030700c020002841e01050484d48042d0103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207933669 1250 207932419 207932429
    0xc060f3403080c030103050607120e1e0708030a0801140a050904050606011d0f090405010b09100e0a021903020703020109021c0506010518161e1707020705010e0613 72
    0x900140a4801050051800310506110791070300d01181d6100c81c0010348a01003440050130642c000700104204500032100d58074202c005c541e0220303c480d0408805890850013003144506500d01204400f195041800306001500c009006949480300180c4020000c01d41800317030910340a2030680b041c849c0c6d40c3c1c1c040103000805019014030300f245000c0c10469203030f00b170842e02da81c081103200010124072040b0310003c0702e48150040403c0701d4000c4180c14000c0c040c00040040310341d0340d0b0b10b164029403031740e6814125110f500c2c46071020303810a0038102000780c914400340c0700300380660060201200c8210396210794034800240d461700507250311702c60608a014007000c80c0c0181d0042c0c10022800ca202480700f0071280d0070f5010780c1c111450b0381d80e240d0030700515200301303d007444441003404040b5801d00021080f4801c440080d10f00451400a42020700f4040080c91800b440414900e80008c4005250740d6005c550100e01c500240501515040000e41035241c50140c19204400014012007403207016292440600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207934919 1250 207933669 207933727
    0x20a05060708150a030206190314090f0d08070c1e140705100c080a050c07080f0604020a05010206040302070504050a060b130501020c0604180c0509031606110c060f 72
    0x41810800a852030b24140c070b2603c1116091910660a800c0ca520203900303c3c1e9000e40014a13001d0100300410107020903481010805031600f40440700345020240f42401071b120b04001d8641e800b00441d03031a141074a04100c40042c030000d0380810900e40d800c25010350801780c00000580c140491441e01c040c3c002c180391002060403101141c5d103840d40f11300080d050107850381a1071045000380540c0d000e07203082200300802084020100102449644140e000e860449055011202c115455000072810715903890802c01c040e83c00082080b0039868240d8020300248000e001628182c241500c0094403402c040c0203481c01141c848011402d540381c0b40c0d211000038001014450307140d00c0d42c41500f00c0d82288501c155401440b074100c1c0e0100302d103011001ca4040f540107c000030002003030000501c014008501e110b00a006044c000e90442d51018882c82c6007810300804a04041070500d0360103440b6480303a041c110f116921402200c5100d80710700c421510203000032440151140e5030005503210300480380201d00c03540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207936169 1250 207934919 207934921
    0xe041502070308010312020a0c15031107200f030a030e0105210a2a18120311070e0c090d0c1509030b0a021602040b0a0b03011401030509010207030f0807020a0506 71
    0x2150340b200f0f0b001d0680e4451038070980340442495040382e46980b01840908580c20a440400110810681c0f41410407260304000ca000003070415042c10542203c481035031072040a030f03034002c0da041c1440d1841c1141c01c42207a82d01804400040031980e1881c0390741c801810302c0000c1502061580c0620203680d129030100507103408504480ca41c0701580d2a081e61081200b608001e0208110700c148449500c251000c07020320112420318000c100d680100b89840713540b442041c940c0100366024540000c42d10300b07000c5d48030700c21095005201a490400a54004041c004640c800d0000c10005041101c01c2c4586c2207580040350811414542100182030380130410b5002904c49081680390003000500481703004aa140d441c030360307880141d8400e83c81205418040418085065001440c080d0b11943d028a00174151200c2d030303a00e03038202e07588562083e00a0100703008080700f40d40203980e050150580c803d0b90314009600b000300c240d0780a49002c5400d2134040a2002c00c03c00a00103900c01c101100580750002c00319596 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207937419 1250 207936169 207936173
    0x11b180e070c17030402030a02091e0f04140705030607031a040f1b020d05041502010f0504140f031c0c050c03070f0c06022a06130f05101103040e04150207 68
    0x24903001103c4501880c2071220280030303541c0507284500d0f0080c001c4c0c17841051681c02c006010030000c102e04080d1240e2050b2040326100560050310880c0c946420310141d080c50b00301503e08011903800e510345980031b82c10900058401180e525042080d508001c50200700b50309000b07851170400300c030080d041407400034440b00002d000d40200e00c07180c20140710b2180021070303107034101d880740b180740140804640b04000030811050801403d20307004403e0b1000085021400809800341d9005031402e65190494610200400ca818800c92000c0410b00d0019458030780d110201500c0c0c02c40c0100020400f0341c1c0c40030b09100c4103005a00320f1309082d0590058035134407600707454081c502d010015803d60b6540c6204a0200d85280001910075000071614621501c041041e4616032a021075020750316040705052105000c502c61050101d4054200caa00d1702c644c45003004140304503e01d000c5403140070030900441d15040c40201108803001d5910b040034078a4030303503600c0c1840c010000700e03104030408803840040c164003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207938669 1250 207937419 207937427
    0x504060209040b1c1104091406010509070e090a090201030204030b01030305030108011b050d0c0e0d05031918151b0b09010b010302090315040c03060203041203060503011b180e07 78
    0x7107014802c42d02005100054020300c004c0c00e903010700361040c406900c0071800116058840c1d0f00b05541380200040b40c2d00f001ea54800c404841c40b9488540181d0090740140100d107031218603558041e00c0e03894881d010030407403000100d0040c800740c26401802c0c3d44211010540e48a0b0701180c0243d40c01c0120071520307580d0f0349401003180d4024882d04890354a02118022404080302211140d200150f440341d062142c080340100050000c2420300003401107081d00104143c654402c4080c81d5802200074644030510750b260703050403032040c103000010012510700d40f0041d011030916040958010291848020851440a494003084c4074075805a441c0a081c084003000400603e4510480124000f401001c0401006605a000c0c1000090b130541007400040e1041f5000b01d100703640240543c0e100b4500d030380e89403680d404036402a40c0130756070480700b0034603500344039003500400307000706015002088546291000314a4130304d00044440c08010300c0d40c0c0100f00c003050100e182c1000d0701d085050b8000c941440f41020b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207939919 1250 207938669 207938677
    0x4020c0c180723281202031905150405070c11030a030c1401060b040b0c161a160204020a03020c15060d15090c0e0603160b1204020303070c0f06080c19050d090605040602 74
    0x6000205242050445c4010394000d5a015000c00c0d00c4402d038110068a801001d0200100031400c030300300313030f2041c00d54a03500c80c010349000344c1d559103520803414407606040c0e5810803c040280d000764442810f11700060741c0605a021626001010144c03034142039a10703d40501260b61007040520313400315001c41e01c0701b101ca0003001d14038101002c0f2104014680240032848540d88100d0004000d5141c62402c09000c00e00100003c607007104a001000032142d000030200c0e0458801900029408101c5030000c007000c200715150f50080035460104c51412200040051041440041441c0010880340c11221702c160001c1881da035100240d42132050b2104441a8841000c8601c248030780f09204070004500740105035101642d40c0034529920f00740b00b551603000c21020282040f40c161000b004234030085000346807018041c0c80c409074018412450150010f01205020303128000301e400401c1007903aa01e5405540080c0c885079820403a0b143c46610301e01070b0080084c00805000941448100020080c1d00d600034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207941169 1250 207939919 207939997
    0x30f161a0117012d02040504020f030604110403050c060a031806050411011b020609030a020a1203140307050901030902030f0102070819030b090f0c0904020c0c180723 73
    0x401c5101d500785540d090710714003400036803513101d042c4440300000010143c421400324202005403804d56680e001c24126030101d543d1068514000c8103000092400307009010758504014a02800d2904584500c0d45428039040c840f4844c000028100b0000e50182c2c100b18404005050480092100d604142018000c21901241d10b10a5159006c14944c0070390840b280c025094001e501440d0250b90900c001c42c3c2c09441e040e9414070400e40c401d40143d44507800035015009050244400151500d000341500007802c840720356000040c010850300c65030000664851034000d28010400c1e42890000c603042c0f0400094080b2300c0e500000c1c514050103c01c7c001446144045040c000728100051011011036005040b007551040c410804650740d0384100301031a4120300400949441e12038400001001c82e80b103004241039540000b155a44d00e40b91205072681611a044220710340740c036000f500103004d00380485c1c4d94402c0c0e600043c526507441c040c601c00e5a00d40d035556004500c50280c10881e0004020010365a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207942419 1250 207941169 207941189
    0x12090c26060a05130312150b0403171804150305030a17010f08060c0a0e0a0e011e080d1110060f0e01121e05100c030c11030309030f161a01 61
    0x420b02548040c8611841034802034195003d800c0c2643d0121034a980950800701043d807284441e842c0d5840180c4400c00900d511000e03e81d81d14034524080c100c190622000c00020f04003804a0050110941012003181d807080701c00242e02000100c414082d10740a40016100d031001081545420741c0018075048112003001640d0340316a42c03001076078040301d031f9401800400d4100b100800c01c40b900407005001100041d09001c081c10104c0400b0400c0500c19602c03140318110510010001d610904190125050f035101c2884909410080401d5960241c403011000704410410206400c03034040c807204078280d08054003403040990750340038003114170b1341406258040d007140400043c03800004180390030625070207480b0518806040d116000c00e070400c00c0b4151680d0140d0804811808503520600740c0d810100e850004211680500060080009060300040c81c0d1007002480040c0e4170000c159500303a0034030440c40340e0f41d02030395100c0c0d241d003080008020005e8030b845020a09040440c46058180e65000c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207943669 1250 207942419 207942421
    0xf051921060b1803070b03040606090c020f07170a0614010305011b0c17090907020f0c0307030302060c0708190306080105060906180414030a090807051012090c2606 72
    0x3480c00c200c451610403100310420800050600380c100800c40b84800c14000c05480b0140c2e5a2030400c0030390391080b24100c0380d460b0380b1541407001800a20030210034030542e2004105000400804603070701e0b1294050304c3c034442250032100031040c41c10045102000e0340b120b02400211600d840d0b8880703ca20030b0204031015400c001c80c0c40440008207006820506250340d070f5171400c501544428505038900080000c0e109410044080640c0f13a007c849400303400c495008044804418001d141400040142c0034444d40241a003000031076800035403650464000400a561948980340070b00052151300c1d052000e6000100c40550700f190180d00080840d030b084802444107545100c108034034200c0c02c550071503000250320440310380b800c01d107444160300901c207181444001c00c0807030304c8074030b150410322058002641d102c0c018840441c0501c1338400070102035401d003e84d0014204050558403216401100c41030f40c400e2101e06002007050380c28020692000300b1000031114000c1c240c00344c45482000d103010710400c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207944919 1250 207943669 207943727
    0xc0f0d0201090b070618080702040b01020346021606091a0904090501020d1d0304060519030f0213090b100207090903090515030402032802010f0519 65
    0x1104894800d038140e4070b16400e40e0800c00305030a5030300324440a13a46240c0c1d42d840b00140d0345a50400d006c03c40d005199040e141e002c0752040000b501d40119059046400520190030006a0b40401030900c81360003a134040e02d03c810800121052071140a04034060f00d40300d03042d80751560040307a0300390410911001515400c0d211402560304030300d07610803003800010344141d403010040128050240464014000300c1c40742816144d607802e84e00302c2c40310368040319542c6001c109a40c0210200008545105002d941498540280507043e8052500745040c0740100c2c100307644406100ea80b00340d81c20300f40c002c011501c1c0e481c02c0340d225800312050300440e4401c0b450b24880c491989011044150008002c0e80102200c60520300c1000c090070303d03c5030440034803011550101c0c90340d90b280201009250403040c215141e140034010985003074180003580100e180c01c4040812800c800c00011040d40ba02800c0000c44518450411200c03885040760000454400c0540c0e00309895009908480c100c1020f840d01030560564 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207946169 1250 207944919 207944929
    0x901090305091507060e03030105031e06071824080109290d050a110315070905061b010c09030203011a24040302030a031206060f020307140115080c0f 66
    0x902405404500144080e02e420f1401c1c2d0091030390b5015040c41641001d0040da190340039108a20450002c0c0c3d00040014026410108020f20b0743e0342c07036480d000a48249a00105846103070251590301000840411140240f480340303081c1c0c008141602e029000382401c400c1d0704220080b03e00100001039100000080d54510600951442031602e0301c005c0c100345034031007088403185445000c030b5800c030010b64a1f013004030b442440603000d281c2c0140c1e42620021030410400d4108001d40e90f8000c9141c10081c24801d03502c0d804001c400c2665015109035a480d040c3c126682010808a0f4072000150b0030110303043c2381664071802da0710889109038000d10080440310312101c0194110285c5079001040001c9084511070190484c0d400c0110f01d405175442c143d12900840e0403d03412090640104903603d01d51070601030248603900060600789807525480c2c40c4c00d04001c1d12445002c0026022101c00d480781c0d40d00540030f40c44401d000c0f012684ca124101d03583c0d8503441d140e0344080d00552080c840d030300354060306081c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207947419 1250 207946169 207946181
    0x7031202070306180b15120a050a12091a0f09061801020d03021c09020609040501030813050303040b07020402031906080d021605030604080703021213050405060a03031e1107060f080901 81
    0x1101c0100300c0c0c1c59540010781142102c2260246c1e40c081e08400204182000901c501102940a580034000302c034000d04054a44141c13440c860f030100091414100480c500b03881c6501298084c40b0040340d07503404140000d100f06d0103406180b503401500017440b160740c40c02c4054111000c10084e000c0d1400d20b1643c11041c0c0c124055000f44290110224840b9180703145154000b800461006100704c2c02c00301c041d0080780c111003090708221286079000500000d100598041c0c100244401c8005514041c1400d80384446401900402402260080301203001080c44405203c0c1c50541c420081041560714901280d44141140d42d50015002e082e0f4010001c001c40c41d030700c1c400e403400a80142180d89941d45c070040503601c000d806400318020f0504001c41c00758a40e0051900d412003004101e052400c0400304800c685014200074403403441e01070100000b981004840140b8013014121920300d0f21607035010750340c1143e5120050700360701981c3c0002c40d074180c00c60006d50040d12030341d40d000c070320707a0714410054201d1724 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207948669 1250 207947419 207947423
    0x19020d0801050d05100617100209031207020d0204050924040c151403090604030e040506010f0302030901020c030403050319020601030b0105060f09062b0603150e0703120207030618 79
    0x40c5400180708504220b0b070255001e5100d201150390040010100341300303c0d9910b41008040d189640300551090204106542c070700070000c00c045140c10000d00029942c4d1451083c01100310b40b0211710031056640380701d00449103d8013b00300f8401c030718200880342e0700c8040040d0610390107200344040300850b01d01030600605c01d0340c0c0300d81c14403a00c40c103044542d0750036841800c0860401840700c403041c000c00b03180b40246001d041c507440105082c0c2031625000c0c101c06120b900d0103001c3c529090800000c0c2c0e91100304c2d10f0480195050042c0c0d21b0f00e9408080d0702900ca401c0d000c09162000003400420010004010000904504a00030f541c07401a58200e8696400b8803003c0c0030214050f00500c05490a00d00034648000e42d941031500d813010b101e012600c9904002000c130100d00023039840528103003904505000c1c01c15164420070030541540d0b02c4040300b0401145140310266900381c42d1011440801c2480041c0d90414082c9413010690300c8029503403940350004071403144c2048100482d0080d001c4607038036901d07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207949919 1250 207948669 207948677
    0xc0d021002133c050102070e09060f150a0815090102040305120f1e130b09030718150308190314071209140f06130812040c09060b19020d 60
    0x24a0000000c00149150f5602200440c4035a5010034511000142d6000102e50032401000386103401e0029003041c00650208102e5400003003086440c3c1000700c3c00681c00012102c1070a00341d143d1088812607801c000c141d858102e804064080352141000603402194007034000444513030b13a01d0744803050a0707000d248001881a070141c03510860209000c0098804044801d060a042445801121101c4c0c81c45003191510102d000070041100305005250502030305082804038549002100800d6448005c0d20640801040d4040d095450b071105400c155034511890102113503046d141d08020481d94858034481b2501d8201c0f1519400c158013134010404a440c401007a081c20b40c1c2e910805440803583c16004000361955644c20358006840415034202d03403040e00d0020000106170320392a9141c101c3c058115459200c421084c40c00013620702048444010344000c400703540b03403210b281120000d20350b6003081e44528240078002c0f43c00000e84000d020300710340d003400100c06003210301d03c141d8540c40c9402a100c002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207951169 1250 207949919 207949957
    0xb04030201080c070602030a05070201050604090b13020103020f0406020d1106010e040602030a1503030224060d1b08120d14040c090c02030d02030c030108121303110f0301020c0d021002 81
    0x5503010301440c2e42d2025812522503c4c000c2e5a95681c4226071084410b2011b5550b100d0500c28119424400d10740d0080c1c0c00d4400308081e900ca511424840d200091150b03070100102125401164803a0b0155942c0d156002030482e215038441034007079280c100c000580000507201c1200303d0510040050101e04071003156007c0001906c0b00d4440d200030354401005910165118040d950b0300311102c50700600214040d0340a0040712210102132200c540c600c10011791940701000600100741d0700c00103888200b0b640040b5101c264100c1c11154203058200d07512503d4940074000c005107490460400034000d030352001b84200048402c1c082e002e180c401d810b0b10040c1c0100e078041018407401c1101e5200c407114144c0b0b401241e04202a030803d040903030f44115102000d40002000402000104000030065401e4001c070250410076691100c0806902920016000d06044829128161110790020140395400b07002903542c0c000d00c801245d50713010044006030051140702c401c0c3e0a441c0480c820345182d007a40c01550094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207952419 1250 207951169 207951173
    0x2180702030c030318150c0a12060816320d03230706050c0c0303040609081312060f0504080a03020d11120907050307050d02010c0203070509010e010f05090f011203020c030708100b06040b0403 84
    0x9c8250100700d07541c110355580c001051880080041c503483c0c00b03d1001e8004420f0401903180407402103001185038007810040b031980c101d0400e810651a400040d11190060324290800301c910490115a00d0200311802c01d41d1000b081c00e84004180050003010203000503103507204101001d2040c1c00c40c2c2d03074150b0010b001040c0014101e07080098241d015032600f6007440ca40102c05180f02c07166521810303104008040c2941088070f2401580300c0c03980c60440070005480c0c141c03101c11482c41600504d50803d035002480a4400107181e0040501d81640d4403a6070702d4442c00600240507031030507282c40026209000c3c0015640c82c2c001094005d4550190440d08201d0090380196a04001840120303414011705002160303030303203a610140707000700384407004004594982200c0c00601d0015410943c040d91005082000c0cc50403040700a04640c010066000b010031242001c0f8107060040101c1507150280b5040005d03150800204000000204813080040d0900c0f18100400d61142d803042480e030300014041000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207953669 1250 207952419 207952427
    0xf0503040311030a05090319020906060c030d020403081206040e0706050a091a070201170105060f09180a0e0d0905030d030b030a0609050105101202180702030c030318150c0a 76
    0x40c015129003091802c4020098000d402c58100d000d141000480114041500c1d00e810000c40f0344003a4100000c1e07180344400d0300031401a900003803010f405a40300042240388080104101c444803081c00d90119101c940700c0c502000709030310a03400c07000040c02c010003298851506102c1d40b204894410010170440740381201c140c50341d4001080c048284869848001111020b2883c038050601100401c01c0d940c980910026005079180440000c40e01900720060065440340d50884890038403209c521030301c4005100008032a00701984404070420081c0c0148100c101094200c0c0d043c988050040d1b6507481c1d01d0020403141c6100034411168150b014140340e45d003190107503000001c1d06001506a641c4249183c0324101555481d54040303e040c0c0d507840130803403000201e0710118080d10103500c0300b142d25007090700042d1348a107031071070315007050106040451403440c0204211680105030f41d05494480c500304d0314032803140311200880e40d168020902032003c0c4002d079130b0341148181d0f4001c01081c00e000c40340700211 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207954919 1250 207953669 207953671
    0x1060e0a0806010b0a0f02160911072301061a121510050d0b0a050120010204170709050703090c1202060403021302030601090602070f0302060f0f16140d0f0503 70
    0x16410040304032020441c0740c1c09021140c007801a4242895540c1001d800003003903c18070040c842c0440d000b9800c6103851664920050044480408000c140e1080403804c0490510910500804101e683c0b1032506940e00180e002280200c0020000c12415658201c600300c03400500840e985108010032081c80314610f061091500003034600c502a0043c000c0e0008a02c0219401084c10b0200700045107080090b1224000d500c100c501c01d407400340c0d44900d840006001c200c01c43c01c8100c80c0c4840040380301710100e030942c140c600505e8442d50340305002e50700b481c0446d150301080c0140038909003001c2c0000c2d8064040d00840385000e901480442150307107098070681d91100c0f001c400b00d070b002500308070000169903500c1c0600c46010b1400c0005030340b414090005004103203140d00203010340d04500300812102c0c1c00b101c05c6500f00d0360103403081c542e1030800b4140050144181034440c4010000460a0078880110000100320103105e041c4101545407100b005d9903607050558621070021f00042d902441d000d10440c051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207956169 1250 207954919 207954947
    0x90504111204080316090f030303050405010b030607180b0301030803061c0b0a02090f03060402031c0c0204090507050102210f070f05010617101a04050709030803040c09050a140106 79
    0x9410034040d0000200700c5481510306541c1648040288038044c120101d03040302c241224109880302c20b1608421010f194083d10000e000d155039071000405220007034108881c0c501f0010141e51f828035041c0c0010340700b045040c0c0d070301d007000b040c07510017081701449030b01101d0580760014290b40c01d640e40d2404001d409101302000c00d42c20402d060740c180c000303244003070010300030300c400500542c40d0700b0001c1c180f0284000c0d00402c244a6032200040c0805600c0104a01c241a0300404100c40100d6400c1c40030348000900d940002d400501c2e01004505000303002c1046000c1e100c00b44e0984600c80b6203a0741804030f070a40c941101c0081c01d0200f02205154504800500070684a8400c88064182c3ca4503102e00311000f580c00240d149400160b03282c922041031221000c035842804d0704000c00d01980184415050101600f41d00999913000858141c2c0d024030940360095600401d4a5580c0c80e2600d400d095030a460322070f2804060610300410b4a10700325004280140244202811150307280010495068281743e0742c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207957419 1250 207956169 207956201
    0x908062401120c0806042304030e0f09010801060f0b130902030403030f090f14010e03030604090201020a0c0b0c06060a0518190c0509120a020904110a0b0c1c0e01090504 74
    0x1240400c05428064a445840719840f41007017031400c107040c03105540540d05000c003070036011040c103446520503a000703580054151030403d0014123544086090030f00000c09407644224400d000040d4440150413240035520400c080154041e0344040400c41c500420b89480d41c4103043c490188156409503000d560710501034640031036009a041c12100840b2a00101502c03800200707202d403018408000c060020002880e07008001030148514803a0b00c0b40409051180b1842d12400407105580c400c105401d40340da0884100b014065458051420039030041c0c1e0800120f000b0000060068904074040740211640604148946800a88180303c086001090441022880d0303410b001100070300d11401511410684600d651030a610040104040300840ea03003509c0d40c01200076070300580f110250f00360001d500204502d07080030309a0005403c000e040d000b407614100b012a091401000001c0c01e00d003005c1d40300c41082070351400070304d080301c021140c00040ca0108078501c004225606140c3c2c041010450071100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207958669 1250 207957419 207957437
    0x10090c05090112020f09060a12060608012307050301030305070b0a2901020714030a080705031909061116150c1b03171603201c0908062401 61
    0x400141c04030000e810660401d80c0e160040c10440c2040102c0c04034012044466000c01d140410004072590068052400401400c0c4d1401c2c040044507081a40502603c0000f0b00400ca0708036050224107202c45d02d200c0d1520000d030080f0b40880c1c01801200d059941642e03c080ca00112919061a8074038082c0c1714044450f5902c0c05c190400c00c0c42a003858424500c1140061024000c8000a1070f0580c01c0d0403551600034004440d4031140e50000c0c00300300c2c1c258071981407900e54401c1e007415070450041d681d00b5400c85a800310240d9a46601114440694402e9110f0b4004a481c0089941d5070b05001c0d0389044a2194102003802100410f004444500c3c81514020091a0080e520902c003c0c04640800e5070365000355a00b4030800c02852442c0c000c4081c4070700b40c02d081031200000600303801d80c00200034013400300c2c20030350f031032a9140180000c0400c21140115007076100c03420702000b000040c041c4d04da0b000a40e80380020500c00404901107000b0902100c10840c0c2917070b9410540d5110458410540c14051106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207959919 1250 207958669 207958679
    0x21c1203020301060e09160305040c1d0609070e0306240a090501210b0609061807020a110406060c0b07030204080d090303030f022d1b030c160810090c 66
    0x440404802849a402680301c0d45003c5001d051a4991080103214440200801054050702800315564220b545004103c40d1070324200052450481d40200192201e450640d039045160f000c000e5010305000e484000b86035844a0003100e585d903c100200d98907411010104807540c50030118030386400300681b54018141e070702a0024010030700039844802140d80b02d4004100ca00700c0d80000e6816042e4115011071031000c00d80e01d647c254600202041d1080303409001007805603e511a0445140c14480c814483c80d0a215401a5459040110448080d010160b10300080d0800d0300071101265050740700e00d1010001e07507555014030031004101b401015030901c800030700b035070b81000b458050240799140c0100050071420000e01b07440160382c3c42d1a846004001000c02c8407031072504c44506001c0d078410012820103000e012030461082c40081c50030744803660580100098040010174949200d442140c20144500ea070301801c2c05542c0c440e2400c1500079011541129010350058240c4030720410b0311012890f203030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207961169 1250 207959919 207959933
    0x903030703030b030609070b07060c02100603080c06060604180b040f0501120302160b0306060705010e010c0f110607020c06031e01181a060405011d1509100504050904021c 75
    0x140304141c000a4642c002607040b4202801500c0e00042001e010f03041d2076042c150107a2031803043c030300000c1980340d6480000301d00c00d04c00c4c080480c2011410750144505956030510b01066000507552030854091800860507910301001181d00302d520751030142030403081a0040c0c20003031180242083d041034840600d004824568422039001c1d00c01ca1402010100181c1002490642a0000030b030b0400340241c4188810f4903d40e0949502541c11503c00d0b5941140d071510314007424603500701c41002e60810b800d0215190700b148488500c2c202da9a942102c0c0502d00c00100c0d03a650081e28514007503000a08a0074080c1814001140e01c1617580c4e100c58040b503c007030005e580802c1d090b40302a0301d201c0702171a4442c034242540100c600ca0b56201071380b41080302c0440b000515034421441b4841c1408040c0783d114070940b6118070b021038150002000e40040840e001008103503a4032002030548034121800b1824560f0707000b1025141580c0002d0010130050f940d540c00d1240e0000d401c080580d1107284144508000f07850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207962419 1250 207961169 207961177
    0x150c17070b070210020c1504020d06090507051201062103180603140702060717060d08030c0904060f0308040603090c030501051e060a270b0603090c0102120f1e090303 73
    0x4211141e40c0107192070180242802d81c00c2c071005514900410280c8890b0300001200b0021f031180710b1070201c9030b448a01c00520a0401c08500908240c00e20091406000c8003161003030480700d0503580300000580b800e030b20500301c40181c05042a2601c050700442c9051a64851700c3c41150710905019020590b1101000c10603030301c5600620000e074440d200d003501c1d0b602c062002500030801d40010b00030f50a111034040e015003c00c1d00c162040480c4a17000486a9491164102a01e0781100c91a6520300302500054042d03030104400d5400b690400100081c80402c001d910006c881c2c12030b00b80340c01c007400d103042100500203018081d80c40074039040020010540030300c1214042ca480c80354090306080d40c1142c80b400c1c0301c0d0082807d442884d04e00010006210350f41c0c40900041c040c01c000300d84c01140e02000d80300030305205001c3c41d017104001c0104004240001220400300750309800301d4041d080d1551038050b0720b100340070308900034540c14804401400d5800341c80c0050308440e0041c050801c04000003007495030708 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207963669 1250 207962419 207962423
    0x705100e28030e0111030702040b060d0f060807290904091202150c030910050a0e0106260c010c030e011205070c06060b04060806102601080c0406150c1707 68
    0x4000700301c0700701604a400c140c1c2d4040d080c00e0034540300c40c026100b20340300e01455101038081c60701c0d088079410740d503100c0080b10440466250100041c4000482d510700900045c001c1d00c0c09032068000206108081c80500700894414211103070031a40d40a046402a40049000d9500310341ca840c99440000c012001c08a1001aa035004115441c60000d001c1c0507024080c1a85860100c10000d001c0c2c409008119030400321004200401e16850310b00b10381d001400b8000c0810540d5190040129070304078501c0107041398040c0c4031507090740400c1c1001340702d44401150f0700d04c0c0c0c04205000380c207c1c0084c1c0204214030000c9414100510070407040c119420680e03030101c400d40000b80000c040b06003042447c0c07048001030030001c1101400c003820520058082c030809080b8a100d00d0700306100c0c0e00414459010030858585074104002406141e0407131220f0b06000b8005d00210740600b01041c5201d09042c801c0b441160358000c003417460480c040c001501c0b40c1c03000600170740da40c0100c0c00c50305009804240c010400c043c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207964919 1250 207963669 207963733
    0xc071a040f0314062401050906070b04060b090f10060809030c07080c010215190506120f0109140a0b0103140c0307180c090f030204110412050105040201030c050705100e 74
    0x403100c8450601000915145d070380b0300c0342c0004010a61741008001781026080c00d0a43c1e44500a8000a0b014002c0400080c0b50050050401040144a4000c86180c0409458200302521966280e204400d03044410340100000c04800304031051080b06203503005400c20040d03d10344031005940604010150300300d040c1e83d500500f5000c10650303040108000856410031348030310300c0c00d05d540071259204041d0407100456445101050080d550414142c034040343c608112052070203000c0585020300081d00c01965900b1007510482d2040802040b581c2506038046c0d00d1064581c25a83c4072045444400300c1c8000394441c840702c03101c04c2d8408000c550301a02c880100e80d2603211070000b0000aa44441040e28104030121408101c0780803074a51a005881e4100e4000c02d00300580c0300b09440721300880d4003000c0307108100080c0906002d01903214034003c60003a079051002d08a0480f05480368401c24100500551010a50490810255001004400c010b5040d5216030800102103d4a000e44160030703a554 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207966169 1250 207964919 207964943
    0x507031d070f1a090405091e151003050606090c0918040c090c1d060d050c0705070503060601020c0d17030c0a0909110405040903090521120c071a040f03 67
    0x41d441c12841c54006001e000c0c0c40c40e405482d400f034101024040c110145004a445201040f00e05c1c0051000c010b20440ca10300c0c9501d89a501d462155807890340d041c1031f1603498002e00102e6000304402d0680025079403c0401444a41c880c00c0a00032a140018402141303400c09000c6280940d840961440c1c00c1c503e104528041030401c3d041070a40c1c494a81c0c8030580583c0340c00310008405400803020b4056100e82c190620050b0000004034050f44503506000d8407251134a0200301e00820140041d0220500841c04c45070415100d0040c1580c40b4030982c0d074903016910210040c80c191034094200004c4603c2201034680007203c01401081a0300181c030341952262001c1032210b689a400206a00180704d03400c0280a50146140400054411401418011a2a103030240185409244d00344003d0034080c004000e11041202d1010b840800c1c11030300700340c90141707581d9000d13031a21040c1a50651740000c00079190a616040500048091411009010700c0c0b092000088418955030a000210701400c204411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207967419 1250 207966169 207966179
    0xb01020606060a08010b0c01110d020304140706230403060513030f03050f0112031b2105041a07050a050109030201020405040c02030a09030b10090f150509040f02040507031d07 77
    0x20a00010007035801500188079451042c2da0021405044480044c403455490152014450241910011070440752400107102001c1800ac2d50096110b00d00401001491040b00c00c5441c3d140c8520b4032039000000e22108500110b066118041d5135661248a011441e19941ba6104011741e20116009903418904d07410440a064001000c1d020046641c9010000b502c1d10041000c14180180201c6404581400040e01010b000c0e54220054240442c17000400c15038901d083c0754221b1241200c80b804200f420340321068030307000c0e10949007a00e917403041e1950300e540b00c560f601d54550009801a1000d100c0c10280c8000b0510038400c88030040e004c1e41c00540e4841c100018081a41e1081000608550041044170b034000e512080d180c1c00e40340c1c0503440c5407a6455910344603071a80b849800c8091010b1030303d055a000000da036030050012030042028090083e54600030040340143c00c581c090608c013802044000149041d600469005106040002ea500fa01c82c90b0421080e543c00044401e9920681061003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207968669 1250 207967419 207967423
    0x306090e010b0f060a090902070305120921090108010b0c1507111902010c020f012604060507020a0f080703030908030103050a030201050a0b1011120a0519020d0507030e010e090a0b0102 81
    0x3040345401c4c3d44444c41e03c5820540100003541c144a01d221455000c202241054400c070100d41e401d488031762902c442410218591503c404181c140d03000b94001070710032544c0b6100da1505948035800f0584500b4856841c00e0b100302d606a00c80010740d04203014a9100000304a03a1031034403030090025030307540b4821510380803103e407038400111030038185404984075000051b07034440b409003145641501c07a50904064500140d1308400000201000c1c0341c1c64109820440b01d181c00310318403560250406020740d032601714040c0d0326a08545809000010300c00c03009000315580340010801e15100346000030380c0c2003181d2112102904203800c11605900310440160915509000c2c094004240303000801c80c00f180100091000750a00b01d82a00f40b1661145410301d182c0c0c24051888402c0c0500e0049940b400d4030107009200d544400440b81011f480c08104c494003d100144400c0c84004a4843c9458420030745c40c169495915804518100500748413002041d0b15030b10071440c0038482c0c020010800c00d02120000e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207969919 1250 207968669 207968689
    0x313050102042c06090109020d200a0e0907050a200601140301050a270204060506030c03010302090106080603030406050f09041e061a0405010e030a0515010f0b190806010306090e010b 80
    0x2c44a83c4880a0201c140d07030340402c0904491140741e0040c0c1e80d028a01c6001c0c00f42104514081c2801803805800c0d102c00303021401402040680d80d940b48c049105003003080181501521440c001560500440001070300840c20300205c05240700a41d10030300030a410542ca0039000760400080d0400d1407c80040f54142400344a400c0b42055509102455181c425015843c0c1805c803603803040608082d5400641d11590f021001811b0007604850740c03490b241c8140706030355000307200072401640388800020303641e88200b520b64002d0340001c010f035203010310f081c0701140c40d5005082c4481d2410300801803804c042d50b5a2054003101d030085c40c040d22407982c07548407130002c80303289038070000708010556a1080c0001341d031021181500ca003401d003040a80c0e002ea01082c035210301d54000a05034400c1010b247c0f1586030007420340307040b25035542c41040302d161070f040030081c00d01030880c60b8410001c1e000da9080d1064045c1000700d80c806418540052140c1d911746004055175050303417120105954402c3c00c90a2030928143d80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207971169 1250 207969919 207969989
    0x6060b1b01020313170d060e0f07050a0503040b150603040c03031d01120e0a0b0a050105100e01200c060f03060a0f03020915041404030206070210050603070308031305010204 76
    0x318218640b13004180c141c000481001402d021242c0e220f000c01446030703029038400080c1810104416038899280180b480b13001d840e070a50031107003036000a049034883c1c822039805500564501d400d42d2200d680f4103000c1c0401614001c040c40e2000d92891298444a003d1442035004604011016246003070191200040070310350701ea5410613a48079844c42c0d03048000e141a0f003204007400a582c1039034000442c01c000d18060000c144018440c2444818145a0049816038100321416481140741e0726040e1411001249001d010801a6629121811000600c2c0e400110f0610584400d00003250008641d98400c1d03c488280c0c035030100070320030f0b58244800c5e0b06020b0001218092040e0b030440d00000c840f0310004006403464130b401c1c10070040c41d844942018207400034407085600c1600700307481c0280d22440c08807021001441040680405200503014482c0217080c0035000d0010709045486103040e50380001c203075444c803d011a5201001034000d1004100810700080300b50b000041010707086604c000d6a180b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207972419 1250 207971169 207971171
    0x3160e0a0315020415020706110c0108040b060d080d0f05060303090a170705030313062705010509010201020c030a0f080f010810020a0c140304050406051813030c06060b1b01 76
    0x18a0311440a20010340741c204019590034106240030030040d20031030300846124070341c108034008020780000715002540d0f002d0700e407041c20225210f0250750350880500310f503000030f9411020402140c090a20b0a070889400740c500140e001035034550000551003040602511341d940c4050340b02d00e442610420b500032004034007952401501e4000620b100380c25000c0d55034052070a5091150840041004c0c40c0204030140c280e0341c50328103020848500c40c610b0f02c00c510100d02c0b40d10204102114000000144c001c44d006101c40d454200720044900c0c0d0401c0c801d0505542d401c002c455041b41081007c1c28020140d6039410050b02039407600200b4030301010785441c5040e41c101006100101000c100401070a030341040051303c0d20701c801d100711116101c001010380440000085011482004001402500c00982e030500c801d9680c0d8080c005281030b8802180e04030300c81d41010441124045e02c1071150680249043c01050080c0c0d00d9035011191190321401403e8000105201c48201c0d014203030901462102c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207973669 1250 207972419 207972437
    0x3080d1a031e0f0d08150d02010c150b0904050601170f060f04033c050703050904150305030d06061d0f1009090f05041406010f29030702030316 63
    0x80820381c0d07503203031403040a0340c00c0d1680501860500b0400c01c1c403114003400ca084440b15050104081c2c104542a00c48094404121703103c10200d040200d40e846007107178182e503589050200c50312060400d4003480341811030720340c45603604a440c1d80c07002c80d014002d070b000310094540c55140680c84070b08992035000a607695002b090403d0708000f000b1900581c00844045040c640d0340d981d02d411070b07558010352529442c501e40720f6000910080c50420030000101c201d03030710b400e0a4260003c265440d00400c1001000140104030f00d51780750400c0e8001215103884010300c00d50f85030300c0783d640f0390954000402c610072043d500c0600b08480b81d0701038500445101d0300b03200809030650a60104602c0c9a0a0035101d001d68074004000c125240700720410001408004003c014440747c2c0095a0060041540c050721800d05280c02c00c0d003460404503000b4101c1d40c43c1e102a0400c2807800300c00482019103403041201c41880b00d11800d042c803804c24015841400702d980510b030340f4641f042280c0c00c03201840b02c1c13240401071410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207974919 1250 207973669 207973721
    0x306061008130204060504090b0901050f09030414030717060a240501050315090907030c05040c050306010f050f0a0806010809161205010b0d0311060f10090c110703080d 74
    0x3010300d60003074102d8107620603a0840d400810050105980700303d8116140800150502242c00102c2e8050004c00c1d0092101d07450303c1c001e44100c0541940c0b03290854104120400801c182080c01e04550b01d030150175945925900c1903403116102c408403450040da00a04104201905c040c464a501030300d00c41040b41e0b1030781501052100349100c602910b81841704c00030101d030409070749070031305425010001c12050031440d261482c0d82d224103aa210440c0c2008503032a0101e010b2405004101f071120b001c0c2e98440c11a5140d1004407100c0400502680521800300991100007540200501025080d41c0362030096041c50303800140034a0000b8103600054212040400e0b09080c1c98007450308030b6100101c81071082c0e020341072040c010141d12281e07650010401c1910400c00d90050ba078003840f8038284056813501d99540b50141c9941200304d03103000f19900d060070140319010f980ea00000305540c042c81c01400f1000f030507007842c3c50840c1540050f661424080741a210140c030317038010040004070100c80120070031404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207976169 1250 207974919 207974927
    0x501030804140f1201020a0905060906090103090311030f090a060e09040b0a06050a1409071b0f0f1505010f090207050a0803090f0601090905010c0c021815030d0201060503060610 78
    0x140141030b03464181c2c140003000740c0d0728859150407910005090401d13003450740c800c0b00c0c000d5000b4000d8501260002000040900c0e1035019110f0011014003040d182044041c0110000c2102100032030038032003004000115004204042e05d040001e040580380c2d5050350404024144009030b1044007000803201300d80b8966100d0402217600300344d01044122542d00c82507031442c064901904410b400c0790030700000244400b2291058001c820098404102c15110480300f110300348903010030205007080c0e1110600024042c0c854410003140250040d10300c4240316035400108050901344030b1905c50303c0f900144030b140724608170b050045c81c0c4440210700c1c1031450350700c0d03a813646140c0c03001900051380480000d8507800207008881f08202d0903001e403040c542e100d1880d02c0081203030001c10303203181d03280c041c5120140d4041d4480801840c3c00401100340c6204000244c2c0402100410b1142076046010540d1040e84007002604401d8015800109036a4180000e0514194009100301d106e0000004000e0081e600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207977419 1250 207976169 207976177
    0x30417070221031b0105010f0b032514030106080f16022d0a051605040c05191206171002040e04020d030c0b0a0b1815040b0a0e16020d0305010308 64
    0x42c51400c034141d8242c1040606600070720f0701028a131600501019010b46065210074141c400744015200c03880c5d01c07811103054500040b11303000d40b01c2c81c49510004410821010320501d4007443c1c070300411602117200d00840150403c1e8840804580043c080c04030801e02000c00070b83c4440907046001c54400000d0b030080d0fa070718070440c01d000100c148401c00d400c001280d401d0280f20300e081000301d8424600c00d00d005581d4191660683c2c0910748024000703d010f14041c082c41d0316555042c0c0e20035080c03450109804100e8000c618000d01072080e41a1380610300c600b140111002003500912201c400c04900c0b450b00e04110780c04003200001407042109000d5081d0f02c003610781d0401d0301607a06801c6040145801c0c0e40c00c100d08040544100690030400081320f032781d03400009013000151211450484c101c030040300d04010690705c5400c00c409038403810b403113070034103611041c881000184455015a80d8000002e000c1800355a58010400c03091031703407124960100100e681100c010724040009601d1030700e071f44c052806 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207978669 1250 207977419 207977449
    0x110d11030717030108250506090f030f030a0e011e050708072f030a02010e0405090109150e06090a0f02010f030f0203070c0309120b01090507020708030f0304170702 72
    0x16050200981844100180c840c4554020040d402c40c01c200d44204580360001d1052065030700c05c8264040d00c034201206954141d00c5e040161006907404d02e070070807481e40c000d191460780128071148207417115902000701000c400300b0400a1a5030303810401e0020207040140d0206414085402c14100210b141c02c000c64240100d5403402c10380f06c603082d18140d00c50b4400e098000d40340000f1440658180141550303060081e6280c8070100c000c80d06002d082c55160300b00d0343c02c06408104002740c1c900702e50400e40c002d0750b8003501403c00060410465950b010351141a8001400025540c040c40d0300926410480b03550031083d51300c000c02580199503104103c941000790020b042090000011a134240a904010b0b400d1144d800290740b0fa2501260042c04a10010410b070001a83c480c00064098254220754480d507030000705019480e0300f040e0f5008064040500501c0461080500c00921058180050025a4200a582c90784c034189414482403000c281035042d10316440c20000303800141d84050355401003503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207979919 1250 207978669 207978677
    0x5040207111c050f150105041b030c020c030d0c14010b0907110a06050c0c1e25050d0b01090c02030a0c06050601030e060a09051612080705100f050108010c110d 70
    0x3050007100403109412000d4000c01d01c2c0b01d4030030350903002034011505c1d040b040d0984050340b44983e40d50b4104030a981d040f007805001c0b4102c10b03010395101072080e08020365140d66401201d80c04480840400c4c90214030500072000140c88401d07400400c0002e038150881d83d0b0841c6c000340b14a80442c00010030b8201c002d45000c0074482c940300c0008440c201445a007502d250002020403071803a100344114142d13070002401c40801c1c02001800081d8041c060540280c01940b4401401401010505080a800c01504a207241c0000c1c1000050543d90070135500465881141c092a1039450428010700f40d5108107901c80954106101814407079510040412042c2e4210348007050035141c4900503001048461581165802540b00304007a00c4815000076590f98840d204035450440340004000700c0d011035002c0c81c040303481422200400700f40c80c0310180c11414011130940c1e8004220000301d4007140c403421a04418251900c0040168000a2081815400c0c0508200c40300c0680402c00f20b840300c0c0340c914110140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207981169 1250 207979919 207979939
    0xd0e06090c011413090f02040306180b270105010f080f0a050613020f0301110a18050a2603030a060518150603090c041e110a080f06010e1f03060504020711 68
    0x461900d00c0e22070001e103501c42c010007000c00300d241b500003e5401400700b600d025044c401d000c3d1500f6060802083e416400024128590700c0e0310b19100c41c030300c40300c5400e0344458458005000d4075290030722907140245800b1503c081c3c0d041ca00a041810a00704548510007904611100004a080400c095a20200c05018148051828400905003000841c05035070150b00e403500040001e50221f00400b1059965100d80c082c41c2c80c0c05a41c1c1500204078060281c1101c01c0c007008010000e8004030100501c4e860030041e0402e40410b0030b940389590012501c2c030b0452a1142000c005504007a02110b812140780320281d8064070b00305422040b06070004c0b100d0750140000100141c3c0f2540c061240800c0c80c1ea00504c24813015078620098503085c610b003c40300c00c02a00d45103660712403048550480b1400201ca40f101c182d240d07910007a034019000028840c0d81030084c4084018440c0c1c0d01c0b514411030040e61312526000c040305040700101250343d980c1085025610400c140d601180d002e005000d00c0c070300304803440259 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207982419 1250 207981169 207981187
    0xc1002070204110c010902010801051c08070816120305010e010e060f19091b110d0f23120603010623060708040f030501270201030b0111030d0e06090c0114 68
    0x9207150f0201c90000000400d4991300b07984190840510380e8000d1382c450f002c590b21407007000315607aa41d1907404500b0803504c00400003d030540001d0003c2600441087c2d00341020305480400301014128121124103801d43c115a0300e5415115182c0504400c1852141540c1481c56152441e20003a108500c2003101c1481440d5580e103c60903808050f400c04c074903510041e903504040b80541443c10318035951000042c810742d03016104210285902032820001c0c00000d22140050716200c101c04402c004206403d2810f0b19034114228903d1802c1c1d80b401b480c1c0d640d03202903170a2441410350107003590344217905140b03040000303003c91121504440030f00c42c04000050350714400035019206094000740b404001141c0025008864025003044900800003800341d60344200d12040800041e01c082051000c0503010742d4090751082e841062003410604040d1040329006054500e1a00007450094842c4d0300d82619208456041c0003094011180c81c004007070944280c070002c4d0010840c0d8000e901500d00100302400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207983669 1250 207982419 207982421
    0x6060319180c170309120309090106050a180b031f0503010905070f0b0f12090a0f121106010503070608090304030f0b010f06050910080603010906050a05010510050c1002070204 77
    0x10384021480200441e120440030503065840c1c90505640d0790005050018030054210650030b00280003401031490b102a40040113000c8091031240d1a580c8004d00690300c030351b201c200c0301038080c024903100c5c03645075155071400170082d9002c00c585500381344e4079010400070034445100346d07031b0040012030000041c0300821003941e40d070481c50b0740403030751542c00e02c20040180100402d5807401d64810074445110252280019082031141100503103000208000c000b0b40001030920b400c6d008100181a294660304a403144d41003060f801c041654065510300c0c040705d41d6500030186522150300400070303018039031521000a445012030320540b014421a00001000c0035800d00845020710380c00280b12f6000055824400e02c84c54007400303000202100c2ca01d02180c1c10f4003940943d038444100520f83c07100400c400504580c0030001408003505036407106032110002d41c41d4011203216403072868000407a58502401c108040c0001030802050060420a05410740404240b4a0000c0c2030796801683c1c0b0a0580b001c03038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207984919 1250 207983669 207983701
    0x702010f0908040618081002070c0504380f06070f0c08010203100b0723161710091e1a070e0f01030c210b0904080c0d0801030209060603 60
    0x60414908501d0303908002c0c001025006451259569404419504041c0d84846520f40100d9010b0381c00810f616940145a030020b1402621500a43c5004c3d030b40e500210382a600141c170f0f9022440d0080300505401d59a982c0c082d07034255004c0b084041911000390105002250f20348015004400c00102d540501040940440d0090382c02640d9016942d41e5002940c000e41050b24030042e031402003200020b401040e00151340c001900144404c950078031b40c080040b52030030a091449005d02075503426110440009012030018400d00c0074000302082d403e42e80c5400d101480001390401441c150b65080401c400040d400b421300042c1404242030880d901344034400d0301081e19810b4685c01101d0130003c1c4280d0040c000b40c004101a0380c0b140c400c8802c0b200541c01e5862400400c800030348179240c5035400744d030030820310422109440c0740007a1507228100440d0038000c0464043d03421400c0003420040001d420810307076048469a16002c05e0a505642c00280b95890141100c3d204400201c040f50000741d82036400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207986169 1250 207984919 207984941
    0xc1e15071e0506070306050f0405040510020a030e060c030f01030b040305090d0807030206090a02060a140f040305030405130519091109010f080d020a152c060402041b02060708070201 80
    0x2041d588004400c551080500c4841240c86000c1d050214280c64002c1c00b4010603200c0041440e13201c5102c2605120041000400c2130310184103594400407280690700c01003400c81c400c2d0f0390225480304100380712441d0600140007012036003406c20403c40b0045001c070ba440c1c10340394080080c0c1c0e1540c865003030840f203a0217003c2c0c1807a4442d080b6003200041112032002006030360300ca6002d941981e61450b51480d1200b00e030f508040d4201030304010035400b943c0300b61a8803104512a402d007d0908511640c169004c1e00700d41c000300c61a41c8000743c00d21480c9003182c81c2210340d966800e4140800c1c03038070300081080080d202602e600c40030780b113400540801610390500351403603502814807103607581e490325440c4400c210751040c80c0c0b040c050020308240c103030f10100d4000e00c1c15030406019a411848a0000340081000e0041120b80b0051358ae610007038080708503041c1ca8805851070043c0ba06041500401045074651502c46003004080f00c00c0040003600803400903800303042c5040030125951001c00c1640500b40341d0b110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207987419 1250 207986169 207986183
    0x5070b01060e150c1507020a05070924030f03050a0c080c0706080c0a1e0908060702010c30110903031303060f060509040b0402041d010506030c1e1507 66
    0x12558592003448264200030464100f602040c5260b80099a0310400c00c00d260140c014014890300041c002c0005a04001e15104889214000740c40c0c0604046550700002c440540341e00b90f0041100e0000c010801c8080d549405900309841c2da0f136204187c0d0080304009092140c0032a40b404058024030b242100070b90462612942c9840142c601c5494510a001d00b502023000000865200e92480055440b50340c2c075920b5000d03d800aa070a00203411003c80042001c200d100c2d130000c034803694140081800341905030008120040e250308003400034400101070a40004442030426107040d14503100d030840b0b030031807803000481720380844184402c7d1050501701034052000050280c1a050042d0700c1204070303401201c0c01c200341480382c0324441c155510381c4501031b400b00304040400c001c00d01020700607812610050000031004140700410b501d030300c074100502c0b0140c0d550b4410020b4905041c01308048070541110000440803405051180400c09004210700034000300300c0d0600c0005160701115040c2d50400d44d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207988669 1250 207987419 207987421
    0x6041b1d0903040905010b0a1101020a0504092c07060801050d020604230a060207050306010e060d030f02160303030b010f14040b0c070f03081308060405060a0209042904060e01141005070b 82
    0x40c7c0c01b0941c0d03015540c06800200150750307419000b80d040c401c1d03031020391480e65110f113850b00d4644000080e000002c14600c1d20100301101100529141440403005c0306108081c21809203003001c003030074844050348400e01071044120a0300050391f440c004c0701c0581e900c2051501c40004403013042914036620490050300110000e0000c15025000201482102d01c11402c41d041faa80f41c501501e0b840c2c0c029a41c0d46d410080b40302c0c8910010380500390078120300c18144102c402c0202544d5501e82c0d104041d60090740420368070605090300356072103000707464500d8080c281003050328448554140c2e1442148541c109101c4c0201d240003000c3c1061041034010248410b01d0b400260b2071b410000b509900c110301c0200007150700540060580d8000c01c01c14804e50300000035292b240d90b0031160b44080d5120350398079603007c4c0da10320614500001d0000d601103000d0b00103002e080444540c800380b004903015034010246d900c10580040051088000315150f0304003007941c03541e441e00c0c04040140d400303001d6010002d1968250740 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207989919 1250 207988669 207988679
    0x45010503190b0a180b030f0a0303020903100614040605010f09090e0c03030705010218100905010e010516050106080f01180828020604020109060503010b0d0e07120506041b1d090304090501 82
    0x51308603225150341c002c20045131801c40101a52002c000d00f21102ca60020780e282c4011a01907805400342038000790990390005101d0700c1c0001120810340000d050640100c82800d85c50a00340b056201a113800e0070700d0180c4100450000d8001c0030948200341c580d603218010580880f4050025211a030344c09404c03030741c81c2c90503858031602035080310b80203c644040b210155401841d110350700400301c0d4050b40340c0042190078200115040c145200c651414403004108103000c1d40c805200501da01d5000c0d10000860904200a03581080741c00d400010140c0c0c1007006058240c03959034940c1d10b5241c0c1c04991a1b6880701e15030340040c1c40b0003010411030f100040b600f01507010365030041482407250340700744d8914102c240c0b52401554580030a000310340600c0c07400c1c08001e0703018003980d12125510a45000b220f06032a5641d44100d802940404d0484940d0008403e0008028507410003e109403410500402194200319106155104503841280f10351034a801168882d041030045a000d0545240280482d41e110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207991169 1250 207989919 207989939
    0xf0c0b0f09100905100305091912030c030e15130b0f0412020d0905040f090203100207061109060a0c0609020d030903021806060406030209030345010503190b0a 70
    0x201c0501030042804007600403445110f100080256040101140021421600101d0080500400f03504840c401e42c2444c030b072104908441030310030714412200600c1305601044028183d950141c020000c0c1030405200060b040d001194083c51503a03d030381041102e07568005500c03403405c650100a07050038510003d1103096589040080d10aa0107248a0104201e1000f000c0b40e940ca420354981000407140c034030600640c580b54001122900c40a540801c001900c0d030002428042031684029809900189040c1006094020318104200d070349101030912a000c40400c415200307443c200e008000810000c5000c000442d809214bc090300900141c030914280d1a0140101c0c51501060b031040c0c0c80c442c4010001e503000d9806a104100107054581400c2c540001030340a03402940029074140014841c5502c0c40d405000005820055a081070369407401d40380e040faa5001d42005004000c41070000b0360b2200383d0f000320441e03400403440721b000d03010142e0344c451500c02003544255007680108600000540403442d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207992419 1250 207991169 207991177
    0xe0103050d0f0e012c04050a0605040b0109050303040515070c03050307020f03010b010c0201080a1d03030a0b01050403081210091d0d020a0b06090709050a06030903030b0103090f0f0c0b0f 82
    0x410b840e11801120502e405494035182920581d00044a0812159501c0041040900080c640100e050501081d100c0058282c8408850221040e0340d100c0301009549000d0103280c0040f0028200300c0c1d0b20904040100e40c403407180f0f0003071600620740860103018285000c0c0403a964240c0110f9040110b513240d240154695003d040706904c9a0100a81c080042c038042c80f8516291505031111f10701c14107190b00545001c80c0041464410a60324000743e08009245100140c07080a204003955913807500c03900c940c1c115155a2070703160401009002c28170016060004032036840c521420b100f4060760785d4610015a4075840d41099038018100301d409082c5400003100410b00404c840701b030361400f00240f070040b42d442d44903070070103010540b04501042ca5403c050040c20742242c814036040c2040c07625074011415064860b03012400084e03598011005042c2c1c103205a92030000c09103018070000c0480d89030b80040c4811924003520000c0242c62610800c404000c2030f4008101944800391510000c03d5a41c0560300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207993669 1250 207992419 207992443
    0x30d03060810020301050607030e01020c0a03050f0f01020c07170718020d050c0a050706020d0609090b010f08031303060e0a020a090b03100c050a08072d1106240a0e010305 75
    0x10031400b004075011814001c0d60705a46000d00703810700306019501c08a4040d5090340b111415401054108212501e58400c0c501c0914080c0004017a0720483e013460f9071400464621508030f5901c140168661114045140c10407603415909a1000450704241e8900701141135114118844c0040303540412044640c019003e800300842d01040340c1d54510003280036a114138824400051010881d020000d134095002e0a80b1240c4180000342417506c0ba0207010072038840000640f002c003e480c004005280c00400c585014042d548044d60801710703401c1a20f02004000d00006144030348483e141000c0c04810042110166001801000210780c0c1c0c005410003480f06500d03c5020340625111000050458090075005400a64550f4903001d03141c84115400b003400341042040190071141d2081c0c6407004950195141000e00e40c0b101491108080070700092500001c140c0150011400c200101c008581d514108511141007140c200c2001000551a00d00941004d000060398a00110900c00001032142d0001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207994919 1250 207993669 207993673
    0x1030b0f060a0e0606070f02030609031e0405030c06210c091e0310020702030709093f030c03061a04030605060109030c1e0b0a021510030515100302030d030608 70
    0x20300d405062000710702c120301403950400d81820215040d424244c00420002c0d00a040040710300146a0001e8101003068801c0c5140790b10100d10b07143c2e060340350442e118084c5840324000380b5003454603001c6501d03250040c00301c9100b000c0120b0441c41c29585481d115620081500e0001d540b45070107480d00c402d41d00100781da01c0c0249100b02c02004018403142c9888094140140140800500340c0070040295210341c1040741c01d8040e0080005c0c00c00c0c00c038000c141c40a4440c0c96081038018501ca0900d070100405500e0b955000c03032940082c4600140031012940b03a2003140390108074000a10026005012142d11002140a079104005405285c19000e8829a0302c10314040c040b546030503004540910541c00090405150b0070760400040805009801211481040c1a4101556080300540390382280c2429809a0050311480c0350810207517201603802444a8140c08000741140c071001d035500702c404521204410b4100100300c900d14203100450045a0003000c40d0301c1e540c0035060090160005100d040294 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207996169 1250 207994919 207994921
    0x2060c1605100504090b01110d0e1804030f0804081902060402130e060a0b01090906120506180a030509150f040806010e010605070f060609150e0901020f1209100501030b0f 75
    0x1601d01402c03041c40440e115900c060419003400e404000070302c44010071606000819210340340c400d0080c8489003400c0c90a840d082c444250302000c1c481100d030030300c200303503000c0348054108030000750401c588442001c480e10340500d0580c0c2d14641318120740726401800030b403d080120320103011a400103201d44910710940305d00d0105001450b400068a4102c040c0e1000c030f80005c00021106110365000c004411014900100c0195440c010082103e00c40c0e084903030606518800f140c140a810486150421298070480805040e001015030301c607185031100030200000003c2c0420703036960350b4408262241c80743e95015075407607482d411500113900901c114400e0780a24000080c40c61025040c0604960864950900d41800d41d907803042c3c00e40a403d0204c504640d200c00c0456180858450801200d00e0760f201c0700b241900f450754910341d0140060214a45038010030600e00c00e100c0354003c0c1c4a403039400071460041a02c40522003030924881200010100f880c04000106020480c601c00b805155005024202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207997419 1250 207996169 207996179
    0x915030c030a0215070302030d0c0e01030c080705040603020d0e06010e07080f04050d050d14040602091306030816020315090604020913030f080c0c10020403030e0d240902060c16 78
    0x2d036102c0c1000613511040306041480c10249140c02054418824416649001441c40881048030704441c4041c0005030a40e0141101c0c2d42c15100b4002c10304100e04005400d4170b0318004c005c001d13104a0141d41c0800d0f40100320b15101082d10b402000520701c802060380d00941c0c640f0050880f1000860b100c000060404010689154070030b10030303d0240e0340100140903100303803541003910b40c4d40c4003c0c003229a00b6a104c0b02d080a415205071a40e001c0c610408000d40c1e100ba8060400c208201e01c400341c10035840c5072400800015110b00115200c519500350a04150081400003a007040e0603040b81d499904050020455078001c04581c01d07100d94404c80c0c242c009900e83e4050144048444274009000c2441034900c5040c9a001350441d03540880006045482c104081e2200343c14280c00b0204c03188540d03000303d001c0c01010f0b004851007003401800c0d118407004101c3d54941101140c0148408036199046640c2c042c200b0f0788a82010f0340c20364010349000e03940c071401d0318010b40e00c2c802450340c90108002c580011507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207998669 1250 207997419 207997423
    0xf0a031404030203090d0c0302030f0604030306080f06190603080a11010f0212180708030c0304091107020114090105090d080a03060602010e070515131503050c04230d020915030c03 79
    0x70107503405500850400d402a401e01030343c1c120209080e580b81d00002c2000005030340402c0402481c0c4440f60103002070341007524002d402c0c1c6400350003140c01c40d000288400440715000031030962081050800300344021070500208024040e54001030000b11000464603445900842011490f0309848002c00c41704004515460072802820405400aa00c050110781008144000d00212030700c680182d402c001c0e514080580b8540c040d030042e40003600301240800070000c6912900c0d00e5942910400c070318001040c1d0008040c0e0041e43c014444005000c5185242a441102a141c01d20809040020840a5030400110036041140c0c800c0c0007034200400418414810b0260070380b010540c00c01030414078103081c1004544e000c0c100c000b51072804140070105000e2203084a5100401c1c841406510b04031031804010103491004000c1c1481400410003013001c08511181c07101c2e040d0040014480d42c40c01c050029221000700340003c0d6012401e4010f102d003a4000200140f5180b1085080f103211881c000203040d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207999919 1250 207998669 207998671
    0x18030109080a0503180706020a0b01080a0812250e040c0c0209060d08070f06050402030d020a05060103150219090821070308180105010603061404090b0115050405060f0a0314 76
    0x910724241480b0000c0468065000b454005d248218000680d0203a80701140c80c11341240d010030010303805020944140104540c585014140c2c0d42c2c040c2c100c040280c2c80304e9610307100700800007a00503403110001d031500d00c0c0040e80440c0c0625400c4003104100f04003000400c507915901c2000d10491900c0c40380301d0501d00906907550100d5004d003201a0582c1c0760010400020918001079880e0203040003068002803041e01074041481c8512000213090405005140c504a03100440702c0656001c0000d80b40032400004085044a601c00007240c500c0c2c1540100001034098030701e000c00b00100c010301400b403d40d00004c100082e1501c41d0202c2c0c0b51000c3c1900c294036140403101c0d40d5800414100120310101c1e11581200381d000c0310640185505e611001c840c9805c40b070090740410300095880c0d0060000c4510100d503400162f10444040c014100f4680350316066103418483c400c0c0209480890b00880e6028005450003044014221903c0364406001c5a41c5540700c4d42d01d080020b850f0008164032005c03045101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208001169 1250 207999919 207999923
    0x90501061d130b0310060e01060507080304060213050607120f05042102061b0c09071d10090801060e010e0c1912061503020c011512150e06070518030109 67
    0x18000100014040b0180c41801c54010494403a51901c0c0d03180c80400c43c92400082e94640000d10390318080703840c600c220060b0851070030091304110f80d00106441c441900d40254021700c0050b42c41241d060402c04988081d0f004580207903002c10f0320024009107103600704035080c050321101c1d0044201002195548140d002d00740200d1007442411012003100c00b8a41490303880540514504154655080105500054500c461360300c1600c0d210700382e04100054980103506030400074a600f00c030002218003402c000382400e00500c10003071200300e110307c1910044020320380403000300034264071903145440740b10782400f5441c421000038001c10b40d03a4a004044480400d80010800503030309a01808540b804040899030020a03120400410580030302d080e1340070b02d010383da1401070b0b644c17001500d0b5900707490340500e8003d01801c0c20002007244070b01001c0702300c00c15603000490459210048903400f0007000c8e403001d40089803107144100603401e50000c0c001d1a24030055900044c100c0c0d00c01c810182a18201400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208002419 1250 208001169 208001207
    0x90606050a0c05120c0730080d141504060f050a03080a0e030319030f0b13110c1c02070b0705030d05131b060e040b0603070e010519050409050106 64
    0x401c0620b48542000c5820520450a0352015010550f440485030481d20302c25102c0d4025907004c10401c2500405003941404c08070841400a1310341714503040c800c90158001e0000311001880381001003e83d404581c2d43d51915110a01509100b480100b608080c0c1030342c503000380d250007404128003008400803401c41e20b0090001807020b007190340f98103258006580420500030340b0080d41c030f0300e80c1c0c06201409081580003000035a090590030300605481c8d120342c65540c01c1c0e1a0000355600c0c0d407150008030000c05240c01000c00c44130084030008149105000401c0f0050260300c08045200d10000451102401c40f40e0841d892076403600e14100c114442d42400800c564400c0290707552078040c98101540c40790503100821210400ea8882800e00310740e18000c1c00b03001480c81c00a11207540c114407041880ca10554081018041c5000807500034880a80303c40180300803000d030722136980e12410441d4185034040310007044203038801801401c1da800500540c0140c40c10034002250306880b4822108d004407007013503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208003669 1250 208002419 208002427
    0x70503070e060f0114370c080309030417011401080d0c0b10030b07030f0c0903030c0204050a09080c010603021e01080708180d05040311030c031203090a0b150a09060605 74
    0x3c011038a14006a41410300c00808111081d500d103100207489440e0b01d00c0f0008810340304401c4030032400c100107802044551001100300c404580e00c00fa07501e58940c0d0200071595280c076401c0480d031450040354051000c0d1a5481280300c000036040d08203544160f031159038048541d0300ca45070141c40741c4c03071a00ea010003c0c804034800c2006c01c803401e090301d401800e44c200c5002c81303903180d480c2c941380058120754a01c04203440d9030141051407018841d00c1c8070300246152000d440c1d4259940145030180d19207001e40b046498601091601d82550300400410307900200d20360382e44024000541c049c0c0b18903c07040c2d100e00709601201c960180c840100c012050380503540c401c0707141e9846d07134142c0d8003000151105400008407018024804000c104036110010681c480c55201d40c511300d490b100a400c0800040e00a030400c42d0b0081d00c42e00d0004d89940400070f00d0850a8482d0340754045507140020649002d030039a0030745420b1140220085104041c076240544504400300c2e00c4140c0001982c080707115900c00500700700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208004919 1250 208003669 208003681
    0x1e12070203073809030316090f090f06120b07080106090b190314240303042907020a060c1a0708160c060903211104050103020c011517070503070e 64
    0x43c458285408600301d00140100d4161002415412901c10304964000000e0024204c0c1d121503508002c03900380b400303000d01420441180e01c02c1340c0034858904c0064485c0034a0480103280e40042021f4081e808e884004600c2c2d50801810701c000580d210310106240d030001040f094498808981660701b091111303460030070b80040e07004170b0910a5980d40304040d03560080c906150f03d00186d0301c1c040d1420352103401c03420084260102c0d0500c40502818070aa0040204000741c030201c510b01402001d14102c202c09210b007c05110200c0e02c18620003d41c0100142c001282080d0081c415000c0341c2d008031400c40c84140269130888080c9004c0d55000c4c081101c030800507100d08102c5242c0034043d011807600150402241d52050107440490a0880100c1c0352091000448942441060b10301244508180680c60f40760303102700c2d410f2242d0302485041540005030a002c400094000e458450140075034940b800d81d03680a01e040403814241c5c0644103000b00c0d0000261443d0014080b019500110070058907070b1541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208006169 1250 208004919 208004963
    0x30f0c0c0e040206271c1a040201200105010905070302070b040213180f02040b010215011202120607080601030608010903020c130b0a14130c020d03111e1207020307 72
    0xb80102c0c1e11442c104040d2402108041da0f418121803c64400000408400c0c02c02014915100d0202d01d41c02140f07810300f020844050002c241e00388440c0150180b0b80715400102c2d402c20022040e11030f00c42d24107108180790901540124100c404d001404c111035118484100e00b64418481c1c05400400c0d044081000343c917000c3e41c0120310b085c1c5107400181d26900d100d80a9035984e160f90080e22302000e1501000c042d4106405140c9558009201400000618103000b0801c48810f000b654140190046a50210748801721181c1001d41200304a4600d031420850080001d24103c0b2104c1c0000c0c101440080d12100500460614030b500d44c0180582c90101000c0c8071082016240c1100070b0740c0c807580550601d85450041d00302900074100c20a511140c1603044c40070101c92400c180004903d00b419104c002d903030110743c400114000c0d00d03000c10720b882100c2c44d4440c180240e9982003180440d040c1000d031084040001441100c420b6210860260344003a016038483c01600009807206464881004850b12a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208007419 1250 208006169 208006171
    0x4150e0301060e1614040f08030408060c040f0e220b061f210204050402210912270405070909050f0c0403030c05031c020309010b040b0f061605030a020a030f0c0c0e 72
    0x85e13100450b0401d50b56508410f02050075902400b85c5c1d400008052100d0302c410b000155101001f440614603143c6400b404407149501485100a10791014001c51407101c25411010660000b0f00d08000716807007107040065010030190341c0d8511030326801c10000c07060082142070024080c1561605008400b1a01c018044070300700460b9501d119500300004202945c8038030140201d800d610704a0005076010341c81d200c61800010b01310441c02d074810b500c80c4112100000c2200c0c01c42070040300e2800c0120b81c3c04040c0094a900b0110240d02900740000c00522961010104e4200c4d00203080500c1292940b40325200200003d40d04410300c076204100c140301182c01003174018401482134084034644807805001401071440c42d1010296590000b0501c2445642400780b907050801c201c1c0c0c2042488040f2001610300828030340114021440490782110312140400740d0080e880c0c1040c2541ea4404400200039211600c4810840c0414484412103520603c10800011041d600c40304112246080c880d0031703815024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208008669 1250 208007419 208007447
    0x1908070e310e0c0a080a0c060f03090203151b03060906010c0c090e0703020103060501030e0607140f16020414011a1308030c0115120206030c090604150e0301060e16 72
    0x108010107070456101034401e8a04006400d40a44a044411010854086001d600413001030340503c3c10f50303000c070b44004001412266241031030018400c0100054020780000000607525000342510844800c1c420006184200d90780f034080c19244072a006003081c40c0c0419503503d6000710381a000a00194080d80000503003e01a0041c0ca4180d0b90341c00c48103050b52031342c4100c071030311b90840142007085503094011003014100c00d081c28404101321030019691480000c000c4400c100c0820300c00c2450303011100484101702460410035699100c2c40301c21104a0766616002c9000713910f8000042042c1e0740143c8040d0690780c3c01c1c1100101d840f80240c211071513800c058902000d00c25424000110001c1c00c1008244802805001140c240200146011100c0f025440a00180c40c117086000050b958001144e80c0080c2880d111034032550084003140c640e0240c4e402010200420390481e81c1415003040c0c400d004090700707c0081c004a0388070b81e8020303980e10082e1004000c1078000b0380b400304064060140408621 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208009919 1250 208008669 208008739
    0x507030908070c08070e01060e21010c03141003020a0e0c04171006140d1b15110d030b1e0d0209070c03020f0d140c030702061908070e 59
    0x88541d15080e00325400490121200407101c0d034100200c8000780040310050003600c0c8622111342c90b1010103400400010100d52007079405001611184203840c250a0501c1d08140082219005044000c0d000b00413600c4405255100a000039208103039200241043daa409080c0780b00302032404200c0440000c0140c940c01d0589001d120200348490301c10400003c0e9842580100590304034220201c044800075001036420446940540091303480d10340c1001d01899100000307000c020989180e124804500350849088841200428400b441d4480018064031507034000382e0304400d0080b9425001ca4002e920420b400400c0010018120183c081e080818428043c1404a01483c2d550005150040496100e8081500141140c05065040269020b148400c100070001d81d81c1c800005414400141c030003d201020002d14a54402d00500c192054107601400f041d4803111a00382d070184040601d03030030100247d440780015451510500402d00d800d031010748880b1480424107038040d1480125203c2c03070080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208011169 1250 208009919 208009931
    0x1b06070c120c05041415042904020d0c0f11060405060105010302030405010b04060608090106050a12020607081309020403060e01050f0a05100e09010912090b18041d060403140715050703 81
    0x10b034135680911030a88009100031415464121500c58024040300c40f514026890701038000492055521100944401070594540100206d00010042e02c03642501d142002e0a00d01c1040f130403500600b0b000d280f0152900c1c0ea01040c1010b2480759610302d8203d1b0050700591003c80100301ca035000e5401980c010b030150700085031055402e070100d019120b040d44000b0008000030108125482c0a1003140d01505084070f15221144c645070304040c4000c00800702900c66000010030100300b05d84002142c6116414805082290f035454001b00001c7d00b15200640b050790a025041c1c000603011300c01c20b44904802543c3c8641c64807004c0c6000c0080000a107801c0140c04a200d021482c06002004140f0a0001c000003184916a518004041070b900d18000b001744140c1313110a003c0010f0800c103a0344006144500c980309200e050001030007912580c050a01c07030a643e610035000c84000462050311843c002d48131210301d80d0750804c00c0c40c080c3c429248080c0c031840304c00c038441c8822800b54001d1034000c91030340b4001c645 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208012419 1250 208011169 208011179
    0x31808070f0209010506090918010b03190204110a05030a0e010b040228050702030d0c030e090405010f0501080609030706020304020f0a0f03050f1c0c1703091b06070c120c 75
    0x154440d840588054401c480c0381800c52805500007405058181e58150415a01c176002c50360915028048000f403550744a100038a40000354040303210210001c0884043e074140d178483c3c100d21169000c00380d0240741010038182c2c0b0b0095400485465000d540d0f1102e02e5969000900c60082040c4880e091881d521540c625003141e445002910031307040c405409408040c60b2118000801d04440d0000c400d01c441440304001595000ca0a044184142c1c10080054000f070318040301d1100301c003402d10340c7c0710307c49106110034001d0541c031600c1c0d241e800100801c101c0c2d0b02c1d00807860380c84c01c040b034102d0000d9108103c5440080c80a8015503001032000c1c21382c170f4440b90854001509507089800c81950780780e203a07070100140f00c01004142c840500600c0941000c522800c0709060380d2541d00500c80501c954041c1100070071040300b0380300081d015981e020588904061444c244c0320310180404c049041c26000341c00d569443c0880c1121070683d4841801610346280403441600c42011590981e0855622640060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208013669 1250 208012419 208012433
    0x60a03030e2e030b04060f0503061b07080304030e010206090f03040501180506030114090705031b030712050f070908070e070e130e030901030501140a05210f060709050603160318 78
    0x80d410100f910003060b80c082d14010301045849560150078807a0a241c1c1c2040300392004075204d508a680b9440609409008292039040c52080d81c40c02404900d0020800c420300d50702020b44204548241d0940305c540e11402219603072034502140b0500a41c0040108024560140050070458410302007000c0d01c465450002a62582003640302042d08058451900e6031480c100c0b02c0940d006070a0f003007190031400c1210354610000d8400b0001c1040c1440000403c13038440c01039000d081c0740100c9203401d1000746040700c2e1620b9060750566141c40403480c4000045581d40d804114101034429a0040008981d02d140049407070f00214108039030001c07400e1503a0a0002ea00703002c1e0f01d5003001e03000000c582e1a00c02100040846605078450107210318403441812081c0c2d81c0e600c1d490201d1340c0440e62010480500080b20382d001441e56208001403080c22903d505a000118005214038a07944420150b00da49105003c0584800c60303020007182c0190300081c40e4540031f607204040c82c410112040804121a42c0c401e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208014919 1250 208013669 208013749
    0x190c141f0e0d0f06140c03040f080405030604060e060105030d0219061401061d0619210e0f0106050402120117070b0703110d0f0912020f040c05030708060a03030e 71
    0x500ca80440d20024001d04c24240207412a102451182aa00303241c4804001c20600025000402e4000c401d00c2d81e0b402d104100c02078402130f020080948000f800d0518001c0010103540a0780300d0321340120000000c0300d10b40406e090203216203c0c3c018103240440000381d6221004412000c65003180d40e500f14040c640d407800d400c503002c1c0030780e516501d45596541007006c0620301031034049881110200500100d25140400c42a85240c09007400c1090302e1413500000411500070441d141c1031498800d9038040404001107005580c04890000c005207070316a401c0c030090380b14000b4084030601d2a1801000880120705440007006444016100b425845d681200540c2d48903082c140c0000300d207201c0e4407405031800c0c0a18240041281070440c00750030b0155001d00850301520803282d000c480c103402c02042d03448d02c40325400054002001000305d0403c00c14003901ca40c0055842c20002211040040c031a41011480c4000b5030350140c0b6552018ac035248100305039815550103c240030100119004000c5071208440c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208016169 1250 208014919 208014923
    0x18180b0c0a020f010605010e0907110303190f050403050304170403021302030403170603100f0905030d02040f0f0b12040503120709150302030408040e04020111190c141f0e0d 76
    0x30740d80e152100e03030003854509002d11100c19a49008020081a030f013103001d10407500700070380340d4400d25929068107840c1c0b01824941c045280c0400010810030754603001540555078605c41c8104001c1030201d4000045a20460f0f005010550400204010401580e032402c0707030300704064042e4900f40e16903021912580041141915464010041c03004040c0c01840c0c0301c511000c0c1c604040300c2850030100083d62040103184081c0d20716581d2403000050042504000d4509401108403036861840c01c442c135000b58050b1052150840400310046981c0621400704000c03281040b100a003000007081d00c59000340c601800440c0c142c401041415408800c0d0125244684000c2e00c0340d210a038079006070780021107004801d460805204004100002d03000c2c005540039682d41c1c001300380c11070359a4401a50080e0f101c06c012845407140f18401801e0709170317505e1001f28151051903c51041d60b5600b4a044040c0c00d512051948440e84881c610396000700d0030404007030803006151200d29451000c0105080b03030002901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208017419 1250 208016169 208016191
    0x70f0305070b18060403030b031501031406090307050a020118030b0f010f080a030815010203090307090b0f010509061c020d06090f05070c0c0e0907030c082518180b 72
    0x6a070a00c5104200540d000c070310001040d1101100707180b41501e0b00c400400040070700da80c0d010340391900c0e00c0400c041d04012000c8441c08006507101c0c00c1c0f038107503605040c090f03241074400e40300040d000306004415140c105074480c0042100442c1b1741d0040d180c10b003402c0c8070030242c1c0416160000211b039003040c007540584004803800c03060b9414110018405440f0b234100d0382555000e00c411400090740601030982c0020140918441407401c42c0c0100d0440c03041c1c0903010b038580315407180403400042a074070000c4101800c4881043c0000341c10300668950207181701c0160700080a000018000082c83e200b42c8110740801c0c401441e15041e855100112599604004001c0b03565408503103640c227942c03107246d40100a83c20140e0b058102590b481c600208140101168070f42c074040400c030002e404001020255601070f4900b8242e036195810b02c1c0d9614090481080f420a500304000701c0c03c03981802c5036041c1c07060381800c8400074101c40303c07210180c55a40103400c1e25644810004c0d000c10361110343c83c0c1c010b454141c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208018669 1250 208017419 208017427
    0x30a0f08090607150b03060105011205040606080a200907050a031805120d060902030c19030e06130318032013090501020a1d0d150b210d02030408060a11070f0305 71
    0xc40c0031600d50074000c078002e5103c3c600500207a03030814854241850000bd0105007581c851030702c00c0141400341d1103420b05200f022207000c01c000d008204440707118280d200710340010ba006010810a101d003036601801168003007042e10f00e028817075000200b610120311401d610703803074685d561503140a81c444405003c40f1800701e00714086120341d0140c4401841c101d0801e5007541081218010f5a107c1d4000134041e01c2c1805807075180250281e0090051054400140e50b05441d02c0c22111941403d01c0b43c2c21070020302185001541441c030358411a0980c0d0300700d660b44019400d401c900c0800c0000c1c0800c0b2540c00f114204000014034511700400e040184504000350710380510460181841a00c0410410300c2401d03134140e2031254031412410002541c001d495074849121055800005115903c100c5811441425500d0344000745a024402d83c0110482200e580f80640c6a0403600e0b405a40031740c9440340c21401c080380c201203007900b00c507020440940d5418541078099942045051140300c0c105c0200e28041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208019919 1250 208018669 208018703
    0x4021314040803070f020c03280b090105011706151c0803010f0e090d080601030507030212270312131b12060c0c0210080c0405040f09050c0d02030a0f08090607 70
    0x201703e10f4202c18140000d040803400500080e03200c81c045484002e60030714032481c2e9900d90700341e1502c0a000940203107010809041000506018103802d0107511400e06a0f0348095140c9040020018401d4180c6c992541d03640b00d440040104540428410140c540341182c4510302013a1480d00441c0201102503d5030303801440c2444001c4007850080c03040c0d0081e003204810010b100d80201380540d20420910740003d55680320320303041c0e009009181e090141040701c2420441d0300342c5404000608004082700c500761a4441000d40d69807803051460218506885034080340740881e550581c1d00d011445009400024030541601d0428510707194414070306440c8200500341403001034401c01c101d103101460f0a0520b4800c64010034060f02812025404000442c0700188040c0040000c2d034025220003002130102039600c0400388064585500140c079603014140380002e442c40c152103100780e910340c0580604071000140e00d42544101c07091806880c000c004104540355030b5901001892035078403440080003100751340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208021169 1250 208019919 208019927
    0x106080d0512090a0302030301030816120e0117011202010509060909100303091d070809011b05180f0a1205030412080c150114040207020d0b04080415050901080402131404080307 78
    0xf802c03207000754110181380300c0031030381c01b008480c156a0003205a03681c0d105000f048141c000c40120003d04601021f041c0008225031000f20018a04400d981c1c1c499082506800000c28103800e200703424440303280d1508100194040d5010f491800700040001f0b00303080400000c6045004112000c00c025014500b0500070144c00c188018090040e40d58502500c5840e006000401c540160102040c13090070400607103281001d4214517101c0040385d500c02c01d1400000030144c529000002d81c0601611a0b81100b80b03281807508140b420300d00c005261001032071810034906404460b076881a12180001c02000c1019140ca5082039061407041d070200e41e42c1d01ca2150f00d6030401011084240c3c403035154600401c0b180c0e150141c2d001e010281101c3c0141eaa030170300d10002e00801a5050000d0030340c281c52040209000d1500050002c50746c02d98100456400b03400001c903030520038a14000d01081803240401c000d42044600e0070041603464900155203079440f902d0400c0c4800c100d800f00c1e0810800401c026600d540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208022419 1250 208021169 208021171
    0x2010207080102090907030e0c1e0a050117010b03040309030803090d0305060904020901030803060303040306110414030a0302071e1809110f030a0f11090c07031d011b050106080d0512 80
    0x8070400841c100007034a00080c20300035016003854101501d4180c0c80d8242d400c24081c07e2505607008200010303407841940f042d000c1c000049203181c40385e0a0101c00050550042260303034400c0328080c5000c5141ea003044039401d038130740010f04260f0800c40c005001000081c40c5100540c00f5000c80c200a100040c0303c03041c01015035400606140c01040c0b0002403000507110722502d40d040d0f0742e101a17240d869130707035032400b082c81d5005940c806408503081405007000c2c86c003e034000b402660b00c6003000034071314840941410f907144090f01d00100181c2c06030800f0401008140c50500d00e602081a402c201780f035982100ea400400e01465498032265506000e41c20400f03075544034038011500f602c8041c81c600ca02c0300000d484448124000e0300700034032400300c242008041030002640e110020814040f60900ca0f0854003a504540c4080380820444941c0040189001c21604440c0d1816510081c1c008400080288401754000003240c40390f41319840499400d10074828403514220765038a517030b2111644620941c4802e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208023669 1250 208022419 208022429
    0x60b04030209150f130902030705040c080f0c1303110414070e0108180f0a0501060801050613020a020106091a0429061e040e0103030206090c060a0c060906090f02010207 74
    0x4080108000580b50040c6603684000303580d40d010b18020404003c2461101190f411a0b4402e80f1507030148040880d9900400e4050f0003a400c8810941c0c4800c103100440e90340104007000300344142c00050496800b038088580c480c1d12000014140180e5040340380741907186800444440d01c66000200490501c0e2042c040d88051042c030102c0603042c003034000740182240220b8130b4104010180001c000c5420b883d010391020190100326601140f4500d141a103401d00182d04991075420704500080b0848140140f9000d1000200944804450080b800009601c114101403d40d503c4500001d565025880340c1405150012441e818a2407100100b10403036022844245100813071040d60a910000d403142894503002c141c41c02e0786d40d004000000b14011030101d00344001194000750108121010700640781c1264440e40031100b15440f582e480741e85407000305a00a8012405001c41400d103885503921501c2c040c05403c1c0000c0c040304503150b59040c0e40d00ca0000703440c0400400480801c40d6810000707080141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208024919 1250 208023669 208023689
    0x27041101120c12110f07050102030103050607020102071a06030a140105070e01020a2312030103060b0a15080a0213080610030209011a04051003020c030a090f0506091f050c0a03050c0106 81
    0x42e07007104040c0c50301201a503100c034010b0b0f8410120007861411380480b540d48801c8010291120814a0594080d52090008880d680158000f003101e0500500948840d81d1748101c8d010041d800040348881181c0e0300905c903991500c5106e000402180c080e40c0d50b50b40d1844560004501407a0100c005000e14040595090455101506a0011645226030000304a0010180500400d100c4480c54602171103420f500074100c0000000108100181e44515584070050340c05502a60342c88002e150b060007a0301665010400b0b180002d40a02c850f90b00401c075001c400040031a44503100d2000d1481d0410440c0c0d113600380c00c2004002d005502d0040e103098010075003c1400c100c2108041804904c40c0a14440c2c180104030f0103c000a00364020703019540108500d0089035201d580c0494001c11200e80c42c401e650300e07099a5080815a0b040c5a0100c50203c90701401e1600007960310911040700b092030034112030400000380000340c0740f00e90030702c81440001d000c1d54440c1d803901c0021880d07130f0271070f581c0d58850300d07840c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208026169 1250 208024919 208024931
    0x60912020d08181b040e1203040606091416090f0f050915031002071703040303050604141e04020d0f031107090603020d0f060b0411070302150601020c2704110112 71
    0x32100158019400c038400c5a1210413181c80400700b40604440501942070b4050096800780050802c03001c0c600c102e006200c1801281e41c0c070040c2d002203807020a28182904450340010300d183c2e442c0300600001c1d41c00c40c5031031030350503039070fa02c4180300e03161103411000140503a200c0812691a250540540080307100400b4030206100c0000281d440084c5440c0e06119038000c02c0c04014800d0086084003040c560b0010266a4030305460300400034001200c2c214880c0345821b02540c070205036140003030b100d401c083d816012148130110101800120041c0100d0703120707120154040c0004c20950394030145500ca6154a081880422000c0b0300385031441d000764a50f1803401e5000c0000d80e480a1680c682c01d81c0101100900b03003528180f10b00507241a403a056046800c0c1001144403140c004005c118050095094940c0010001901200740c40207551550041c1d10900c090403817450a6050500728000b04080050282d00241e070a21249030221003c0d2030240000c41030100799600080e880e1406000d5a00c10084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208027419 1250 208026169 208026211
    0x203061e1602151306050106030f0c0207080304060e0a1814010e0601120f1401060207210b060405072003130e0601080403050a050708120709061803020409060912020d08 74
    0x2d20b0750142c002001600c4440080341212407010480318046400001c00c6c0507640e16864060083c01d4084c0d07601c09914580210011076510101e1070360241d0758040d02035494a0b2401c402101c400011044c1540d10074403520002403070103181c0070710344a800d01d40e070400b04002540060600584005a124400c100700e000104800d5a0384a40c031240414101040092003441220880e002085c1c42d428004810300006c001180c16600000c6410454086500e001a4100004151080c2c030880c103000804200482012504610f016081607034849203c1c0380262581700c1c5e08071140c01000301c44c02031462517000060041104240f1022540c050420244013922600340000001c000d410002e1020b0f0400201280072a0301070b10078801c651070580c2000b80340352074181c0fa0b041c034a007007101500c0510105880b4080052041c0c040d0840f400c80e1103504140d501c20710326540a2002030051510106d46180d96080c00200060000400400f00c2209074020002c00c1c239103a0000d0502c1d9000b811405000075070103001c2070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208028669 1250 208027419 208027423
    0x1206010b0708070b0405100e0c01091208090604030303050f060d030c06050402030c0d031101050601090f17030d0f1b03110702121603050f060a060b0d05130203061e1602 74
    0x411250401941a941c01e214100a40c25010700304006000030030480c00d10080c0b000020760102420034200c0100203200360b0a1155985100c03612180380490400c3c801000f2010600e07032502291030080010303500d0b280201d00000c01c80d50250700120b0200b40c4c4ca409004617140248c1205911000c291107800041c1820348001e00070b0104040000c04050b1984001011503c040c425052024405070861413200103a180c080d0407001c0c801501e01c425031802c00014495841034103254200d034103804070000c0990400351104000c4810b6003854040d403104002d0500c50844a1040004403554180c0c0052026070300c4c80460b150204802c0102c040500b00f041c610301c034100640480e400151304036080f1032011211003145050480780440d80351407400c210f00001c10b001d00401c0580200101c1c4043e50a65540c1001d1392040701c849003e1860b04410500403080d0031402c981c441e94010451170b07600b0034403480030750009280080c1260284160418400d9203611544103040150b04445604c00c50303003840100c0c02000f5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208029919 1250 208028669 208028671
    0x3030f030203150d02191d0a06050a03021003020c030a0e0112050c030a1d03070302070f0f0b19051b0f0106050d0f06020a18091b0f02120306040f09060507030b1206 72
    0x3e100713140c0b1036a250300315569081d000c8400884441e880505c560790380b251521504400c90040f00140e2800b0005500c990342d84142020307108004c1400c0300a60030341c4c0a104920307a1983e040010300d5401c2010000040d001c001410356841d032a0340c0c5540c5000e5181c001040c2c001070721030340400282000706005520f845a803c0e6a805408600d0003c0c685501c01c1501e031450042c0000da90300c034000020300d2400d140c2c0c0410860300b541c0c2140d03810f41c00e441e034461480b400c0465510824115400c180a00000c1c074884101000e90400c082c41c0c03490030031480034034042010780c0203025004107602ca5240245d400e0303000e0050328001d0034203c400350522200d03502c0f01000e882d2060001051039500160960000340038240c080a040500c83c540500c96407140100c3d8010804904441c205001900f115885036100b20700c204024906076000c0c1c03086d0403500c2c0724440b540e000500032681c810f8803011204c2844030306215014855000f01000306113424100d90103002c03100540d940d54045e140c801d01c5520841c400203541 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208031169 1250 208029919 208029961
    0x90e06060f1801090603060c09060c0305090406180c03050709060207120507031a041e1509150c0305102c07030f02360102150402040f05090703030f030203 68
    0x34031484500380041c031007a55400750b07010003141120010030f562103903038011011380c0d10615040004443c507100590703801c0200d10400e000a2041c40c015800244035801501c00c00202410204038180c5480003181d00e8a4024140303c0e00942d00d0560100040c0c2c54010b4030342001c02410040c1481341005070081d01c0b41030500440c82081e6078004d0307401c10850108000c0c0011078004040303001540014103500e0030b9910680307040d6210005200e041540d2220000c0304174803e0b0348590007903155849001d490024058040c02076070b8a201c078441104c5008850f02558002020b42d41d00020103142c9903110b5410030000781c0010208640c40c1e5405008031910000700000300b18442c9020b0f1250b0f40e03100b0304401810340c4c94114401540007040144c0010f0054251028000a04581464100c4000306c640502d05c5a90f00c3d07140180e1100300721602c1405810340c0c058005002810214080d44071584a01c25120261103004290340008010020f0550011010310596200c6c45e0a5140d400e040031640912a801095 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208032419 1250 208031169 208031179
    0x6060c0212030c01051602060f13061d12121e010e0c09040609050a0b0d110411070212060403020d0311030105120c1005090a1221090e0c0310090e0606 66
    0xd00900c481c10001d640814010000a02161a005080403010150380c503403d4094415200401c410700d0b11100068424600d0490440039901c06465082c0501240351018525010403048412454070522070b408180014020417942c50001240e1840c5810008042e82440e2824500300310045451000b21411210b404020f0440c0c0c2d21580c00d14405032081480d990392151900b01c000561065641220b4407410381302c0d804000307003d0340e902480462014060000d190054800280150785040c1d070140c9280d00c1100d041504007186039001c100d640300580c0b8241301c01c1e80100100701c10160304007c0340d80100e807107180c04d12804103400c1c07103540e0704c3c003060080900c00d01e02c07590359a20443c1c003004a43c140050040c00e0200703100192101a10b01e40c001c0b0002c034010380c1c40420115803000d01c000345403003295211403003c0c18010055100700070f8000340092407080100400e0b001650200d8001d07030b0b0740524004074545a032428226096410f51169070301c13000139141881d050804d0700701d001c04d1140d0b0180c1d0540d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208033669 1250 208032419 208032439
    0xf0105090d0302130b130608070206093040090902060c06040b0609090a0f0605040206070f0302070504150503061501020f070e010302030c03010207021c0203031306080702060a06060c02 81
    0x403442e400c40c0290700401c3c1d4618011801c03050346c0310f202c81c030201100c0460b11030910399114000202e0f00e03023200302d03000f030a941e0007070510140382c1c1ea0000304102007213046000c42c07600c80f035034038550401c692009d0000c08a2040501c0c00804541d801c50b00c0c200300038848401780c903030034002510410100101d8800d0514495580d0703844419134031103804480c41a411001a81c01c00e02e42490950000d10b0244c0b20940520b140d500020342c640800180c0000c03180d0001c445030400c0001d90780710340103000000e0080360003100920205c00050000e00c10000300350302c03d4001d004c240d4100014041121032048643d8540c001c0d0310300800041c1c0b40400c8054102c10419800910711141c0d20040c1e14010b5a14801a240d00c180100000d020800e607017040d050301c0c4210140c600040c20b2400b05400d0303006080010b5880017040c80b8144400e411401002c005c14409000e4038100318903200311405143c00c07a4003020111f1004000c20002c668103010700d545c0003c00c45400c22030b290a01c1e00041442a0000000f0302610401c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208034919 1250 208033669 208033687
    0x204032102150403021b120a1401150e04060b060906030402010507050a151d0d0e010c03020705061606050a09080d020708040801090c06020d030c05030c160c170f0105090d0302 77
    0x2c4400d41c40e0420a08040009040c146030007980e80c441d8507402005410601c0b000811490059403c4220b10003203402021625000c0e1148032904000d1002c0c00e0b00c070b641e500d001954190124104030010202d810300d005452070141800343c143c4071480103245c0b09050822420140f81e50340c030300303494001c1c1e0286081a00c030100c0386001d03132a01483c1742d4003603c1e0280300c4005c0c5510300c03010707009041101e140c00404418400d0750104143d40c0d003119140c5001207088050030169a512071164482d955000e03104990000707981700c000c12491f074800035600b07002d00350003030210b4140106402955000107412a04002040b0701c0d0302d5a11047c0655585081e82e550001030010078403030040305030b80203042803400801480e1640d00d4070060007405d602c00d01c2c0260141c2a402139401c1e01902c1040c06a19203604c0311842c1d40ea80c1040000c1d81c2e441540b2241d100c0d8240e582c06804907980106440c040c0c000e9003448805005601b504d00d02d80014800000a140c0c100700400800540215425801c40042d080c050385034401c80c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208036169 1250 208034919 208034923
    0x120a021b0f1302040513090206180105190518100807030507051209010203061930060e01060801060909050c151e0a17010b16050106050a06090e09010204032102 70
    0x200c41e40c0e0310800d01200c1844480480d0700600c1101e000f103992000c5190178244203010b4030003106000c0e40c885010b200740400f08048816817011703d0300500d01545407824018400c0998501908480d00007400840c01c800100d48090030500408021070300c01d050b10452032001801050020003010402d40c440e40499201c0c0e00940550300ba004506000c000740e0319001034268000c1d081258040d2142c58182450740c400d03600e101402c425a0404084808862640d13480400c901d55507034406c2031014111400702000c91a80c2c884c04c030aa000810020802510386628142940c0305030304058aa140350540d0000015400904410000800d940d14022001e20244456150040381030700303115090040014011880100018201c03d4996182c001c04d00c80f080400340007041c400d01803070700c241c2e07800c0001100d465081d80c480c0c11103070b03c110004110f840e02c4902081c500c1e0f40369407001d408115052030a10200011392042580464403a00850400e850360301c40c080c006030307508502045003402d010018600f07031003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208037419 1250 208036169 208036189
    0x4210905120c0915030631050a0c05031605010c080906120106080c04030206030105010305090a1e03140c061b04080723030111030a020a09050315040302120a021b 71
    0x8054107001d01da9410059114201c00120030300c14440f2200240113034142c021441d61a15000c0c0081c8483d6460050765000d02c1c001542075100d02200c03c442038101806503209072a0284108040d0074032540500c0e106400d2211074001511a030444100340a4800c42c1e58044006c8680034030788007200d040a420000740b01e21031444204e802c6400016421808c183e40023095040300c000350b0b22160142d84110888109000e5800025808a070030001040258460f400c0250080c20340e0081c0c8181e000f09595400d603501c5003080f0340400090b4a00314805050b01f2511325449104007248941c904900811716585555004102c402240001e406004d140d16082080d1009000e00704100d0350150385070072501c00d0a41724800e582181e044142c41991650606010700c0c440a005000e00c2030864440c44800f401030341000d4041c800b0130100600009483d0307010021040d02d0042d4019104540c20a814002c0c28103051803115a081a020003507030850503070014882081d01d0a8400401510303810500250900311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208038669 1250 208037419 208037429
    0x6010503221403041a0403050c010509040f05070f180f1e08011107060c0507030c141204140a210813090f0c1b020a0306051806040804140603042109 65
    0x491442102c0d244003000005005a950000c004040450703160091220362082d400001e1030341d0054803a10426502910141101c440700400100394004002d4954085030411944c080000c0c0003aa01405a40d030000650b0203007144c040a20404181400d44003a00c0780c83c28410b902e40d080c4210029864100c00d00c01c1c0c00060f010035002802584001e900c010310580080d00259495494944214070680c01a0111044113038561255404000f00351100001104202a111000d025120304080c0300b036000c800400240c044022100d08201094003807100d26089038003d03800b00790681408140451004889244099000c0b20705aa40c250802c01601880c2e600e0b440071200070f0030060944080481034000e40c14031100742e03840d90f400c0c2d0214840c1c00c0c7c801c1d60303000c401b9400c500030030400c0c808038015400c61503010306c508901041c5003200d0340890345881030440e000e45100700d01040c18000c6800c080310141084008a6201e0f0440c2050b40760251001d007007103140c224000c040110f160282c1c0c00b40e00448003e01d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208039919 1250 208038669 208038683
    0x161101201c05130f0302090601080723040b070303020403061d030d09020402040e0108030d0c0816030e190308010f081c05031f06050c0f0133050d0606090f050601050322 74
    0xa5078079604c2c203098070701d140000c900c100c5a10001803047d501c20304400e44600c2c81690ba1508644142d03a4084024080d003c41c201e4203c2d0800001c038040708c0390402024010b21030740d001070b0341b03a145040100413141501614080d01c5980c0704090f03010500081661103850829500152080751440028020710490b0f009514514500d0000240080080301420103000f20700340910250020060856143d90100d030914440280c055040d6012880790380220300300000d640403031350160240036141c0b078100c2070080100c00003404400107110300107002c4481001403a5400040c8901d18141d4103181c01d0b00d0b07001c0044030401c68003000058082603550b198481c0c0c4820108601100303521110014081d600a180d2a1428811020918106001441042c0c03000d920310441c0c50480464900c090300c8484001c0300d03000c0c8400150404500d5031b4402004840c4c0500c100c0c030000361186440441c5081e155000100540c19141a0400080c4c0e6005001ca03a4003008548202000442060307030020a03540d0010041c00031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208041169 1250 208039919 208039957
    0x9160512120a1119110904051c0c1e1208040f020d1b0b0904150b030612030c1015060c020a1401020a08120105090c03010b04030611161101201c05 64
    0x481e103200b440c0d03100303000e521600300f42030483e8107000031b01c00305940090980d40003d0008020702503811100450682c02d180c1103800e80e14507114040701868007030081d0282c031030100b11030042084400c1030f034084440c6414040f06514051f1a2140c9a10b14104c2c040e0147c2680212003080000c50702415000c41081c01c1d9415205494030307000003142c0c0100000314003c13803500300401c05440715202d07888202c480c10301010713107140c2d5410f0500201c1d400ca1030408400d40700a00020403011824494184040703506440013034400e074801c103480001002c990213001071240380080f134405030716014002c0c0161100350242603030808641004030725190f90b881000e001d04101140210303070102e445280e94101d42044800009035141d0605080207480300b0320514803030f0b0108100410010358560441c240701004000064108085034a100301c3d4450014021241800e54807108902d644c0c005114030440707540484400c80b030115800c4602d03555443c51400450010303c42a840300c50364800ca08441002031002014140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208042419 1250 208041169 208041193
    0x2060403021804110f060322021c03180b0318030409060f05030d1b0b04021f021f0203190b03030424080a0513030f120509160512120a11 60
    0x25280060303c085569141041100d4900d2030031092022640c00c3c01409036185440d1032034103611464040b020880550111510381000d80e4840309a21000100c040502181c81094640140001000303041c0c90740d07603145013000707000711088042034035400b40194040007191030b010599946140100d41c80321400508205022030a5000926440210b1b00c040d0100c420000c0d540038180e0b03842d005400d042d4581c120050707585000c00d51103520144c210b40054480c401c80310180c0b28000040380d843c500c2c100540c0c0520541070703103900b0380c1c00c1041011503540c90460a41c2008441c51140d95610307100e00003a02e49030000410035560500485e0020000181d070168210340303040c2058410400c0403542004a40080b000602000301c40c040e1900c03038110008041e0383c80c0050f58090711100c07031444900d02001951250800700d01c486210305400303100c5070b90003800c41500307280078141c98145642045008101c0880400c1c00c00304001100d03480d40580d4100706071900e5141e00226592071000b180484548165004500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208043669 1250 208042419 208042459
    0x151404090204050a1406030c030a0204031a04030206090109080d020d181109010608043c142503080a11010603031205131a060105091305010f0f0308040b070206040302 73
    0x1181d2040c1c0313a03030800070358900340c0c8042d1048a04009421050400009440ca8040300c0256400042c12400500f060348984400380b881001e55030a50031042880c00b80010b05404108080c2d010107440b00a00400ca415a01c9003214002c3d074502450254003c56200082c1036235400841c040700010300101040c2c941401c0c100e4404450a01c428091200c039800450114820081d452081b90003c41040050414a22080d001c0100f8012100404280700011448030980d000708940140615003807054010400303006403c3c03030391040f0000742a00c1452052811130445260341c07002c49420070301ca0364a0f00c001c00e10580d4910314100c4103420702e520b80340d008020160020140e01542c0c1c072540d4204400e03540c440100456440d017031070241c964800ca0f416514481d0004c00d24a07030014061500170b06007429400411003451a90000030083c5032103400501c0b1002c0401c011400070803035500701c2d01c0c800d1300c1c0d5100e440d07540c49503000710303d5219000581c09095450340380844001316406450701c0390002102c6d50703c41c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208044919 1250 208043669 208043677
    0x1081e19050f0c090f0d050a0b04170a02060a1d1203090d03021813060504060e04111c141608030a020607030204230f0d080417161514040902 62
    0x20004030724110108a004040584440c420507508807080d181c40104030800aa07908121000d961264070103411400080c000e10807610b4043c0300b40b5000786181840c4c07400c0b110f002100c9210018107241800110790f196400610070740c01040741000041c50548456442d42c0780c01c1a0046d080d214800c244d01d01c100c1c22201070040d07229100c9102a103010100d0000e04a09030b100d0140001c3e85800440c0f20350710140350060203101600c09544000600740e0750f5002103010750b202e0398400704040074080100024031900c0c10800c140c5160441e0135014000d0310200e0800410742105001d080302043c524205004030041100014140f4829070381c0030916034401200717690307501003490400140a00c40c04100c240d07000e0300a8400782c9800291710740e03000d404441c0c80004107a0410405501100390400103040c4c1c0c640100d05c030f510034012002d8596807424803510010003410304011000350350107018440507800340340b00e065003640c80003002450f10405054040364428401102449402d03800900090503041541c014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208046169 1250 208044919 208044961
    0x30518010c12060f0f0302041e060f050108100b1204060b220b0d0210030c0219031e0801030b0a02090d02090907180504080301050609060d141e07020c01081e 69
    0xa100c2c00f40c881c5a0951320720801d10600782083d0078100305000500e0203401c0500e00d07802036901080003c4072011301a06807041c60380025002d42c0c48a10038000c5580c82030711568800c0f41660510f074014039050800304544501045202140748000c007050401c081608005c1a50030b00802c503400004000c85d02d0030f0360300460b4800780032a520701103610300a130501000c40703881d0a40003441011380c81d80058080d0098044002d01c801140150180c00240c408030859444d0598004d1365001c4045800070b07002d0b13100d004a0303100c850510131100010800200540c45d0340c1d81c001e2400d03c0140e01c2d0081c4401140340e814030014002c3d400244d54040009259000072043e08849200781c0000c0c4a42d02c10340c007441100d20617103018084100c100018001406c1801c010b2803040c01c043c041910745100241e040007154481110b81210916001c03d00c40700c00442005480c24003200351010281d8282408080e555019401e083da0500c080b000019a01d2040704100c2d144014080700d80021501e0400990803c00c00140c040e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208047419 1250 208046169 208046171
    0x51c0c0306050c04050f0405040f120e130c0e011b0f0f230606060f070b1e01060e0103050601050412061d0f1e0327061c021e09010906030518010c12 65
    0x4440e000749014080d1500441c0c002b0f00c001d01900a540301c43d00c20b88a0001d0000c2403045031f06804643d40ca075008844c0f02d00034200e400103410181542e006010048660405041080341000b0900c581e0003900c01c040b8960340420503407c40c20b10783c074010b4000c144111b405090f0458520100e54802d203092012002c0c0645041a207415565100800c222401101030362041c080c1d0502c400000a4200110550010703603246801002285000c02c066111400341c101c031000a0078100b03e4415543c241c020641c02030303802d00b899400c0c1810414505840181040060652605c0d00442941039400d260155040284402070b91000500000c082e6030b900310003805c90381042020f440016480380c000c001d80f50000759001ea060f4200c4001503016882015504c80f00703130701000c200311913182c2d080440741d01541d481e001100540c5820003025040400c00d881d0f60313617500f6800c04000d4054641c0e8041c4c1000700b0f0741c1c824200040e02e42c42d440b2204842c0d030301e103a40e200d501d580381c003222801240d00b003008008295602c0134 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208048669 1250 208047419 208047439
    0xa150f08010b0a091a0f04060503011107120f2a1502040f050405010b03060d2f13050412141e0702091005060715090c06200304051c0c0306050c0405 65
    0x1481c011964807003010381d0291131179a0203c01d40d00d0101c40315002e0042c01080421003e0316030001a00b110784c40d1481052040d0000740341010040c4041007084507125030300b420b4103a45422600a42007003004c0003821599a800d0800e030403215120041752200320b402410500e50108110f407010002e40c8070340100416030407018030000f550301e81070203141d050340c0f0116089030443e240c000510419000104040790221650403001841c9a01038120308900d40c40450400b0f5044d00c2c16040c040c1c5d46402800003144142010204070115a0040000015000c4c41c80c011102e90141021051503001d00d29030080e81400040580c4040822540644407180c02103a0b0401552201c2003d4039400382103114050300050306103c0600800e090f4000c80d0203006c1401c10200b00d000c03140d80c0f510340d00031464100c3c9000c03030002103c1c050442403840070341400c095020015468103050070005003a15074042d0960110440b840840c1007040444030b0030704021580401d00f8450b0b030600f280420752035003080c01241d0140400e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208049919 1250 208048669 208048679
    0x8180402030c04030204051012121716080c0702030a0b07030c02030c0706030b060904090f06050a020403020109053001091203180308220f06060e010e0a150f08010b0a 73
    0x210807a800b44140e00b8650f4502440c60b07091002074900288030090300c00c40c0040c000740b2003c2c2c5072002d03a002e0b41f1800542154000e82d04018100c0000501025051203401041140d91505019031301d034200482d00340711f80660354100c40c0c4e122903c26500000e4150041800c55000c0001c2658440c2c00b841c01900c0a11400800b010200d07a80e014181c00e09545903c1510100519406617211410300c001c090004c80c078000b08a400b04007a5880b01c1009c640316421000d40c601446035030311840b60807044030341081d8985071030760700002c0029005000d458401c0c0d11141003001038080d210100603102c414410318090310000000c145000303114a000c2031b590b00070b40100d4980c80030b00c40e1044400001e4076102c04e001125050b1000c94582000401c0c90305015100352814403203040080f0042c1d00c29200d00000f1440c050580b038607905903000da50101c2d28068069005001c0c1a43c2403d141b075111a10703040000c0c0c0381e8040082c0035000740c41036101d03850529120801148241040d0005050800305075410043c07141d850f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208051169 1250 208049919 208049921
    0x32c060f07060e0f06071209020402120a060501080c0702120109020901150f051c05090109022206230909070f030803011e08031803010b040c0c050607230304050a0c03081804 76
    0x610313104200e070300302c000015081801030044581303d502c0c0c010300150084081d4003040c12640043c06401b0750f85195401c000300c8481500540f40904420318240c07540781003a400e0340000b0300038114001e01c240700b011501616054250301192001d40c00400d41c0e00f45507510320b4242e10a035103440303912002848081440c0c0c281ea0150040382d090307075101b800720300b00d02014842c038800400015280b021155220310010f00981d544151091106009503400c3c007480c000d0503a280e048030b00d1a441550009051074440c12090352041c0c0d0084860000d030b41103401680c408140c1802c000e8140c1000071000026500442030200d00070165060f9034030b048000e081c40c040081d001412811612401070154001c01286400000c2c040007841200c6015001044051a850019040e1090440300a00258980c0b000f031090180420038103801008074248101d130304140c5072080e45007a41e24000e402407444008042002c1082c20407494a6894100c54403100050326031500c8011923005030050700d0704000c1c9003440364292403d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208052419 1250 208051169 208051183
    0x2a010c0203030f0f0921070b0f04030201030c0e0a030309050a141c02180c0d05090609060610050c0105090604061103011a031b18010908010b091f170a0204050a050103032c060f07060e 80
    0x89e0f400c0c01420103203950300450180c0340c88907a0a0030000b41a003d46519141c3e0440c11016510035114405180c5c142028008800d020f40d11030708440c40e600340c658420340c461103c40b09500032104035060300342c1b00c94008181c003a04039aa030385130124026010403050254880142004050b030303403400d00030b903110f002c030f4140d41d90025207103041507420174800301314549004800039000c2e4031103080c214104a41c000d0759a00b1207408407103103c843e410810400c004c1001d50306c1501e0340002020002415941010407aa50071140c1c2e103e00048004000041000c04200c014141d0020b880b150b0441c0d034134000c451945035540000254980450002040072441d000180522182c0f2003020740301074142d940d20000c0588090072401036000301800014040381d0390030b070000348900312180a0b0003000d4000c0144144000c4503001840311102500c0c100c01840042d90080ca210140c0d00400c180310400110301502d0025107080e81072203a40200d001607003035400524070f0007429025024070000c001c00f001c04194140c40e552 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208053669 1250 208052419 208052437
    0x50114010512150f130501030c0b031605070302030702060a0c11041116020a050907020715031a130605060a0909050c07021f0309052a010c0203030f0f0921070b 70
    0x2c141400648101030056000c411141d0040c4400e000030f40340d0000c1800b4400c0d00303240d00441511000140280400400301c00300504021441516500e007036189074401e158600594010014002021000e040c400c00603103030b080c1d4009001680c1c2e000201c801a011a100e07100031103a00e1500c0082c00450b15180c468007409028482c0340700d1600c0c801ea00d81e06d220a40b000c4040340e2180714454049055150b0202c0c0b0741c41141c4035001441003e0401a07004254001e0404100405007440c580c12200740720400118900c10040d9000c4400424046500b4043c1120b40c1005801060104405040700c0d1321181820407201004010091038881505400d194440e843c800703500300f40202c0414403926110403481601c24020702d000588000e19613111800e0918401c15444000106240181203911303040c0703500c41081d42402d002c121502694007080c4c0300d0040da600b061140d04c0101d00810501070180480b500c02c20f005021040781400301c44102003202e80c218800500d440340e84c40100d00109440202d86c4421 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208054919 1250 208053669 208053697
    0x10c0203030d0b01030e0f06041b06170a1d011a090112021c060e03070210021915140907080601061812030903050d1101051b07060b0406080a03030501140105 69
    0x1c0b0020b41c681c0090b244400d9418101550343c4190017003003100740a000301c0014841c003d400103042605004036109540e0a00360882c0001b81c904001c501d0304015000d0b607101080100504075070b00c5031034140081c0104072889850441d80103c40c000e0a1042d44900d0150380303441c0103807080000000500102c24400d028000b410003441102c600549040c20340801d40200340110724082811558690017611402800549a544082205400c40c50040000ea0081c440c3d8402070103051092a01000d90401948018002140c880c025600140e20f5407c08500107044c0035024126040a00086607541c200c0d02c0b0f051424040e0600101e01144100314001034034411010040d82d403814aa4012800b2104030b2040b0140316949800200055041c00f682002c000f841d01e40300403244c000403c140c25510001c1840410740d0012040c208030030054420f03540d40c035400c1170700001c140c20300201041c02024642c100303404030700c60012100b04044c0d00d604101e068400341044000c00c1200c40780191441c0c051108500c2040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208056169 1250 208054919 208054927
    0xf070c150b0301020403050708160909020609041e0e03090a06090509041514010902070b0702031e1b1603050106080109021003022a0d0e100507020d1403040b03060f010c020303 77
    0x100281c0c020300c0450000400040ca459540c3e0f40300e62404103075038003020850f0044140e446030360034605c0000b002810810001d1112251583c000707038480c0300e0400c1d00c03441255560222060981001c44c031806641c40180204140348115040d9a502d410036036141d403244052040c041510351003002c9403000c07140081c114507031645403541c1e4201041c003201400366026554240c1000c20448800c041802001200c0f00141d4512045c24030110907000281400c05541c000c0108050403020f60880d0100c4101030556252107004048004002e00e00e81980c1400c1031044282a000c015500304c4014200c902c103a0003048016501c1c0500d40c04d8849400c001785d804614403c0c047c0d04d09020741c000b00300f03883c0f600c2d012859081e050061a0813100c0081c455003416800002d03021021341d007080c00c0b0403520320201d58504025588460061244c454900028081c00700504c070042040040311520105141c020280c035266030311400c1004440e0021585c8030f106402c881441f01c2d0650040080c104200e401601071468 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208057419 1250 208056169 208056203
    0x130b04062f0a0807050f030d0605010e090f010b090f0a030501050603300f0c01061401030c090e04020409080409050411040b0105090a090b0a0909050a03180b07032d03050f070c 77
    0x10f641201000703a8480c002c00c040c03444d040070b051000b071914541280380064924100800181225082600c01c1d004041c01d0382404504012801c0090440b4842005140daa2600341c0100303508003030355480d03a50800c040c1c540202c20080190400d510410b01542100d5042c1c0e1171a0011072540c00aa2141881904010605d104050f66500070441c92490440c2103180042440015086031100c0e4810178a0488270403400c9015070780340c018903140340043c0c074114528a040c0010740d041c201001d00000d105554491a003000c2001d2402036034002c000c00c050030003a501d040d00340949034050f03d002040c8900c2c50031031042d0440d0b01074001c0e00c0b03001c20040d00d049800c03410039241f0002071040814140d80500610b10010702801180a00b00c2282d00c9100034005806151030040d04009100c456004404113492080c00755250784401d6a803032a801d40381c020459002400c45156851103442072a281200011401c0f4040c1e4050f00081d01030245690120480d42c1c0340e110031103586175040401001c02089140c03801d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208058669 1250 208057419 208057433
    0x260a0c0b0403050702180708090c090105100c0203030f030a110406020307020d14030d1e02030105030a08090d06020c0a030e0103020c0304030b041b080f061509010308130b04062f0a 79
    0x7600074840e0408914003041a000111035090720310b49030340c2003034414007040405580080340e282c01200c0d5400408154145000041021605000c0c06014043c12140d00c090365100342e09944405801506481c1c0d21800c0c1207203144164812220f0720000f0307090a1b00b0a8840300030340110340459040d80c2c0954100003842d82007042010b091041914804080d680d50600044244010a80c2603515403000843c1400030036201d202141081031303c044503105000402464030080780000308154088040d82e5a11042d800184016032580340141400344081042c2c0c1d248580003a41c91089802920b51070700b916409001102030b40308056540400390020720081000820144001d034100c0e2180c0589020045840070076828075a0940c410300f110790100d04941c84896084c0440c03030300140c64800503d402440705c07001c203001d2041880024111900019a0a4118113241105001d00701e0a191145d40360b45d14100180f46005c00c0c402c07501035600315102d0011072f24520084500748440314001d1300c2c4146864481e84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208059919 1250 208058669 208058671
    0x40e070e040f060b09010801050a08060403080919060e1b0a0b0a02030417010c0810080d050a0201090c0b090f04020414060f0c010c020615040203040309091512260a0c0b 74
    0x10341c019803100d903031010742009401800041c00c59562002d4840c0803600005007004010303442103004c0c86880100b80801c0b07201148540d8810f8040c03e04440544501d811245080040c04178034000f020300c0c4480c5403c20086402c00000c10b68136004640f03048264a440c1c22055407420f014950000101604109040c102006454260640e0060741d02f4250350380440c001c500100c1d03880340f9807039640741c002419890300600c2190b04980008031a00340f00341404083c0d5079910781444044180400403401c00b8056100f50004e517000c1e50b01075400d240542c1d480c407a03045560004103515200f4103044000d0303041810244250740c00c0740c081d9400303001c400003107600703000c550f900c41404038010550402410344513403402d01070440040480c3d8018011031802905110f615507881501620460040040c400070030b60211850b030540c3c1243d540054001d41c2032803c01c087d00210f80c01801510000c00c000e2080c0701303a400c0074a65006080e200000316000d840c082c0030b5144540307018400170a03210740c0003001049880700c1c61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208061169 1250 208059919 208059947
    0x90507020a032604080918040809040b0a17010504050d0507030c081e16050712030e01032d0e0d140315010512011202030c01050c150402130c0203040614040e07 70
    0x40c1d880703c0441c40d400042508407025602408000340700c2c4c0c0503040c4071281e1901442d0201021507641800d90b501b0b07800d4415a42490310640d00c071003030068140d4a03696201d00031702a0204000e24170130708d440c5a901806007264262030a005184000c0411030146003244e13a5140c0c19074504004820940e1101c0498102e0041000345407851003800b0f4140a501000385150141240c0000305da140d0b40c50210300c0c10289402c01d10010410845100002c0c5d000448504800001d00b4080740e00c0d01b00e04045542d6440c02498019401809041c2c407139258456030042c0c400300c0c40b007001e88400301c965040a561001788425404022b800c02c1000446425880821855404051510f640b4040400d45a0280940280c0081843d881050070300b10440c0790030010311401c25030030b0804a00b08550088010340b82c603403924138402041c0100b0002400c56413031050510b0000d43c459820065860380c4c00d0002d41c1c980003401000c012480703000301c00000002c49801d0b2000c80d64081c3c0c3d060040e0761a05012140f403041d6034a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208062419 1250 208061169 208061207
    0x3151406060f0f0904020304030c0c080316110102210409060b04060206180f03040b0406020d0305040803012102040e0f06090f0c220c0e0f060903030a05030603190309090501090507020a03 82
    0x528132a900c0b0300045002d140a0741c0e800140c140241082d050440f010380c04180c3c0d940c01080302030011080300c601440443c0e08080051f60500c00c03100181d00b4400f4070003425010351a041e807004e1a45440a020340f0548400d03603010415991142da45e925184680d029104c0564010380008500ba100c41424220030003002c0190b50921030401080c038a103800942015003489004102440502c1e41000090300180c0149401e01090825448201d010b200c18024030610b200751103000c406401815120601241d030107082002034078400b881c02c07521144440c0c0e50034614064030300400e80c071745400610790741d9041002c4c001d0080300d0201070801480305482036103290034112160fa6200c008050703124034081450319481d5120060000400c00500c48600303854207200306400c2c01400010340340001900c4500d205824015542c0d1103013000a494074000f251040f0700c208550301c483d010154403a00c12000c03202119000d000c6641c030341c4c0301c40054550403034401d001a4800305070900800e104050240035807000d129 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208063669 1250 208062419 208062427
    0x30a0209041b081b1903060b0312041706090a031706011b0c08010b370506030103030203120a0513121206230d0305030c0d140103151406060f0f 63
    0x11200c524550580e20011491304106000101510024070f4040c0c81641114020084104440e0290196025010280a0564403902402d071505c08000328400c0016809602c6d40310381e540c009680f481280245071641e0303800392502003105410300203007ca0340144e240c0c4418200742c014050707004c8140030040c8181e0411604165181c0754910a4071010744040c09555614985400d000805080d103030f40080481c000d00302001ca80c050003101051212203141aa1600402c07040350040d0100050010f402956000b24004000410550000014401c008103102d881401d991050b04074012100708899084a2136660a0b9610008017241025040b0a11034101405001109421001280c2054110300280c02000c40d040c203102442d03680a10034040301b110341c58130840b0556002091800040d001546000c0049007030300d1040000c1d0400111883c0100e40000e040d0b0b541d05141081400040006401510f044a0310200e48102d18465205142c0642003e1820071030800c21020b5a201d402c8401e0090802e00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208064919 1250 208063669 208063703
    0x4030b060103020712030b0a06020309010504030b0a2304030305010f0506090d05100518190c152102070209091515121c0f08090d0f020c041119030605030a020904 71
    0xc0c0700c0400501c503031b40c0040c250055009020100015401034020356000b4020a1080d0fa4171008413030a0320307408dd20104c25915840130f0800079010310f1660400b03c040c0c034034040d802d80320f051704003a00c258042c1c1c2e01449542d0740e5084403e1124081d004d2580c015070104407010390b5007011031003044c07514803510894580c02000b100744c0045503000c1d40d03001500110080150140350b41005180394804629100381c40c5001140d9455481c00a280b103080140b0448107039081400b03024902c45a5000081d0380c1c4005100c0d40200441c00075809094102d00c90720f003002c045a1a1540007510041a02c0c0c1003002030400d44a16410401d0256002036443e4040380030010000321100c20302030701071500c0c45a0720640510704c080030054028840e903001c1404000c11101080741c11080004c013200308112609140f2589549008200c0c20a14107981954005041001840c0c40541d408000c0205028550340300202e6130200c0c1c1c08800b079405510441c0c0e0300d41c0c0254029409480c00006e2250014030072110360345410840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208066169 1250 208064919 208064933
    0x20a0e0603040f0f110f120601090c140309071802160602090402160602030121050714010c05011409010e01090b150307180f06120213090510020705012f04030b0601030207 75
    0x8403400321118200317011043c1703c2d4206099286813500044803842821501040c000d40da0312014031801c1c8140385c440c0c0d038515455004010880e5802c1105840556074074001c00c10550b120541d100710100002c1401d50b220f5003a03583d100f076540360010b480c0854041919500c4060203900304004040d442a030800400a108800c0300c07211940900c1070102680320f41c90110400c0b062100d40d0702020040b08104030f000e0002c0c002040c844140c400d162400140e8903140401260084031141d001030282d8a03001031450310003500300c2c020344500c145038001d22581c0b0620425030309039510442c009005450820204d40d01030420320380042d95203070144c00c40b05550740d140482c1c0d6044a0540380b002040d90345103030300f44140710031b801298060a604500f08560f50066800701d80178100d020700d08524580e40340720f00000c00034241300303000114203018015500ca10013420118000d2041e0604135078001190a00c40750b4400489458032507000d00f0f410040d0406d0b28544441043d090010221703030405900b0400340300040d045c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208067419 1250 208066169 208066193
    0xb01050d180203060a0b030d081e130507080706020c060904020f07030512091207030302030709080f0709150e010b07060b150d0c08160507032a050d03020a0e0603040f 73
    0xd40c4894054207540149810540054880c42d001030174501d0001580d10000349543c5941018540145c9aa5032041c4280401c01d070345110500749040481807100c5034000000030020f040c007450540e0000d6603241d103010303a20342c1a4802c071000350f042401402401c0c900704002c0c0041241c0944052324145140b4080c074020380c09614120041270002c40c1c03408101030041c040c0740d4404481d10040c0150116000101c809004840b4001c0c10140c0010024880b02c2c8200c50020040c0b04c0c240840d4900c60118040c151620f00c58080c41110310320300320078041560007802c202c0d070403070b00c000710440c105034200212807147d5400b00708240c4a40b500d4801032000fa840d00c2c4010302c850301014102903201c0356680c01007001c1d25050200c01040050b40801e00c68201c140e981a4841c41049081903559400a4034060740c0086908030302919820750341c400550703803030724120102c600c4d1845081034800d40e903400c020a804038050451320000190702c128480c5035a042210040d0b8015018110051300003040e542c60b080e440c4c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208068669 1250 208067419 208067441
    0x11060108030c1608060a020a2615040b0906060c030c0d030c0e0d020a0e15091303091203080402090a11030a06050406080c060d0f0209030d0504031b080a060b01050d 72
    0x480002d0241c038020007800680310314082c90340502da42a18080146698140140100c40455030015000d14464014410250850070300610981da085070b202d400c0303200706404c54103003000015074100d840d200e20b0144514a40c5d501300500396401d030f850342414050141c0210150ba165440100100d41a195081011078000c1c0c02c1c41e03501299a060380f5400501d0b172012400006c0c0298079101504006a07074006007901a80c0c48104003099940d11070301044008103044402c95045861a024025141d90307003094100b6060290b140c440380583d43c2c00300b665608006120144c000380c4120085001450001b418940001e18510003260003407007000103000a03030054a81d05481c3d81e0320f11040040d41003d0003600010061103010f429031191160200d000340c4035914045034050341c0e40c400540545180d81c141c070343c0c00c0c1c0081c0c00c07a010700207000d8015000b5401400161b071841099803c501e80560140c090505940c43ca80c090103950710190340d980098508800c205062110600001c0b0000c4101d100f4200710780 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208069919 1250 208068669 208068673
    0x80309160806060307050a03080d05070915050d1401030b0a051e0c130e010b1b0312010e0f06031b0607020102072c0105030c0d1b0909141510051011060108 68
    0xf042c9041014540b003019400140a0694003400300301081005090380c121055a210200342c0d0340d54000b04403590007691300420440b201a2042030100d0358054050036034180d42e8801080b102c86e003c41c9082c4044400d01c0010302407504440000c4803168160820354005d41c4840300d4070905020b0842c0070802e040c04688075551b0003404151f0890010608403008000d00c0760b8481041c03903504003400c0030284c2c4594208110080075404400240724803c0080700c2400308500424015541c40c0e00d48210000402ea80e80d440d00440400807030300310b01d00400d000035242480640ca401a4880100740801600890b074142d056014100707000454407107620b54842803e024001000690305050600700c2141c4041e0483c601030760003d0f04500032a215074143c00c00c4283c00550f01c6428180b0a003820322201e846400600780282003801c12070810824900c4400d1005000042d5405007441e5050902000801c0f14190a4007203410010040c0b410003680c030f0100007840307180000e440340c03414904600d411b00a0388410310913 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208071169 1250 208069919 208069921
    0x215160614041101080106090b0901050c0106080f0f0c030703060b0616050f01150b0406031e020d1a0315040b0901090503030903071703070f0513031212180f080309160806 75
    0x103030450340f040c070703000e42401e01410550420a00a0071080b650065140550000654080c80da0044055400c0a03441ca00207011040d103507800b182c0c4554081c0084400c03807140130405c4e400604040369409103808041c0060000c203203540c440704d018003400e608140d0005c00401400b01401c2c450404141224014402450301c1c0c0040086e084c00c40d0300c40c0c41828004082c0500901252103140c04a034100c0d030503450049024020300002e90a40c3c00c0391605a0071141c0f000440710303402e01c200d80216507103c251568802608000e002030549494031600a201800c41c040c0010f00000c810b8841a50480e5518000180140c040e0f50b40c1d62565006a0710320615501c0482d030001002980007000c000c101e2594203040c15410701d0903016007038440310f1400c81c09110000c00d010010490180880e4000e42e0400108059490f600070060300c4150011a03c0d000141070801d41e01124114000015007141e104111101d02036140d228014150000b405510a40c020b100c241c0c6090328143c6d905201500c0800058602 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208072419 1250 208071169 208071173
    0x40212070f1d0f0f190f0503120427060503031b0d0314040f06090f0b0a06060207050a0b0309030f030906010e06030c0904110d02040501060f110a021516061404 70
    0x681420b03050001c101c200322800320380c65030315050055141c0b25016116141d01c0c412902c0041c1c00441c06116015600780c4982d800201d000703800607488200e030b00540685912800da4400701d80b042c03045001e075034a41041010303034203a01c5d220300d0301e8880c0d5424100e40c0002c0150326000000e0659210740444040598408036120486000703025401c0b144040d400c080145606190048554030070003000a00000740540c400001e00c05550040c901003a8494807440720003034585030205000c201916032180715480e0810210f001400011040290703a0000c2c1480442443c02d03001c0e10455100400701d24290000384100740d03a03000a1000386010340c01c0440900102d60401300d40c2100200000e011603c01c0e0711000c80088140c0701c0204494206410a00c0c05000c440840040307000c0b1203901300002d402078508000000d070329900100c90132041803255142900d00080407001540e40e50003003c040d41c0701186807011145810b619004140c0b958122101002200203074683c031003101d01c401800c1001c10310180801c41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208073669 1250 208072419 208072427
    0x1009021b07090b090105120703080a0819090302071203090f15020f0604030e04090809090c090307060c0b0c030601201005071706010f05090402030a0e06240906040212070f 75
    0x30140405841c100003103000c020004e000500188a0340e40115402c500c0001c00420600280c0c01440c5c001405a60712551488010100041210304466168003d24100d52003449802416003e5406a000b040c440342800c40000a00045500c21414400c4c1c0344c82c0018260381042445000b0301800f00400c0c442c50010401909000c1000d130761764680d4101104120000c1e070041000d000441040d10001110111850021400d10500e00d0380703980301c4014010404c1e00580c0e0001805a940c06806640c03d00e03030785034000d8568540454009040309200381c0002c200a2841020b5035000718145071034006124001581c40b0380403525004015a40c00450440c01c851665000b115000740040c0307810b4000c01c0c1180102c0007004800b0b0403160410540c03540d01441d191043d000d81740d50000090045503030b42051500c042c01007104c2e1041c0c0500d4010500001d070b65408000b0907880c8584400d4000621170410006c11401030340080c180c51703000781d0038800980c8101c00c050889218485540760b0340840e802c4003002138 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208074919 1250 208073669 208073683
    0x30304020a0f0f031e050a0f120306240e0904031e05040308090103090501020d110711010323072303061905010c0b040c0911041e031106031009021b 65
    0x2002d05140a54200000030780e4402407800c0360b41000440e803003007054501005042205402c098114800c100e0b030035062041860b25040098450745403d4100000b814040d01903524a11462088481c0040802c0204070301c9000400380c0f0400d4074110f10301c0d00741600000d04041d029501540040d540301d40140401c440c1c4132003c2d41d91507003810924100307490760b81c032480c6900c030341c4185604064032a2048810440250103882d0302c150303d164144420f11034401c000c41030303030880102a0349808101c0b181403080e5010b44112046403404146580f850312041d010f40f14854000741c501400c0000f109843d007808402c2412081b4481e681402a40c1c0da81407100400070b001000718030203a0183e00c1900700b080301d0380c0c100d00f00243e800d41c001d5003591540c0d65814642c56203000380d40090300301030411000324604600c0c44001c07c26100031080c485460074031110030b540c2420f103e000080030300c103e44020098601e8400f02560740034072140a40e200150b1107410040c283c0e042542d108010406014480d1f8000720148081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208076169 1250 208074919 208074929
    0xa0203180114040512010f020a02010212150901030b09030702030d0302040519050a21020a03030207050907030905060a0b0f130509070501021f0b13020406180b030f010e0a0e01060305030304020a 85
    0x70401e950742c0b04151200d104500c511071240d066800001c1100c00290040107821607003100864941d081380002901075400204841d05825141d00040c00c01806480102c90b2000701a102c45450b0303007156100c028019002d0070204d500c0c40180191001a0b908000b000440c0689540158aa51410044c0301d440704444aa000590303034406800c0c0055190380c2c94210849881249a410580016a1017401c400b207141020b50000142c18000c41490340008440048410580d034034000c1d0317130301d0a004400311492510000e1240d00b115022414009440e00416400c5100800300c09a85140741d0000f12040404d201c00344e2090f0301d4204001d0700c24000d0111900401080c0003900c11100c3d40c141041100f844010703020741d1a5542c00500c2c6080d143d44518541307031814100c00715921034a03258040c0c1005034010050300c80c1c510181021444503e208140c9018100100424445900301000d6103402c210040c220407a850b521000000c184100740103490045000d500a941e40c1c1c00d080c0180a40404183c01c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208077419 1250 208076169 208076177
    0x140a1806051207031508070f0602060f010303020705240d050f060312030103020418020904080915070b070c0314070c1806031a0901090b0c0310050f0609040e030c030a02031801 77
    0x4041100c8160400c00d0f5200b0918a07000a94561841c04d820000d091500711007082d1040103008140944410040d0056034090b8080310751954480701c50764800c403024000100140c000c010204094203180480e40c0b000f982c03204020007103041e00c0c280210203420546070200100d45590604c0b42640701c1d402c0e207540060054001d8500b5402160303481c6000e22042c8170007030103550390740300e00600750703020581c0030002507402030044605042500b44600c907508000100f03440b440b01da40d4100c180c0c0c1e10b44421103d4190340032148440907603e03042c0544810344210320a9080c0031007640f80288415502004240d03052090b20381d00c440504000085a0001c0c0c04180e8161440c906001031020885070010b030341d8402404000405a59609060307a800f40c00130020051255007a9014401a414440099403240b402c4e106078900c4aa502c204000c8500c043c003485a0f0401801c0103150701c641440c1e004004191000400c0340e11b001002010589107a00c0b000d0401e0040c0c2006c1003104100c90002103051b02c1003000d1030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208078669 1250 208077419 208077427
    0x131103071a030a020c0105070c030806090103030801030605060406031b06030b040e031603021504030905010e04090804051512090313090e070504020d09141c180302010f140a180605 79
    0x4140725450780246000c0034140c901100240110b011034040382d15150610000384481d00301034074041d05860000000314040351254001850a080190a290490780c0544e12080030740d00c2c42d01e90000500001d0301451700582c64400c00700210700d070440514187c03142c40640002d800d10b4004000c0450701e24403080c92155003001c041003203424001040d50f960400032480901d2544540c601070746411104445141140c560804100606800850007000c844007a01c60300044940d50301000700316907110400600f00d40b0180020320180c140a40c49160082c401000b2070320700305001c450059803031001c84210846500001d01921010041c1d26200c004001051061020555003103003562225510b00503c4c0c0220760120f0070000c590b2494003c4001540c1105000c0f8444803014142a01d500d51080320741c070010103540302c8015061060704900c0d0802d180042440009045030700445026629a15420400c485548605c1c045c2034844020305601002d5150442559110640c10400c0002e60780107a040c400240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208079919 1250 208078669 208078679
    0x51e160f080a060c0210060e0f0c0c0601032d0503030105040b0a1d0a110313060507090e1302150a0e030709090b131b0608041406010f0306020a051213110307 69
    0x5402d001150740642c0100e032810142d40101c0c500030040802142140c20603100041c0d20000140142c012105101e9030545651040d50280340c43c400e982c10706245a10500c010801b04203030095206008559640c840c0040c500744550a0700000c100300b0a465a400000040240703180ca13200c1c800b0f82920a680f880c09191410f4a0440d00002080c40400e41c0e81c03c1800089041c03075140e03c07004010790003482e815100d0030070024030002100e00d041e003122910300d00808240750b0b9010340191b404841c00c1c400c0c2501595544c041e11001c450741720308103c3c0c01c00644047c1d400c518058030082e01601000742d0300d50310585d0301201003600d888495403100d111035151030015008940038542c80c0b54800c00c44c8807420815a0180b4003c909400889030300501c4000c021000b041050744460518000e42c052a100c00708a10186100b40c0c440300700f0702c42d1015200340341c3d00400004a054000c1d2032f121240d81090703130400c1c0c0c1d201c10030070354954103d03031500d0904006000c0d44d00300700d05040004c0e400d0506600411845082c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208081169 1250 208079919 208079923
    0x1909090914060f0613020c0c120318041a0607060b04050702060910150e060d02060d0f0e010e03030f1302090112050f061005011101090204060605090a0b03040f02040207051e160f08 79
    0x4120581540c001601e490881800c100d08c0d035246001524102c14180c01c01010f607100d4000903542440d006c20011011020319050150100d208034940b6142003022081081006c2c81e8080c1d03000315445511307034002840c1c65840d4803485100ea0340d00d402401c00307481d04102c40c0c0c0c10008200d5200304a189800b8072100348011050021083e242d035480360030b0703a03034852400042d44da000301e40740254420b40c001144002c820560300102d9149240140c140030425541400d80c3c00d030f48815000f1030850340140001154003584501d61178015681540c0b0310100301c01170300070a160b900700f40c100840e4141740c025003004002c800c00621080c0d081c110043e01503030511606506900105104640c10010201902000d0340c00a61100380100d0f4028000c10203503654901c094910782041c2541440b8404102d00081e220311074504076881a584084d0468500003151708000007034000f03680981d01c40c81550303500ba201e02c42202c840d01c0501d41d440c005040c554204592083c491005822140400c551414100108480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208082419 1250 208081169 208081189
    0x40b0f071823030615041505030a0f031101050a06210c030201141b06040201030e15010b0310180e0d020d0206010b031b03040614070f051909090914060f06 68
    0x91032021072522000509a107000a40103402c00390701d40070351014021700303052011401c03401c0748041e00c00b03000c4556141e030407004000c0640310342e0360503070071842909000814802000b4800c1380b00b82401d04e140c0310349076516401c40300c04543c0c5000c02a40d0301408e11005c040340c0b000701808540b03203100c404402e11556910031034840510009041c081c1c1150307080d4104421000382c401c2c3d80324a05803012605001a02c0c40c0e41c0d11800c1d00c0a9010915000c00c003104c00c40c01281c1840c01520b008500c003502d0f40f810103082516880100440103004801c200424013901c1c1d19524041d1310883c1e00c4c0403400e213400401c0c4d0360900090100b500c042d0340c84030055000803600810624110f804100c0700300d880e9920f40c11100341c1030903a903600c8607403581c0c004100301c100b159903807041c142c4031581005c04240c0d42d00c8120a03140407500e10022000f00700288007050500c4401e444134280c5000c149011000c442d40c900d000001e031401d100007283c032034205402c440d4440a0400c9076551042d204000158141848800f142014074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208083669 1250 208082419 208082429
    0x307030c15020c150919050c09011e06050a02010204090f021324030b0604030b07020f060907140f0301060306050a061707060f050a090f1d0708060102030409180b040b0f0718 76
    0x491392001070417a131014032000c040302808640181c0280810316102ea1100c0c9002c0e40c2e280f280c014540003003065030f43c0c0200c0030140108a10261801c9080240503101c540041e5810b90440d9001c01002c5100601d0740240000d03030b0104080540c0f94405000401e408803560341200a5614095121102c09043c0d90041e01c030102c0e1900b00003841440c40c0000c5696803140c0e0304060701c1504650306001040303a0016140080d205c00170250751940c0c441c121100c1c7c13900054032901d528900c10b81c0003c8810f2500003c940b5000100400000d54540e0707a507509801d4440031500103020790354581c02000510144001d203c02105184060320301e26060941c054820041c0c1c640807402c00402040c80740303429000b0701090002d08503580e01e152100e0741e030b511070180040000b42e08084038907951000c03690050007000c070035001e418141c001d0350505007040201c0e00101030120340c0410f0540c403405184003046880d95820b0149014007041a002e1a04002c00c0c0c08078900038000d042042180021046120081da440c00d00b950 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208084919 1250 208083669 208083703
    0x9270c091404140a0b1306141009030f02010806030a0515150103020f0d0209060409091101111501031202100e01020a090e040305070f0f05060901091b050102030318010207050307030c15020c 83
    0x190305e0301080d00581c018200d49000352910304041203009154a81e24290b0b0b40450750f4114000d4061401c90340112141300050254440c20711107401036014405403a445034010703040f0f441702d15081d00c0700352602c2d891012041945000405021006090303010b903544a001c207080a6180016002e09243c0c1441000d006c0d07540c00b94040340155196070b406080324014000040284202c1c8690308064650148200b90720740810a40400c002100c100400c04243da04403140c3c02002e0303a861900d8903e209103e0506070300071030043c51008510892240b050900c0d80e81d044000588814070404042c1c07010360960084111802020304020000754040c084030301c03a50f4000e521003060354080c80d00390f01ca0020700b83c000b0486d0003001c0401410312815800200310031b0148405521031102d8401c8400c80c000140906401038008100041d11466142007090078240704000040c54065291201402c5030402c0b0030440001c2c220401c01004d000c040806424064070042c4d04501d0105d40690040d45d41110f051002c13a0b00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208086169 1250 208084919 208084931
    0x2010c1704020d021f12050c07140115030515010807051507020105070807060e010b060a0c1b030c170c030321061801080703060509030a09270c091404140a 68
    0x103465045190a0680c0e01034080d81075502041c0d41914910004000c080004d41c006c00f40c01840342c03050003a01c2c010303000024110700d0700d415922409008900410424925900d8880c410700c07418109108100450103000904080d03c074040c1c50b811454410303442407007964480035060210b50385149684403034404c4c014480ba5a8030f103620040c1d0341402904005400c941e00800d0b0f90060042581240d246c000c8100020001400d001f010030108d80180350700380f00010031501d244000600b26040c044012202000c1451b1111394239503880f05854151341101440500f910703800c800c0040c00704a001240102100558107144115602c0700004410500e48207540841c070f004600c550311944401440e43c807654045c60465038442c03040f565908203920048514918040c00607103525808003d0b11052240342d1349d83c020701440c0c0841a44034024403001c05150324055240d010f070b03074840c0e0f2241034040c10694594080b920719205a20107510441070003980500d062504000b5644a41100b41c5d5110804040010b90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208087419 1250 208086169 208086173
    0xa060305011a0312160812010602012d02091c1a16050901141210080706050711270405010507110f0a060e10020f120106051201120602090d030c0507050102010c1704 72
    0x31707800d040c01604014000541c1003600e03044010540c10780e5080e400900105912160545818441d0f032440120060380444070710f40203040d0f4000709200c44005041c0c15070300c201175500d00000f0310405c0c0112a05015a000d0040030f410b40044140d12003107111035041410340e1100c0c0a40300b0b100b081c10041c10851300c00c110284000c0e003141515480401c0188050480c941500007180400480c060004184940c04000641c01d103d801183c0240d68031100e4035184401c1041485010021070038085180700b0030380705151041c1d00180740c00780704034051000400c89013000c58002d0055101803e0301b0070f0b03d400c0000c650000d0000015800c1989500150000c3e081c060380340d026040c94060340c140c0c100340303000081d40350306903010b4405040460012007403c50140d0741d420040e2510b00c9600350346407070200010010030540280c2100080498000c080c007505d490480b000040c101006003e044012036100c2d0102e0003888010006500500020b00080100040c0708801034000031044110841000030702001500b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208088669 1250 208087419 208087447
    0x71202090402041e0303140a1218050d0c0b0a2a0306050307080601080d21050603030405090a0212070f17130204050106020303071806081f030206030a060305011a0312 73
    0x1401074007210180c104e019120318403104814172080c0c0005200d810700f410840e00102c21101041525101d414200304140c006d0701c082d002584002d1640aa100721a201087c0144202610148944d5070b684182041c3d1502a024460181ca81c0c10700030b10b4090751061600d084110f005001014106d02c0340301d545c42301c604030301400c1250030054140c041c005001402603030000d135540c143d58043c0705496060030001c00031920324005c64002480362070044141072421b009a8001900000060240c0c1d20f031689802c00705001d094103031200c005007540041c6800111014109258001001d4030380080b104d503110200800a841083c62001c2e511410004522442d40341d510030003680754058018001c66030340c3c82c8082d490360000c480300c102082c0c01c0c10a031005880c4190113070043c3d82032a141c80d5015240c0700e40400e07414070031903910355100c10491000700240e501c1c10040d610036401018007050346401c6207049402e4548903880c1c0099000c40301d4161305030b0360f0302094072850480d4003d0b482d83c4608250480f04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208089919 1250 208088669 208088677
    0x30507140712021c230124050102060f1b0d0f05070305100843030506061302040b03060609031608010c200709021804060906051206071202090402 64
    0x94454200d0004880b50b003050110041c1e0300843d80000301d11502080e07402c84803450100180028614140781d46105100500d52010401c4031000142d131000d10001c0815a0349100c008000340d24091004000d5582d040140da070b407000f92540d44079141d05200320000c0100701800c07a851300180011031060000c11440c1d0002c440c06540710310030301c0a818880b00c00b0300200805e503990418038030f20480202d00c0100010b103603800b800d80c8860482d1340e94800b401c5400b40b52500da4600242c8203a02119805100c0e200441c02c2c044c40c02140138042d5410000100440201c003031800403149801480204060380c4500e040e242d2009003500c25941c1e0700711810000e8280382c4641e014811450300c4400100e44004150701c0b604980c01d8903101d46000004240c011100c801170f0b90704d4140035920850042c01035400300e0b0003034484004460b29900902140c90005025660300381c22010400ba5585001c01c102d1400300c8804410070b0f1306c40080c09a41c10103910044c441c3e115919820b01d041d070002544d00d0a13888660440e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208091169 1250 208089919 208089953
    0x2070806070e0901091a2701091a0303070308190e0303071710240e0a03060f1a0f0409030909020c21040b120c07080705030c100216020d060603080a050a090e1003030507 74
    0x1d021235230b1106c4150b4020140900f03543c19955515103a80300c1c0303040001c02c90714500e4260321880350319518080034482119400081c008070030344480f50384031090010070241d40100c8443d10f030040000740078224405062001403d55040c1e0307101c90820024030103d0080b41e8002c3c20300e400a01303001c1403030030000d803443c1201c0380c8815003041401c803002003440764a52264008000c4001c0034004140340d04c0c000404d038a0022034060740181c0030700c5a0300c411314140d801101c0c2d60384282042c00705240d071081c00d0b40c1284c0091085e6130450b0440149038082190b4034001c3d40504400f070303465030b0901d8242040c40d404c6000d8401e04c989081300c1c010228500c1140c100c00d441c500390b8005141e682d1845030340340503902c0307401c80c402103c01c42c800c0e00c94142081c07550b4000ea0b02c441c050201e103140c1412160b002c0203208402c0784015603004d9507841010020925007001010041d4179038503400c0d179681c142c050081000365140d00c151600e10380e44d424043c0c421001d240341d10460b40c052405540702d88042c140036006582e20315030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208092419 1250 208091169 208091239
    0xc05030c120703080f042f13150b070b1f08070303030905061b251209030b070c0b0106080414070806011703040b0304020108040302070806070e0901091a 67
    0x10081c1d8941440300038800d1611135070314101e20f070719505c801050980054400034000f508903500b80002d030600c0b180c0650b94410031a00654442d001c0c2010461030304400c2d0900071290b0319201c1d40d850340e10a01420500400c0c001041c1ea150031025240c01200003800340080000541c45020b1003227140460769540040c213028829552103958914001c1c00800300660204c41034010080002c08800701804055588000c50400301d140175480301801c24022440c400000d440040040c003100441c48041c1d40e0480c00b0380c551a850f00c1c09046007050815268010910713400c0051201c011030000349111001c5044502c0c40c01c0ca0441d544503480c0441802c0a0901d04070003034071582d40300042c0e4160014119040342c0991132801c0b002c07004101c911340c880c841d80c0601d020302c0300d080010030015449070882070b41c45400391054444207074031200b0070703818a14292802800985803000e0240e46280c002c1005006001c140c00801416002d15200141d505800c0d125602c28000c1d0003c03c4003124014103041030092030b80031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208093525 1106 208092419 208092433
    0x507090b090103020f0d0902012d030504021f080613060f050607030504120c0603230636040c08030a05031f030c08030706051006050a0c05030c 63
    0x1031000d0425a00300000c420172001c0c00b0213400c1c6440d41074000301d1182c0050000600080d0100217146140c000000c0c501141d10a040c0d0490044856050200300b03030b44c43d400010395080b4080b1500c1c84500e40c000503140000d902258051182000720ba41519403d640c0300d6000c01c0b2140d034082e0300d103a01c000e0801403040749405809040000d01c02d103080e03403506d40c58520440745205950300494100384cac44807082c01695050701034181c03100c0364080c00c3c1c00d90788007000c2006405000030b80000c0c0510303454010303482403281108118400031b04c80c14240e0340c1e042d048912a03424000866027914241124a000704102901000300c901c200312503590113045449040500440c071900c0d401e401103410a4960004c001895480d8841c01045400055a00c602044c10a10140c1d00d004082880b200b080003024440250080d040e10280141460111b01500c010b280c03c518510980d00030700c600713100d074107 = true := by decide +kernel

theorem cover : BRFrame.Cov 207913669 208093525 := by
  have h0 := BRFrame.cov_init 207913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207913669 ≤ n) (h2 : n < 208093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
