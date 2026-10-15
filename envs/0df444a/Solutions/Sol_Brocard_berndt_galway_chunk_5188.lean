-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:02:16.200522+00:00
-- url     : https://prove2.me/submissions/d63fc2cd-6747-4a19-932a-f7e365c0363d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932913669 ≤ n < 933093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932914919 1250 932913669 932913677
    0x7140f060f010b0f04050f0d0c060504060305131e03050d051e100b0922020310051e0d060e0a0b0703200f0403030c050a2406150c030e06090303040e0106 67
    0x40d9840020301094404c1e010305034101c42040c0b204114502c0d28018107a0407400c0901000e4592000d5502c0c1d040d12010381d000240441c401180a010283d0715109955101c0f01c0c0c03209840d0000030a403644801c1c1c0001d600b1418012110018503000c06200303000743c0d06000c0f441e0005000398109901000340d4080c480549046014038000024000c1704055003007070450703034101601480c0c0b924950500074920420120552411003100106481148034401944078024080c10b003640c86d81042c0410101d400808070000408507515200010360b60396041700070710706030f000400145039000e010b215810000340740c5010f05000c118904220303100390143c101d00d0403542084c1d62281e1082e00f402c5100054051050554984003040c001400000d020756071544c40305008808581c6500302981d1906010183c1c0c2c05400c1c805c0b010340401300900b5480740580c0003c3c2480c5110070f0805001c00400800342101690702a08010401028882a882d0781d402c4460300600502601da4031500c49019440303403103080c42120002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932916169 1250 932914919 932914921
    0xf06020d110a0b22050303010807051005210a091a0709090c1407052d060601050a050304020d0c09110414090c04090c1b0b0a0c091a07140f060f 63
    0x203040c011440c10b41039a0700100510003a11620700d80e9545124020440c505008038403a0703500450400c002a43c001d003180e034024018182880c0922404028242918003400001c2c003400015281d0713445d01501d55601c0c103c0c0b2051a545606e660300c09003005281c06808450049655980641c4201c40c02c0e100d804562a05103500d0342d2078410030201c80c035542c40100003030340c400d04610b0080b03c1c50b00184862801202111180d4101180e6030300281d4011119090400d06035918658241040c032445502c1042402c2c0681000007002c800741c1180300c003c000074401e0790786040200401c0b00c1a81c1c14406005d0b030010810880b40759900401e00c0e40d04c075002d900003051a0b01c07070f1003020b890800d0f40c2d14800d4000031181420540303441200805003034207000341c900f8080080e04524078042c604680f0894140120b007c45000d0415861080894010510800810070f0884041c03080d52403000c00c40d0210300011644aa40d10000d0801d02180e003c607400310302c4140206400300040c10030003e500c50140f0301b0309600c1c00311 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932917419 1250 932916169 932916197
    0xa050f120a030b0112114305100509030705060f060f0f01020f24060306011a0304050705100c03080708042d02150703021902030c041a0d12020f0a020901090c090f06020d 74
    0x1c014002d4880c01f001a1340c0341064a06140c0e000d1501c030005105804440d4000001c0244a00b51401101e80e82d0781544081411828010200f150725001100d0541014541c240507011500c080c003220583c078011841c80d0002d2519074820802d00c0301d0304880005070396290b20403081200341e1083c03a0001400580002010400714600411144d04881041403000701641c41003450965035040280251214081c000d0009116241c0e080504448102d65403004601c0100b481c0181c43c100000d0403107006c20240e5820880090807071070501301c4a02545210150340c10a0000071810850300c600009e40107408440b0408102c100f07080036001282c42034003901c40c2c4164040c43c1e004403160140c40650325900403859a020703420164411102d402035901003c04000d00540400c980380c01d5100200c54022003200060601c070f03070500c41da10540c2c501030054210443d180d00010089001030140000d072503614041c4191443c050200075006210f07000c50400f0043d80c036880a5155200c41d000700000c12021540d00c0300d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932918669 1250 932917419 932917477
    0x801060608060915031e030d050112230c210c01021b10030605092502160b0921010906050c030c1b1e0a050f120a030b011211 55
    0x221514010b480f140c559070762140b10b1000400400341c8150140900801d140e1007a030289040c00980c510540190b5031384a40d401007500300d50781603008031030350f2403010410000250300848503404944101590704801070900580c1e42401c0b00190316a0344400751240d0720400c01d4020203c00f8007807284000b50350840389140016070319905000d5106100d028180e000c80843d19180409030a082d0b5a4600056600c2d214404255a01d80a50341c07200720150083e50b855041e680a00515400d16840c4043c01170101c400092910000141c000c500e4041c00208604049490f00c981c4084001a56030030341380c4110503482114000d0105400544102d03040c200002c1c1d030382d500b88003140d00030034071701c4012490704440381c40308200c10400d07000d25541400385005111641d03a5203d280361650542c3ca01504030341c0e1039403400301d1a00d4808001100c150304181044050404100300b0b9840403041c604002c9805551080121041550318914102851802c1d28180305030311028054494000f4121024413082d981c2100d240c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932919919 1250 932918669 932918671
    0xc15020708070b0c031324030b130905010b0901171504020f1c0605011d13031b1103010c031b0c02091303030908042405071e0302150708010801060608 66
    0x48003541c0700b41010420325550310002c01d400071903402030340d0600c100501000300e440c0e100c0d400002e1441c003010f10b9107400404120034507181741c2641000c108800c008008903410401c2c1200d40c051860391582c070102442400e41040d80015002440c003069036031180501480246030303100101c0e0a12601684d15481e0003041c02041c082c940090900a644c0c1500042105480c020f115101c10a084c0240290018502d40615406000c140751042d01290802c5034009400d50001c00a0700f00620f95030120000c290030411814901e42e100d500c546400703980c0c1c20440601d0900c134100607015840d001c500c10348a949a80300030715030f50364a45000801d02c0d0b0454115084e038070503031000c0d40c00240300c8c001c1b0f29403e0a15040d01e101610074140455124000e4843c0407841d00f00d640f01504682c07507207103141044484144209040d9882d81070250030042c407070b01c68900246046c0c4084201c1c80e00907158005240c02004402074400c13415003030400e1032904100042002000f13119400c107960a01c0710202e90540280882 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932921169 1250 932919919 932919929
    0x30f020d1d0405151023041415041802030109060e07021b1c0b060109051c0609140a0f05070501031a0402031f0b030105090c041401080606160c150207 66
    0x51001d000440080100902000d4644c0c110082e1840d1070a20548881100c0031600d103d50300d0784508001c801c5051101c0842c101803081c8000c000308800d000d444001403030201c2a040c1a00c840b908526040b4503410300b841250003c8007020314040d00c000f80b0340138640085060f90714140c801c1c0076103507403000702e034054030015140d20380927030170990f1600105420085501007540c401003520600308a070680c80700010710752040c1941d0103400c4004002055800480810040a0039102124202d144821038000001020740c0188200c1d01c440802017030240b126201050000d10710180c0305414902d1a160111008059007100c090085080000d8a0740c002e02c523104480300d000c00e0712040340c1028400c01001354002040e200d8585c8445074880ba80500c000c100b040580300400d5496039950402c010848a600d004200d175460031810841441400f0452000a007044420309161149032542c030001461405841c4143e8981062540c68100b07002c40441108212103030000308011419510a08a0303d448041c018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932922419 1250 932921169 932921207
    0x2030115091d042901080f0703020618040f023006060405010c08070b100609050307050607030318060509010f0e0c09070507030c0b160e01090f09180b0103030f020d 72
    0x442030100041e250043c1e40300f4810410701004500c0c8070710620022a545505250000401c03005200e030764000c10141c118009600f00a01d506441c40e8001085071141e4040044160511018200d0035166031f0400407203050002000c3d0346850580c50b0f800e41d11003a05582c034078400d40e500e5248084007400c1001c24015840581201d2400c0c0c140001580c0c0040b584008a83c1c0311000c0101802050301c004000f4055502111500c04007440c00000034400c4010ba00042c7c840d41200b40100501d64170754003141c42c0c05a0504010450420b40c800c0140c0104000c140540401d04003810030900c0030066000300300b849602c140400000040b1800300c0d0b48c07449940b1034940c0002144000c2540c40e030140024141c030034402d28000c0b81803852543c2d90895040e090350309281c214003204210f028180c200b0b00507071081400784ad0007650309261001c10320b0070a405210344110303243e40e06a106055003140c00f01c086001d0f0003100d4a8502d503903070f15004101540710300362440107000322601c2028291184c4034800380f003221655 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932923669 1250 932922419 932922449
    0xc07020103140609011a04050409110118061709010f0f1514060405040506031c020703020901050d03021f0603050f060f1015121b0c02010210060602031e07020904060203011509 77
    0xc1074040c041401d400720880c06d0003400000381540c2c680c043c0e03450107071140e0801150500c5c10f000141c0a00f0080c0181c480c2030000d804180440d035070099600b02000405968a801078581000c03050040c00d8500e900d0a009003013024001c1d4001c84d039082000d0318400c418203428901c0d6507404d9801c2c04403102810b41d900c00740c1000200094980307604034617003115004080e20360700319400800c44041d01201c09041e001d41c00903203040095141654010740106030642d0310840550300c3e5500203440781745640b6080107500315030f036940d884a545507006501031948513045601001c110180103503515012030300d1407050441e03400012320b01d4151117110400c8400320702c25214100004501a40c1c0890403080e49940166502c54182d040b03c41ca528a40020016071244010400303c2d0000a00300980c070034100c1507d5007000c0040101950000131200303201001320980654441e42c0800150a20654001a600448a00900080c0607136580210b0403641d88582c041100080340d00f06a401c840148280f03070402004c15 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932924919 1250 932923669 932923679
    0x612140717071202060f0d051b0a2709020d06090f09020d030f12181a060d0201140706020406022404030909051305010f0b21061303170c0702010314060901 68
    0x1030f81d42d40018130060001d41403031007a403100b00c02e64101020302e01c6041d44079400d11107074880c050441540c440940340745615180c0d4202c0007412140401c00080384074800440c20780450b04c0a100c0001c050140fa408c155680c014088076007018003001d0003040300c0b580c9000b00c0d0302d0b0091600d00c80e02108950151000c0c450004544003554142c029081e45810f20400103119452110b181c402c404080009043d81941179410341048081d5140341002c1d04003a905a805000c02527640c0c903100050940c0c24a0901c0340244001c0b4011418001e04000820040c000306000c00d000b500811003085e000c09078880881400030038281818040404d86000e008501902000c2c00001e071030350042036000c0352a40c02c26040d8070f60307a5985800c4601407864107040750354400da161180c0c85d01c010321420b8002d000c58004400d0442c860082e0701c400d4050012544038940340401010076000d14104500041482441003446c0b500c02d5801c0030661000b00300b20300081c034200017030707103103030f1030340a816000b40380140483d2203517030a00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932926169 1250 932924919 932924939
    0x204051006230403081603030b010801080709090501090503210915130f0b090c011116050609120105100911030f0621061906050612041203061214071707 67
    0x165034902c220900c20000030020607540b0000709400d051066440f51101e00600300101201c00b81d0052504024002c1c0041002180c001410019a003084c0c00001e600c0140d49800d0b030051029840c014650f0001044e1160300754084108070061095440f03241c61241e6500c8002e985074071040038180c8800b4607020200d4550f4902200c191100d81c0701741003285280d4204d0329680c5010108403049480d6910803071410701c555900591190b8958460001059802d801000701070400c40719020700da018920101e10346071107980d51041300e105040703140e008010504213042079101084481c020f000c6254201202c41c3c504084207422070784a224000741c80e40325521131104110900201400d400114030801455030701101c005e006190040703d24102c80f03408009402c4051050340d10540c40244617110a00444600c0c0100e10222a40035a100e01c0c10600b45103034120540040c00c035a04040500f282d0014190200b00c0400710b00700e844180c0c030040310141030341c034101000d40949004c0c2142054105001c200805521 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932927419 1250 932926169 932926217
    0x120114131a10053f0601092708180a0302030c01181809051908070b061906081e0105060702040509031b030d0c05030c1c0905010e0a0204051006 63
    0x5044400d000450303840c0009104051505005903504d20090482101041c00e04140c40c0700c110380304000408901803900894075518144210000c03151076031140324000c9454100520f4a038444129800140141d0a01502c59000407140c0035030068602c01d004043d18001c06444201c942c020000c1402c68440001160308805101405615104201d000315851400007584d4404410b99040041c03078410508000c0d00e03041106424442248014244c1004520b41e034044505c0c0a81021522a4903104e0002295645442c0c4da600c00c02084c00783c001041c450740c8008240d006610f103087c16000904101032041c80c0794020300c0707406e500000402c084e0780181070a8200903400b180c48000d90341051f40081d04240190481d4bc484132850304000f032044032a52492044400450321131601c14111311341200e4451291140c002c480d6604640c032103030024032170925000070f40d4444d803040c000c0c01111050561140d4401c0403031801c038411802d01000031a10a000c0048404030740c5503603504141c0500c021400103003ea9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932928669 1250 932927419 932927431
    0x160b0711010e042d050f0c0a05090d030905180c0a03090204090b0f0f070e03030a0c06020c160f06110d0c1b0e07030e0105060f10050702120114131a 65
    0xb07104001d035a4582c1c482c45403001c542001014038201c10040480300e41000010702484044034601820b0000885642848a600c900d824130165070340c41c4c5419060b43c0a019140303d0503031201c0c60008000c01c05901014460458070107586c45803940d039880751094030001044500d4400c510003441980d84c0903110b81c000e490300720b00240c0001020411915101010305084540000041802e0140081a080c0c0030801c2c1d0300a001d0f203000901341801c400007948134420b0002c04d07020091201c2074003003031080984c1100c0c4d00c02004000c84911101f0158001900301d854030607150017425420000941c1401820010308000040c00907003031800e400740094501c1c021040064070403c1010a091080302d40301c55074100a40038488480c06a0300e131280c8010207440014084492a0b411700b000d0ac081c44e103910414034000c10046910038010007029000b141c40d4003801d50080d46c064170040442c40c5050040d800301810380f031140c024407884c0d900d01c420762605000050008284c85040440d0380829140e1202a541040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932929919 1250 932928669 932928677
    0x509030a0f0e0a0e0a05090607050a0219170c060702120a020705120106030203030c031215030c010822231603411e0a03140d0914160b071101 62
    0xd0f1540ea1109840c1012034840211766900c0062000903901048940d90001c0d10b442c1c0700745010f000c61002502c80c413080d0075101042030408400e904006ca0302c3d20404191211002540d11500240030391580c0e81301c20745501000d8082c00c0020a0182e40c038101301e40c0c08001c0e81d001482c02a1620303080c0814034850030f070420400e569035040840140c0e0240002c0043d541c2c540011500c80620710041c2c0503180000e401e503810742d4525480e81d13403140c40100d40c4c288281d000b401c104c49199101404161558102d00302200340360000d01400080019030041d0242c3c01c002030f110383c500e694100c0704c495a80e500a2601c5840f00c0e20803c4100001181a50391001c4403d8402418028501503074440d550a4407440700040031762030468940b0140ca0f42000b0701c000d4100c400e8007900046014601d40703030721016030342d0010301040010120b071121040d40400f16050354032141420450400c0782e0602c120140400c554202c0c55001c1c05a8503079400c42d0850045081e208207640e8245414440e6984c101c4d0030081c0c1090324140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932931169 1250 932929919 932929939
    0x519060e040f1e050604020a0804030513081c020f070b0301051e100305060f0d03080a020a03061d010303180312120b120c030c1e09090a0f060b01030509030a0f0e 71
    0x4265405881e44542080300f2400d0103446078004002903a4000344854003591041c840d41802c03641c49900c40d43c0298260078801e80d150310600100b131000404e5081201c1510035a0121079583c5000044550010003980c290307070745201d008002c0b40e220502403041ea5050381d0140010300c0030340341008035651010880c0707102410500c211408500f2000c0d042d210071002c039583e1410441241801d1a580d111180c0889a4841164603a40c0c081c00044003d04902e0000760302003407c28505010354400c20141c5a415240040710344c08000701d000c0301c0c0c000d0008400241c030302c0441403040b6a001c070200e4103817940040d60603542800150103e07080c695120321040495100e124201e503030745a0200b0261019065000340c484403184409151a22034210729041c054903031200c00660390f003a0442980c0c100f003070072551b494150700e84c20b514510340403107000050801066400300da0204481e40d403040048000a0324144020758400025036120f00844a012001c10401ca0340165114407070303509011000c030700820500325 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932932419 1250 932931169 932931191
    0x303161809140103020f0102010e10020d0209030307050d0f230f091f080114150906040513020c070f061e02010f0c0c0c0b0705071205010b06160c0519060e04 69
    0x351222452400c003050200b10050066050040380f10100310406c7c0000d00c804c140000a00e0340c2c0e241703d40e892020541d4046204580b0301800d07011541c1d035400c02011240c854045042440d04c81030a0090303940860742d01e004901100d800b91084000c1d13074242d0b504840312068403184448090780090303603000360010700304000c02c2035039602d00c0c5140020900103079801d120028907101401c00201a0004c0803070305403581086100e07544020b40c80b00d44440b03d00d001600c0e90310000c0424440c3c003958100952111084411070b541807110741c090b0200d2194501115a002e550315205072010002e40101d03030002e00404a40c03081d42c1103601440070880c10502c00000d1103031b074180c0305004a417100c60080d400078060061840600041c0c02c400c4015040e00721982c1d1074601c1d40d0303550780d81c0c3d80114440e0070040c1e4054072000092102c294003007480c1030000341c00c803540d4400720740310704180d80b0300804100e40c3c400d454200410141420300000882c40c2e013441e50a5611808e00800340d43c669034260f21a60300c6074450016040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932933669 1250 932932419 932932421
    0x70b010312030e0105061c0f02180415050f150d0827030106050a0e0a060317120a0c020d1416060c1b030912030c1a07030b030303161809 60
    0x200a40c02810300040308150118010709071a54007030090060b071704140a00015544001480c000202d00d5264800146100d1070030810000012501950280301300d205807840c4403200316004e20030303071141064400301540801c1c0c0d4804c1b101c094500d020b01400c4413001900741a0758680420800c00020f11003110316850395074003c465444645040c010481205c0d9480155407030160080700c8003021002030089908101c04a4020380180c812038803426003903004034050342c0440d03006501442d009440c044003003201c05100b04040c2d1044400c0000d2680c00340000d48290020301c521001840305601501c51540d852070b0895a520071481e41d19020705007045041524400758101d4042a40300e1900401c04140740b074409014080802e0006080c0c1080343d100800003644a000300081c0c45d00d0a005030310302072250600304c4281002980050840350350b100822601448090001c1c403a4880342e0341070180d03003a450107054481c002503074031011900c02d080b01032903450b0040d00701302520740b442160007040c7c50741e9a42e140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932934919 1250 932933669 932933671
    0xe040c2105100b18040b161e02010b0a05100c020402030717040c0501081003080715110705060109060504090f0b0c16030c051c020606010f0905280e010f0b0c0102070b 73
    0xb807039a584141455050820542c803846100c4407080e10303485881c00307848881030414000c10000181e9099402d00c031680703000c1c2003c03180c00050000c0703030306400d046100080d000344980c5001c248140c010300c030b0000e03076890400b60844c4a02102d684400312006c25a0920010f500003402d01c1c07007448600c80b0250258134027040c046d84128043c40d110012a0b2400002504c49180505040e070b074194800014000b00741d80781d0440300030340e6000842e400b80700065074186c00100004002c5c203442d90301c0000c3c04c50a210780050194141c9071541c008108060391001044202c40c004040200440c02406001010601c20140240c0c02603001c0c2080d40382255604514454a101c404101d01158203114807005200040143d00b8400020504000990744115006540d03000010146c40c1005001502b04482d01d10460b2000001c02000d04407074104500c032441c00e440300c0c4000c00c003001302104542002640081030340d0900d0494400d0014103102a050082000c42c03a8041d40e0138410740d40d0204a0300e00003075009001c0b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932936169 1250 932934919 932934943
    0x414042933190906060201050601050a0c020f06071406090f0705040213090e160510200703080d0e1b01050f0f040509190f06210302100501140a0e040c2105 68
    0x40090340f82019008011a0102d0b04040d00f1680b42c002000b0050b40c0000860380e1900c454181400c402c4918400509007043c40c02e10a07408c0400468020304105686000081c040140800e0381d100340d468003145aa100c50001c0c4c18540c9510000d010802400c0583c01002a01c0011100010301911841484180c8442807442d9082d0ba11481d045040380c04107902d02c0001d48011100328682c2030b000b120050103200300c04184840300c0a5070006100701c0034200710360300c02540e200062984424076010300b80018084030360311110030302a102c40380200d0342c0941c590900041d01616811b05001c0101e81382480c940140440e8040309404000100d02c3d560b6212110b481410504040a00035105e002c244e02920021920000d0a900b005d000b8170a03006810b8094426507144515002078032800c0c1012032400101800b0490030318501400481c407142c00b045440c8001764152041098269101a1910720541c1114043c01d66040200144001c45014500d0114110628040f0710a05169102c0b5800c202d451002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932937419 1250 932936169 932936209
    0x161b0302070e0a09020f040b120d0801050117040c030b06011107300209040605060f0d0b090d111213090c021005090304030f020d020414042933 63
    0x42000050045010f03034002c54480c0244194039140c1d000c242e0840226050318803a946624580c401030b00d031100d408594080b40022113200a00009024060703010070700405000940d0008200c10701092825041d010303560001c00642068a143c0344c1e208242405810603040244220240070492020800340024180480071600001c82410990203441c904499410403641032411500150342c4034003030350303900981001000ca02036950300c00182491a000c07034107950107601d00381038009004203400c6251081550500712400c001c4560400c0d9660400e18010054960080c4829681c0100b0074000d0019000316074000c08006403500e450780103440000f00003a0040c0d020b5211b40001e02e50600071180c1094201e070245140c9421510b070300c4a041d054020190049809031202c108545a582c031100144039010707100b8000b07080c40c0c601120f120b200c030116441c8000b41202582d41d0041441c00310f900450005c0c6807551021039040d156500d071f855105881c90341807414191a00d072507c500c1c0540001a0480d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932938669 1250 932937419 932937433
    0x20706200406031b021507020c04020d0603060b03010203132a09150f060207060813050a0f11030c0d0b0604060b0d09140304050307180608030f0307020f01050708161b0302 75
    0x500103080340d01c0104c56142d00a5030000c5103080c181c02007054003250f002c280c1d03038034580d5541d45402d9140c101407a41542c0c10900c0010140ca1101050788442e042d04d1242030240854005282018240d0005039001d50340c07001c1800c1400700007116400c00b80010b091480380803c8024550b4035034500c5501685c07002c480c0540b110400c50480012914a030054000c0c2c2c444041140d007080c0700259a00c10350700860080c8800040400d0300340002d602e1007103081c1e40c1712040300e910340035034a408880390210005c02c03940d900a10704c4d0316020f0714010a06180420700500b0f003071800042e50300c032000d6803c1c0282919411981d20340b000b007034401c038080040c00002165080400d140030140b520b05110101c00401000030f030001d2109000c5960080746030310403501e039200480c0c0d10743d080e050007800415099024a40078880011580c0040c441900078500c501e4454084c1c0e20b0b02522195450700341c0740129504d500180030703280003481c051840f10404041c2035440c40d1004100c401c050304450501140031064001d030344400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932939919 1250 932938669 932938679
    0x130c170a141003110109030503030c0a200d23090409240506010e0a03080a03020c030409021602040605040209030616030902180a05160813141e0708031c0207062004 72
    0x10704280d4031358828030304103508a1941d182c442d00c0707000c050b007800f1f41c4420005451084501c1a6a480d64070840c00a14034502c04040d05d440390740319000304010000c2940700400c5c0074059010540c0f011115040c56442c1d10b020007a508010082c28065801c80e40c4903940104031214080d98202841081089440020113040140015005400440d00f41c0e1013100003910600018092500356101c44500d4100540c4495595003203600b50700031604062034561000c15400d440400d1610b41c91a0b082c0203440801205131030f2010310080e4403410640703d4041d40400c022841c03240880b21850302d804418900000e01c0b28246c2c0c00111f00d0009440c59848550000062007907400d82440740741c3d04240e0307203480049a441903a1002d400c1c0c04004040d111710303802d0a286034041c07000d245144082c0520181c180c0c1d202e10b035505c48400d1401011030820701e05115008003c5501d00c0000100e0307000602c800303080c045241e442e001441c041c0d484804101c070155191303c1d26681e1104222032030011542c444505030f8884d4144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932941169 1250 932939919 932939933
    0x402030a1d1605031906050402280f1d0609180d0909050c030103030c030c150c23090a090b0a050406080325110d0c0b0315130c170a141003 61
    0x19040b240c8660090505071103048403146149920944c403800108092303803680001050a240a05140c1c04202040310004210720b05003c094180d402d1400c02c00d01c401e80350181e0318052001c0511100c0d070031200ba004620a8a003440003030754810b441582e03189001c0030884c0c0c450b003400b45511944000c5141e20105103d000c040c1d000f1a80d001c040400c55905640c51a24020310f04c0d011075501805021013080000180708140703000c540c170300070440800d0201c0b15403010000c0030724200785003e11107110305c081c43d0500c0f07811820880c0c0007030800a114994890a100040c002881c0b5400c0c02507210401c0d140004040d180d50040306c0051040c440907580710703940443c0c0e81c1a2a081c0400d45190556240511b10008800d481d105040050907500240346104a29100743c003019990442c0d10070000200800c01c24501c000401c1140c03060581c2c0a007074030701c01c0d03e2144c0b00713480b42c3c84d0704080400d920b0641071003492921080745a02c0307840e401c0045844071010006000e04241030700e11509001c001c01c400c0c400c0c040302c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932942419 1250 932941169 932941213
    0x27060b0f041a150315120102090301020304111804031d130501030606050123030403050a0c06060b030a11040f03030f0221071a0601020a110a0317030405120c030403020402030a1d 78
    0x11202c80303502d5441c204000750f40d030961250045119164412034081301d05408d505503490160b015000710365a00f800d0610400758035400c0760251162200700d00d640400f5602c2040d5602590341901d50400700000300340505512400900043d40218128110a000780154080c1d03d0095001e0000001c0c001e05040c0010011a81c0712000f4210200c4030b41c8062035490502d084a0b402900746c40e220f512200300c40d2040340e026258110241070a03080c0240841d4848408000f54081c501310103041004010101c5091880e00880c803820031404c42c42d01040011902031040143d02021510585400f07880b280789031064102044050340e9109008242c00042042541d5002031100601a80401510308480002d60303800c09204010174900c15007a0070000b945a084207038001d103500c120b07140643c00d0361155800b2150000c55041c0c4076886040c07001c800180342c40e000c481000a50f5806141703420300b9902440044d505c00b0f803040b0001039880c191501d400202c000407000c0105c0310f0b0040c0c000c80115841c1c000c24861 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932943669 1250 932942419 932942449
    0x50907170f0a0606020d080c09010306090504061e0b0d150207050f0304030501060b0301051e030f0a0609290c03070905060a0c050f070b270316060327060b0f041a 71
    0x803050041c1c1b01001d4014036000d5020f00c0140301c0700d5580a851340101d0152a065014004007402e2500f840100140794001d0244d100021142000340c104990750b0400303940e007143c1025000142003002c8004900400c80c0745103540f00d110005807802c0d6040c1c1c0e0311480c2000000b800300c0160000f140078010000203015036002084070303000407401c550606002540b10007841e1100d4500a1115504042d1a24107001348400c00c10300500b551400c0d0100c0c20b0000140a0b10f00040300c12a449914a54030304407120001170b00c86154054006141d5102001c2a800d0780c4090301d550148505207100045694843d802070810300a90341c7d81c214106003c1c0340c01884c0512180c10710f005a00320b034809105007030142d41a80e40c0040310103116050300c0c60448001200700c044800045e05070040c444441606003140441c00e0455203e55400c1100b0a944050f690010380c0821040003c2c2c0c5140f01000046462500030403002d25009024407104031408001400300c841182900c414070b10300c0c0c4000c01240c0b40070031110031402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932944919 1250 932943669 932943673
    0xd1b0603090c050613090f092607140c0d080c2116060b041d06090604030206060d141015060504121e0813090f0c0801050907170f0a060602 61
    0x6201c80d503408020050b180200d80c0a9440030500c0030001140c03080c201c0080c018000c040155403021003050002d09445101903401d07560100c804640d01c180c0b05080d41c810090201a6801c14101c0d81c0d8411104240c840601c0300e5220381d036814040e0b40e0f00c1440001d4194401c0c1c081e5a0b48200700c1c040e0a0070010080300707071045460b6410301d00b114000ca03401251240840080382a8440b40340e443d01200070002440341035045842c02140c0922a400390300d00d102000e50b000304685103545c400190642e100002c42d0010700582000021030420301305403883c0c03103849220301c0c4401c5245800c0002c26280c524294003000b1810303120107a90b00310710084036804c030203040b00345405490b042c2042040020b6030518a4000d00a456440c5010102082c3c054003a038131941c4109826030b0f60341500c004101001142c001c2c64000c0d45040ca0a054001240c821141203194a440300d0311168688800c00000e608010f00500510a8101c0251040503059002d944a00d0090515041b0780c10550b41c0201100d1080d04081c0940d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932946169 1250 932944919 932944931
    0x1207141906110306031b0a08010f0b0301110c120f040e0901140601170115200a02030705060301061b050708100f0605010f02100c09120b060103110f040b090d020d1b0603 74
    0x5d46000c180400070001e8003921401200b00800403d00d094030700d50003400c095107800ba11030502001ca410a10f807460044000744910082d14440d07004d039100d8080040c905d039200306416002140d004000d0400c0001c10440035040583c0d400c001900a50121000d45031659191602401c0005109545d60080802e282542c1000f406400000104406000355200c0b9071207001c400204520991a100d689100e13034800520300803002405581e540001c1c2e200300d200f401220000b2034607062506c20f40c0d048810940e81c40000d201e080110420311506600b050781e90b070184e0803002c0b601c24410400645845910b810004000d0080c40c008000c07100e07550806410407003800e0710700304003990008042d600603521150000386486c40180a80740c010f4541c1c004840301420f00c0c4000305211254021034414002a00c05000140c00303240340900300e108142d00d403102c1c0c18051109106d00d007917010180440f050007620814540c000c540014054006002d4202c5004070034916a010940902401c50001c0c000e81c1000d000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932947419 1250 932946169 932946181
    0xa0203041e050a1203030c0e1c0302010e0714090901050606030c0a0924020d0305220609060e0102030403110111030f0919030207060f1112071419061103 67
    0x12881184603540d000c0050341e40c1d041072010024021030042070010080c4004950301e00307000076000c130f80c00303810b4021030715040e030801040c1d001e00c0140d0140071001740314040148904900810721104100250119940c3d92007921149108200c100050b00620070759284101002d0100440329000a003805600d0341050284407042e141d9105076508603000d0400c454840f00071a0003180d501100354001034205514480c400aa80035126440d000c0c0c050719402d42d100712118010135400d8500a0300c0819014a1405154519090400c1711181070781c231803000800c29003035a0711100c064404a60300114281d6000040c8010141c2151042d0185a240320080c001c0d080b5001181c5560302001307045209041107480003590b0360b2800e00040f40e20b0250790514624a02041c01c0c02940c0d00114040c11010640d000c00c0c04406501898450b0010710524000b01442500d145010480740c00505c0122224013064014210b0a1801e00c50200d9843c03200088030003200090624005583c100e11842c001c0e04800c10a2101d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932948669 1250 932947419 932947423
    0x10e090f07150e0d0f03030b090a090b0712020c0601140102060f040b0423010e0132041203020c0709150909081801021e0a0c0b310905040302030715020a02 68
    0x10075101c8a080c051070f0200e44030045007071a003a29800501802e200d00a1108168045e44040341c41d12065944940d10395861829600312004c40101500006200700041c511501c6460080d83d070010015026043c041c0401100d0304c1e094013070300001404001401e16a490356410813100f60300100d42e2002040b1400e158940070366482003e080504001103d03090440c03002480c0c010554010402c6008012030071007507200364001c044e400c040c0521131030000ca96540d034500031051030403034540c4c00450b000e40d52540d5883d061507141442c04807060540a02044002000130700c8070000030041400d002c0780d11000d0740710400c4c0c460010380050400760b28200070703400030500c04015101d5010042404152000348000141d14055089107410455041410300d154010341c00304444000900c503e44840060b0b032684c000078514042c158001c0c1c08440108140e02085804041545d441541c00f100112015200e01000702501d40c11241900980d00009441040000d621403810105900310800c508124250100035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932949919 1250 932948669 932948699
    0x1203011511011e090b01050102060603120903120a0c14010501060c0b0702010f0219021203041e030c080a08091b0931060e0d020303040b040227010e090f07 68
    0x40401c841e51020411100d425880390f94440c1095102000303a00144018101508881000301c840104481c00050035500000304280a01c100401400f024212540d0f4004950400303075a00764140710711082a10030442d500000d00d0003031f05954030f01c2614002800d001c0e40065441d0003100250f03250100400c041a4010004014143d000c01c3c0744c80b0360307120900120b0142c41c0742d494250290344006510100400d40705081541ca10f8180c080d80c469004242c045511408212000740240102d03000001d51001da50001d80e040c5840b03410b248078803010b503454540d02500710803003007000308020206028801d8000c0140050118207900104941e0902e100404c00004001c0d140b442d01c0d0060318040c50404051131107007000842d8107040200341c0c44150910001a0a00602c800245d0045000c541e818034404011240300d40d4010300e0030f0341e064440f9400d0103031042d400cc8030040c11070780e00d011000c0d001030441c40860081c00b12480402090500c03d80c040e050612040f1003c20340d0f488803400700603010b8590228 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932951169 1250 932949919 932949959
    0xf140a030c0605150411041404060e010e04081e070605010e1603050c0c030c0a1a1303210203240307140904030504080d0302040f050406031a0a0219020708120301 71
    0x4109a198603c1c4e181d80d1400c5001001da2144c1440801429030400c80064811180c5444504003403009040902046444d03501030b603028610908014440c248039000c6a94202e44604086860020140c0b00c100071010340c031000b050101c034001004801c0c08014081c55000d40180d0055035010706215480d01400b046100c1d000d4181906c8500040440e5059003c1e509907400580580f0340e0307440d40c5c4180f10b03118441a00708840381400b0080e1040c0302c1c803804400501c1085581800d01450040c1d4906450141120b005c1269136086509454400350281c0041d60040302c400380c01c601c4011070a052071114621720501d450299220070003c11840d9680380c0c4041c816003042d588080c1e0b40c0c40c0c500b0300300c5503031003584c0012030107103c4c020612a149500d40d004008842d811f40001443c152141c0801059803401c4c40080c4c00c402010900401d04000f058003240c01c880300610052400c031503054080103845401c001304001d6048142c0c1000b1000c001d2100c80740100c40c26648030b10355810404600c0440ca00e081e20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932952419 1250 932951169 932951171
    0x602120117030306101b150f0c1202070206160f020102100c020d110a14060708010801060b090105281101050f1e07020a06060e0919020604062102070f140a030c06 71
    0x2050085405001110b8458414040103c1c05420074104200070340d91140c2d8581f01303540f42420312110b0380c0003407044150407891a5a209a0f01c0030b1350702c40e0340c0a50031481e800e9920200800018405400140103098028483e14030301e18405c1c1d03036000190800031030b6003142401ca03080c840e040020b20781c0464245018100c6041650b5442c4454241614001c0d01c21402004071060312010410a800003520342c0c880c2d0199540c582d241d0b87c0395180c41d0700740c0f03c040c454000004000e1118440940c0642e0182031690207900c400ca0f91642e20307070910352246071884d41c0000801c44034000c038648500203000d183c0e40070302120054003085c140703032030311070081d07202c84200c184a2540c0b0f40218080610a00403518110741049081c806c02d510f03236400d0020303041d050303a48051601c00c2c1c90a080480a014540c000042e400412141c2403902c0c01000361002211410600803140075103200901200892004e452030724007503c00d102104640d8601400000290410151075038040a1035400080e80840c2100c0f1107580110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932953669 1250 932952419 932952439
    0x40513051519020711030a05030403020a0609080607030507210b0310050609010504021e031e010503160e0711071814040c0308090d05150f0c0a0507080a020313030602120117030306 79
    0x40213012121714240503541802506e04401c1400f00c00400b410075a8000c40303041040c55920f074400d8a24010900c101c0c041e541200000a40c503138020341c80207521020a0404114120a490228242610314015200752542d00c0421003078504080018610107507200c07504008500b425800100e10210510810b0700c50740c0c00142c450100645100d2040d13640d8207450003540c60741080c903c0d10902140036010104002c0300c00f00001401c0c82c0000d100354000c0503610310200e00a04080c485040440c0c014199401d20260101154610804002d00c000406140c076030b000081c0004a49407050303460100c54100c800c00050180400308500044440807644d0180c0015a15440e000c0400d62262030480090039501401540d841802071031100c1c1031007441c039079806418590741d040188450b03000b5100701000044050111000144508008050040c058011a800e001c02a4001400d440d11500200d40751600411340442006100b00540d0140600c9014035004a0001c40f10b00d0307480c040140344d24441d010b201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932954919 1250 932953669 932953673
    0x103803040303060f08011b0507021f0e030d0504050a1517041509050d080c04080a08030604020f131a070305090402160507150e0f09010e090c0405130515190207 70
    0x1a10039801002d150784085000340c3c2c1da64601b4020801a40141e44401400b48050b0000740700310704403006c440d4003d1200c8655940004203081045910700d85000b484081e40092080307075020032491110700405e5880d160f07500d0900c018841002c80f50381c00202e0368032018041c2020203400147c240d00786401c105610034140d980c0d080600c0d511240c2240380088520301188a400e021011030404984030542e101c400503501c0350000910a40b1851049040340d03040a03400381c0000701c503100215080b0500401c050708000714154414020f6009448202039210348100411140c05d030203040d40401b40700040d071743c1c0c1400c0301e6407005045481065403040c451940060600ca10b400c6120340603080c2d98105c400c4030101c0b030b00c98107a80321080034108100301013108c0851311452407a01d00c000d848014009007410b41141d00e003000135415890094007580250003004440c081949951003032034840c03c10702c011020294030b907003091418280c00d20303080d447c202c180c507042000702c0c1e180e0311048800040b25007006079104118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932956169 1250 932954919 932954921
    0x40608160608100914041a010f05010c030c0c080a050616020303062704030f091e060e0102030408010c02030703121a190f03080705010506101d18103803040303 70
    0x40c0c0101c1d054a181c07086280d40172408040300c920862252085403000c602c031a03211031010300300b40718580180100420920581d4401d40c0c2c90300c140c91103811700b198420282c1c6d0b41c11104141a40052641d90706c088000401d01504200564220200001d400801d17481d10310002c0d2644001048540103a510040c801121111803003480c0410380044901c0310300307050500c0c005154010b610405800030301c800700c0200354480c038803035800007003c0890320300e40700280341c440c0641d00e41500e100c0e0781c0d06600061100141140080c0100000744c902035010f15581c04040ca0050b0200019421107821946021600d0956904440c000c50003840300711284200c5080041458402c84025001401c203400c2d444000003c10600d0006002c1e1740e48150020710103591000148141901121407010004002c04900c0b5065422426007a00e205c07000380c001004000050460388800c00c00342c071125102c1e42c1c10f0104014110700e281a00c2c01004071082c07440265003102418860411100c0e042c01d1140383d00002260425000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932957419 1250 932956169 932956201
    0x50c060f040608061f03240e0a0b01052208010c050903060415020f0c07180506011202032a0c0f010c02030a080c1306050d0e0606130e1e0102040302040608160608 71
    0x10243d400484417900311001800b80904844055a1001400f1410303084c5608160b094140c44144e086041c5590360038155a01074100e00103c00e0600134204100c81055964007102100085e594220482e464600002e031800c407260301001d0fa042090138040c420381d5560104956030000d40000150118803040c1d150355000703209501034820340f400d002480a44000010403d107003103d46044801c0018000c43c0001000d4400440d000c0340020090568811003169981c00f842e004884d501c4415407000501c0000a000030425018446100003c02c2c0c0c41039101042003642c002d000d4000c001c2c4030582c9a424080c0d41ca000305444070091149800005d95084040c0c0d05944101a04032003140803940d9a00b4080e10550101d0000716000c3e0528100000e030a20015649015480c00382c03e004484400d040d5100040840014160450144940c072103407100c1d03064404a05a16150700059446185104000448101754030940032a001003141440b20102201001e04072862401d000c4c0780b90352405803409540007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932958669 1250 932957419 932957449
    0x40501110307020c010909060608060603040501113405120d0b040c1e0e06041502190309080f0105010506120403180306020301030c050d0c031104060e0f04050c060f04060806 76
    0x2030040100a6420760010b0303c0300680000b81c80700c900c8240c0703426824050b1401402140d002c42d0b9484040f810310300344440203560090294000150181084d800120302e03621200c004406401448240c09503050349007442c2c41e83c0301090140701e68046070303940c49640f07501d2061585495551b0210302c001b0b20b100241c20415020700002d0007084100c52080000e03010300542e00060290b000b0805450b00700324010640d4100c0034900034061070810380740401019514007040c002004500a5903904071000e211445401b80e41880380c1c41d211034507800d195003945414818144041c41d6814803004108607100d500444407101920328103400342d03981d00d0400303580040003500b0075120350088050000034803405070301031411b072403069410003040c9940d2010032014041c0158060404051003d04000040f03103140900709503400600f01007206c6683c1c01e4105d0841101700d0342d20700d0f0b00e01e840d82084204a401d01401c1c8241e94119003030fa0410303102504501c11400744d0f008240c14003110f4804509140d90302c540b8958201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932959919 1250 932958669 932958701
    0x1b090b0a0e030f031e040e19020403050d021b04110d02090303120a05040203100c200c060705030712050a0801150c06050403020129060d150f0314150105060301030b040501 75
    0xf079104990f92a800841e45850408684a0601402c8460b004075021201140d442d5600350b01d07200d00e6940c240018011b14614580e00700000400290144850300c140d20b141d40280040404041c00c2c184c1210140e84028403c80c90702c80400211030054050315400e440034440140c890003014040703403651080301c0c94501c0c6c0d69081c400304030901e2055048580b00e280700f5030603500601c00c1c0294190554105400003004144c6421140341070b0400c0c00165003101601400300c40d01600c81d00081f85c1d00342d00c1648241c690350400544801448556400e0000d2807110380b0b880d615090741c03800018003a19060290360600e2540b1912460402c0c401c1c040b071044250448000c2080382403614020340204480c289844220300c8951600d0b01303100104c14204611070014101c0c51400c1d001035042002000700340d954924000300c4d850301048400440040034007440c407503000c0da4202080040002d03d485204000f4080c0317504610014403650301e400c2d06880c1182e500541d000c000e6202c03890304038090241d0714078200d104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932961169 1250 932959919 932959933
    0x161101021b0304061706010e0f01030605150405040e060f220501020a03021803011b0309020a080304031a0109020a41030105010f0503150f01051903020a031b090b0a0e03 74
    0xa008040010001c844445c0ca5181502d40d101000c189402c0c07040b981d0301d02040d43c60780010510b0034407144515041c1d0051500255454880c0005406045107580145081c40e02240500460405200e09410f841e035100040c003152402002042d01014000c200b481c1c0b9914008503450420720000d1100d80041d4000002c1d51a010a0200140203401c00d1400841403031101c180005641010310442c02031400d50100f10800800c4074105801400c0e0703104040b0b800c02c0214000180c408404c3c4003510103580300303480c81d00400c618100310340b08140068000d160540e20411019604030b070404502d0800c0c0841011214024000383c503104d280400c5c3d403c0403440080c0403460490400341c440000d5041c0e4101f600c40c0031034241d00751000c0300d241c04100da20f00280c1d400f03000c2c1c071801850f01c1f0b210841303135080500d4038a1600c040c510104040381c0b07460103000086600442c4040c0c00c143c06018408200d41200a06103d1603143c0358018a08070451141c0b4003140c100280540b51288a554000341200000d400c40d410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932962419 1250 932961169 932961217
    0x15010c0c15020c1c0c0506090f041d160b040612062102120109081611030f010606020c010804121d040603030503090705040b0612060d020904050d1716110102 69
    0x80b0100b0b112003e20440c14984c2200841c4820b40341c1c900e5580d00b20301000740c86402c3c801400007a81c08070031542e611448004204c0c4c1141e59902034003541128103003100d20341e14554150b940c81d0031100303849005500110740c003c3c042c6140c0b40c002d0340d04030b807154a403480005a61540c000c0007082190011030921050b07200c07180341640d0304004e00344020310075204c0700f1040849c0c0440c035080306c1c00c4404c000d0000c5420003070300340c20b111201e1700401428003418407007500b25080b1000034909000b4589480f2143d4440c6e5080101e5601480071340e014901c03e08282078607107419030790628581c0003440c52005100f01c8980900620180506024100714064000c208094a1f07007001703001504207c6000c0141d11034010041041d041502901895034800b601c018140207801a050140c0302c002410103030000148001c00001d03a0300d007090b8174000e42c001d40c06003941c1c0007078a00080801c41c02c9002c4000d00213030030f01480700000c075100c09841d21030140e2030840c85000030481c026000e807280300344800480004c1e04004803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932963669 1250 932962419 932962423
    0x5090606093601020910110601050402070308071818020d050a06030537060603061b0e1c02090106030c021b030c0103110c010c030c020f0615010c0c1502 67
    0x100544046810000603551542c010075a161000214000c001004840040c2c64080300403002001d520000050f082c44c41c2d031408070b09a010311090200c002820049511464801440614050002a41e0551800304c0c50346019100315070107400001009000c80b002d070810482c0300140300203070141070410300002e110130390070303101940044180700883c0745444040390b40341c00188a0401140da000028000c104200c2504d00c08150700c820f00c200710b00c6080e0000c01035030810030a1001c40389100d100001030490a50400104603900518040744076641c900312049a41d80145d0034040300c3e00229200c0d08004008820b6080302a42120025000340c1c5480c004600300b0780541006d080821035501303d80424115480750f1070020f407400300c82605600031000d40703802544240c0100d1031210840f81c1c690b2424620f002c0d060300b140d204a2100c00080ea03121084030010382d050082c20410803a00c0c0c000e00c1d8034280804036122000341240c1c02410b111803550315608205505e240d2000400c540400001064040e44000c0c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932964919 1250 932963669 932963671
    0xe0f06040207241505100f022e05070e0901091505090c03041106040b0a050912100e060105010e060f03041a040606030c0e0c0901030e21091309030f0c0213050906 71
    0x201d0081d0422000700700b1508981c3c8000308580c5d0040880d0303450202d07541c080e18400381c2240324900318058868000d00d1124960511044141540c4607500c1d15904000d01c10f080b9103020b80300d00304014050803c1c003801e50358402c141d410364200c901d00040f20010400f003415584220750101d50082d0030041004070300c016590146200f0b0b409180d4a0f14011241d408106681c45540140700e0207600611507030700f049100b8405080100c0c0e010b0501e200101020010a203480030394120780303403040d885030846043c0850503c03405004280030f00b06401038800007000101c003400f4811401c12004d1020001400703004440300c0e80c0c20b404800550126007410320307007010030161049000a130360041c07070680001208545507201910170590304c40402e05010000d03004602516480c01122014400c203200c060b07a103502d0b517400c451085466242540e0b1002c0507401c1c0001003202210003081076107003c003186e000c41d42150160095422610301810400850310005090180d60900e40e01d02920708420000e801304002403403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932966169 1250 932964919 932964983
    0x161b0f0209010e040302030a0e04060e1305011103010f1719080d0507020d0e22020309010b0102070801020406090b030403120f020c0c0d02010f050d09170910090e0f06040207 76
    0x907110a81e2560202041c0d601c05560050040e441008101c20885c4079000520713901d000140041001569122101c44402c01a5060007001c0303c0e6072503010400c442403207a1240008010b4040e81558901200090100250700c0f809558521003080481142001d000169690082014240c80f504950802e01e03000d80100101d180c9071403901001c10f00c0c030760000440d404c00b03a14503680c1d84c4003c01110180141c50b40041c4ea4804d42c5200050300c1160b280351800a5807145181e0380000540f01d0111000915001190340040c10300e0348108010f00c1100d5100b803c0e41c0641c0d421550300c2c0d0792500c540c039041b82c01d444403c290031240c91405044442e00701090f0018108c820208c0c0807121004e40303c00030030410361181c0070002d0104010004c1a00e20f0350040003e402c210f401918005501e03010390321401000c840920000214400004182005181000303043d071140b41c0c076107410300c0d07080d00300130031814110809401d0584501d41e00d80010a260703078540458449035400031100d40c0c024240900380300c00c10180540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932967419 1250 932966169 932966179
    0x30305070b01061805060f0d050403020f120c06040605250c03090b03060f150c03070507050109060c080d02090607020301140106121a040b0a12050d080c040e161b0f02 73
    0x21694801c280301d48184040c1c80d90304c0e0040e450217007000180c0d40300f20000f0041003400d0003000303078000c40d510505200b54002d03005880280054401c080c00e00003640807412510006205589000d80006020755103da07204000050940b1fa44411020404008190551b6a040c0803e0f6074101680071a00d041c0e003074401d032115480c40782c82e03503609501800111840d90300509103217070700201450170b4008600172a080c44d14a81c0b400000321512419a8000f0400b61040e0340702a10410465902500715402460030f0304d8403c41c1d05140b995814a680f1805813012421a000300e09484103941b800c040316161940100200600c1c1141c50149034460424403860001c96400c10344c0d540a00100c1c0520717218000c0c103616800c1c3c480201c00410000340802208550803c10f24a000720307501443d40f007401400390141c0014040e00380c0c04070000300250002800e9152170202408100403081c850301000703030810b10b175520b43d00300300e01c107041c0407208811400b421400340a500d05403141030046141160700c00c6402564 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932968669 1250 932967419 932967421
    0x210f27060b01090302030d181205070f08010209030a060915020307020d02010f020a2a0b25050702090612160b090102120a090b0d02070f12170f071d04020301030305070b 74
    0x10740f940b400c60311019401d0341081c040300034100e12400c00341d080006412010b100301a200d84070f040c07600030307081000c0f1a03070b40c404002131002e00d154619280090889100039460305402c1c001194465240080003040d480d182c48500c01004880000c4c071100b115594011901c0f450312110080d0359507440008440554a17040052606c011180200c1d0a41d13800e5844142400311030500e19040b00700c5c07041603503943c0005c2c46032030340c0040c100b588400e006425904034880f02c201da03071100003000030800350750005010b070821110300141c90b01c8501903402003048401d543d0200c00403035150305100c2400a1015138811403140860000303004130151104920030303801c444280c02110118407040c803030106c052020405808041007115400b60003003200f04011440941800703070950303503030a5111401c2000c83d10441e000005084046d441400401040288525125030b424610210405090085c2590081251613a1104040e0f0b00b403403422140070001402c115565039590070010b00e19040711408840000041c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932969919 1250 932968669 932968691
    0x60905070c0201090614040f09020a021608120304060e070609080d090e130507080604060b011403070915030e060411010801080327041112010510210f2706 68
    0x148203151a40c1a1511130016040071001d569030781c80b050100310340781420000410b00400d45540000141000400980c549000d079102904140541c8500c0c0366107140350904001c2d00c10001075002c1010381030b000069503a1a03606000024110710f0707400d9a8a4828028006a22944561600100cbe0070160589080c1910450b00f2a480d8401e40b1800d0751601c02180801e48012101045110b070b14481d1302142c0b94580c6c0c03210b500707060940449094030000d555042c103403a90350f0000303050400d480d284802c0c01c0c074601d80020090003120f4280103100c04440e00c0680890802d009501240038000000c003201c103c1d10b01403170b010190034010414076001903a03180000610315800411b50b00c01484461b0489040d8421240b030502c150400c0d118607a01588842c1e010071a5000701c402050031228801880e2055810300040c8030000320700c0c802400420481160784494a4400032098001d03a00d0740c030010580f0080c0165440203095030342120902c2941c040c0004e00d005038000782c142a0948100028441c540c008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932971169 1250 932969919 932969927
    0x607020d0512130c1e09020f0703080c13180b010203030105090c09220b03010605030c100e0a0b040806090105130b0f0907091e0b190e0903040b070606090507 69
    0x42445400481d409004410841c0003003003049a1014403011240b00d0300090b51514031030242590300c0031450700f004100c030f001c1c4003082890b6035010300310804065183c04003280c4108050311403100060300f00241540480c802010410480707007000744010100820b00c1e00d80407038402c40000005242103080c0703803039420701c455400801603a04841008060508945d2001910000c039071001e004c0c1a80301c02c80e22650301021482162004542d0080c04000035200303c014103050845440c3d40025109511480c0740a441341ea440282d00040c1007140f42120039016400702040080e007080d040313180800c1010801041184001900e580305610060084c40161110a0302d1300c8040261000a000c4194401c001060080c0210a07550012030000444902c1e80e55038548a0482d14041c4100b03080440c00c159441080069000e80b0f41c2c0340904548201c070020005005405c850103c2c0700c0e182d0030400a0000030701c81001031055600603c0003108469541945160000013040540209101240751001080003a407103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932972419 1250 932971169 932971183
    0x50102010b041103060d030525050c0306040512130305030f031e010f090908120c030118060b19112b0302160305090d29011514070804030b100602060702 67
    0x1883c14038680b107400c10301000d440108010b82c00d2040030400e41c03a040007540b0b80c0c100100f000700025501030400d0710300141441d080351207292203503210310107100c007158001c1150a4100c0c80900480da83d2500f64100049a078410343c405001804040b80c1c0b400500021001175204020b0b24039180c070100c000e00c0c2d5030000e844080c000c0c80f414854050003804a200c0075445601454004d110050070b04074040880c00000800300c403c4200c9580220041100c080c003108241b5482002e50014403403141403290415040c01140c9807000e40c07440f40712044980d030b03014409044182d80c0340c000303480d00703000c486103010840001000801e6142c5001a43d00c0c03042803182c400d98070702d0703a0310b4007aa040303c44260710200c42d6500410011035200101848020001d20075541055003140c0e481e080494880c05a030303003031841800583c80001c501e181d0400b000340d1030341c1c07050181c090902c1d808440707900e0340900e050401d42805250802003402c090b00c800e028054032079100290445001d03900720346075951005400ca85a1030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932973669 1250 932972419 932972441
    0x10e030408120a0806091e070f030c051602210d02010c0e01080c090103050636010509040c090f1803030b0a14010e0d11151e03010308180a0816050102010b04 69
    0x881c070081145d42c40c181c900f030b43c1c00c5090954070100521001299585180050f00c0a401292806410100315a054002c20b249071140d17003009030611014580d07030224007a41c06002807184403c070681c4080046d400c60001e60070b41d42d04003102c2098450400190083c404c105071480440c5441c54440d4556120b480c40620804010302d000d0700302445200150094140a0003c0340d202c100d100940807411422620283c01043e50417500b00c225000f2104680e941d001a00a18003c01042003000f01052010501c0400c40701c1000000440e05903000940e801003a103510000340341102d00e210079007850780c143c00c4079104007030460780807205540e555400840101946411804034400741000c903014588810130070a1280a800e100c43c01100c9100060800c0d0003542c001e40503880c0128500c20000341d4016090344c4c0144480d40717503203154150784880c10b00e40140718103030100402c042c030076601c00d4070307a09640c0b0002c00400c01118094114004d04025180141c01000c0c0150300e0b090341403030340d460304d4020180040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932974919 1250 932973669 932973677
    0xf110309070e2a07060e06131e0503071401060f060801092f0906040b0f040f0b0408061302040e1e0f030f090f01090b04090501090506040c0207060818010e030408120a 73
    0x41810f804800242c2280f07405032007003940c0e041c112168100921403140300d020990301400d044480c0749802d00f100c0f00d0f05018240203100381c20000c1c0c00101d0010413189003680004016103504044000389000d4240c5801c000b10b420002d071400901c094018412a05a9803050310911169044000012030042200c01800400e420305041c10014003d140082c0384800e00034010364a0191101e41070325459220188101c520b0798001400c1000460100d060343c045e10480c50300c2498585448131195a030100500000c06915900131a1070865440703500c01d4507001003040554036410105050041e100410101c8411980182c6006084552020040342e40c40e42c3d6800d41d0a050010b62014011540007824940d810300c002d14601040003a281c00180c0001c195034180030800d903060081c1c030000c2da07001424482c00342d410701075402c00050700401c0d41c1e001e8800501c0d16a255a54910960740810700841952007503510f880d0030180b00d186c0100041c8103442c5400111540c107281040301d41554030518002030700107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932976169 1250 932974919 932974981
    0xf0e070e01020c0f102003041d09060c0d0b0904050607090621090305130b070215180d020604090c0c050f2a030a12230301080304090f110309070e 64
    0x139190905507610fa0108502d8843c08507125110010200958049210026440400d003080342d1241e280c5400e20002c86070942e00307410300703105070100d86c8e80501a1606d0400c2c400030604ca4481c80300ba51000314a00b0000b0810072050801d8100240c507040700b07440710000680c20b414081007207802001035100c10b031074440003502480f00f05002e6270300501c0c520b94200d007003000411074914401a02d0307071203801801ca81c000441e510303026481005900442200d81030155003081c0700030184800c03c40920150f00c0400d840000313042646100258083c411a007007a00140d103400182c60004d03600240540c2c415100700100c0341070800c0d60034055501e804500c0005124141c0c00d509c420550385610b41d0f1a01454081c080311440c841c2503031f0301500e0120032200039000408400040c00280c10942041e0209160580064659410049419241d01c210701501050903103070100e95113660082d42c4120070541c0080402c07a01c9080541d00d203a1100f105110b0a0300c540903c002107142c17480105210142d19607801e1424080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932977419 1250 932976169 932976199
    0x30309141b0d140a0804090c17070e0a090519050604020c120c0a0f0819031a0121050f04051203090a1103100501151211071b0f0e070e01020c 62
    0x21050341118101c5400c008010301102403001040003c1c24148105d09054495051400c520204e0307148264900c1002010b241c42030380e036410403442da600310219151414043c00000c000c201d44001c9540480d400500e890100803c0200c22010340400341c116140910003900c910041000fa0700855842c0021504001c003206020b8110400502c244c403400c4080d10a0420b40ba213441d482c200c0e04d180b081d0b03030200380091841000044200c40c01558015130804004c4e92501100c581540c02c000e050780c03070501100a01495021504800076035400c20300c2c040078050362804c616046000c41c002d541c03c43d003a00c14284180c031b495002205072481104600010401c40700309403240781026100880b60f54040c0900d030b0303546151201c0e500030a4041c03c9182005040c542c00d21100400c14614108100c545606c2d129600b5a40c012000c21034410980248558081e8010075150003980806076100c2d03200c442d20203d000800d00c04e0f1720360452088520b80c980c0b0030801d01e002c0041e0384401c8100c1c440c55014105146610f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932978669 1250 932977419 932977429
    0x90327121501060e0a090c0f0e03010c02060c0309190c0306060605121303030b0306070306080d09061706040b030a06050103110d1e08090a080f0c030d0801060302091c030309141b 78
    0x382040700401d0098140d96a8074102c00b1140c1ca502c080380080d040c05810323003600303401040c100707030080059008104103400c09000070f40b2103c0180018420ba0000804100383c10f100f040480403004030003092902e1002d45183c400c88900241c4811200d01c5d041c100005116030140066400c1c070484503001c8490781e0384002070002410048a02282030640c0c07180c00604549003041040d10a10046d100050a1420300322864984001803011004025035480107012195010500682c1298001024078890312410001070180c00042d00d22601449546200c41c140201da4100f00c1c1240d000f007003040d001c124644244510362381c4910020b0916112110100c041d03205042e1729041480c040d08400d824419044001039141c460396001d4072041e841a4260032400b00b0a2100c41e0415008a0042c50f4903d030f809005804000c2c14443d07041810b5011179901500d4940c600c0c407650001007c4102403034900c4520700a001080d81c203400741c81c1d084a4101d903c401540006010b0b41415482c25210304501c50a02004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932979919 1250 932978669 932978687
    0x6010804030e0d08070b0a1a01170a0e2d0105010f0501050d06210201021203060315040516031208130309120f0c0e0f0a0203061809032712150106 64
    0x25800603a00301d201d80c04962441301419246200390203d501c0c0d401c10038415800c1d1481003410781a40004c840c121501030381c102c0c0d55101d10024a80d5180210340c0e8258402004040304150460300d8010301407c0c0c3d59503400004100381002a81202c1c0c2e40300c03403000303031401c6c00c2b50403d0041c00c546841c0d0350418032603503000788040c080d40c4c840d0800108815842d05000018182c40040f20b010b00e0101c50301d000700319070701400143c01c2d420820451a09602c0c00400007030ba00c40c090030020584008220101d41440024005001941c02d401501c3d200d8941e00d00d400d1007440c1800c07500b43c001402c0c40e000700b9545400100d20f1498560191760310701036641001480e4201e00c0d03601c0821110042082c40c0c42e0002245c91014500a01808004034420310b0900da031f010890100801c944101e9104004221740c40d0303100610f031402d01104003200c0c130550399680307455440d6220310b4103409402101107004000c40070b2805401c07800098241c800b2441c409031a04226039640003403800c010b0200c0c0000c0148034561040440c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932981169 1250 932979919 932979947
    0x9210204110c07150e0913080f041502060f090c011202090301060f030c060f050c060403201b010905030d080c0702030312010803090f09061e061308150c030601080403 73
    0x403440d01c100d5a00c02071425440e903000a034420a480e0030b4130f0300e0030342100081006010503600c113142c42c6041c0e01c519484001c13024004103068000300e40300301c0c0b4a910038159005800c4402501841c9040b180010b90703500f100f02c03410b6800042d1200012100c1c40082809102d00340181c6895842804d801540c4002c0d400801040740c00d5981c0d134600007074000d080320030700c00114010440c0118450903c03600900360180e403400700b0188281008083d01c4100c002900d40e070301c9601840e14110101400611607070142e41040c6078407462050707040300b550042c1282c2342892101c400341c071682c80d2903980d04249611015501c10200105986d800020f03040300c0c00704000e140341031004080d28580740e40c18464649030b0030280c1081e82d03da800420b4040b65400c1172400b900044408a45014091501400107008501c032040802d02a404007034102c145900d41c9000c3d56450000108a541c83c96100d004e02a0340e80c0d2000c0b02d1051511440e008554440503000460f801080c060759104050f540b0381e1000ea440304480c0c181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932982419 1250 932981169 932981201
    0x15061b0f0203120f031506030c0a0c0609020607110f1903141203071106070203070b06100309021c0b060d02010906050a02030408060a0c030c0807120e120307030203060109210204 78
    0x520650290307900c0040c01034031092804035845c0d007412040001c1071a207051a19004031410014044035a0130541036944069051910141d401e0592800c0c00252250080017900004003041e101d0030006421103105540310251a800c4045d0005000c00141c496080c0c180b41d03400120300c1081c800701d603c030843d500071220007100b02d0b4144445825900d070706501c119080d400040e41c00c1c2c6840340103481480a01c4c0c01110602c0254206805c4c2c2e110b54081c0403018106520400301c0303000307030396816010350030030305200350010680d0712202e820b01c4000d020543d08082c1201d1241200d0300207101c0d0710300003410020658040c1c5da1045002e040040503940e55010741c901d0f000307510090100080700351080103030360b01c62213406201107146044128040c0954065111030b0302448160420480034591020410f04a070182c803501059424a8241d00c3c1d0500549044540b80c00300000100075145405800950140700c0c00e03652014100e50361a080d1505407844860103070303100b07400b081c848090715081c1c004403445554119 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932983669 1250 932982419 932982433
    0xe01020705060901140c040605120a09060f3303060207140318150304051c030b03250807140103092d060c021605060a170a15061b0f0203 60
    0x166075140900454440000d82e4640346000349082401e80c4840d084100e1580c00f90400d0b0411401410381d0152069a068080e5820000f8401e40c0f482e4104162054224608114400c01404000b01420040814100b8003080003034041614055910920803051403071001002e250960343c0c0c10001e9441800d0940381d0785103001510b41c0741101400105040c041150252004500326001c0c043e00006c496004181d20405004101c00f00b200400d140302d1402c3d0401c5000c0b030551b14000154010001d1403203088d0135104162210b410504450700340c2c00f200030840c4080c0420381e0303118082c03a076903010b50207a0246c040120072111290b5010b90003046032184940480d10b803640034401045241e10707002010001d40600e00341c0f2102400102d01c64a031420029202a115004c170454041c5400707111031090f035000b101c00064180400303101e04810030b50005503001c0795041e420100c0340d04024040ca940c40c92414500300d00b002038001c0c0120400310f10301c00c074980d83c4a24058103403a003450924a91605076014010300d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932984919 1250 932983669 932983673
    0x20706150b030601032706150f06050301090b0402130b0304031b06050f090c030a14070f0e0a0b010c1a1003171201120b18010605041d1c09090e010207 66
    0x10005006440707442456a00c901d0320000041c02c0e1405281045034034002131500401903120b42c0540e0368155080040810302d880662410030340d981c3c0e2944207810b544500b1101240d00c0c1d5010300114100d4080d010213020003c01d0b0703404c01c4100c4c400e00c5400080440c41070000c02980907500003441e4414001d05212810b0080c032a410420074140c200102c601d1513441d003c00201c2000c00c0f1480e90440b04ca0307001004d56400d441d011030b03074410030034030003404200740d66402c5442c5110411650300079012200c2074a01c01a640c11011220202c00d8034040f6002d070030148003990a5108800b00800e080d00800c0c134407079030305400b4032035480e002000d00700490003411090044007207804c45204008580c60b11000603681c00c03013101e825440300b20607001000b4000600d00c1381004104c401080a4220103102c1c0c0d45c030000d0308850400c1e80100400d80c0007a42103420000c00040d89071624a8408641e80f00a099905000c00c8040d4209441070b0341c01e4043c0401d00307a03d807d21100d40103600100512402d4400180741000270303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932986169 1250 932984919 932984951
    0x10e010216050607210e010216031e05070512030403020a060c02070f0509060a0308090a170718021207030e1f200c0c240a020f0f0c13020706 62
    0x1c146036240d07001c00300326028200700c010008168803080714070f450040440031139144414004601c5640207002d45a55441048890a5044404042080341c0314211010289005000f000e4417181c240d0501b0308204d51180d0b0f85010780104d07511540d104001e080440075a48103403c8941015209600f11312078094101c000a4140c880c1502608880d00101040752a040c41400043c0d600c0e00300c40d01a44800050103450380382c181010065990045205840d440184042491410140d12800302a6800c40a09030204c0300450301800b0fa5400207084a10b11180850941c240d11410b8030310b0351001c81800010303420758032941c41040800354440030307500300320040507040c000b040078901004140e545d1240c82034103404040d101c10340c040a078101814181521101d80a4031513040718080d034000d00c0c0050f64103810700b01c00d95601080010409410f9100c0030540c00c02566a855549598964407482105071009a00054480d82c660801402030f5080c0220340310340406904100c4044034410f4589180040c03105e02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932987419 1250 932986169 932986177
    0xd0b13032001051005060c0601091107050d0e041b020a030c0302120a0e1c02180406091a100602120406030f06090e0307120c02090f0910050a0218121c02010e0102 71
    0x703003a00215080c2400800000d2844507544421303c0f0340c1042000c0402000085103490460744548000103080606000d44001442a00da00a20031700600300b20816690700032001400c00c207415501000091032110a41c0c81510940714001e0140c1d000e0310154002a210300107581e0403074804e02c15034140d050070a42a46081d0032904014000c164102d0390460f007401c2070440c500c1c030b000003204500f01801081d00810100f886600c102c0980d15841030004051100903004091019403081c40f55148051010031130083d14403c0e1810a043d403c00000010745d948006640d001c15103031803208529240c0381240a400030400c148000741c031591100c10010b00d5031030500c03820000c048071102656884005103449590082120000030074000c04480201c00b43e1030300812071ba401204252800c2c0f041e1100140580303005104e5001c01007040c1444100103103201150081c00e410860031002003042e01e400c00400c180b2554800000717a40343c3c0700b1502140300c2e0b090086410018240b0b4000040d145a5003017055081e070340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932988669 1250 932987419 932987477
    0x4180203070e061b060903040317030c070c090617013c1404051e06060105070f050a030e030f01060510081b070b250f111612110d0b1303 60
    0x48150340e0b01c0f804505010f4150312071b12101c00b640c83c1ca425a030ba0346038400724080c610504500301200107402c0d949448111b45030340d40c01920305200c03540d4501058015103a54000c15001622404001c0c00c0700d0070500800d17100c0c00c00410502500d078175102820245101094800e00119012068200704290078815540010846001c0100500c1d0600f8243d15040401080b481608200c0d51030b44401d81002c01e26a0f004042440d0039980c031308035410000303080c43d20110083c140d801214960001c2607005000c00305144025400c0d900c070b900b070250382a400c0701c54500c9a11340041c032403d034040c41544038451960307205200c60800608407031040441c03a00368000c50710031a405050042070000d10560f00300108441c2064080e80c0b0340303041254000600325005130740c00906000100c0680740340320100b80481c074031710f59190090b0b41e000c81d65046000c103c10900002130b0307601c02c2800008104c2c0d0500004009051385c004441510b50340b111030f200e0038501141e00c0c3c20b80402203010313480da08805090f544102c00003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932989919 1250 932988669 932988697
    0xa0e0f0a0f08010c03290f12061003030906090503101d0f010902030c0906130519090303090c09051308030618090d0f08061e0d05010c050c010f0204180203070e06 71
    0x4e07a5540302400311128a211001402c03905030404c0341d0f1a00304d00748020402c0d001e403040e1001d81c81050119507000712402000c41da5016030320821410305140c0003203c00700e07802665204d1000b607440c1d40554004030903014003901a08030340c2c8140c03074443d6030707800401c01254180c41c400b0300404501038190400304400e1303403000e135a51109085015850100030718644507004550020142c10854001006c0e5480d01c01c51441c0b00d62920f000032002d548030b0800c0e151070000d0000502c0301544030f1600070010300c1650421240030507041c078040794054a521030310740b0440800595004509091b01c0b0021550002004154060f2480b12855034014105006a0003400c0c40c000a00200b18042e001800b01001508200100480d090403c00c0f203984184122a900003240c0d103006a030500c90f008030b03101458582c2c4c050560760074603009030ba01c140d00c10003d02901c040c51008100c0e6110010004050744124440c5a4108291200816880a16034011501b00d040ca04049800400040100d020f64100e140a14080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932991169 1250 932989919 932989931
    0xa0b0307051b07050a03030c23070f0b090102120d0b22051b0316090305190302060a0e150601030b0a0308031b0f0301120f0b0f060a0801020a0e0f0a0f0801 68
    0x414900c265001402c045080a06411400c0001041c10361a0510000c0c08000c800940e0301300b8015559201c0c40e50703440d0580c0b004080c00903055140d9481c0c3c0a88500392042100b081c0008024002006a90080c04144d02803d01c03d00075220210b01c94124030f484c1c02d080f5075203d44205050342c5062513210492a24401e0441c11100240400200c030070003030041000072290142e54017819207542c03c503a8080d0038a059000003885a290884141ca05900f00030014821004080b00d400e80e03864030101d00300d106e6405c4031220b07910390f00114240d80490225024550bc00d0450010202e00480943d41c4401c062600180c800c060301d00040881c40d965209503084e80c400018003410803043c41c0321003d000015284c1e286000903440d80c22000748014845c6100509205e507841c0e0410228981405038039402070780c50720302c606103010300302402e408c141d403210f104040c0550001440382060094034068016521003107800c0ca003a4060001480414803611303800700c07a040c00402c4407446019094003608091000050f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932992419 1250 932991169 932991187
    0x1c05212b0e03030402300118060513030806040c030b0913030201050c0702011e02190c06020115060f0e0321030603010b0d0f080d020708040311190605090f0a0b030705 73
    0x4032581610744010740d400402c104009038440482445846000c50f800040e0240300803180c0b0305406805840c80740d0f80d42030000c600c402c21101081811a64098281000303c0c3d120f000301c400d03a41c0742008000b804240100c000541ca441d05a124800b13901660401082c51110040040c016000403030304101014043d040600c11715038244140b075803100b000b00b0314a240c4062600080c20506030707004405850041042c1c02c1d1100380c400d110308661603491030082d0441180c1c0e8a0030540340d40643c0180f02c019840c2000030111441002c5500003240c002e0784a03402c80c4000c990003101c0c1c0e41107030107045400d440b0b00b11001d180d003035003c0d466900b944d8020361500c0c3c89051420400d4292203150807110f109845200080d00410110200c460016620800669441c50b420841402234019203201074516000490300005100706e440b06480c0902049900c0c48018118a1650301c1141d1030b8050880041c0052184001d9410400d68034454040000d1000152039520100c11000b54002c84030400003d0012034003c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932993669 1250 932992419 932992421
    0x10303050a14090d15020f0301030f060c030b0609010e01031b020f120406020706180b030c0a030b180a0902010207030206070c0f150f030506120d0e1c05212b 69
    0x30115448400c2e90745040c03a0700002501c9111285000380001c030448404000901c81d130390440d00e105005400c0d582d160744c1c2da81419400c3d003007040c0741030f6103045c20564010306541c0b082c8260038020b800100020300b040c10380c40c011920130f45503111440c18150744400740601540ea40d40c50001098643e4020720414148480b0f4506252070141400d40511090105021180d00402c109064035410303e000b910340303035080040c0d01501855500c030300d401c00700010074403482070170301401004441401d89041c050401d580083c000001880c3c91710380c5c181e0081401091850f101030b04110246401481110940d40d1680c000a00c2540140c004803884884d80001700014180300880e0402802c015102d88405140020064443c880604508080569910014030305a40c0d034884040161034400459450381c07007924001d04000c0510109030f22802142440d09602c0c08090707401c1c840694031401506014050f10230003070131704810500941d01d00e402400070f21032403006030b6622f0f000c03407146816801c8682c15003a0514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932994919 1250 932993669 932993687
    0xd0b091f0b06030402010305100b0d23061e0d0204050a0605181303050f161a0a020c030f1b030703031a0d030e10030b120c1906170705040905010303050a 67
    0x1582410018070503116030320641983d500640a08000c6819680c039404001006040e0704086203c2401040340707155042c0960000103083c400c2c4449150005800440c9450148216040c0d540583c22010000400c000101c0c15040c5c1000a010521b06803a82c2c3d000078143c1c0d104840031103486666100c100824034064244c01100310301c61610601ea8148003c2640e009080c020020782800000120801c42040140490f0340070b0b403145851045144591410307601c031145208891a00036075540100d86607600b0340c800c482282e1020001503150600c1c291391500307590815000d201403001c40d0422044101c2040c801400068800c5c1e8001401802e4545000043c40d00704000c54051000d00c028080000c0e04411514200038044138000d0b620104e01c0c108034068428401e401da01720032000d0349201030f4600014907000492040f540b807601c40040045c0c4240ca03800038850140000d0103030502012004c0030001c3c0c50740000407464003d19150716901c00c031050319002e0b4012000a840040c102c1055a4010300b11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932996169 1250 932994919 932994973
    0x6040e06090610022a0a09090b01080105011404050c16120206070f08010909020d12120f09110108070e030a2010140c0a120302040810050717060d0b09 66
    0x402450b46203c00000e40c0c4180c0300c62040803003003004500c00c6941c00818142c15841c1801840800d905e51a030142c000a002c41032000c407040d04103c0004290510180103090580b50302c3c0c10301549015000f000c02016100103006040c03da00c08002010a409107620f402c0e1055005041d1541c0500c2c880000900c0c1040c020001c20400032180c14104042d50701084081c11284007040c0840c001c1c0e01d40c0000390718034440344401403440c507914061050b0241c0040118140e007080c24030400400301060240801c2e540200c1c402050325030721000c44a081e601620100d81c2014061805201c0c04d07004001007403801c490010203480084980b158100c40072802a64420445816a001504042d031094003a290400d00c102d0705c10380078000f10ba0300c056090100081500c0603004136212640c44120600a0002d5106028528042c095040e19000200035070051038080e0f0303025910103042d800c107a41604e10311000036203441d50102096840c1000304207048015406010900c020b003820402c294100341c5241032000e10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932997419 1250 932996169 932996179
    0xc07080903061f1409010e09150403021c2609030708040305060115030905100c021221010b07030905040b011e0f0305090a05120c1504030c060515030604061a06040e060906 75
    0x13070082d1500e07070050241c110f0ba00485001d40c59241c80f4042410103070300110191200707481408004c113066000170852046440406450901c85029104407103030806021081a440c0c0000a03402c005441c400b14203620007486015203007016100d0365296242d611561054409900003030060128001044032400117000c2d500303041165194a03981c2d00e0b1606070308070a03a521300d550742c0f0500c402c442c020b00c404400c141c01c509030f25039210070401800d18030807003106481c00501c0045001007031015561040300d003003503010345400c0416403070442080060f10140d01041d04014003100141c842c40403440814110746d11945a00180c3c103098180201280d40081c00815660300c103c03200000710f0008181d0502c1035800040a5507281c000d10356607840c203550351000d00741003a003140821051603800b2051101007880f03a681400103032120000e203803140c2c85c040050b03903040d042080802e000800bd60320450708145084034590f80da00320308000403496046130303104d2a0120040020080d640c504407103401d07071114044803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932998669 1250 932997419 932997449
    0x15030911060903100b030705060409050a1802130e16090b1003061d0402060c0303090318010905180a060314071d04030f081008030417160503060c07080903061f 70
    0x2a91400700113a00054180c1d01d018100311514107014410141102400316940c4954070b0303a004004100450300c000710305d8500101d404283c1ea081900382e5084c1e030010403810a42e000f6104c036000071b00004001030540c2c85800100002c45045050004c01030180b040c0018464a0b058103100454098480d1402014034100062050b1406098900c86030b622229264049941d94404035100d0b106004240e0700c0e46c03002100f00319421100000a0200046c050000e4444e8030400b0015103819055005032039018115800a41c012034080c5411a80414050b030045001a50fa4030f030016210100003048059400c0058140804411804454100180c480010400b07141c2910300408c21601c0d00d01450801500340040342480c0800c03078014028000e02c6080e2580c030f0b40c0d2400fa905100903410940759003405503886003c03038040f042840c0400c8603800f4010707088030f0791032000d0314980d0385c0103210460b900201030003000f459450401001d4400d440304082816205060f10418201c001c042c2c0c08440d070300a4500b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932999919 1250 932998669 932998687
    0x509030f0d0906051b101b0314010b03130f0b091203101e1502010614121222030f0b0916031725061104121b1503091106 53
    0x1141c20401c491541c5000d64480d407011001780491425000e06441c1d40c49800850262144164808008048100700c12140103c1c1071006a00380c402c10440d02e10806100c2c030042000310701d610002c44c0d100c894805c0703ea000f8130155940103002e000340305060701d00a09013410810120340030010150014502078607903003507103842901c1441c0529180940c051483d45505c005019941210302c500151500b404e01007044400b59400a00900051049030070b0402e541c02040543e040100e10b40c1041124800a00400e042c40c00c1444c0080d07010380c225a040c0c203d40f0341a045e1290391076584e0030243d841080d15584406041c14a15a0300c640540900d00301d0b081829001c1414442103280e004403079100e02d0454884104040c5800a0f0240031040106500010300709482c4c143c40408944400b4800c480802c80c141d65240d90f09921301690040c6082160546a12804250f440580300034039001300c442407407003640b141c000d0f041480b1021b00c03c1010a8803000c0c041c5c00c20085400044a00c0340950f1130f581801410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933001169 1250 932999919 932999927
    0x1f0f1e031a15010311160206041d07020705010c0809042c2116030e0d06020d02031906081e120a110105090d0801180e030a0c020a05030114190b0306070509030f0d 71
    0x200141c4181440c00c079503480c115166001540c2c0100401500404401d07403c5205154901084032f02100600500704042420b41c050050100030980060f142e034102075070141800000c044e8204924110912560884c16410f2032410050b4076004104c064924a00323500264182a14203400103440502c080c02500711101a14070304904043c1c040c41c00e20b404da0416004201c5641d44d0f0080a000c260000403014050f41c0150010760203013003403004400070b4405d5000ca0350308031000b41c015000315030440b181c22402d13800c0b24003c000b100306182003074070b080c844c400c83c0d41c8456510030600880440c1d1281c0350302c00c08103400e116095000082102610b44440b100e0300041c45144140620640c0700e1030b02200e1407a506040c0d0084d00e02d000310342c00b00e0350348020740034003d4000712440d4030891003500c4240b00444d0754103040c05040050f10f110301813541075440301000f503500620075041c000344085e5103508200032603904000391805500c0d40e0f103c0c140e440c0f0f400c0f0181420f100b4443c903a01907682c46880202412684 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933002419 1250 933001169 933001177
    0x3120b1216051f08151c0209130b06010507080409060f0f080106081f0e012a02120412050f01050106080f0c09010806010e1c0602031f0f1e031a15010311 67
    0xa00c1d000c403155403402c13174103501c1c0d51562100c250048164a140010110316264500c207090003202c030342d1070a98810030174841b21841d02c00010f02040c00403000c60703130720350041e4041d000551140c059603080507111020982201d0669000b801010300004040116001d84041e140281203224002d10826003040f0b8281e50b140c146080c80900f15010f4418150840714550003416003c141100902441c6016280c0004002184081030055200c0710030030450f0350b0001034411506070055410a080525000485d054103116410a484500074000c40303405842d82881882e01030000f986400105041c40c44410355415802090020429010400c484481e078110040c0e030b9000c8002d10707204082460650129001a503c0742924010208540c0840100080c070b8020798400c80c0c1f4201c800e43d9800050b20346c80d00480d000d11a4220311060b203001403000b00180c03600c14644015540580e038505546e940c45440200103410245402a201e0f414000e4425100d1201300001b80300746000d01044120141c181c02c6441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933003669 1250 933002419 933002479
    0xe09121602010e03012901020c180c0f19020706050f0909090102091c021e1008041a0403050a030605010807090b1b1501060206010b04030b010303120b121605 69
    0xc41a0300003401c40e88181505140c02d035000c1c0c005d010407082511b0010054408902031101041840920300c200e5100140d98120140b0040903001540c00c940300c92041070201519040d8030f81d1080200c8ae0402d0140c90003406902e401101d4042d9520140800030305001041e0415802c02c40c04215001d255458802512140c9404581e015069150307000410700a21441c179600350001007041c9121003191031200103461040c000d5450315103d82d00d00d11800c03044040803907001d603c00300740c402c000c801500c10110309a01030700c160220140f203580655000c0b81500c08a6007280040d41c0052886100380d0b141c0560b0000782800c0c00c0c50314260810038009000f0352454001c0d002450400309022640000128a4481a0186800b81c032002040c000310408005800d02500002d0702c50b28000140b010b00348407c4404480c4c202c808481e0907400c1d03980407075102c031242d0f0b1800a0145c8881418520750307a04100b80c0c641114190081c03e41d0005081703000c0001c182079204504c030702c41740500c040321043d00302c083c4a0444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933004919 1250 933003669 933003697
    0x2802120909091606020d030f0c0221041e0501030e06100902071707080c060907150c061d060106090b09030709020715150e090c0a0e072003040e0912 65
    0x2e6a10440b45260a18030180c010b1801000080028a0b0b50086540a00d40300d80da43d0521222842410110664544800810045c1d0054003207041d100d100492102c50701c1e8819030b41038901613440c11071601d1031a4402105561540380c4004000700d6800d44a200781c181488000780c0f01c11710300351102aa60380ba6503c0360b001e110303400082d184204007121009021510700f000c1203a40300c0c1c01d0b5080001560300702d440000c50380d204040100b03208174400520402103d034000d444038804507190300b007181c01390309401c2c04803000c42d120f5104403da42c01240d0080d56040d020002000158508480200040c0c400c6c0e201c1c6145500c100803081c3e07180c50110380281518000741c0e016a84c0e0041c2e10b4807441032141e0b11042099241350012000000a640c1d07031100403103252640510303594440b00d8291351034a600c1c0345030a900120350030040102c0900c580c042513100c2480d0411a000b50212641c4540ca0810b03a02140090b170000a0148064102000301c01d8100d03410a00801c5501c100348000c40181c40303030141103447d80c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933006169 1250 933004919 933004921
    0x90201050f03041505130f1e0c0e090d1409041a03011d06060a03020112020309160803070b06060406081501030e010c02420603010b0d05060f0f0c040504021e2802120909 74
    0x4040d00e4010029031127414040d80035614800328a40700c4080e6520503150040c0c074084040540b060300c208401010b06031300c1910304907201c4200b10003840904044a60050382584101941c6c0d020711504028107100184410038460049a007424a00c0c02403940d031003010080b00601c0540d07403002226020561000300141d50303840d062880b07072800c4480c1d032044c00034003800c004c0030600c00340110241850714030550341101103032138210400c601c9008038010500011565800191415040b11104052003018140021100c01d404209070030340f96442e0000000d640200c1c1206800b8042d1101c3c84bd074030804480e04030070103510304030040500c1100f03100450f245034490080744095a080d840b408150000034020400e0032428900303035032100c0f8211442140826504001002441d03403542c420321601a299401e89003504017010000203400c0802d81d2110900040700e81d000d024440c100900000c410700800c1100012030f050303100b204045d007410b01000c46d04030410303900300c200b00ca40694070481c008507207036281c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933007419 1250 933006169 933006203
    0x504030b0c160302071502060c1818150a090506060a2312011805100b0f120c040305190c0303031e060b09030c0a08060a090201050f03041505130f 64
    0x11600510000c1110b18544200300e104060300000c107a822146201c0d07040ca0a40c0ca4204180d8036041c04590701440350f00c0800c50440250080c2c0e403c03402000004203500c2e03600c198000e04460490382126034a00300750840040440f141390040d4040020f0250500074001454440081a054000d40c14504244814103028002e0802c02507a11402030781c0c03101440d41c84030b5550041d040964420f21403c0d00f0004440c1003603400c20164040e851040d05d190138080380301440c01c40820015400303e4419805d4200c10b210762400010341d1032070580654464144113031100c0c15030504c0d500305261251894100040c500900000604601584d82125054100050383c0040c6495a030007000d003602c0343e070221510300f030000b141014544000c0c0000712000d500303c6402840e500140300e5202c03140d01408001c0c0d400b120004415915a0b0002d61b0840e1061501506110852014000315042618200c800e0025094510140c880030311074154800c10035104900b44c0e01d100c2d140c00303e480d02200006405541c6100e05009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933008669 1250 933007419 933007441
    0x106050f2b060504080306040e060f18100204080109060e03041a09042403050705030c09010e0705071205040635041113051501020319030207020103061703030708090601060504030b 79
    0x8110b0b00050203100301d1901d071038101031320361003210351500c00c501e812403280041d00c0c00a0b40d030f440b4054801c0a02c00c2d5171182581c155850010b07000c3d0503002c0c420b044014590011600207080188043c00000c50b0455182c90800c2c107482807000401441c0e030090200704135403481e0001d440039000b00c0300040303030740c0306841800304000e007050100c049952650301c07030408020f0b03800240300d4040301d0007081643d2016403100100b544910306001403642c40b0409000600400d9844441d03544c109030a41000d5180c010155550200c1c05070342186034001c5800403c0422503560003032141091034000d25030164030241e03000c3d07200203c0103440c01cbe15511300c07140a00040030001070244031441190b0090038207911240800d0300e03001810040b03404403d054181403d4205650002081c2c800103903001208481c564084042100290003210007a810140c07a0140019000b00d040c14038156a10801d0207541e6030301e072114000d01a09009860000103a001c00010040075911a042d14241c992004ea443e030162a000750b425 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933009919 1250 933008669 933008749
    0xa06030b06091e1806130b0301091403041703031311030a020406122a05010804150f06080610050603070f050c06090a1505060a03120519080105030106050f 68
    0x982c0094001c840c001d071040c83c0700810340034460b04a46041d41207100755040c032100c00e01511199000560401a21085402c9404c1502c000c007001d0000107542485898480898000000c0340b000c9400020f418000d1000100c034550a0303495690055203181042282c100e0418801c0002500c1640d1000032814513680c140403086510350010001d2083c56202e4241d003500034841d8008070303440070200b071400c40030112152914a0120001089013a83e80c41c05d80195546040140b0032511013003d004901e003890030901c1481051410007000080950a122480385840c1c0040d02800032200008001c02c034030360380d01d070840342c1c4400946001c260b0904854410795082c010705045401b20f010302c0c01044665540015002c90040c0a031310031021030542c8100d171804450003624000d411521200d02030002c1070800b0794410706e01e11280b60551401100d640c03541458051401e5110010350801c004210b0340ca024029500a03080407184540310081000000307070300c2d40b005411030f551000c101174508500c921414202c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933011169 1250 933009919 933009937
    0x306022101080102180301150e1b0705010209090106020a050d110f0f010c020606061204201306141e10020a0206040b030106081602191b0e01030c06020303060a06030b06 74
    0x510000d507116407203903000c0c0d00300e190743c100e2a1a0070800b0220341d160501405101d01c2008848c2c140b501d040c5802900150030060121109610414007011600980001811402d000b1030005898841c0841000812041a401001194401e04082012441c08200c0000e80d803094140481034520f400280c13802d110181100030064026800e201e40d020006400400c80c0019a40c00d441c1c1c035550398800c010b00d0b0b01a15108424880355440000c000500d038100b241800c44c1c100280b40c043c0160748000481601c440b10809900c41c2c3c940304100480b807042d010500030307624101d480d100e40707a40c071440b41180c00e000c1c1d00070030b0b10a00f101140920782c2c50080c48813086464004e0a6190303540c0e01d03a03030007021a500070320600000461000000d102035600c51a1160680440d5004d484100000002001e200c43d03602c0c0191103800000040c2403002500081040080100001c00c42c0150700d18180302c40aa81f05510807810b5410400405c00d660303581d01c00d404151a69414006949807040b00820200d0151041e9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933012419 1250 933011169 933011227
    0xb0708041e0501141b07110114030405010b01030606050306010c0b061314070206010f0f030602130f12020f0f010806090405150123100f0c0501020717032401020304030602 75
    0xa51402c1c01410b42224402c40c040b00c2064215450309101c04084a481c811030060300003042c0a4000041c0101441d040460701c149032007015200c00c00131265040e4415942103585a54072400305030207503054003030003005203064140503041d85460760028001c2c1000f01c030300030b0680130072034009011a0340c4c0c3c6c60100404203002c1d00421083c100f80612001155094686001500c5074400004150000080510640d5403403001d010b50300d461660f48001941220007074010004c2c4100d17000c1075441e0004000c0e001804060545006a90f0b02d00500494011001049008110820034040c1c180d030424402e0341c1043c0140c4000d01a40d8803801d143d070502041d00d900d02d0754681c07004000942c100200030700d8840d440031000071601c401581f504000e08a01c2159441011441d2401c90f21000c0e806900140c1d9140d020b080090b01d480d050b9901c0981c840b040c170010440c50741001c0240420300c07011110900c03041c0300d0140c101400b0b200b8440081d649010b1448010321280d0002088000c0d040000991200500c1038a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933013669 1250 933012419 933012473
    0x4020d0518070b0a2a0219060e0609090c070302102f0a02072606090604060e03040303050708090a17060105030115141921020a120b070804 61
    0x10030040d1204250300e601c41c440c0318000002ca01c05540c04215800340e82c0035201c0d00c02d2000d861000b865102d03000000400c0100c1030308548409a00c0d05200200c0c030000030b440d084c030010b003440005000e08009011041c040d08090220600684421525503001013403040000d4840781c1d01c0c9001c03881c013601d007280c484100d820520040d01c01d000e60406c00001040d5181c01c144c484a054003020810701584110790016030024808100c2110748203040124040c000c081a040075010080640c501401030f035480c0c0095011074108418021584200c580c08003088010f50714040c5103417030080840c00380402c050704d002c0002440400b590342c3c98049a000b81086030300c0003481d640b03404030b1a4442009200e658040d501f866440308801c8001034070302003540c02d02d42010081510380c5c024044549a1400c82860f40e202c140d501254141c075002d11000c006190109120140e4200e105000306000c05911000f110700f1041c0011000428010b0405c0e4026818546841980d8403820a900c42e6442d0000140030181001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933014919 1250 933013669 933013681
    0xb120102031014101d0a06050301140604050a090f0212070518010306080a0f06060308270415120218091506190302090907050306070903030201290f04020d05 69
    0x900a1440340c2d21551032400d20982e0707620070030300e560010a8890b0380848218004610381e40181401428000601e141e0022481c010300800e00880c1c264100c034012980100040002d080407000200071071006941d1541407500e401c010038501d01d00b50150800150702c440801e00398810310f90543e0040c2c5020f014040c41c9081c00500507020307170f00c4800380501e0300c01d280c1c0d003010701540240501c0007144c0b14a001003510844644421012a100c010115942a114100040440c0180c000b03081d07001180444814040c2c0700703200001015206589060050307050803d644404c0aa40d0042c1c021900c08070074103070442100c1d1000a041d200d9610101c07008803045014840d1141d000200004850418562004141c5404c0104a21010b01c40850342005015400520050600d00c00f095004071041049800c0c143d1540002410404126200e03400120640000c0040c1942401800324180c105003096441030076107032a00b05252024a1781501480388100d4003103541d11968100c81401480c24001c0102c0d0501c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933016169 1250 933014919 933014921
    0x50904200703143a1a040209120307050105061c083016090807031e0201020a17090114130911040504110910080108060a051008061602010c05070809040f0b1201 70
    0x4910100c01104c000341107078044144a100b10f503018000508076140c0c1c0070b07204003080b02a5100d1149280c2166000019102d00c2d0700c208060320343e10703101c0c0b030010031949882400d202a0005421510351b48000c214101e402140b05c0d0000c42c1e022101d0101120342240c580310000c48001d4103c0f007003150780c0d0054420000030414541c0680348151040d500c00e14038943d03e09690b41d9503003543c0005401441c100040602d0030502003152004a031040c01941d59404054072000048008089103d01001000030100219a4030010340c1c090300c4001500349041c10f21448000035200f0983c0225010280d481c00028480303102e00b01500c1c02820024000d01c001102000d10308010b4001e0302c14103002caea281d0001011414015081039040e6500d000050056075540d24108000c2c0001070610b00c00402c9025000c19400d40c20321000384075002c0e951080451141c41000282180c201401110401105224080008807210100c820f0700408079000720750365440c2e0403032000a1030824107055014200c1c100186202c001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933017419 1250 933016169 933016237
    0x1a03100501240905040207020418050114060a0608060f0301020d02040803070c050d03080c09040b04060902181f0302130503190501180f0605040c09020a05090420070314 74
    0x1001d8a0082150100360b40410800c02c141c9915001c40c0c0004000d0250781010b6024000707903400140080344031464050f152640280f850303802d58907a510741c1007520b04a61040c211a070041c5090f40c56a1070903140050050034010301400c1d041c03040c2c0b000504016195000d405444a1800c410011940c1e25075603012141c0e01d90003181d00b150301c000403250014180c54208030b550022500f54031400a2550348841040e5a54481841254059920130741071201d615030740318100203445030840042c3d03200d03540400c07040441c008001c9a84a42c03009000804444003c40e42d80511000782c1c140580c40e40b551184c401c00d42221600f001d034152090840c02e0203081c42c005011640140034200800c0b0a600c1040002c80a5211180c00341801d440c030491480000c4042c0e1140f40d2281c0074421801c4520380741d004607016640040f09590005a01043e101d441e0b1400c0d110300a0070140300c0d280703001c0560f42c01d98110154010984080d0601000c1d58200c3e19810303042d003c844034068950201440d0800040200400404e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933018669 1250 933017419 933017429
    0x81f050609062a070509010909120f03020708031512070501020c040915050c191b02010c03050706090c050319050a0b07022503060e0105100b0307030914010c1b0c06031a03100501 78
    0x504000046c182c4a07446802d080701d8210ac0c80b04681c8518000a807519401c5200b01d01c05c040d42048082d000c141c6440180d4011f5000354228045180000c0812508800680b840491500240c504000c640c4e00081e00350a4400c040e10003060b645c4003401d00c407000341c109250301420075042400b00300300d000000c001003082c11040d881c201c0a1400d84101200c90b24864a5400034888000f004a00958060640c2c505858800d142c22407500c02c1039a10b8009a55103141c00301c2d00300c0669030051150385010301684040c48903040c01c03a009000c568032041c0da41e4010a03000b401c48a41500491061442030200709003441e0500c1c42141c881d03d40c0c01c0a0b0314a40303030791711054a01e00e02c0c1c145036021950060107103e000c1c114420f001c8200f00d0a04a005216a20240050050503a07410b0700c00c0001d8003715511a00480000000810844a1801905a49041c001da595a04484645000260612100b00c0c199075081c540090b41850a031040580200844002c5500d41704111440f000302106800c8241620 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933019919 1250 933018669 933018679
    0xf18040b040210261003140d0e180a09050114010b120f1611011b03020c10150b090d140a020406060509010203120c1603081f050609062a0705 62
    0x3c00d154408507100c1603e1419002e6801424100c10100f1482d00481508004d980403907184039a0741e5510715962a040800c0c00041c0d0b000a10803007030b00754101c2c0a000d81e040c0c0c192800e500d0f0070012840002000310042400010590300c3e00c045e01840425070106007003200f800d04808a07541c45103a284215081103032040d580700e8154000030030142c3c3c08120380d4064503078514048200d5503400c40a80360b8822014882816658540c800d00121070a880e09240384500c90310b0041e81c502c100504036041c07001d44030005070380d182002003207240501c1c03180c070450480300d00b44112078440803d000090000030311084094001c00328140003044104004c54840819807013120200072107603583e4000d0324540a14204680540c02c1484015052144828030950101820b400e1501d802e03140052000003941100d015400a1100e01c1003210f000500d0131840f52104440322034400342e600d004001462071007100d8005004440200380481014190040c031160030b001d030125481c000b40500030300c0744d980310140f003014070030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933021169 1250 933019919 933019939
    0x30309160b090d08072d030210020405010507021306080703150c020f0d0c2405090709051b092e030b090433050103030f030f020a09050f18040b0402 65
    0x400304020442d2080e81d405040d80c040400c460f1110f90b0590061001600c41140841d864642984506108100d6030503148402600484604000f441e1104420100c074030184104814420380ea001030603105501d504a800c615081e409644000241096500c40b101038480c1c21008010000c14011103002180030036010400107103e98800ca03910007040318104043d030803103820f044119205407400d2144900981260a8013084151109925084078452040c010741e01c40a01004e00010720a110080203c02c505100d54189010f50214414150300c1c40c01640c2c00000700340e0015110b01c40283e00c0e00700a644641c4848242000d2480402020354005001900d48144009103240124000f80905e8000407411441602c410920b140d14800c90076554900025171343c28076031a543d6016840c080c500c80d94030883d95811002020b801c3e591103d034404a403d00600490700c07c6548680901c003207400480701040b03994019001710322000660940424440240d20800080c07003c081001d03400340c1d1094a0030444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933022419 1250 933021169 933021179
    0x1b0a030c14130b010f0302030a020403080c0a0302061b0a1218060b0415140f030a142416030b040e0307031d1f050a02010b120f0d09060f03020c0f03030916 68
    0x12070f110101d00c5130200300721003100710410b8800da02945e4820303020a4010b1500da101c0d1500340c03954001c2003101500354420350f400d000f0558117201e0f4940101d2010845844600b0241d4445c0042c0204582d05003007202001d555918010350b500010203030b000840505400446905000c8090075031040c2d43c500450400f407810308181703c0140c03414201d40308481c000f006400d4800c100007403044c01c8034105030f052040d000e00c40302041d801c41c00081c200000d10000e05268446a8041c1d000c071610704007234100f5200c0d00341049421000b400004080c141e80d4070f40000d005054034001070041c8140f01e508001c41c407020629004040d04030f4901202d20b824880f40c01c20340c07442e10f0108a45801d080d4550f151044503240c201a889002c0d1000e0507075055507000225071034005a0100e2001800c9210300c2c070580d40128643c4c45088018003100842d0300080c41c11081e01820450041c10803030301070140c07400301036000841c0100b0704028413850740000c0081050303c0c0d5034100f101d1105d985510a5401c0b00042c00960070002d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933023669 1250 933022419 933022421
    0x2d0702150406021f1b0c0b090d0806100903120302120105030d0e1302090d081801110303010621090c050a060e0d02010f031407080915091b0a030c1413 66
    0xb1505254010008080b9003115a050503511901c1c40c408252524a4084205480066118070f1005a074450880143d11706081e000b041c009401200300790080c0810308409581b1014460307101d00e041e5522120040c5450084440b0101c503070018003040307041641030405540c5a001009000024042500242d0300d540c100364880d444040175602090120350120b170117040405600c0e0000c684600b0041c10245a180071900c40c005840007228030005c0002d803071644000d070f0b0440321580310342860580252502c9050451340d910060040105109000607001c900f0b946c146080c0c0c000d4450154103110120542c6841c0307503407004078001c0601c514080100480c0481c0700e82008030603070100034080c5411030303450380040d030307041e5651102c200416441c0c02d240c040e609008000c0501a150700e44c1c4800803031612119a609003c08a8010446070744010203104a40000244210442e030120308030a014000303400000b4000110b03984010400c0c0c07100480042c902d61200040035000e0b105490b00c6880940205602e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933024919 1250 933023669 933023677
    0x6030605060d09080f04060f0801060c020a1a070510050601020c01111209060c0a03090303021603050a0809120615090a050705030a1d07030b011a040602122d070215 72
    0x15000300c010b00c400b4090421035040384280b07a00510215140c074a8080c0d613100540d01a40005000c5641e001346114401d910074002ca004100c5841c00c80c4103094180d000030340360821840303001d6080c102c1400c00042400244c0868080c103600204544240e482c03904440060201120b0365805405684a90b0303189500a227036030001105514003400c03899442e051201400d8100d0034030190041000d1110145044c410400e03445440e019031160480c19203140b900a160400d0134951312058451203401700009500020300100700da5121460715140c5242d9404200c1400140f091504a40706080c240030b46007010540980d9245c00640b0708100c0350b07844211070402d0340c2007510140c0000d4800c100183d88901ca03a0b2104806003104152085031a107020f51641c900500c41c0c001781c400445030310041011b90f00c0100786a06c10311800714110b040a03e0280c0c00303500c410405196160701180090603100105d94070700461030681c15106c4c44083d43e1400602e80e6450f81098004900442c501104044403c0c81d0f802a5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933026169 1250 933024919 933024929
    0xe011b0f23030f1305130f0638122a070317041103070b0d05060d120f11060a091b051c020d140a03170108070608090312071107060306 59
    0xb149000c540110f5603da0350301c0f0f10082c44200c010070a010455039074030710300c1c0702001151305404501c4000c03421501c07003105c150350b100703d1b80b4444000a0340d4400f25002d55412802440e43c11240d40880445c4111030315105007403e100703500d08054200f190000700c0410015490400d0304038102540c1d22040104010300c0fa83c5000b4021803030300748140c10b5404c2c4101c0910b40c41407041d503da081146019010134030b07020075908008110744000c01c0781c0c0740380a0503104040c0d01c039034102c40c01001d5a12a031180c5000d02c1e4440700c01c03410030411140340694540204040015031041d601110680e140030000324004054190046414068900301c440c11059103400380000e4070001009543d45d00c031051403100c2468030a42c0126000494403804501207020f884980050001071005030403514001c0c54001e1800308190280d40842e07400304010b204203d80001c5610603602e0604250034540c607108182c910f5805008203820300000c400341006411503200900140e11410802100c50190310f42c0406d81c190380040c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933027419 1250 933026169 933026173
    0x20c0d0c030c08090f120606181303140712052505062a03100608010f06020c1306030209040317010b16020915150903070e070206070e011b0f23 63
    0x4140400c0c509002489081300050500c6091140c22020413a07110300712040540340e42242e0200081402c1000181ca40c0124400031b444081c13a04030010950009180d1014040001450082902e041200e0488250b0360708010300140b00d560b03030a00102594002800414100b40b00122114203845084010a02da0f03400809010076584200185118803001c81e0003845e5000014a52045801000001c42c000d55517140162417a03420300c00e003c0c1a40d54103078405001441c580303008000b4160301040d80d00498204030381c000c1031480b41030f40810160101e0341002e1b602c83c03c2c0c0d1050004042d0017031498180d078a40184060320607a81c3c2d050380480d80c00750008000d4807000d032580c023600503c1e100c4031180e40f020f824400460290391007004151801003100e0707442244a0001803e201601e400c01a000051004400107001d1f4900305400035100c41005d0401e0003808848079405405a0040d200c0d243c4046c4001082002d141d050b0420008902c1182410740c1c82d0000c11001c103147da00b0700d548400300c444920700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933028669 1250 933027419 933027437
    0x30c1403040602070b0913110906072105031e0402061201080609010e16050121060f03150207020d02060901170a0606090e10170102070f08070302101506111906020c0d0c03 75
    0x20312500031f800d0300300080c01c1e00c480c00c202700074142d0f0315400030b440d21500070015500c0215100e407040303030011860202c40013802802d104001021400c070351150310101c130342c0d203035822191910f06c0440ca01d8081e03207049080950341040007051800300010100e106240c040e000340030000d1501410b03030302c0d0805c184d180c0d051440c0f000c4085c00a5402030042441c400d6000c000841441e00a00041e4103c88440d0000c50400e85141070402c24400c4110b010781c070700100c0090441c0390482650004050b5080010020700407800414000b20903800780141d003c80650101c41880da901d0a1301d1001c0041017a4061000801c414601c00709070902c4003080c40f403240f05000441a030b003d09218180361065800800080b556408109000004025902e12400b6611030900a901e0f0074003407402900300490f02d44140c01c60b038500704059a409002203500800c803004d900b486d48109540e05501ea0a0549895520314030700c1060000d1001c0000e20750007000d40e80e0260b0243d44a03002040303c1142e80c1ea2b12200050000b5904403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933029919 1250 933028669 933028699
    0x31f050a06050903070b0406020d1205060f0f01030b0307150f090b042d0f0306060b03071706040b15040312081902090406270501050301020c19030c1403040602070b09 73
    0x100c0185007090f030003811201a50b688202d025665032250300410700580010f102403900f503030080160f5040740c0c24640140114a000c00c08104201e01d4140d02510811306e10f5081c28903640030b6484443c0d03180020742902c207115213404100c00364011b182403040c00964250414200107105110f140151507801d400a46018030b802e51041c2c0323000c1480450801c03003903880e16402c03240703d291a04c54003c007036006401c8201403650a203441210700d15880880040c0d0708008000740d0716031201d0204940030031039007040450b44130340000c9001860f01c118030355000761808120901420b903a2015004580c0705140c400c0071004909821680e000c0e05407043d12458518a2070b8054607c01900030307150310700c0003820005420340e03903195050142c031608045191401e68800002804040c41c010907002d414168029032803c0b007881903250350f071940080e01c139041001c86d8120408141c40b50803441c10460304019006000c001c01c02c41d0640b2503000348170741d202500c00c20000160700e0441c141030721b2450400401154103d0604 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933031169 1250 933029919 933029927
    0x40308130809120309130c0f110a033006051002010c0f0507052a0307050102010e030a08090f0f0607080702070501050708031b040b040311060310050d060207080f031f050a06 76
    0x1902c0c0d0b0f00d064081400300c22660748424001c00305143c41d40d00c020440b400b441c8400340c01c00e5010f9480100300400c8280301d0110003000a5070a41d5039030300d403600000d0b02d003074020b00080030200305a40f40a0b5603900205030241092940043c82030301d00485085a0322080d600c426402c039184080604c004c100703414442c002140c0203038090320400b805142666116000050b40204c0d01e59520340e000a80620786082c01c006003410000320010b4607003800204011240d050809030b4901540d8038410800801400140c0017042c00e000048130001c08400301d9040602c419070b480d07148c01c01151400c00241602000881c4188005110412102c0c11b031600341c0350514640b08c400c00341c0d20080c000511300d5954403011540d4000d0380003c00c010f044081034552900d0039450b000c51941015003404e40304c1d48042c020300c01480800ea4219084590032a113042210003549046000ba000b065000b03811418003090520310301824200031440f40481507112079421000000c0524201861f028158008803400c800344030050003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933032419 1250 933031169 933031189
    0x406030b0423030714060a0501030507090b0118030302030406080a0c050d0b06160309080106080f0709180c0b180105180f0301060810091707110409031b0b040308130809 74
    0x1c2c160703011816040ca804035600d10740c08480c0460362502007900030314200c9024440d80350042d088040900c01d40d403658035000d60f0b0b59618012200a95500c03040c0d4241e9a0094040d8410304070314501c0803240740c0d9682400ba40700d40092241d0303004588504005129a0171320320500d2a0301482d621014100480480c0b4070004200314218507030030090402020f00d0030742060f130321490494420f0340d80001903030078400c1d0f0600f0354a56902034030322503010f8029003411034404178441381601d0b00c004000601030064107102c4114804013101600c542550035002c621045401c00518170603403c0c1c501012192291030044510f407181c0d22840c00240c008140f01101c80ca044240d00c1d4980000800105405451304036040c101503260710351418103603440d01010308112aa074404100000600f0314141080c5550300c0b0051000c0f81442c542d44920f43d03501d100010580600300d001140b003007030b03450419405114500883d4482003030700c0c260040ba40201c00500e801c0480d40540d02019400340b40ca6040c003603058103008200c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933033669 1250 933032419 933032453
    0x612040f08070501050f010602010c021b060309120406031b0512040f0c150e040c090506031303090f0303021e0615060310050301230147160308060406030b04 69
    0x8070810100c400304909014007402161241411500ca501d000400b0b401c4030074003980308056401038401d081c440000180903010700203003613591994030740d03c1d01246800e040055008511b1502d010401003603160740342d4020080e803510030000508010510905643c41d024444101e100200780000140c00950000c105055561244000400d100d40305d031181400011190200000200d48000f0034140d850a80907488a82c00d241c00c00c21001e5080030081981131100405080c82d410880024904143c82402e18100500c0815903008505440780f40003911404010f00c00c0383d030415038080000465002044250146003140c6803402c030001448103001c0075410043c461000c00c02c00343d000041544003800799800c91802000b0348080005091000700103c041a04025a0841900c0cc0b11414007030158000100e010b410110000480914852290310303001210824202ea0000c24060410003603031001507011407094480040c07541d140301c180011951684005043c1d40840b07008540450003050314102148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933034919 1250 933033669 933033683
    0xa0326160c060513030e0a06080402060c4e091011061e070201050108151302100504080106080a0f021512090601030b22020418052a0612040f 62
    0x18426403111411680101c0e00001410b0559000b40205a40003050540c0540708540003107c060400d00020500706005100030701407800010600c081d041d0811070070002e01c460b8405c2482c0c0c402010320010b0107202c5a80c0144074044c840c40005201050340c4c003004030110880840b1414002c6110811021008001c2e00c64144104e070748a80c007602109201039440340d52100c030708044800f05005e02524219004090324116494140140508600800d5114144070414031120850715114541c24090179000e0000b98885502502e08245170f07005400f03081100c03d071200030404141c2d00d103145a1100c2002000420882c401e000b440014541080344003030005200119500741b040c4001e000c4440042581c00324400d0780058010410403121004142d4041d0300d110b40d0f00e04010301c00c1418103228198040c0280300b56143c2c00c2401108403041c04a94619400608540c0076000e00200c10302c580c1070380100c03d512a011304031420414184201150548a40b4030721102c3e19550313030740f0354020800100070126840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933036169 1250 933034919 933034937
    0xb040533150c010516020f060402040b040e030304150c0c0c17030c06040804150f120507023a0c081804060302130b0f120304060c060f020a020a032616 66
    0x3550201c0c002d0440701241200024003401c081c080700c10400a201c082030115030002483c015003440209038107412030341c180c0300402c1c0910484c0005000d0549c3c07043d003881a00c8044200001c0c0440c02c10704c5412424180700420603080d0a28080b200101c0c038100203050041098800c108420540184001c00e188141c00daa00340f140b2840740c3d608040013a202503560140101d41032010300109081007403d9200781c2400840148012005824a1100d00c2d424480b65640da000400150003407081580001048520703580d00d92514140100035035042d518070841009540039a40c0c05400b0350324400710203410403040750400303490540c01d100d80040000060782040d100e100000041c0c449c0c0c1010f10000100b40c10101d1207420f00070501c0380d0b00b9103411010340300300400c1c40c80032501c00c004000c44003900c0c01d625142414804905040c40900740260001d4081440047c1000c0350070b5000c1065000140b0941e2803240c102e0820406e00c041004070341d021000780080c0004a0000464640c80a4210030a030501c5150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933037419 1250 933036169 933036199
    0x40302030a0507080d030c0801150903080a030e060a0b031f0612080d0f060311040b04090c08011d0318011d09040809030c0402040305060a0b010507150b040533 70
    0x41a0070703407808030ba00b030f40b00340014850040306000b001c000208503e01004410711005009000c2c42c018403032001ca40700316024203400180700c0c000080103150401411035841400c014000e0082004881e0000c4030300510740403c012070007501a010340c40d200140101814a900710300b560066a800c261484100c0d030700c3d48005501ca0002c000c0c42d012a0190007170b81d4070344406128100a44809200b49000c1901c1d2400910000d13559400322005d140c030544000881e5041070001c18020321500e18050009071703203960009030007401500079081d200c60780c00c280c0c2c1060705085c001613038070f002e4130b10320a04113640b040c0c240e581940300d60a0f62801390741d440a4070340c44408840204040703820a5405440c1140001800010350604105002c007882041c0c0d4114945851030b2500c82d12230001130000c1d41247d840d02d01c4440307140e2003407064862540d00300000743d542da2031112500000f400c624500a01032400d050008444200c1402003481c9200440d40c01800c4082000358190800c02c0b564555a100c0032241c91000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933038669 1250 933037419 933037423
    0x605040f05041521140a0507030308070210060803070201230d0203060d1401050a051003051c051e030103200303120a021605070e13030909020d091416140a0b09030304030203 76
    0x558442d844c0c0d03044801d0022400c00024030101340007400c1e01503225044c41800100c000400c00c0480b50107182c49400c40c0c40d80b6800301c0c242200c00b107502d582d20303041542c080b40150000c401806828400d0f02c42d44078070a83c44e0040054a054100b01901144d41480451142000d40c1c0007980d21140082042c408881c20740d64070f21541c1d20305548200281e5596007003107501d118911855402c0320796603209150113895641c949685000b240c60041c02403030003001c00d800d15070191041d1815859196070408190440d40c80c158450f4200f4401542c0b15043c0040180c04945054600d2900c03c1c00a80074610b05801e400420005a001a05002d00c0980c01c214000e4590f440d6103011041c02e00c41c10103400c1240c03501c100307580390b11009070441c1e810705144c0780b1900000b40c010f014541160360806d40507031504150b2007030100030b00c079404001c0c00c6900071044400309440086221410f0715001d26240034240c0e15811204441007842c80c2503500656041c4003800402d440c030700949400742d00202103d203050307200d90100b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933039919 1250 933038669 933038699
    0x315040204230a0605252607030909020f09010807210c11031908250905120f0d0e040b120a02010f0206072f12040f0605040f050415 58
    0x1d40042ca40d208880400d20746501c02030014400d40c6095400c0c1400d0007081d00c0c1d1148880e0000c0c091400080801c810400d621300840511044a45507000c0c800415170049142e900400d0200d0008884810106202a1074401d6500241920700414201803000d0300540300380d40060006c00502443c5d0340d06202954a03950091020a0540c4000c036440d030708048050030045136151056110b0f002031100700c4012102810300c081d00c69003403904c00b0041d124115111421001d201003103501c0ea46405400d4000c507007003c0d411084801c141c07849500000e1080e0555150080407a03000718a4000110401503c1d2048c80c00d0300702410010000103007020004001101c002c0c40f462810300a800c031400c16000d540e00010265a5045140042c02c0c0d189481640144503005044042511040e4130880c1f4010704280c800074280c203054902242d81d441104441810726405c00d1090504c4040c890f840070900c0c501c03032002d0310122208115038119082c00c0c081000050301d00301803401d1110303044880010303280008103188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933041169 1250 933039919 933039959
    0x207053304050f0904200d120e1e030a1209091509050c120f04060b0904031e0207030302070e1806011202010306050405010303020303180309040c110d140315040204 72
    0x40c65441e480d010a0200243d0f5180205125031014001c010200d01c200340a6200f60b5148039035690700c000e500d000039120841600c40613020b02e1070210005121038000d106001102400c40382200303100343c05144072803242c001d280420707010b030000591907000403a0441c41d89400c0085040c00e010b955141c05066048943c6000b80030282084e00008009000c0c00f41304860700040ca6802c054030b000080d8209244604000c1c01507040300c3d25582c0001c0c2800429800300400800041106440742400e00f0000c00c0d44160850000e040705402c5110031940d4000213010080342d40c950060a03d140c0340a030758448a07030009080740a107064440c00840d1090060004601a1003800e481d500c8a07000d50000400725a66500101d00980c83c1c5401840480e0300002540c3d4466000e4003070200d410800032000382580103000b072039a0458148103907020b501d038120144e41420352009086400c0c0407010700d42220b103400c171542d64404000c8200080b40c0c07910841000640b1449000c3c002614080d0745020b1008481212021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933042419 1250 933041169 933041269
    0x307080d081509060d1502120103050d080108061003021c0602040b0c0f0c130203060a09020a030b0102011401030b070c0302070f0e01090b0d03091719050607021c020705 74
    0xc101c2d00d0140640c08072025041691040c0d101c1c5070040c00b14488401c03e880180840d03403d03062160000c402a0119113000060050b1a54156500d190841d910030345a0045130100b40724070000301d80034000141e450f01c42c900c3e2028a8003820b1a603001e02102c4c81c0b02d510745140182c20042490301144450005000070100040080c2d41d43c0c003441a070b203007060800d0306d55000c25001081507074403a5644026000e503141e82d840005a0703075224040002c1082501c0c2e808424060300100d240d03040c03550954050440c04400307030000d01407604610503d070844030090000401c8201188045480e20f80b01d81844203c0340d100b80119402e06440342e0384492140240c0e801180c0c80303e4010014001e9444c9030147d20000c00055460003101e80c180e0b640544510000c3c091000d41c2c40d92101c03e000140810045a03102d9503002d25034603825240750030400e0300d0ba24211079042c054071900700c01000034950883c241c4403004281d4050501c0da4204070030410680a440001070084201d5050360b486101d20b110030407107a00308900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933043669 1250 933042419 933042421
    0xf0e03030c0a020d021f020c1906050a14010b030c092205071202072f040203090309010311040b0406030f0e1917040e1303180e040614060303090d020307080d08 70
    0x1400038600304e040f907010811034002e99041c0c002800c3c101c001030300c0d4114000001d612010200c024a14104c7c0448005140c03800d014941020f00c9901e5000501a001280c000d00440301981840003c8140a09c10300b604100d0030000901102c0c82c1c900600003c107001000400380c0b07443c000880c0c8011080065060a035a40c0f035090001554010284016080814409508001894440281180000500c06c90411074a841084c80d60100f80c2e840c220044024404c64981c2040400715603260404050b441c04246001210b052010803403042d81d0407100303886481ca00e0a800c0c040218068120701c00011201074440d150701601c16403d0180b0b40c040310488503036031006001420008942603440c100060807980400090110074443c80c0b1441d4484814162607600340c4580c5000c030b99003805004072400c440c0c1d41e417401044112841b0074440c0541d02071034050001541c1d40c1742505200d941915944e41c10341c020072203090316061100d07540340041d000034162404190742d202e1441c01c1000d0340700c0d80c2c0700042c8804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933044919 1250 933043669 933043687
    0x50c150408040e041b3212070b031906030b010303051e03070507021009061b020a0e0709060306150903020d023105090609030426030a032307050d0f0e03030c 69
    0x10300c03d8000c08100c0c00d42c01c6622071a00c6e0038070518104043d401d00540c00308032943c03880d85030040450324008603002210301c09580e5800c010303c06d81082d01c1d0b5024080350500c0303090301045a80150015650841c000350a50392841d0f0301940e8a034031540120f01d00d440f410388007140c41d6a4880c0a075102e0000d6458a555601c0148108607032401c04000c0e45060000c15081880042d60040c0145038003503080a00d0010880c25000041c0110101c1e4410320a51a8450400100543c00001682203070301d9034505001254682d0a440c03c085030005603d40060441c403410800351401560384000c450018003409043c0d0065007041248041a40502e02c020782e0b9012510032100b0b003403050540c031580c520b0143c140740c1840081103449100d10300c036400078030040e100602414000c003142d9205004c84403040380d035100f4407240080c014190904442031501c8100412107943e0307620107640ca12480890396090b2410040d00400d030000c2003c440091103140d540c100310203000c03108000450154071806251900c1d01019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933046169 1250 933044919 933044963
    0x13050a0303091d090304061d0324010603050c0f0f0d05090d1b020307050909030d0923032b020d020f03010515040b0702101e0c0b0601050c150408040e04 67
    0x9003c215045a4850300700300f0746820100a903400e032100c0d840c0c071002c6507102c4911044000100300c0066454001c510301d80c1062881e00740c1420200000d0030080040d80c0e61060141c0c01c52701d04460030f51003280304210704411462500300030403443e0424003403c3e08290b40304200c40c08a801c125228a00d5610402800300300541025260080c40c030451104c4128004540c0403945407540c45c0700c0c0e54000c085006c04551404801c0c0b003622860740d1082c0040010b0104d50030180030002500c3c05ca0115079a404142c01d214420100071580d0a41125007070943d100c1c0950410040481086941c20b0002d5092000d080d0602440c002008031101e0b12034000d0f01c80d414001000110358850308514030600040000700000080c0901786c800751a011150105c6d12131148005841d917401442042c81d40d12544045180c0003608102840c0d4060b01900c002c0c1c0c040c1d5900300056455100e00e2140e102c2d10b40c0403131040000d041c0ea40c445e0603030091007100c0c52030030b05a031101c120052500946d030071101030007401900402c100907 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933047419 1250 933046169 933046199
    0x1306090b06030705150f0a050f0f041a0702091f090f0213091b0e19120312050606090409060b060c03040303030e06010f05040e01060e1e0f011a13050a030309 69
    0xc111000454a0005e1544903050f00c40d2030510040c1d041c000c104c451005004800b511700c4030960308021540c55030203052851503035104e4010b41c141d60071013000348241250560160703403c03945d020301814015118010311840d001501e80440d070380c1168005010a00c4a118068401c06081103030b800350716141086850100c02e02c103500018455480d1503950020704130050300e08506090035003081d903940e0382c2d21000b2407150700140c804a058603030056000600903c444020317085081c000c0e40ca1012070040981d100701590001d0b0340c0ca070f0388010103102190a62416a0110707290301e1107560001810b0b01c030310000c100e580d0840700c2c4103e0780c1c1e000170808106254050040803d8400541d014100a604282d1003600842080c0240750247c1e80d01c50900c0a0101c0c250b104802034000e0000303610461030480c5141d00d4041442c0e40e07003003030142c0031004542c031644c1c0706035014103075a0402020b44040c024544107130050f400c110328405250090307440005458a80b41203020143d03002e5940c00c0c20789801c141c1e403454010703c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933048669 1250 933047419 933047429
    0x6060306081e070e0c041508041b06051b030d0608031309050f010b0708120a1e0218062101060306061b05070501050a0306050a09020d0c1409091306090b060307 70
    0x80c2d00200d0701e0080c0d00214010081d1070481401d94201c2e181c84800c0c481500454108030b8518041c1003158000a81010009100b9881003040180040b2000102c4034210200d10075400441e005000c00b0b02c4290880b007940341003141140450342085080138004068078155800181c0d19040020f0040c201218910f8000140c2000d4206110b142044040800310a0381441101c2140b40b000c1180760070002032604030f910380450744904002a04114010f0001800c6030a4401c1c10b14052000c80390315110035000750b0710442418450b204c8520108014064950310101c1c0ca8031b007070b0040101a04d00281c0c518a01400f07002c19a5001a4403401d22102412020017542004040c01180011000003403001440350280c88007072800ba5144d48900600341d0180c221900401e90105000e14003280038210399010b400d500384002c1d001d10244c13542d9070060b18040106241c003085070404014803246802c061090b1508664000c0350f8401d0b4070035a85408086070000402250810542010b0206500e01001150b010700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933049919 1250 933048669 933048703
    0x3040b1b19030e041b0207052701030f020a0806041a06010e0f0d0c050d0303090203070b0331021003024803070f14010c23030603100606030608 63
    0xd5031990090529031407030000804102007081400320585a40e0041a4003070340c001d42d1000c0c100400300f0f01035100d02040c010075008811181300d402c0720603921124000303071005088c4803021590941c0c41d1207030f22058481050f40c206d0346a90380012114020801240f00f2402400c50710100b1307035101004117004801a080358108420350680700803e0792100d4842e840c00e4801c071900080700d9a58604101c50030300550201c3d074804000c4911806141d003542101c15820710880130360700b40d680c03039240407080d41c001036030746190040c41f640d05261425508580050016581d00c2078421442d440c0c1e0025919039200c1700c0030b0f40001d4010900d240f402c1c1c0030000d0340742c1144601c420411600c00329640b003c400860140100e10000c41e0164551820209100301c6904c1ca41112401002c14520700b00101601e01c1011442000d609c3c100c6042042441054001c101c3d20924440d000e480c4000008082d02c0e40007d096a6031500070242010a10520341c4102401000c0d03503200402d609150888842c200781d92100300c07803004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933051169 1250 933049919 933049933
    0xd0c08031e07150218120c0301060e01080309120a02220b03070302090a0c0311040306061e0b0d111c0606020c0301050c03073209040e0a0c0612090503040b1b 69
    0x50f4400c07495100c1503401e2000140c440d1103008082d07410704000c0003200d070048031400250340c0005020501c02260203098000303009566951001c0b59202100748107000003a001844011030919000035260303045502d04044940d21052900025480400c031010b8a40300d040140035207120903100d010300c00592804602502085103150007160154500400560f03a0030355903410303401d9882c020350124000818840840b42c86a07100d241c80c0700240078034000c2101c5a00884056405c892015086d0000e4801000c90a41042640c1c000321f07020301501c9200041c610001c1c000c0d5003254940e1060000340381d140b042c012600c286051001790074481c0314206603000381d0520040042900c0c2c0c2604407900081c5a01d0300b5402920100f494000303040c42c5000418011000003444030244244401800c80c0050856042104210796a015a50384140c11001045d40014007000c1101c50301034040440b40028000b0081035880440d03607041c0c2550302640003510040000b042c0b00411003031000c4160150b146c83e400520300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933052419 1250 933051169 933051173
    0x9090504030c08090d1502070618030c020411040e070906120b0108060f0a120c030b100e07080601030b0a0f03110f090a0f15090c0809030a1403060d0c08031e07 70
    0x82400b8429015058102c0024220215190340b17030750502041c0c000c00e020024400750044100694000c1c04161840d90601c164100b09094448609101e9581501d4030004400d541c4e007403101821a4040c0d54121481c140000100540c2d0000060700c2036015603100900b003420450050b207522410038a8418061a02e588001c0c280d0f0010903030b90304103404454075294040c0c0c00d03000800c400803d400c146c50340c0c402c074041c6408002d2881d4014098078810b804c84450355840c504e0010380b0352103510449036901c800b030012a1045010303001941e000030040c58045405400140800c0d401d4109602400c00102144010018014031540f200c1031220100d9501c5440200d00c03001440140d00940f1400680b07590302d405501c581b80a6002c00d416108080c023502543d03580d50402c500500310720f11180007090201000409145000c0300300c13945410035807a80b089100008103c0415a00000e10783c0ba041000041c0b11008a10864183e1000304046c500550fa54014811144607034281c40c814180504414410040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933053669 1250 933052419 933052427
    0x9040b0601081b0f09031c17060603071d0f10090303030b030c030703200d0f03030b0d02010207140105040b13060f090305060c3001090b0a152106090501060909050403 73
    0x348030341608009611804017a0009042448071401240305d80303c4480300a003055000740c100881101550300090342940c0c2e21741800840e10084802c400040c004103032001740b034122120032041c00400606294500c0300114003250711030421422800c041000103104104050381401401900701c030035070241051744c5001000c0780c0d40303200307500000740640c451020b605200c2e140b005603000c80b081d006101c06a518020f0412a040913244001131300083d0501c030091402d410125585505c466040c0d000741140f5151015046c141196404043d0401104200004038110b01c080501003014040704281041071411001030501e1150280020500c5600541040403980110314a980092071500040c1e54003826040d5100d08052003881e101080c4068003040344a030044440719060300c40c9a041041000d51450403c52028581d1060641e86c031000d54000c1c00b8544503040c40809441c00200010740030002c002c010781540e2040c0c0180b01807543c0d42340100900342d03110751080010520070700d041115040c945c60040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933054919 1250 933053669 933053677
    0x1090c03021011030a0e0f010c2607050303040803070906021f1d010e070306050109060b0f0a0203160f02010e010f020c0d030e03070b0720030d110c09040b0601081b 72
    0xe4450300d841044505000d01500b008141c3c0d09a43e016a6501c0411820150640840402240c01800006000d80c055409010002c10303054001002c04185d00c0300b081e0080414060282c14017080070203000b480b0000b03008201441c000d6100300705803134484c64502c0f001810741103d90b00c0341085511038000c036020300705500b040b0740001d20700300c40120302c201c94050381c0201400c43c055104038961801c3e881000e02e501c007081d039100307a92150000307003d9a6614440003040d100b4502614000c09010031072440840c920710002d0030040524010350341040d02e0301801c00e0f601016050180c500075281c401d000110b47c5d0014281c0c021100034284060300c034007840340080d40d0780c8140c4042070251a201c07865a00389070041140c401c004000070200d80c07145d0b03194424045181c2020000b140c1594040c0c070300c45c40001066510543c581c0740540200a40c480d60b810031907940303d0000c03034a0154011204440d24540300e9a0075070341320303502503005980b65081940005204610040142c1708031180403001e1030010488504032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933056169 1250 933054919 933054923
    0x515010f030f110c01050a0606110705010302181903050f0d0e010804170c0d02061b030609100f06050a0216150c140d020604050d08130b04050f060901020c07060201090c03 75
    0x189080422401d0401090b20028503c0420008261104030328015084103202e0182035800303200c41075444400b6211000203618003105500304080034050780d4440d0b4082c00080000454004030b101480740800d1a01013145854504054070b69020300c14000104101b240414006004003445844401d000303007025400e01d5520304212084000c00c0034880b1142044203805002614030740c3c2d44201c03547c0103aa035410b81107050f026020f41c00000b0080c200000b0440c07010319000c01190b1456656108008002c90010b21521070034220a002280c00d65080341c15001510b4191141940c4094408010b03142182c40c000001005100c80c100740500c010305003a102c500d080c1410300207000350b21850300ca2100d0400d00000c0d12144034102d4012026580003410354080c50151080e641140714515040780c41074001c4640c0b0b98664810640280081c4d10040c00c594000c0c05102541e40617039078820b07164180705055a40203500d84d0003088004141c10300744111401803d00c0d00081101c1407861f501e01503284054440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933057419 1250 933056169 933056171
    0x140c13050d0303090501051f050306090303010b0a0c050a030207091103100e07020f1515030604030212030402060d09061a120a021201150b04081501081c0e0604030c090515010f03 78
    0x80541094002e0300800d135019031100c000d1000b8601104c490703540340d56040c4042c0000307440b00300000715410042280c0703005080c10000345282d607003032402a148a5110f601c00404022104120300e0100e8404e00c0003d01041c440d5014040d018a851540f41c15070b9108200038401c42c108000340003403d075401d035004c000c03201e61041d81d01855884c0501a4244040408100242c3c000e01c07030031a16031081118618071480701c1e40f13a0050655460003e06640b1802164020050391009040701d1079200e2a0340596882031004040078580b41210418905a4409400449189841e141351590249180d01c2802105005498000c9040f5411000340e6030b902c08044064083c40d403c2c07000400f600001e41001a800c149050000d0606a5500c25801a90711a2003004101e0007410003100d00c40754000909412a10700800034000c2040c000c0c0141c1103200100074020500c00c05200c48401a1186006800198025030301c038803009142c541c50b401a24001041c0341c5010001d80011303511a030704006001958079007898 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933058669 1250 933057419 933057439
    0xf010c0b07090f09020c0d080c0a08090a080408031306030b1e0d141c0306060e091801180215040501020d050d0e01050112030f03060b031602070f09140c1305 69
    0x542980c2140c055040f4180040039100082901e56040d002080b010010030100c490303840b00820120303441d4100b501c983d010310004024400300e8a108071012a0400c00641c2a6160061180c0da2a60300b41d01642c4000069040032600c01e890b038140c403940c58002c014506080c410b04000200048040e205000203e403d500d608502c2d0015071140c1c000c001c0115800b010901400070280652940d43c6145015950114074440c011001940310380a0301c004c1384c640ba11461a09103c041c200204034000a1951150700c00e015030302003101c4000d0060304802590698040c042554900511040350707002082109e40344400c2000b04a940d90000f500c1d10f81451a1500030303201d02600303103020060102e00100c03040ea5800d180022a4001e83e05011300e0401d8400e48882440c104054410f07030035103409100d84411070b2014000941001850b0050203041078085c81945c0140b6101c6000c0d0f92042842d1300305c20704080c0c0c2c0d0f00316615019032a803521078214112440300b1b0304202c92074860715030041c203901800d40140e050700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933059919 1250 933058669 933058681
    0x7020a0209190e0d0918020403080915070f122007050909030c0f03031504090c03031209020405041b0b1303020f1201020a1d0d0305031303170903180f010c0b 69
    0x30b80052110f01929094403041c07400b541000342201640e00a500030a002c03c4040700002d07030644200c8041b640c0c45401c060070f00c089501003103d406210300c20900409020841300c00000e0704284801c2403a8400e03005030701300030036802004200c1d0300083c54040340403080381a2491078900010743c002c111a0200e07541c00d0181e41d444192800c0d33019140090540b0b21480a000d0f0303842c01c010000d14411486c41800b03103046440c990400c41619480b8201901c40348031400c0c2840400d1080b2051a0101c0040d940402c1c0e580140d0701280c11140f04841c250347c200d4084a04281e50780b401100341c0c00500c0c160811070b041181c901d0880b469400f0f10f2000a1089030450840403c0d42c40e08104140c120301085d00841d121440244094545c01801c15005013000e0030501c0c0c1d2a00740b400c00c542062890b05565914210303901c0703034a80c18100441d40c005905004440c07949400d0711804442d5a449414150061034440030240c54986100100e01ca007035104410310341c081003099a0000c04001e000d5042403203601151240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933061169 1250 933059919 933059921
    0x1209020a051002030309060c0702100e0111030a0c050609070317090a0b1801030b040203270a0b1e06040b01080a02210c0c063402010209100905010807020a020919 71
    0x15510640d080300e080400c42d558030343c0100c09103102d03007000015150302d42c1c0c2d20481c10000d4800d02c0300082d80304502c1d004000207a48105d45c402250041818040d12001410100c1403541e00401c00190000d1108403040081007001e11600d83c01280100080c00c8540c02d6070f5401c8542c01801e005461030341d13404900d0007032550b20100f40400801181110540e100d10303124040308004405401c00e400319040c01155242410103100b228450b0039031000300c2151500b2400301d02c0b95125000c030b28445920510a980000c5180070f12000e001d804020207034155181d01c0c4130444200b1030001c00329445240350410050259800030100e81d40709000c05001030740e0b941c3c0c03100800040040d0480c030103544007601040291700342c41e807002401542e00c10000c54402e030750f9909800b05074460301c104a103500c8071400c10540343c1005400300e6030200500d900001d13040c1039407800031a50490040520078001000f80d0300c10080c035600511131580040716031001d084030380f817250046180d201014080014904214036040112040c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933062419 1250 933061169 933061189
    0x10312030902061305270703020703030204030210200609060403120e0105040803090f060c07061d0604060b0f1002300309030c01060807120f0611031f06030c120902 72
    0x4020300722620f43d102e204c0c684411400900505000350b000210176003118888480c0000d54401c554030020380c03070303940c00d1086000c0d41140382c003103041c5034082c04040b00603540c0590100c05240c0580d2005403500030f448034036600502c455905c42c0f450704801c040c40f52034500411416801505414800300304600301a00d20014088942e01200c0740d4071f080309000330440c03014021400340307000c0e20481c0c0e004110158941e072944026079450003140030410078800000d10701c0d000440d20012440c0c01101c03030500c0701e100d9820f200701102c045079007590ba0003102c8158604000d007180035070300540300c0000c84882c0407000b03552001a4455043c25400710700c0207210700c1d246190741e003842406001c2c00a85034281110080e0341d9401c0418400300950070404041802d44001036440110b444000c10080c44a619480d01451030b0b40e06207041d07800b50b8540400d00c065182000055000c2d00c00320300d080b0b0302ca140b039043c402230481d81a04400c0415042c41d8a0712100c5611108a409a699015000942c00c0682c800100d55000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933063669 1250 933062419 933062423
    0x2090a0b1602100f0e280902030a1413020f031c201204030b04050309120d030b010f09030b22051c05130e0702011508010204140d0b0103120309 63
    0x141d01c0101104054503908098800c1d202529051000c140650740036003000da8503000201c41512041140c0b0701120180601d20b40c0c0103540c4180c0441d10303901350720750700300b0340003201c840713030004140002c001481c030601070544c42818980d030760f50819400880701c140c2d41c40700283c411050343d1440340041d58240a101302c41d06c55803a4422032011440009402072072841c1540001c0d120034691120340841c08550740330302d0303403100c5901ca1274182566500c0203251000b600a4070b051005000c102040c0d00c544168680581c4100001d02c040c1c7d4030b2400007820355031a094814100600c00900703041c52074105a220042e03a40c0504400415915810404000e000b0780140034580d400c044c040c881441004981119900e103c40c0d00100c1e0114201c01c192101d1240c0001c11406149800b410044100314440041e0801d09510011440584840c5102c03000c40680c1c1120340e030342c0d42c002401c0011070701100605031018002e640c4800c56a00c42d40364610074402c1440040c04021a248000d40d07654420381c400d03801d5036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933064919 1250 933063669 933063689
    0xb0307110f07180501050a03080306061804060b03010806310203011107030503010e09060c0a1d1216050a051e1503010914090f0703121b11010810080d0302090a 70
    0x20b03960f602800e1001c1210514480254038110021907281001e0707081a00b44da0300321180b149161941024401a03900c0040c3c824640308803e000c620b650366460041c44000c0c410820750949039418102220308044004e4440102154601102c860807c03140d8101b415611101c6140034402c030725400031a0140600050f595040c80700055140c04142d0040041e505846003006246650f50395412000e507030307180555824a64170307414400b0402c403d104007054484440305080c0468400620800300320380c16211180a5190307003050090901c03032511444480700510342103070090000381c5050040b03001c0c0c04441d92003000507915048200f9480c1ca90302c1690551070002011543d5940e036032201640208080002d05203540d0032200483c94560001603e441d210000c8806031041c0c41c51035072001490b04010350b002050003002c86c081010714149151280300e0b00d004901c4044109900e0000400b4010000c1c401c0005408030320080c0300000000030300b550a8000303810016902c038000c0d00010070140c40360303004010782 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933066169 1250 933064919 933064933
    0x31b02011e03090b271b0f1f0305040605060103060605042d0810050c030106170a0f0f090614190c050f0c240910050a090b040b0f070302040b0307110f 66
    0x4100f03140b40c031128a01e020176000e680031400d05007681ba03841c00c4021034000d041645910017a490718101c1d82906003001400b00c4008000d003107040304026601500305004c01d0344d81c02004244082e41c003032142c0c494001d10b400c00c451410030308090890f00440c02004080b0174000035028a0b02031107020b81d844800300688265015650700c0510350b5411551402d00419410b0501007403034089604243e074107961130390304d92030052044c400300183d01502c0200640d0500743c588140840460b958840c0700c2e980d0406000101d4840e00c14144007055407562142070038000074000400440300c20b02d946140301072030b60310000324480c03802d200704441c1800380d400e0340b0400700000180c1c480703031381400240300c0e01c40c000702250110300d445119003000d070585c3c0888bd141301e07d070424040354141c8003650b4012035102908030760004506056480d54003001d00200c404803a07444401c8284403288503802103090f4401104e24040d883c1908040050000740405401d4006000300051a00c02004040c040d4001100800c0106d80030303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933067419 1250 933066169 933066181
    0x121e01030f0c090b06040303050705120409090c1d06010503090109050d0f020f010c360b030106120504030504050d260405010e01020c0f0d1b080307031b02011e03090b 73
    0x414204000704982c00e002a01001a81c0c081501508070207041c02810242004c0c5180c40a076216442544200c0710b07402009014000024884040d2026115182000401000c0c03480c10004282070b0750440d01002501d40c54038003424100c003940c070390700c0482882e10607200d8440e6802c0368090109184000c00e2070203900700c6205100e600204014200240b0340c200c8034075005d1400380f40c2c01c031200c8964080c0007403400805c1c0c40004801100c100f0040e2a042c80001c0c10020341c0300c84a0f1903d600b60400c44400800000420803a50300844840c1c0b0360042480401c414240750f07401804512940c4900c50141c2240710824091002c1d82d80109810b10900183c81c01d41da0800d41d4800083c0d0103805064081800100c2c0e41c03015510016000f103007808058507000150400608101c0c48083c2500112040315402c80701c8640d0131580c625040040c00410001e5032140360614020b468961445410003045030220503910251f0780c021611b070145c031000300c01c090307980d4804401240600960350002d0304c0c4c40259028844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933068669 1250 933067419 933067433
    0x90c050c0c150d140f01170a080a050409050a090606050a0b0403060c110d092606011e08031602010e041404030807140406020c090903030c0307050c0a020a03050109020f060f121e0103 80
    0x40710301040c284185c203682c0c8031100e41c03262000c90f0901c9200c0e0fa0044c6070b04800500800c0040c2200045030502c5410184e5914001c001d59508a54240b01c4c4c90319000944100610b500488000c2c00c0304450084402d0b00300214200c0600a500c03014007203070740b113201d01c403105809024444003d5171150140d40750b410794600043d1084405101e00301105900103903002207101c03441016081d4124030009440543d103002010913036144091a0300001202c05a40040e00b1036007000144040205140302d0515a50980005040032540d45507140c0a2820034441940d94450544c405da8000d605051001c403d88412004580d843c540b00e000140407440010301080141c0c000490540e014812101e480c85070340e0b88034031580c49002c00d48280c07040c6102880841c141c50701070b6024141d1000b001d411501004980e80000d03903021010340c42a215a551000d00000f076080274019890082400d413065403034003900460481ca280710b243c0300c4000da9400180450140d280c00464103220341d050000d45010340d40c481c01d10b12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933069919 1250 933068669 933068671
    0x10e122205060a0e030f031e130f1523040b0a09090e070807050d030c0b04050f0709051602010c1b0609020907030c08130203070b0d02070c0609090c050c0c150d14 71
    0x3e202c1e204501d06c90740080e0000086075130a03611064180c0e0070651001c00c10840c0e81120701c44403150320114501250802c2020507041c0142050306400c4105000020090400b064034065541d14900d1a00c4000c2e00c0140c00d021901154581c411079952003a01c400102e440021903081000c1250800409020500d400143d041c25102100d05468040355640c040203007440048200901107070f140505100811600318029a0141c09101620001c00d15241043c0c00c1c24441c0c2c10020703401e50307143c041c000c0101c038111000064050300d00080007409031040700034090104150b0071141c038900a50308841007014640050b00400c0c1c1c09481c1c400d0340e040400016000e8030400c0b000000080340702e000030308100f0f540e140152000d600640076001072800e00b0b10414a50b80300c10a02d4160382d401700209800034103c225420b00605450b0703911113440d070420000c981504d07899491481009010301003a05400b20200e000c40360800210b891151600501202c0402802020164001d0038034040410461a074284401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933071169 1250 933069919 933069947
    0x29030c1b0c0319110415090f020a030c1115060f0303070b01030308070c0f02060a051210050102060c040f0e04050705060f04050910030308040b070905190503010e122205060a 76
    0x14030050890344503a02100b0f446800c0c040e01c1001035030080310790750070705502140152005114248050383c4401d2000c0c10b4a281d034490480c250343c005403c1c4106030781407088405c0d650451402540d0420070b460720542e140a140d00081a0300c000d08007095043ea640132400a4a0b8406829644c80e5040e82c00e00c49900f0b042440150003280145c400200b005220b02e03181054241c3c0302d0f11071080341c0415000c0c81380c0f039000103541c03e050220420a10042c1480603604512624070311a004c00d1709410f000c0028201100134091201d001414401800001d1b01842082e040d10074102030303804140c2c0c4904000d03240074070707c0e8841c54000400241d41006540c1810041c01501d1094644520640b94101c4500c094240c5200103070000b0100c0d8040b600044454505541183c054984a5a655146c06c00940364181200441c0726020005200f00100d00b000c0c01040002004c06001e801c3d0418594803442c241e105100c0120007803020350720140c410615010b8030002500e0041e05558850f0888140078204c64801400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933072419 1250 933071169 933071173
    0x180d0903060c021c1b23070504050903160203031210091a0a060c1115040305010e0102030405150403090b0d05010501020118110f241329030c1b0c03 65
    0x1481c0160000544540c0c0210101100d40c101400d13841c100e811101c0d91160398007500080c6400808507801668415014140000341c80070403080b01c1d0300c0e40c43d0020940c072050040d0300300f004000c18404040140e03200502401404003a41003544002800c511900804100c94003260f8203200b0400b14881d07904080c0c401c0080c00300105109550046c0159824031070f03607544003900038010b2014034400e10102d90f031144264203d0f1044540500010041c403e90440c400032410b02107005c0041c008240540c5100d038801000844c5582810784502c0d44402c022381506401c0d108038808035003054441c4032000002c000800d12140c69041e0340d08680c001e81002e218450042d802c2480701a400729801c0c000032010399110300e0040f400790300380d0240801484060a96036002405205c680307004d00c5c0700c050b000c4c188031040804941d1881c00150314201441c0310f400551745400304013105008921030000c8107645842d0952401e40340d641e03001c10f0100e82e11400711011844000e854040c4030600c0c0c0043d00b08003071942201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933073669 1250 933072419 933072431
    0x9051003140604092a0e2d010e0712020d09051c0e0607030806150c0604021f020601090506040b060d02030f0112080a030510120c05030106091a0607052a10030501120b180d090306 78
    0xa00507041140a01554120007000e00c0820ac46a00891030b8000b1a01c07185c0000d41482608880e5804450120740117070b0b15034001e09022261404400c00c50004443e00b410032070b0880080d800403480c1b9008208000b1b06100a00b0302068060344c6100700f00400b60046031000e56260525031b40252136180598080740030381c483c0c1d03641d056407881c0011328010380d11043d4020015a8078205660010b01006815071340c02a0392960a94116159007000309221451203c016a481c10100403200003150143d00101d040c0c03210118650000c0c40c403004560b25411941740219054540c5081d9084031403850f441003802504656001d4100702e141c040b000201d0303000b03c008100d9155502955019030b907a04003c01501c5029581001007440d001340070709603103402102220038905486242440c209004520541c1c00340e1400c5008880b0315120006000300d03081840c00740900e5140040c01c000c02c480c11500103080a000303100041f002c0741c0002e00866001d1042084491100c208400640746484900099508a092034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933074919 1250 933073669 933073741
    0x312091403030a030b06090d050c10020c060a0c03260f1f03080d0212091b0a03030f0e1302030a150503072409051003140604092a0e 58
    0xa10348100e0800240195282c5003d015040b0b005000e84052254004070610801e040e5441c0d895a480100b0720940041000c0c100c0f020400800444041c0300300704641c00248124650340740d02080d140c07038030000d0030308211001003864140c94414216058030608034000c444000b000c4884030807280290400380c1202c0407515141064880101d0026405440b01d0302c00703404000060032800104a040400080141000420345049500104c103071080010b541c00858102000020410400d0704000d0440d005940f2503d5942c014100c0398120601406124204d0741046150310b648400c001540100b04c000c564078600400b18000400796402d10081d4030611000100e01810000b0303a41d416541a119480c001200030109080840700c07451a041c100a40540c00140644405202c200d000d40756032000300340401950382600c0b18190052909104608000300d83d0b002c034070b54580030b00700d10168221300c044075100043c109030031694a030b111030407440c44181001601c03102010380106818041c02c11404ca00666 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933076169 1250 933074919 933074939
    0xf05010302030c060f0d090b040c0b0c1c1b0b180303010302091521060601082802090402040518090118030e1c0b07090608012c130c031209 61
    0x2404029090fa001961001c0d061600601402c0c03032004002c50989020001e68481d801e88004c08012140307581000184000c000003a84a42c000c0c2c0a06480c680c1081102c1c5409683c9242d649403034804141203289103110b481c0b00c3c01403201c1003010142040d90304da0f850320701400c12090032214420f081c012210011405480801124122a001402c00000d9111090403010068612181e198440191741003508182010120784282a1445000e82094940300740090a01700c80180301600407060003100382c8503011704800000c44040704bd4401030f181ea1241c0c020034028806c9804c8590b005801006180700607803015041481120000d0080c000e20040c4024925540201d900043c0410040b8404010904000314500e0200c03850340424404504076481c1e1410010042c1c40140000701005010308c030080d080b5040030f0041120343c02a42000e180c00f1f0680c2d5064a080d006008141900382c08945401c0074500c40740c503241e070008155401f2035a84e28208280340c040310340e150003117405a10009050304039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933077419 1250 933076169 933076171
    0xc210206070c0c210b070207061e0c260f0d110405090a0209062701110c130f02042723040209061f110616090e22060c030f05 55
    0x3c07260712204000d04200f070902281540d401c00d0104030000d40c03010340100b54000201800765001d900540705480c20440000d200d10308404202048011190307060034002d9004070070807241c0e5082002c20540303000004100070228030040c002c0492890110f000700400b5280e200030300c03e09645103020840364201c5208040240611b2090590052082d00000c2c0c23540301d01e4005144480c0d004000381d140032005908122a070f8089400d003070b007081c1ea049004082d960020182008106104020402c0011070300c001210000c5d459190440039445042030b0210a0068061b6405803c041078001401c0c2c50007105c1c0d0901c40e182844621401d411300c40002c0b041081c101ca0f00e00302911b03071426070640e41d80e95000d0109010b00948600d80281c4821800c186180718008030045180c1c03d035447d4061001c1d0035550358608140a820045600489042d10f00000e810101074000c0b1580c0a10014840e83c41d8180303070070484101160510003110f9801d011341048074950180c0104082d42d10308001408541641c80111a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933078669 1250 933077419 933077423
    0xa060620070b160b0a06050909160605160b0115021e1222061d0402040b090909070f0902030a0e0606010e010302091302070b0a11070c03020f010c210206070c 69
    0x1c480c0c280003180ca41001405441820031803c060300c40159501003003803a089808004503541e8400602c00d61400c0c000c41a080005800180b0040c09a1800b9042c0d5540341e108442c00d00000182d03403071603641c00428502e502504012203d1303032580d641c000124a00c483c2480300d001030091990755031010794007400710b0000c0c044003c000c00150544e44c0c1e06480e070390b0020126100c10382e10b020b44824108513110102001d000d455030b0343c40080f110700c80300401c100020105030748070701e006010a20428100c034081c0e82c140032080301c405c03000e5150300c101e440c204a681d0700018264500c01d080030544032002c2d00114003542649004100703207040c0c065140d0302d501054036118002009448041ca9942c881d0300500f6008c0c3c002003a964040c641c00d00c0c03010491340101c00441d103405420b1f0801c59400c1080c817030b507031410210003201440c200f0709549030003074504507010091041d900300d00036236280c0c2d100e0010209026444081da003004082030000b02100084007280b03100505c140340c00030f0b03c2c0c54812042c680c0515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933079919 1250 933078669 933078673
    0x912020f06130f020d080307111006080325020607211707030f0e01060602100c032703090e04080324012c0301110d05010e0f04020f03010f050a060620 66
    0x14081d543d1a031103414051060f43d01c48030400901d07011070030b414020341c029402074403980c41d40501c0171261400c140c03021841c2d00c0050300e060010800e07003001008460740361064004421012044509800342541100e1019412680102e415010030070386802d25486540b0741c90426100818103403013202c3c20f40178180f40803444c2468001040c04203000c4c0d003251a04600803c0c0128179000000c5101d402c4440075407006006030321944035580c00006901c21071515400501c0e085c00712081031006829001d0b01d11421461411850000f8014540324852000281920700724841450a02d4140446540c0007942c40c0441e244c50f0013445150102d0555010b0b80941c0103841c1c1128101b000507241221040116064010042c0e8030b02480290340d00f88210400818081c280b6074940098156410444005811003200700100701d007070082c80892014101d034060340c1156007098084122012034007518940e401c0d680c165041c401880700031100e80c0c01a001f620381da95650302c0d030501507400f003108032492403824020342e07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933081169 1250 933079919 933079951
    0x3070509040504020d1e0204140f07110313060c060506030a03270b0c031213173001060f0212030414192010121d010912020f06 56
    0x781003039000181d000d13000512142071000305031600c1c0b01900f0707800344070700301c8040404c1010214609441466000381a800c001e51003882d110403501d4000502034003807000c6c000a10760082580c0c0082080704c2041c94084d84103090a031740d816000e040b80510f408101c0d001030038040094868200020035024a41e0160f50b8003400800340c1c8008120354a044507801142200140c0c0850340c801e40030010b081190300d0b8001181d6450258201c042c150320003401e08000d205940481401007820802c0400c03ca0f4150441c0d969541d500e0003d0511924810801034001d0621407400d010745503d40280c28120f80c05a100c00300201d44d2034070101c0e140d10008a08901801c2d090000c64042078810484c0010b0504c2c210484521404061018030213001001e8201da0040324250349001c5000172288640101c03505550729600700c2d1981130050700f1403034810100501582e484a181500b0726180700d01070310348403200000300701811050529801002c0ba00d20a10058490180f131407800b200002105031041540610350000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933082419 1250 933081169 933081187
    0x3201c0f2f0708030c0c01090f1401120b040c110708012d020c0f100b0d051e010605060d060801050f06030a0312110d1401050306100506160c121106030705 68
    0x20030500c81006024481c0b80d9003c0382049042000301051408900200b4140e80480c000402ca85816084a0192614040100100e9000e003010396102c003000d00700003840040400004000341500454198881d007000d0a0b62401c5400c0312918142d03038107460a4500050b01c48004a003619091030200080030041010402e03008400c0042e4402841075140140c90072801994040c036045680c40000040d4000d00515208440144074041044100360340c4e1210703000d4a51229031b11552030424070003c100b01d425000c48400c50a600840180100406c3c1c0c50b00c1d510001000001085903000b4010550f28140110700c08505101199104101c01401450b5076101503404680310341c880152440007a4491000c0202500290050f00031400a00b000260401101e0b60002028106070700c401e000b0341090041c4a00d0200d44410310b02903070416110b143d5602151881d038a800010020050486a40302038089a80d219000b41e40c5100f0703000c1c10b032802d03408542c442004260710055490001141041188003a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933083669 1250 933082419 933082487
    0x20103020c01021e0408161d0702070f080d1202030c09060a050d05010321180515041a0c06090319030f020c0f0606130e060403201c0f 59
    0x4a140c4400000d03091040c401501c413510b820500c42003090510210307042c0440001004010400d00f081c00f0130404c0b051608030f036540440310310910b110603004408002505c1500270014400104500100f01e408140d5505189880f03007a5010a040062505030401c4c02c1d1280d10f009032070244050b0391400b490807100c1e90402c03041d40d005c100b203041031010a014601c084800c0e803290328002c42c0603034801e6032035502503101449404401d03500d44040c099500e420454420f202828482940e00503102c4a844410243c400201ea004070f078800c1d840365440c44440c840418403100071b407499001c40301c220f070013503100c101000e906d0380588080e040b00c5003040340751011420f2007038000200502d00d10310014074094600400604040d00a1800503540d407182040c0301d40c604080741a2403c001c4100c41c00c020145007460125150355001d0006010400080e4250709490400c9000c8003c11003004111074200868035104c1c1401140c100c0000f02241c0c0d079004c09541c050040c3c1d400407603a8228020101083c1790000c0d54a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933084919 1250 933083669 933083677
    0x5010c0209013c170d0804020f0310020706061d01081203060a030f061e0b061204020f18040c15120e01020c030a020303101e09020a0c06060e1e07020a02010302 70
    0x41030381e03c50206104800c0000b1480004980d6881c190b101c541030404061454000204c442029039910400e460b102c41c0382d00c401c0040c0c100c1d034103c40c1c401250000c140083e151191502484040351302c0043d40743c0410003140e2001d400ca81030340c0d801c40000b17075080d180303158402024840c118050300b050f250082c0b460700d1080103542c0030000501821038030780c890315104c0c0dc5400803c41141c1441c0d443c40e1041100d000e10400c00c10783d100c0c20b0400d00c114032170b204c04180a030148c80c031080000324005000c501159100701850244010180c0441d020f0000d6460f00804864256001d07a1041d00110000c1000c948036482c0414400082e107510709020745000f8110010300a41d45442c5895600344004c2000510500003402c103102c99900460700c90030204c0c01000d001e03003a41e1207004140d410322a07103886c1d5805040030004440700300c030380140c8580f9128805c0d1203d00d5800e9000780a24603207507001c40c0e0341d0402052a4015002a02c0f035525098080c081085007400c10f41d40040568091005180150300c260010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933086169 1250 933084919 933084959
    0x10c020a11150c16170c270c18010302070206040314120c0f0c0307080607140405100f0305070c0b1f18061805010f121e060e0705010c020901 62
    0x21a0380c0e24104012000160030070901c0c0100f0313070440f40c9640d480030521034070840680f407000c180b1540c610400034003d0343ca202600ca40381c00703440403501000401503111400c25031243d000031040300b10b182070038482d011130740601c903a44565101c290740c0d207940303505c40d00c04c0d43c0f2440d40c00782c851803a090071500c0e001d0400016002030f000c2d6108100882e002d40e4050005428102c480c80020986108a180c0c1c090404140c1900b25020740e00450301042420400200250003000c54101304200500303114046519200b0b507045140c03c040261400460b6036482840b02c1070340107155804000c15103501c0002c884c0440e4030340300036156003018004143c84880e4460311000418007447c8007180e5070790703940310300c0704a0680040301c0c600141e448608104544288640c0c106800f14000f0402c00c66050204081e03441500340154401031070740c0032203481005803050408109012072210f1002c001c081d0700d00103000c1c0075080b414030003030302440e400007465501501007603000560043c00408140c1c2484032140b0081c01040c24 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933087419 1250 933086169 933086179
    0xb030102071202030c011a06030103120c0606030317010b191b0203010614180106090e040303020c0336090a181209050301061a2b140103060b03010c020a11 68
    0x3600c001a241090039410b0511034001d10b464400c40d02d1140d003140c10031400c105020f0320642900e5107a1781c5e040100d0781904c0d80010045842421642c1c02c46840500d400020650380c80c142012050540140580a0700080000c1d00c03840c40c0e889800300c94060244443d5101d05031043c070300304d1480328001d05100740d051940903070340d4021291030f40009094410f03980c803c00003140800c1d1081018100506480c03151070002e5544902549042c000401c031402c1882140c3c80c41024202150405120b901142d03220741000081700c0d15542100c80c2c84195045002200a0380020340407140b84074103014500c110030680061646401c2d0752800c811001400d030001460001c5480300c103001000401128481105000b1590380390b80c080d00b443c0926003100c440d078011b01c92400702c0a000510b1010050211000b060b11100b0880c48005001071f0f800d543e1051045a0840f541000d04145420104144440c1264001c400c00e00c00c04801d101810f0032a414400e0090058220b04044804510260a824503882c4003400e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933088669 1250 933087419 933087427
    0x117010c0306031e1506031b050117070e06120a020a090906051003090c080706080a050907140121060b07230606010c0c030b010303030b030f0d02030d0f020c0106080c0a0f030c090b030102 82
    0x5c814100c0f0b096030011104203a19840740d42001c000080d008010340307002c1c28100c1507004004c03d07401041000410070010001002c040790030740c4c0c851400740d0f500c045034007c3c0002c050070540d00c9440030b500a80f281d9000940c0c44840000c1b0f40310f03540260004c8540107809030100325034408040b80900380210043c0e629840000000920090401c03429000f130046981d2113055042203104001510805090070399681e0200c1d50074082882c815100340f540740824249600f0520300d50b52881c1400ca913210010650030b18165002607451504d500038601e403440346a0b0701050702441d84100204200c111100c12b4140d014030300241855000c0c0d400620218082c0c000b01d10400e96903595590112401d030404c600080d22b419041455003420480402c241001801800b0f50115981e40250380e4082d1003401c400d01c13520713003643d006420703690350440304c4000c1010000c3c40050f480c0d070009507a80c41b685601c1e6000d0385103000001840048900580141d0ba40541c0882e0031605e00504440034082c1c02c90300d683e040d54208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933089919 1250 933088669 933088703
    0x1902011d0102071203020309031b0c040c021e1606030e10023402090415020d06291606021806070b0103110103140406050403090e0117010c0306031e 65
    0x50080318880000100159540b40036140019010007840e12040030305005000740a8100d40c048155910500c4805a00a0f50080c050519180820310345070150000e26003821600102e0340171660400c1d00103103d050480311031700b01890540c0e030303403405028002001c1c0ca0785052004501c2904154620050030341228460303c40300f40d005080380d1220b804070040003a00702c1c030034101c41c040c0740200b01504d91004039006034007042d802150010f0b40041000703218940d004c140200001d174980c103448400800060400c110790b01c500650b1030541422038600c00400a484645103c4c26040d411a4001d424540401203850250340c0c40f04040e4000d940b240d801c0d030a4840c1240c0450311400054080c05d4002c2c000802954950704203202500c0050300818105401c100e680a43c060740c03054080d410942c80b140c0002c09640e9400c04070303441c1240d604840d00004003d000082d0700c0c03400820384075451100f100200a100e0182005030101e60a038440207018610080008200d40d00340e0120401d0a030050030600b042d02010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933091169 1250 933089919 933089951
    0x90702030f0a05190c0b04060b040e030a0903060b0a21030507080f0a140c15100e04050312010504090f1514130c15140c0a020405040c05091b190201 65
    0xa0511080000c038041a8000d00003042613411050a60314140741c80c0c1081d040e220300301c510100601c06020310740c40d40c00b040d0680e01ca0754082c6188400000a5a42700c12040b9401049868640b0090b943c4900b40b881071191482c180c50802c08441418103144d03450b2034800113884002d03e20034015014880f003404040d0215042c1002859002841e525141d17461152080160510314000403c030310f0b4520501500d643c4000002e51030700030000c241e503100402d98808002e10720381d0510783c0146007003040c240248020000004058021240b000c04d5400301aa2241e0500c01164000d13100504840d00300041c880c0031907007010184950040740b030408235810400d52000c00000c4001e0350b800c0320a0034074900f21700a128043d132911000e0182a144140360011004004004070540300100001310000683e20704854801c106480103258090f006102929090070800f5400d191841200d0241140c1000203851512249590b036204c81c20100e0b10342072031405c841c041d820942c41c0001c813043d59a684900100c031000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933092419 1250 933091169 933091177
    0x1e060d11090a09050d0f0f1d040c020127020108240a140a1a1e0c12070605010e04051b030f0a050f120f0913020424030b010c02010e090702030f 63
    0x8a0750007141001c444c0c5403041c40c1488180e1224104512488081001a40084658134040a901e0600f41c20071441c140c00701c82c50000305e0001d034054501441240c0854042d0800f8541000c80c00314071030341e40c882c00b000095502e5080700c0280010340507400a281b0203100c0307890490003005017246010150421005c6400d0382c2140d04031011210200680013660725001c00c040001c0c102e0201200c64100b801c00c0c3c90382d81401045a02034a215040050b5a50b9210311402c1c2c81096210500300c5851000c00034440340980e00022056030014248400071409040d0024490f001d00d40c0000201000d4001c0c2c0f074901c0181d0904420f5541c18003e80708070365000c0c00c0030450229014020f40c00707440d451081804007850020b072550010425801400145070078000841950035070030058a000099200c06820030b4020302c5141c200321880c3e00c00050003480600c800b241260170308055103040101c2c90000c0c0054901d00c1c1c1f0754200a0010740c0841065003281041c014840d04081980100c0e400c00c1044000407030a504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933093525 1106 933092419 933092431
    0x801031118220503040e15010c0b040609050f01021b0d080f160207121a1005060403020d080d020f070b1b030a0b0d020a080706081e060d1109 62
    0x1540004103042c9500c41e0990b0340d0703070740c40f121040307020441902c41c00b80304403611054090342e5001d12004062603801c825080c00640c1e680d07503048090280b6410441d00341c06040083e0300c03003c0c02400500300310450005003100765000d003050f50b0702e001e25130a02c0d44200092481400a5842045080341c1c001c0701d000c01008194240407826850205660f20004210740003a0201d0240680380700f08000854500c2120400c80d26250030112840080d8091598013400c00c200410051500c006500d10040c46104030500305820410490101d80020310750800d101ca00007500c1d4208501d40c4a103907846464410781c250003071704070b0600010350f0100402c0160038941c0d96079050031a6a50217100c1e54880c2e801000d50014a446080080c0c4420180c0319035000304002030003007041010038203001c0c0422034495104440c0c658074035040000e8a142131500755850792141c2c1c441422a00c030b585800340f10301 = true := by decide +kernel

theorem cover : BRFrame.Cov 932913669 933093525 := by
  have h0 := BRFrame.cov_init 932913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932913669 ≤ n) (h2 : n < 933093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
