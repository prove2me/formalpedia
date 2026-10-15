-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:50:24.683782+00:00
-- url     : https://prove2.me/submissions/64979733-1c7b-401d-ac3a-962e4b59b449

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753776978 ≤ n < 753956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753778228 1250 753776978 753776981
    0x102101509060503210c19050c0127090e0c0409060c0f0908060106080c090409062004030308011406040509010e01030302060c0a020d0e060f0a030203040516180207030201060b0706 79
    0x311105503406014454492060544031481c1400c0d000b150b402c81515444c85d0240840504002070b050001c442070391203005050082090b45441c103507225000b41c10024100e50348560000c12160a003059034012921440c155404e072500c91181029044d610750f14205440000d004807488440001c0050012956a0404c2001080c55406180c0408c0040e104a01014011240081120100c3e8080c000580c6032041c01d844c1300c80010b000102103841008102200d070703514410042001d01030040000c4e020780441c5000724490001204100211081c441080000c1c5e101040c07030305450462510080540122020550901407900000c0e4012849400400d07035042d0080d000f412640a41c2c2200d54549070345036140007074800e8600d0300d4016002403103000b0806005000c8608085c1000c0d004601d020080349100d406238000c2da80000000750000140001e000781000300d1200041018562050140352104105d00c0084d03d2030381d80051500030502006041c000c0d8008402440794400c0c444d03680000f0b240050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753779478 1250 753778228 753778271
    0x10e2701050a0602191e0209011d09011506030f0e010509060703150f060c0f0c080f1b10140909040b0711010c02030f1308030d0204060906031107060506010210 70
    0x1030141c0559980040c0d0584001000404001c88250070551107402e9152840c000d0607400c1d8010807180c60811b0080180c9451440e14024040302c0909003d401324141144a000c40290034500c0c03aa04064050a822882e000c0d0101110090308000507450320f0b80c2050380280c00b60041c03090195103081c8c10001d40000c08660300340710700d11660342009a01c000030891402a402805040c9034013070414420704c051402034020654a80c0210b00c80c11418409503550310828449821604540d00120a0907240080800001c02d202d40c86400b80194203002d480851907000b031740365042d01000144419200c07402c0c2210100d174491070015162181e00e2610b8105290000300c00c0d034013030001440300c2d407044840b82410700c11010012011360103149010f416005150003500599400c22803603d00c2000083c4240c401c1008100c403901e4454050f80310b03450320901a00e41100e03a84000207050400400c0d0800c596548210303aa030603805400060140c4034400100e180c003115080d4070501a241417202a0ba1034120041074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753780728 1250 753779478 753779489
    0x150d050a0321050c0306010f1b060b031e060703090c0e07090e1302100f02010f091101090602120f070f050a030306052713030309080f03011d011202010e2701 69
    0x203898001010248003c0b03480440354044507000a2000c21000e6100f805000c81c1140035152055000901c01d0139040b01640d04102100c0e0565140000d43d00c5040520084269001070b0306000050303900382509035100d2030003d052804040da214601d508004031000071101403d04801c410b920341c54030704000b512420890080340721410104000803034000402d80f01900302903010f0510311484003c000141d4080c090307141298255505c450206500c88a5031040304882c1d0b01404150b4403d021080014003208241d40040302150001d017110500e4031680c00031502a40c1042080d15074900a47c104500080450440100750b800351480c14810f041e4142c209109030b510450b01d03106003c003062008050389a4400b00040030340f4100c4001410205a805102d0540f07001e41008954820955075214003580304ca1103e0903400341c007000510449401b0020080c6d46000c04062030041d5040c0942d0903020048940c000b0f0420201866054003034803003880c3c00d03260058040b040c0458080c050341c8055902001d0249 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753781978 1250 753780728 753780767
    0x11040f030b150409020f3102041703070b0c090d12020a031710050103020d0204120f03110a03080c220f06080903160b09010b0613060e18150d050a03 65
    0x31101ca0f142a12844140759030060102050107060414007a81214000140b0b04400c0101c201607101c049844502c03141c02c3c0c41e03a80059650f0704142070398540a0b040e5901c01c0143d8028852a8001800b1110080c0c201d030aa0b45d1190b252840440000c000141040000348502010f28509030031036000a0041015071080c2c0760b05040031030450451040e500c0448400716114000c2c0c0081109501070382c01840080c070300150241c0351545071007205011281c4218101c07545800c0c920130b40c040c5613201400b2004a2001d4000e020707445400d4038000d11600c009030030301c80c90707100015030720060018100e000c07000e03880c00706105221260703154050a40b001c0c0b50f00c90030300843d105000048803901c0200c100ca401407000406090010043d48035207958510003059540c0540da240b8440025994210182403000400b02100302070f00e05001e8010880013140b02040e00860131201d458909604900d9240c0c1e1204404982c0700010b8070350000a034522101c0039001c1c005000e540c03803400605505c41c0304a0303e1403c141d02d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753783228 1250 753781978 753782011
    0x417120405300a050d1a011701060c0618020301050c04170303060d14070e0a0f063203070b030903072612062115090c0a0911040f030b 59
    0xb541002c0d903607807200c401c400301c9601102d010800348029001001491410380c1c1440e00503178002c02102c4120300100b460070341408a2054660340811300c000c103684514042c2c60300b5454103a02600322401c20380d00402c1c1d651582481769503d074071a6903c0503e203800400034080b904101c1e60f0001c650b44503004460240b0710b065484c098060000040f2401000c014100034202e810a460702520a1300c0000842c101e03018511001030074901460407a8041c1d07448240003d880d000754007050382140c0450b8024002402104190010040c0f10804030b4010880c200481013504c00440000b030030201c0a0308014082d240100078807805c95000006001e29a100345400c7c200d15482011440361124154005080034000b003165615181c0f001d0a40c68024401906000440780c03c606081c02c55402d80030b0041d09540304a080310300100340d918270740740c00048000203010254003100109a4074089406800b084584800309040000d110400f1240148800301c5c048641c5520381c40e0517600c00c042650362054440711903c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753784478 1250 753783228 753783253
    0x90d060c0f05040f03260c010c0905100c030c0501110d02180a05060304030f03060f03050c1e1503060a17101b1706040605040c02010204060210020c070501080417120405 74
    0x4039001d48400c105003001d500d141d95183e1b4000264140d941803030b81e21281442c0760886450000c0e0610010341000030890780c101c001c3c020702c0f114403584018403070f60b41c0c1d02001b6405904201d0410351a82c162800b14154000380c00c0083c09080000034580b800302c0300050003a0f404503154003a00d16485803103841304442a80f4800c0002003055801440d81c0040c0400c0400c002038050384880b2501c1c41541004103001c0e5440600850b07982407684141c4190b04202100f0b5000e10340681e0105241302c50016069101e00e40740041800821b502c000c2d000007440003c04103c4558a80c0000c0d001484030400c1200c03070300c1c4184c01c45500c3e92917814964040340d090010221107450340d1810031701c1c0d002842d900d24007100280450507109403c00b614607500695103600c0468a0382b210b000b03c0500d10640e0f00096a11860120b009140c0300d2248031102282d4814031810303c4031350300800c0c600c081f0f40c02480d00881030f450f24104a500429202000465001d0025103a944408401c5032030384203a018105a80b00d002120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753785728 1250 753784478 753784487
    0x130c0b0a02031b0a1e02041401080d030f2702090702060403020a0308130b0403030608190807020d080f070606032a1a07062a050a050708030408090d060c0f 68
    0x18086035000d038100380852030115008101240443c0000001c440016481da100c036002188a060144000c0508104840960405000710303a004410314070480865071500d60034a4580880c910144c040645a030f68400007480e850700a01340d03086e541624400841c0504503262414501d2200490117406840006240b0900220781c091040e50540c0140c404044155030445107040c0c000c01c07a038400c1c90081c401e040031548081d43e80c0c0c40b8501c2610000b0b0002d0134a0380b200d19001041011400381d14559684200051500040d2080b0990584030301400c0d1301246032a40c0f2034080d00706417084000c008a003000901000390056411039004070046840c1c0e0f100c14400072682c408146040303207108048002027011540f5540c42a9010403610038035410000d541d6a40d60560341042d450f0214441d000c0c220030454415005000c0b412411401c0403032034940c9103030000d441401684400b4084820200c0060706000c00c0b4000c80b100284001c000400b030062928101006082001510000400d140600c10301d40703006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753786978 1250 753785728 753785737
    0x1e0c25060e12040504090c0e040b100f0501051c02220510032702011101020f0c010b06032406040306090f110a080c0f120f070e25030b0a030b130c0b 65
    0x440100300d00e0305044c6414080603203291081110b041604960001b5807180b04051103010710301c03d07155140b0034141003629010400040c1c2002520120031079040082d6038000d0100d03403030850048560145c00a2007442c60000b4002e168220301040e100d46a40036000c814407000070161902160005a5140d05150460450340122504211200d0700d45008103000e20000c5101702c600c1c4145003140840c400c41d00528260780028540d54041c101c00316101103440c8080c0101c101c070030010380d040f03401e6162226190000030034054a104803150900c0310316405880d8002220003864100900380102e0000c1e00c0c100404252002040d03c1001185400981628240d8401000c0b40e004100910f610540442005041240001c0c1664001001600d000303100300c007444850114103100c03028003649071800c0410340003044010600d0848402141d80d00a0103040c078002c41405044505d0b00160f510300c100041800c00300749400180a1800e0703141000842c3c980385a011446a10814460301001e83d0f803c010007044c000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753788228 1250 753786978 753787003
    0x4080a11070e0a1e0213050a090b0108160c0512030403080603011b032412020307061e1d04110310080f06070e1c060f0e061e0c25060e 59
    0x400a0101c3c41c2c680c02504500301e0603d00c8204d03941a16450442841280c0c0300e43e00106202454400800040c609059001c0042800440c144007036100c0100090070100000c1000300030190030100000000d12a014908015038401c00f21350060000031171070091500100c4045000507002c2d8006241d605043c06101040c807907950284628450017101078020302405150f4412001c88440035240e01d103003005000d802032000c110400031000d07030f0f40181404c00415800050038000c07216200090702c420701303010b00003100641c5003640a02c000b65000c0303103080b8500c0440c03651107401d0038100c244500340c1c10300460103243c0007126005c150750703140d0015440b540c03a546410002e800030800588000d0069807e103e503003000030412400424851500105680f0b9080260340f51651688182c2400c0114881c00c1c40d5058104c0013003081d440c2c500ca00c10842102c02c034644060717031210404240d0700070503001903580c2882c0c8a0040540022084000b0614500b0702405031402030410104117405000420764514000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753789478 1250 753788228 753788249
    0x901150c0305221502010b0603040807080d0905010219080114060d0b1908010e160305100b0402130603140604090b07030b030307020a1421210405030604080a1107 71
    0x14a41c07030a41c0c80d50018000b000016086480c80b070100c1c0115843d500c0500280480da5010b1625804c009086801800406004031010002e1201160540d0180c4c1c5003968850f2889641d5000480d45102030f02d00c000000304650700102d403400751050603580c40b524804941d0794201d0030f42c0e665555503041d81d40c20350b000c681248c1e0402c4400300040041e08403a604135006484c81d030100c9100350401a0446150b0701004107030350755140c00703059024144524049180600c0c9121182811622000d843d15140c0d10710b5004555150010341d8143c450f5015582c1d00035030301c280c1c420b420b903030f0f80f1019018040400030a954004c071940094007902d007a118038071805030801d8101000d9034405e4001d500a040d44040325a1611040c070142c001070350303480300e28405804542504032506240b4002c0c85000b10010140841042c0f00d0301d14880060170005048241c0c0800012420340c52015581a0b440c62081d60800c03a010b000700c4041200340f020600c000d21130b01c200c0e0307980c08200d48040105592507030124002d000128 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753790728 1250 753789478 753789497
    0x3150105090d08070c03051603060b0603070f050703020705120d0210020c1509100525030618110c100203010816080d0f12050f090f0c030d0810030b07030b090115 71
    0x25840f00107005031a102d0030144000035165121a460241417104030300022284c0e060a00070003140340955820800140c07051421801c15220252154034a850014108000420408103061080003100001d003806060201544020031390242c4580070229100c01520408a01d00359544591003200d501d203158402424207048002181d081d00d500117800040f091081d0000c0c400c04068520901f40100d607080c2000711080610181d0040c0d0200040c1010289441c16204000310004806100c008904072000080c00d02084a540030030fa01454103940720b6481556200c0c00c50325101d50041d8140e45100c0101e4850301c1c411250312410041030f0007a100a0780208643c102d0950064064004000640c108034074003803103588800f0111801102c202c01c00314070302c01c1030000100e41400240d020780d485601074842000d4000120b69070b11000c00d0180208051038000030b500912501d0801c000e1540400e0f0401ca9080803000100a00809020741d44100305050000820b814040c1c803d41441004e03882d507034002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753791978 1250 753790728 753790733
    0x50a1202060307110609010218010206040b0735040519080904021c0c03060f120c05060306040b0a080105060405101d06120a03080f0a05010605042903040803150105090d 74
    0x10381c1000c3c21400070312001c60000e5030685010720109120307540301000162502c51032400d1000b903202c0c00c00c0450564200768184004240c50302c805550122071400e01003244a5a01e000d8500404101240c01401c5100c4d040001c490f0b81c104880b5015034012b00c01c07100c09030030445e00805030004121009220b41803c00400d40c003420283c01070207420206903540c8001c00041c1d860802075500680e425400a541c1741020f10505280bc070040e0040e2500c03c118418401c401c4d40e500480303201c01d000d518854400803000070010f0b030300d9400282d03100c50003500410728640d945400c1406840305452181c80f031400c03c00042e819400200e180da0440c4d4042e21401411305241d400d0000c030f407102605064002215480a0019107001c1000c81403051203a5134202c40b07403402c00300e03c450410b409000d0034070301402c0c01d00400085601600303030340c190b44d050301103031080e00f100166a1303c60441c11115061203801c040100000e01000303101661048000402c00b00f045910003004440a02c42e0000982c0d00034000041e0102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753793228 1250 753791978 753791989
    0x50105012d030f02030c0c010e01020c1b0a082a030a020901060f09030501050c070501290111030d06091a03210708160f140c0d030c051f0b0a050a1202 66
    0x58140701030a0001d14030580d448400d0583e0300071244008040c50019480345200c1c024401c1001e840c031000001c504110a014409860b035115007505803a4600f000c0d401081036480046c02001010000100d580d40c2c4110b002c0d0501c100008403014020358941e202042c0c6504000c905145a03640c000d003528503aa0a040080e140c1d0901c06865a0030810704200c04800200c00344a680e01903940d5010407138030b5035418075080782034940356030300300c410502030602c040060007028071114414603007424015100d800707082d40945140100e40030000790b40d00307002c000640c89003ea0f1103400800c402e8441c82003240355540502d41e8030701452800440c3d0040014200601e0390541c03000e07044c014800e40c03040740360038641c410007540300385041402e807009502d1f17200d45000c2200014042c41402018009080d0021a0800050040c1c80c1d814000c3d090082000c8181c3c2000410310445500c6000801e00c0101ba0754004040c0e401016001c1e641ca0141a9a81d400310741c41c40c10b5940c000c1107400d000c004186100301c0d58203210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753794478 1250 753793228 753793307
    0x60103080c0c10111603020a151206300b16020106050a08030d0b100f030c0302040509041b06030b060304110609060a11150c07060b0f030a080d05010501 67
    0x680500606558004640c1c854600c054407100b1503552003464080c40308100d00307005080011100014020004000689442c23007130800b141d042d0a40041e07003203207034a0240c40540c6c00784101403016150000100e60f116105080002e021300798551b00d19903c0b9146000207503502d500d6800380140a204002070442e0754a40054100e401c2c9520002c1041750b51100462000c404540000d41c0980000c11650004903c5102c1c1d0244801c0841702134212154240e8098103100d016800c9204060b02d92500d030700c0540c000c2d01118000d00015003111050f181c1810920080440701e0849241001c00384000141c440c402d01540711040340040c002455500c580d07907580d01400024032166085041407144e00010303030350303000500103040850300c5114154405112035406c202e001e616072403015080e8002c0c861001c410174103860b606031307218000140e0079903080005440384440300c0c0c072168180302c0c40340800200444080503040f4200c1d819014484d90740c03520010340740000203425061030454034001201e26210345c8441c80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753795728 1250 753794478 753794497
    0x20f09090402240d05070309030503150613061d04021e0306040f0513050c060a09060338030c03010b0f010c081210081506060904020d0204080d08100f050306010308 72
    0x1400d00d1494020f50b00b03003034484071600090310208102c44d01600300c0c0240c6034800c12a203000c000c59146540d02401602001d80401c0f003500c0c8032421803915843d03010840d07203c08850190742c2c01203682d408005010304035100d6100170191626011100a0400d402070310601e5000f861004840380119041040356080100015031064482c1e860503802c200610415001d4040c1e210390003080f407100d042092405c818a0301d8180504000c10404001c258441c0811058074014a800f151a50b090002c54a603070011046041041184008041100c0e44442d034009012030146c040e5801e50703001034100f500700c03103480718195001041c00c1030710f807095807280d080298080c0c4520070322414070320b684202030381b1440120340d406000002050306001c84001040504710786440d0355803e804c14a000400718400c0d0180003405406141c0101d4009200031860f0160b401070885041103840102124100500100c0d083e500044240d80318040400c1012403840b5120585074064003c1425929555030000340c0e5115460382d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753796978 1250 753795728 753795739
    0xf2502060a0c0f021e030607090f140303122e050619020715080709142107030206160c06020a120822030f0906020703020307030206030a09020d24020f09090402 70
    0x7800141d03500e0348100c6001d0080074000720703445c00f1340040c0b5242080c0504058180f044440341009210b0704003010006135081a00e62130103220400340881d255020b0b108540040b240a4000c0000e20040145070444401c0c2c1036520303c10112550100003001000c0e4020715800502c1081580000650003180d240d0b000341c244120303280d4039074800709030030840c2c00e03c4000c000080041080c407100f181d201c40c801c80541a41003c00c0311070b1f518030300002c09020b0641c945495103580030442180c0303507401f40001c1001710340180205a45000b08051080d0030b0034540f104032190300c917012021800034400242803040d1a4041d81c03402c0349a030080b03800c0e43e01d981c000301001a551619445050f002e46503c8202c4981307031180d190070a4001d00c5e0310001d0305840345a00000c04542c0801003c0001d6a400100e0380112501560740c15507a8540c450180c014048001c4041c0d0088060f11461041044403440c149602180d41c40d00380580410009110070b0f0700c12106a144c2c03803041803100ca2401e02e007174051685c006100429 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753798228 1250 753796978 753797003
    0xb010c11010c050714100801080a0b040c0902040e100b0a120504022709010b010f020d03020c1606020703030305060402030402010c08130e1005043c110f2502060a0c 72
    0x1e40d80e144c003095801041c0c030401c0d0702048002509103040155014103090901e01621741c108003440d6900e12150074050701e80c150100115060082d03204d9014080d042401e0299038aa480d4045504040c0040e07602080300c1d200c19000003000c2d58080c003540e210204644d1020030410303140c071078000a8080a8416a0f120f981c08440b130040e580030000c0f5142c0036100e804039090340d1801d45c1801e401c41d540032030709606008054014000e00d0740d0110304100b07401b01c81d040058841ca54012484e280c21410700c0c0c51000304a1000011843c90740002c0d100c01103c2c4a55801e02c0a0b5035010140030a80c0000e0303c3c000e0110300c1924100000666810150502c00c54090412440c650348840001140c0c1081d5041d5441105041d01440941454018002001810001651220a150690320600341046400c840ea08103000244180454a0f00038001d290070024000e0b85a00e00d02007405001d0380a81081310b910301940070000f43e480d648220303140360243c00a040c40e09092001400b07440505000c00c0c1140c0744d004405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753799478 1250 753798228 753798233
    0x31d06092e02130302011106040b060d030e030a0f020307080106080a1103030d0504060b0316031205090a030f050616020c0a030323070b2e03061808070b0a0c030b010c11010c 76
    0x405041c103d4040c6406030141d61440c0000b502c00942e107011340c803507a00203008200100d1818143c02d60440e005030303903140c4441d4590030101c43c010030000c2000d0380b600607004a4018084881810107a07580220140c03040255980c03012801c9800324072030283c081d082000840082900c00c082e8001490025095a1910a0304040071003140c41c100d80172558960b807064458a9414104845442c1c03515400b9403010280c216103d1900c69100078401d40d040080001e4910b0240c4c42e0380002900440d4001100c4032038040c20f00d0b2441d00c41d042103849040c407101e0402c044200c54400150550640b1000e00829965419621b0840b0642010305030418120021450360f0788c00300c0c070031005211302806100560703801d0800c0c5008081c1e00403483c0c00c1d0b001215101a45d140301d680d1402500c01202c3c0d0151b00003030501050b025911004541d500c0180c2100c001003084002c0c40368040c0c00ca0301ca02880b503010002000304100c16401c4a034440645400200e900500000146a003040e01c01c3c45001410301e1000c0c503007280d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753800728 1250 753799478 753799481
    0x1c18030e0f063108030403150b041e0c020d0e06030a0f0230060102010c09090f1803030504020111160902030a1113080c15070807140607031d06092e 65
    0x41080e280c090409080201424041e00003d015000b0b80020318070301407031502e9400d100450100da00045a5070754060b03d840c0da0382d991081c1079028141542d54402c6c46002d9103a00113005640424003d80a8002c81c420200d1195408400b9402c0c020000e60840c1c450024a000508640300c401d545180e00304001ca6044180c004144580182c3c882c101c3c0c091205a042c0c1c03803040401400803819681007c0c258000c507038004a41c0c0703040c2c902c840d0340040d40d480303401840c4004d0300103507044071018820500d0302000c3c03640c141c1185128034000c0e01c03403816000008a0065032400c00100718000214141014000c190f082e40096401120300c10300410f0342060040482d800780e2145041d100c842c19900010000b40000703210403920f401045400140810f800890440a40304400c001450b0080002d50350041010500996201140d108100c40a920384888050024841c1104101c0c003207500703400d41c0ba00280006240b622400c070b40d030b01a00501070055408444080071002c804030901e021300550020203501e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753801978 1250 753800728 753800767
    0x1302030f0f012f1809010f080105070e090c1809010902030f0a0c0941030c03120a0c08040e090c0405090c010e012001021c18030e0f06 59
    0x20000740165804105880c1d084850100404050762070220804101042e120403801401d094014600d5036102940d582d84103540c00951850b5002407440c1c0007241c0070389645003800030703200002c000700f00b151204501510340706449100303550310070044000164080e940d036001c0d041c003e08515150728030380502d500098090000344c1116800a03070100030010b1200c12000d0303042d000b00c01100c04014031844078000030208036842c0984803100d405072200e000c00e0414044040111410901000c6445002805030b00315060b00c0c20002d4428403130046e1030b010342d14003c960340506400810b443e81c94809103d409a900203e00c000644010382c040c030001800d0a400880c0510880700030020340f80c01030060040008654025120b014154020142c04006907080b2000d03e50700c210900b410400403040787c000701060803401c18000c0c21075001040e007a9980c0075008048000002100040c070031040b524840111000305848090001402c29040d603110b418054011007010002074070a5291400c11040601c22100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753803228 1250 753801978 753802003
    0x3070c23120c09180709020f0d0c0908010b030d080a0902040207020303070b01080111030c0d1a0a031104380d23063702190203030f060307030b0f130203 67
    0x8814000509481e003d20304541c4600081a42c1c11203078402c03520f03d07a880419001c0c034202e080d40040d0703808002004005503030201c0c1d202c0200348080017290800404511680c42050300560030020b0131005840c0108141502c00c45680d02e010316a45c8545400014215052059800075402c20805002d40c034188010003a190041c840c940e503552400540c0340c21900003102c201d982e410140180402001891b00b00ca6450812810100d503100302441081e0814512812940d80000100b1700041000000925403290000444041180e984041000450003286a01140c01c0761041101c90307800c1074000340ca184242c0000303040c000403101e00350b40f15095850021041c06400c00042c15014042c081004120b502c08064100c80b41080f1044101032a010880e58940c100e001503806410074020079941602c0c0018201d2080c407081061048000e5120760043e80c0f0030385000240000a00b56090010b184000c480d80401c114030242d5805010410800000d008420127040c803680f04405681c0c10080000500e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753804478 1250 753803228 753803233
    0x28170f040b0310050402040e040609020a0e07171605040608040f2009090a0c06031a0306010603020903120c0a06090614010f14010809120702010504240f0203070c2312 73
    0x7840340c0541c2c00303c445684842d02c1940100010f10a05590075141030700300d0b900402c0030410805510001e41c06a02d82c3c0c101d00f02e8030346182c080100196111140410700d52560360948002c1d11000300102224002c1c0c0300e01400304904220030840310740b02e0406a944140180040e00c11980b243c1d680c005030a6004020303151a02c081c98415006103810680c564020b85030350700078421303240a65030b5906516004d100380e40a150307480d0002000a0380d80040344200ca44003c0c01c0c0e440d590386500010b4000c0d00084803440c06803107441100340c0402c00c5401140d108280101c0100945c00f42980c0b8000036041040b400c44410380c030794120140e10071706162601e02130002c03290f00700a0705042445240c0d807a00030089d0141049103007c240000c1e9140070405000b1640711510450755490a400166418404c0394800034114101c2c01c60010b0406c01a19000310504c015910484518a820412a928000c0800103805061043c2c0c0800001483e400411100c3d0102d1a05045e010701220014881c840c5241c8000c0032074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753805728 1250 753804478 753804481
    0x613080a0804031e0201090306021b03070b150a03030503190b041d010507032702010e03030712140711040f0b03070807170a12051c0c0e010228170f040b03 68
    0x3054681a440010444404100c84c035a0340f90002420701d01c080c4005040c550380018000c01c0c11010b01400d50340246002c049076910840380c41d091131501c0d800c6511f410310001081c1c00c80140d25003c80d00c2006c40e505661854110b07101e40050356254085200041072250340c5613516451512103000c0c07100701c1291800c4000d407140c88145414250791005003840c0c1050b140c490042100d150350440c4104168014000a800341c2c00c03440140c0e401540b080b50980d041c0300110701c04040080c407603845010200d0558075183d113851415642c0f038460140c000001c080041c04890f6035981d0425034010300b5140c0d802007010070b41001c0600402d05201d596003001c04140c010420500c00100d0341c0062544840c400c80050600741401c0d2200002620000010f6003040b1000444119034030a10804c000d104414600400182d9032440c009031000482202c5a8090f00070b500c016040d0740c940c92040c0020030712a13006031820b80815035640c5940501084030b581001001d00c111a068078201c006800a00f0702944025941d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753806978 1250 753805728 753805733
    0xc0f060c020f0718022a0a0c12020d061a04060f0501030e03040f0b070f15230f1810052802030103020d08030a0207060c0e100e030601050613080a080403 67
    0x206008003005180d960f009240400480984071042010000ca651006845280c09040c00e00040e540c403800200d04010040750754100b080102d0000d0f40c2500c00d0400c891482c0e90751041c06050040c2c828040e40c0104401808000f080d0503401c41d840340715000c1040e4100042401c0050200c64003500a6031440301098018811540c240c4a000350640c1c00400035401c15113043c042600d8858a030144608440010800000700041d004c11100e01680c000d900301d1414000e09400f400610352440c030302045140740190305801c0c103202200c1c00c0c01206d04009907140c0344c1c1c0d1400218922010340398a48039601c180f00a034851060340d032141900416200c1002c10300f81224240301c0310074843c114401119a07104100400060350380b40440c0c001c1c65800301000782c407640c54401d000001d020307804000e440c050611100d15400c0782d003d00c19030041d06044980360b00c0307c0313542d1b01e00f143c810b01a100000d030554002c1c3c005001b00d00d0120054078030b1108400303080d0002500c03000401d04043e40502c040fa411031010900303104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753808228 1250 753806978 753806983
    0xf04080702030607021e070b072303040e06040513050d0f051209010903020c01020708251815092325020a0b1605180303040f030b16020c1008070c0f060c02 68
    0xa00c0c4c100f00006052171f82c1070038654a803e100394000204590f0302101c25400c20310b552040d401820400c1da042d60307251307542e911071400003000880d0418403983c9081c0000c1c15403200780001b1346411380c000000b040a811108415100c2303001c00303c049c03001e1002c24001d205808620055291040c4484d200215143d0b55601e0082d140201c015201415504100010700060900040040000000c0e1820000d0340c540d0203040000100140c03c18071400c40408540051040c41e90085040f0707660227016990540d03910100d20301103038032a904a00c0000c0703a4201026820165040b0b140e001850a08100c0441010f10007103c5100300c208003000240e00261070351001c2c030504402050f4805a000500c695000d0034a1000308030f0f10a01c11041d5200346840c0400295442c10000d9401400d85000a840040d031a810001da00000481e410902d52400301071448150744003294079464203001074240c0c4450540450140e0b503410006041e5020403000d50484004100400520091035004a500140400100c80001d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753809478 1250 753808228 753808273
    0x40203160906181407030c05040b0403060c0225060509060c06040c081204030c06080a09170903070801021201050607061404030c030206070806060319060509310b0f0408070203060702 80
    0x86520702e4050f1381a003c0c1c9688541c01d03800140c500d4001090164514285c80501407070304a44c8403a64040780200404c001c9500ca0707841240a9000c80c0d0403884d00741c980f00b103071409036132141c07000c1c54982c3c008110090203040900b40c1050000c21650804003a9510240740c400210fa040d12803c050100400c1400d00601076101201c41c060b010b503180c1400e640381c900c40d02e9030341c1c0b20702c0741005900000240c00207056445034603080e40c040c0c03400180054403068604183c1203a042c0c0381c03013405588030004101c40705108490441c00c1020b50502d0300e0703290000304080e54005100555066803580d000c03031a46000d840d421445039200b5140c8035110111802d009151400c0148404140301d40007080c058590384000c01d603580528014a6480703003000d1090440d0103014540d00031500300359414103110502103240e0100040f8102c1031403207000e911410041c0710692218040c054030221455010a2040e00400c4115600c09e00940031300c0d181104a60101e07290540444206005800103040f0a1541880e080e07080f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753810728 1250 753809478 753809519
    0x3030c0f0806030304060509010201090f030e01020d110c09092b271511241e06130603050d030f0e0a110f03160f06030b060403030215040203160906 65
    0x180340c58075050b0302103aa04c0c4100e00030001445004102020180e100350809420507038000d02e2406002d105140107041a48002c1c0b4850160084880c5106500c1c421988040c42040c2407008042c02c0e40314034107210700001c01030b2040030035001744540e070341c05030f0800030104030b42a01a250040c901c29003414000d000901d50082203484c1c05105880507500d0300c1103d680000c1c0c49103890a0200d80e4001502682c41c107510008002f003e025118105c0b100d08006410003601c40642c0009010584d030300d1240d030b441c14100002e54146440e00b0b10200300301d410080350300d09442000400028070580c803502e03140c1c580503ca043c80d4001075182e0720070502d055903600034102c00c0b64000000b0001c0710490307541c4244440d11021090301409005a1205169400308150700440d801e81a00710a9551144120003202d0303000d003c2c460210f4200304114907982001c0c411075040b070390154040d00503041c0119039000d2a002c0a003041e41d0510580903064220810703a102070700108041c00c0c2c00035405241c482d6081c503480c06010030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753811978 1250 753810728 753810737
    0x10c080c100b0a05030c1e100207091d060411010504090204120c05040612030c110411031509070806101707030e07090203040222020d18060516050a0509120a03030c0f 73
    0x1000103031000541d0b9104540102c40c440c500d80c3c015041040307000c5500c80801e50000c1d2340240c070b084990f0040ba010003554040c884c14807504107450b00d1403c0102925085400b141e20240000d404034a150711048405c0350305240c614070340399590011030309903041600078401282e01c9600c000104108a400003004000c240e9042c07202528103000a4130701500e1500c0902804000e00f000070400098000308a24900010300400c28042e40308a280700c180c20894040008080c6025503051500d003400c0d07181e224480555440406560b1071060040401401010760244000311140b00e0103072007141040c1d8491000c9035000140c10034410301c100d00d060130359407040f01194810020720015860b441e80e004503001440e00d0b81141d141d801d261490007031048440703000c58180f800d02c44900384029103204400c4507000b003a09000075107807000210b03100503c040042e0045441040b003801802c1c0203e026003004c8000628101815145007440c608007003008000b1030000b9a104185401550414689071008102d03161 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753813228 1250 753811978 753811999
    0x50f0405070504090f0f0c0309030809070803180d05060c0913110a20010501090906050c18040f06080a0515090a030c0f060b120d09050415030b06010c080c100b 70
    0xa02074194820703030044c0c4001c01c1c0c580e0300b107081040070780e00400e590b44904982086400300d06600140104804041240000c0c40600400c1c0c0c0004009049070985504102940c58a45000d0030340c00604000000c882d0494100402c480100700240002d0344a1000c0041c0c0c19501c10760f00040060350041c0750703650300c0d09514203a000d45000380964182e070384c00d01460900442400344a010b1084143c0101c000c20f03250341c00c01001284166168002901d102c5c8600b40c1844180c4645106144500500c42d1480003400d041100c40b40b1b51904d81c0000030340120302d010009001d5202d90b081410a0300366241600e159000c40740d0004030315a6002c92552201a1201405800507280d5004090040742100542514006030301401807203441d6105403c1070314014845141e15051071213654844800406050100e038010700c0026041c00c00b409034441500c01d803609907000d0350443c0d03170700c2442280c00b80c1182e040100010768280020310b07010050240c140060024200c8080744001a000e403010300348500d001d40310400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753814478 1250 753813228 753813241
    0x3150d03021b01170c0304031e03060501030b0103020307020615040e0109031d030106060c12020705060a0f0305090d0e0405090c0405040b09190b0a0c0c1209030c17030318100f06050f0405 82
    0x440c00b50028580017065a480d141c908040790101c4000f01c0c400003024640b8408140d05805174000c1d0200c507400c0c0c030300380241c84464005408a000071100300d40903800400004d4020390590410001e10a4002d00016509021402d020f0840f841e9207821030100f0242955030100840d00c9800300c042200441c002d00200f13051420082c030a242d0322200074456240740448440c11402804260091300c0082e140584810811400910b00ba03120800710001c6450000031440b109400b02c0d03051003599850b21101554400c4a06000003807000a1816495010b440d03a500c18542d101c0c040d031401640500c441d2176107820040100360800144441d64088072042d9241d41c4002603801550550080083d500021504074804065409100c210001810901c0c1c00005070380c2160044078010560f03026404000e00c040d02c0d01d0303c10150034044c2203078204680c030a10019010040c4041d407004403040840a89000a209030b80c1303002940d62810700218400d40700c0b07000b4403071800e0582061070003010803034052240b420240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753815728 1250 753814478 753814517
    0x3070f0f02211c15030b04060b0301050f010302100f0806010c030c170306091e070c0f020a0915080a0203250e0a0603170a0c1e140601140a140603150d03021b01 70
    0xf4031005000340f104a0000e01488049d610084101e14050000e01c12880c0501c015480b0241c240822031044060040608105101d801c2203810000591600d034000c5c1ca03414010740300e11a550b20304034100941d108092000800c1018000758a04403400c05503281d003460700400288000c0204511184802c032442150440480d00909820540d142030060458000d030500c14229101480081d400055111000074010034560003040100084240c0045a43d19040340b26280d11304000d000c2d6040c2d11107440e4501000c00d48118443c1002c01c1040c0701c00d8a40c0e80c003c45070600804803030050815a40c0c02040003405400d48142c046501954810b83c030300300480002921040249401812402461000c0c6898000300000e2190058202558a41082080c07400c1a40da0009014818000132509024149818441c11200960752415441184000c0440601600e50130040c14003d40d049401003180190301c50031098882c96009a016208810503a540c804e0584403400805041003c01130a411064041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753816978 1250 753815728 753815771
    0x220302060105060f04080a141c0e090907050a03140c10080a0c020f030c06010f0f0e0705160c0602010b0f120c09150910180203070f0f02211c 62
    0xf16407854503100d40c905040c40600803500203803514860f00880b0f105001c40e5030108041a50720104980d6030801440104ea40400e0304240380307021640c03a4991541c5840c281055070342c8400c00808440946a41d440000c0e102182030340141d49071400104441c84004092240d000c20707200681300425092415080148000e000401d1a40302555905051440b40d00c203019030003090f40c1000403a500daa5144071001d407921400c1c89403c0a1110122002500c07002088500c0d0895480032004a6280d551090039a019400704180740e01c45000401d2140c0004d1030700101c9005003c03281c3c00051120418001c1c02074001810032042e20409a603600b14414110020703541c90602d0098592456507110480710480f107002c0100b146611140400c01c104401e001607000b4011102c080d072074035070000718011250049110650704080080d41040d0017003017030f9006030a802c080b4141c5104556561a8120a2114000990180500c10040020146050308080541024840c034030f0f001041030b5549038505880c051034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753818228 1250 753816978 753816989
    0x1303020409020d05070f1409060d0b04030c23010506010810061427030601060509060d05040305120406050601260103121103040311090a05041101051c020c03032203020601 75
    0x80707400c920340440d281c010040c2d0296501100710b5051507156410305510740030318050703400c5104241880181a150890000b4002c40300a0441c0b086084540c648031980c6100074410350a002c0002c13402000a89185040c84c018106c8412181301b40d0403011910b400d60301c001d82864100102c8600703004600c030154240c4000c07284241085041a5250b00d100c005070702960300b41000700080070890441440c040c00003400c0000088068400070380c0c0700c181c1900c407030150030300c42c58000d1810300c1400c6025034291b12032038000340a41040d41c1001f01c01c11592400c01c0f81124121645c9407504207010040d41c03c40c05800803d22071003080072a0800c034003290196004144005802c20b07000c161428201c500500103005020000c1060340c3c2c2e182c0d1079041040b42c040715800201d004d4044c500c000f404903520303403040c01c1c001c5910540710400501031100446e070b42e8001c0c3c0783c101030b003102c1400b003010308501e07900c0204000c001e000040d60322071900c2c0300c02001e41190713070007140c0041d5501e012020000ea808682d4a05450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753819478 1250 753818228 753818231
    0x171c0509211809010b070506061516020a09020c0106050a06091d0705071e030e0103020f0a08040501020c0709050f090a080415050d020d0920031f0f050c0408070b13030204 75
    0x1c00b980005948500991143e422240000c00400d01d16a40801040c21078007801c1201c0741074954200307100c0e209411021801e2144420710242e554080000c00d601407040c001884a520030362141106400c07a44265220b03000360307550721000c008a0a040d00c071a80106900c2c01c056044500c0d10050a007102036500701141403040501c00a01080d00a105071408280c100300501c0c4180f000c203d09034010840070b001038001c50419041c4114540c440d00860341b100b00c0511000c1d0404201c46000d031f543c604003500c2166255002d000c0c41d04041000c0004100800c0741c00342c0461242080003903103a030a00060000d42554110640500114840c00300b00d030300315044101038601080c0381100480c2c10b80194201103000302d000161006103266203800800e0403a016014010072104071040a40c081e0542d1004903070150803054100351448015103665070048a0300ca000b040c0d148401001c40c080313840459604100d01c50100301400301281c1081600040c0c820040154500b141c1900203850401007440003c2c0f046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 753820728 1250 753819478 753819487
    0xf030901140c2b0201060503160509070215090703030e04050907030f110a0603140601020109031d0103090b0703060e0f041e080c060f15090613020304171c050921 71
    0x410040018800350403040d0003006a1403829100f50040c0159826081c00540c20090082224600070449140a00a0720003c26445141030144144a0802060035082d8001d10030801f204a094003c86841007a6010103049000d0643c0360242010344040041d0b40a40d26000400040300d00010701d0005a98000000180c42400703460422404e0201d030740003503000007003000000b943c0c617056008107540011040c542041d40d0b460000480c201c842440c000340000d240740000c0c0d40c80603622000d001ca0080185800314040d00103499495100c8025a80c034400242d0381d500800c6844072100c686600540b060246030034170300301071300d914110a900500d080551108000389030b007048034241c00c403004800b404080c1c81151824200c440800c1000f26028544025121200b4049160080320a0711494008100078016960704400b40002d403c000c03c1116640010310a00f8085441d001c050060200901040c0341450f50301741044040d04e0f0050542c00c0290b024603132110510701e01d290342c1da42038420507912a40300c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 753821978 1250 753820728 753820747
    0x3801270f0f0510092322060905010b180f0c030612070b090a0f2907151e090b15040b09010e19020f0702010f0e0d05030304021009050d031b020604090e0f03090114 71
    0x250146ca42c014003161070455640104401034120f8248403000f01c42c05420030300481c00d001ea0340c541c203c540212000036400060f50110301c0b0000345400c900060414030078250034508141c80d0910940200b0440c03100402c10040b0b92402c84a1040a4036004466040b0740b450b20018041f044003400318000310300341078070036156030204c03640a0b94812500301c0032001c04062845c105a00900b2900d0000500c0203504501c03185205090045400099101c03403112419a2815052036040c1e0b0106081a400341d12600c04085503038510501d14003800401d0041071260610340103505016001d03101401c1440d0040c007801c110025182c05031084181c0a0824200700204c40c80115551480c03014200e41c021080030100c41400380000145d4812403080d80d00c0e0300c41c41d01aa005a4800515225196020445a401400091064640c580e200c50ba21030700030f4440c041a400207c0036046500011702040e600c10001e613800d6001c1200a03002c0e40200080c43c50a450000003d02c040c0c3c40c20300001002c0c0c0b001400342c54 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 753823228 1250 753821978 753822031
    0xf02010906020304150f1104170712050f1b180a0b060a0504091113051026060f0a0b163801270f0f05100923 48
    0xc84a40c08442199245018904a010340c0c00425090ba1600e00e0580c480220000d03a1062811010900300114109464002e50b00c2c03040d2014880d524040c003409400040f40f11000350008001845640a49030807002400381038500300100504101d04000145d154400303890b044007112a035251142d20a0b22581c4051811028140304800250040c1000070b8603500d00b54083d0240041d05d491b207005100302d90340840115014090b10803040c00c0403a121400704031070300e003440c49103280c504181000e601c02015101100388100185244980c6042c2900c108201441c0c650080030031640200c9145c00400c0c10000c0c1807105028011803170501021240103a030900c940c18034407007400d500114800d41d5000350603108640b1a082c4100300c4d00d405501c1c43c00803400e40b400980307130440141c00461100441c03101a90400250022042c0900d0440e038071401c0030700341c0c0d4617030040d80c1c07140303900b1600c20f164a031134206403038202c481d03810b01d20f40703848035101040c0021242c861005410074003038030100380b56171407140d040c20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 753824478 1250 753823228 753823241
    0x30903080a0e1008011406030609060103020912032b050f1b070209101d014202060610050c120f130e06030d030c080406090c0510030e0d18060f0201 65
    0x41e80005008668108207604c0304040e81078400d6800b0010040e6801c03028400c41c1e000a03117110b03038802031880c000303000d5521035809031107000c0000704030900500032404820b080d6030020076840540b804c48580130f66a80d00040740a0320380f0b0aa07180402091412035032942135414041c4c5001402e500454108000f817140000b62400300b50002c003181d186003004184001d04c19044d1081c074001401034002c03c1c01003000042d829049600b10341e680c6940700294520b9140042d0546e6032448200080c120052134684041540c0ba000422078000f01510f0400f4001c004100901c0d0b40d150081040800c441c500200c4003091156400c3d0301480407607160814281400c02d00c0c003503140030f04070300c1e51030b01000541d20856100c0319001d60000e03015a1041c0180f081d04800741c0da482d8050704d01146458021400042480c2e0200e01140d00640751801c0464840380000c0a5018003450503000980304d00000308102401c0c420b0900d851462b04140802840760160300c40c6200c1c0078407802091080d02c240d1044030500030342080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 753825728 1250 753824478 753824507
    0x15030a021002070b0f130f0509160c080318100203090d0c020301020c060c30010b1608030106030f0f0c020d080c13180b04061809110d120f0804030903080a 68
    0x58640003c03114800403070304006e0700c2e100002e01140000400450b10a808402e965001e055402d2940d541d640d18041c2c3d1010319a42020031444854940200380d2000180d40140c1e030b1504080350f0180c003002090314101e00041200e0680c1d1042044c002070b282c0c0010031411030b2900342408940603281d800000d0080c0912003143d01540180e6080001110100004141002c06020050f0b0140b0f071102e4410361510511350b1250303140b03c2000041c0300c090610400b801ca000320140054266201640c1c4184158000b81d210401003501d0310314000702e032401801a440307130506102c010841078501c03c3d4002c0da14160b1071114401d010b44840804c00c049604c0c0200d983c819200740c444404680c1c1d0300d000110301d10280701d2040400341340ca103440364a0b20b090302030b0030308680058054510340240d03908034000800303040c00200c40c00c0d110754652900985540e254401514040d00d000b00e44030300e03100000351600d4000f40845042003d03980c100300000e070f080314100c2e040c0ca070003103504e5854141c5210181e506040d904102c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 753826978 1250 753825728 753825749
    0x901030b060f04030303060e130c121e03030c1103030f0609090a0c03030c03030f0c0c020f12100b0a0b0c0607050a14030f07090801020c101113150815030a02100207 72
    0x813081c550035412110866102c0907441c0540d075140e80061400040e001401082e045030010104240d6101040d40c0f00564080d40b0300141c04803115841201c0c0c0750540350100d02007912880516541600007804900340383c3d0328000b862552400340b240c02600d80c80100440d114070078110101c0d2080c10104100152213038010300c0504d00740d46070b08010b04442c110b03010481c00030f4180805416104500e00602004481d192600490120594200b1034510700c0c41e105190041502c00745030070300c08010803c840181c0b1020500040c5480307441d0a01800e0030154000c0041c440c800c20040d611244006207480d800841450402e840d0300e0020000c0720380840070034001d621207502000b405400042414410700441c49911802d400342d1355000203d00742e009441802d250f0780c01114044034040901d411010039400101c1c2c4043c0781048460b0f04c44032002d00c0c0e4022038490340804585c1161030b9040700c1c0e10354110342803255080409200c500000d0f543d106103000240107041841c2c4102d0014000c1190380050011240c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 753828228 1250 753826978 753826987
    0x611041409070509011b0204110d0603020f0a0b0a110a020a14030d02060c070b1503010608030d052815091a01180b0a140d1107051e030901030b060f 65
    0x1960500544000e1a0074410301c0740344046808903000d030089070343e41d610684450710b64801c15900e84a5103040c216059820989075031030400054101c000621001a003901e00040250a500500c012480303122500c0380a8a4500000c0c0205005401036030041003052404480700c19038041c04501307108007002d0007504007034100000b1580d214001342c1036018440603401c9500c1078125070000c90b502c0000391011001407108000f6940418403031192030b0750041200d22140102c40c1d014010a08440c01540500b000303410200f03650b1702010240c0141c50b0130407020010580c031503d12003100c002c0d800c405010108160380c1c480134045d050011003038420042c48421810080000f42c11607038510742009580c07050000356120b5034401c0b0218440354040a4981140e6580e042560f1324100743c828510050041c03407901c805100850704e01e40b19000c0c008420410302007854680020340b074101d1800800c800c03079042c4c103c401c1d0411030341c1c03400000545411080074600031801c0d00a14012030707110711501080b80f811640020b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 753829478 1250 753828228 753828239
    0x405190b06011205070e0f0102150c0a0f05090616060e1f0c02030c0312042402072013021813140115050301050103050403110105150f01091a07061104 66
    0x5201520420003a210b80c030200000c09070321004c80701c00300c8048002c5001010301e12202d0510016401e504030040c0120b8500c00c1c00d018201005000481e601074580300e000800540441d0312914070800141142420742c1442030400000300d040c01034002082c03680d010b40caa80c4050060541000350604a400d040d1007039403010580845c1c0781c4050304a020301c0642460001c0705658400802c4031402e81c4d0500c080c6040007020b00e0400c0a1b01406401500c0b16003c1000d4010b110074443e071185080b00075424016914022450101320f8609401a00e849240d031a0034440580c0c2c4038a11003442c00e03d000400183c4d51265018030301080105180b00da40c21011885142c06170041591114090b24980c00e600d080c140e0307a07444500507000c40c0030b0b10100080e9051004210f503501a030040c9402501c03d0400c607501e0609110407900b12032044035042148000b070a08400035090410b00b40c0d1062100b80790007000e080c10700066552515084201b0404182c0c0054442d060100320f0748016958503560b40095034442c0d035030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 753830728 1250 753829478 753829493
    0xf010c03091e0b12160e01021b04231510080403120e03130509010b0403031709011d150f24060f0406080703060b0316030905011113030b09071d040519 66
    0x80b00d0340c01c91000045021800701e030051030f035000c105005030300a00140e80c100032040e1440c01c050705001d0700b0640300c41e050030180b0f1120181541122f0004034210062a00300201d13880703d50741d40700040c0211030364807060441541c0008103d81c01078250608060700300e0381c009004010718034901d11150301d0002140c0300b42c0c900c0201e140b07142122000c84000b2204d0b62142e4003003150744524803004021031180d2110241d507000e8489030952140c49007000081d95884400c00070309070007440441c0c5d070494000d1801d050159074030340101b680103115030040c10b40b903107882001c81c01078151001c05080c00c101e038000713034518580e202c00c11a89844a0090150b4442c0e60305d80c00170300098800d48103880440e06004002c1545c0d40500162440382602400381100c01e1440801030b4010f10344101c00b502c0b41c2d5207c82501c40360030312080c0103107514059a4181c0f0340d00e51841c00d041c901c04c04054099416a0002c14080001c40b6030405002025200758004bc092600d40d494014640a00b42c0800d2006440c9454982d051201d00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 753831978 1250 753830728 753830731
    0x4030e1018150207180e030a03020d05181b030a080c0708060a09030e0607031b05030d180c03030809070e0a1409010b01090b091513050f010c03091e0b12 67
    0x220241d12580c0c1e4460340e000901821070000600160310001d810807803907408549443c05148a034200140c800c40041419003550701440c0420003007600011840c90f80030191292560180800c410340034280c0144600a8461070919840850080807504a040c1c6650500541c0c203e20350200030281d4882102c44810384449840c4904031060040400241c03400505005500425606a40385400740d02200c0c01c00903260400f4005800304002d00100d06a422040381c440308007a030151340215203c810315000c1030240d03034041d103200a0040d404050500042d10703408203503054941c036007000791055a50008240c90150f040d40074480c2002079000f44224a40280d00840e80102c2200c0740391043d940e40c2400d00c2c207891061040714002140c080c401c1103104503644c05010210001851a00e0380d124060141c0566080408400d50141002004020038a490683c66549a2003800e0074040070305251405401d82c1510b1103540360315806c40300754801c0c8007148640c00c40500101140b413074a40380d170801c0e00e141c403040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 753833228 1250 753831978 753832007
    0x604020c07170622050c060307030617010f06060903020a120f240b060c060a0f060503010c0e030c180a051b0a020f060601050c070605070c080601180b0d021804030e10 73
    0x104214040c0012241d48080f8139940100003001003603045400d00030b599200824034000c0643d03c503400300d540c0302d07a00b0800c2c41c0b010104e00041200d80e40400040d048400076400b001c28000d48541c100010b032a22400c2c00211407000f082d00003080f54a0030304500e8400b45050050414202400000a074003500c44000d41c020f00c000002c0107024184c0003801103e04c1101940b41c02d45d4490300006010f804280c0241201048448006c5000c80d510300c0400c1c29151b5440c01e940c04a100c4444034840e03420100710341c8562220846a000428582d0031001c05c1000f4003402d0940700d503880d000042e003880804100089180484604943c0d25035180500030b440c0c1100d00f408416501410010907095031140c42075410360081034001e01281072403c030080d00c01b0740c400001103c030700346040400514880c06101d118004d00d07042032204007200c007950140e022031752500d40070740c441c004400240d07002d1380350180c0030283e41d001c43c0d4211100c0e45485c2025608030f0110b00c402c07540401c012881ca800c0d241c0c810a442c00204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 753834478 1250 753833228 753833251
    0x3020c030f1c0615140a02011e09050606150a0807022107120c02010206180a021008161b02010c0f020919270f02060f0a051c0506090604020c071706 65
    0x15103c42607000c1d0040000280740c002071760745c00d50301c170196000c00040c100070400e40000220b421058a02c0c0317040c10343e00441d501360290395015060600100307000140d07109030212a20000710140c2c0101c0348190088025020070480d40d2000254228003c0084151681e18a0390701440740503100c0c08120280c0c40010704480d40b03581401035002241c001c2d030303041607840d038143c0207000070742d481c904010305c60b8001929148592041c503403610f0158031030383c0502d1000b0105548000451070310309ca41d078110810191444040050460901621070000c100c0b0009007542483c00c0c0388074441904044060807040a00a540076486205000c1e000a045e000001444050281817040924000c400f0f10034820110300c03d03620b04407000c80d000008200b142d42c0c16505200903e01c600b000d103e40c0880607190046610a00401c500194410319105000340360340d1048402d0b0000e0141d4603011010034000d5002800003401180c000c50181c040b2481400401e000e000c800350300940413840b01c10119615541030b01d5500303822 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 753835728 1250 753834478 753834491
    0xf0a030e031f0e210a1b080a0f210e0105011d010b0309010e1506090f070e040c09080f1e071a070c0e010e1b040807030303020c030f1c 59
    0x50402042c00d100007a0354081260300700c64418180e01c043c3c85030000201c0c150080c0242420007203c1101c04000a013014240d25071280750160018200c0c1008240041808040c103100000086084003111003403155440d11240850850303c06a4603400104015010ba900d51f8160a03440002940507540791b20401000f0b020903681c51421506420402000d0030030500b040e03005001030304510000f16000b2100300b00001e0301d4000034099904045c0c070900700f003441c01000c1d01803140c0717850710030106500142c034500d204195050500307000d03259008005045005584918030982614001c2c06118000c22050041c2e4032520b0240940030786607400804600140d002035007095400c2c3c800027a0010940301100030701207284c010549d04007040d42000104850001d80c60001180d80d88504850900a00c04144005201c0c00d001114444014414042c840e8100e000c0c401000207a400140480850b601420300581d20b49010000c0307811031055500300821500300196080d0b00030300d40c248910f004d440310142001603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 753836978 1250 753835728 753835757
    0x302030712031a040216020a030507090509030a080a0902030a0203070924050a03021e032a09060120031b030403050f06040c180209100315050a120f140f0a03 69
    0x480304240200815600003d40b60040742c00c00341e004064900f85c08040708100e0603a54000351803000035410071101e40c0c2144004100c00c00c0c80d40115900413860f10b01440c1809035144000b04040001070000c1b40302c985841d650300664506012100301c441d0050251140c0d15201c0703a0a00140115050104803445403101b508007881c54150100c1c143e80c00100507010302485c40d02046501e800c01d4010303000c00c85500300c29601544d41040303000100c000c6101c03800400e05640031003038428803003652413034018008034041010300e0780c0c440c0c10407916103442c1e600710043c0e00070f40d81003510314050007a4002400350250300c5010111000400b920807244600115002c09014040c2151103410940b001400d0002d2601e05020b04030224001c542c01a5040a0050404600800003001c4401c02c15412000c05e03a15408050410244202c8502405040d00c000c0b000c0c41c03520303010342181025030001034a40c48101d07404070204000d401043e0704064444c01119901c4100013040b0b912228101c100300c012400c4541e14100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 753838228 1250 753836978 753836981
    0x33210203060f06030907140316060c23060c0a030f060e1006020f0601051c0b0f0a0b06040513020f130314071502030315030106050a09050406050c03040b040f110607030203071203 78
    0x12440441c400740210031f00c1d0503c06144100c1c1c04826990502407041498108007500e02c200004140315070b20380003480e000b800c1030810b4440010001030401c0100c1d0a1a50388071001032100e411441d5454142d40c0c0c1c0b90812000c50083c03030303050302820b0807500b411030000710190701c204103a01441c0c002c811403242d9a40e4078011382c0da03104005000005504090010021407504400b0380c0c00c3c40a0180d80302c12289060750701c22220120407604829031001d42c10a204c0c04a000c0c3c46010b0b01e4020580300c4910301070600300010300d21004100c19585058000514045a8881c1003e48901c08008801e818200b40c40307152480e441b03034400d0140d07055445582400500d0311400b00c9910840c100c107401030341c0344d0f031540043e582a0700080d92006405648501c2d000450382c4944040000621418070002404c0c2400d1414605450015041071982034060081c00003007079550b001986c010313610054240c1400759900c0c20750300422845d14201c0d400400030031070105050300030000308032045c850010315600a031400b00a40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 753839478 1250 753838228 753838231
    0x90907030513060b010e090702010c09081b15041d040b0c04060e091015030c18080606011d030709020d051e1602010f020406020109030933210203060f0603 68
    0xb406000a0100309012408591025491440616004c1c1040b00041c0202d11060801e89104e00182c0d510410361803c65403022201000d040c01c0d001801400a04205503c00328501003035a84c8918401d481c41007840c030b1144111402010b541c022440604102c92680b640b02c50120303030564603d184400007485c2a94100102c85c25542c040d100d41380a0f10b040020301034106c0d001014500601520003000c50301e0b10b9880c18030b1f80c40c445150ba000c0340e10109072900a01203940b40303a4030559001501c1083c011182c0109025a00000a20300842e050700242d0440740300da800d042c46250103001d401c601103505610350300180080c02d03031150300f031100d511003480400e0309844500c604201e0f07508500c00700d860881022600d0a26202501c00403c1c0001f500c80d200c82241d015512070310150b07540d80c44000030982c1203034840004105400c0000181585500e14150121840b06d001413020b02055030300344068001c5018106109054800000c1040e41c900c100b07000754029661207202d4021001c82032154501407045a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 753840728 1250 753839478 753839491
    0x405121213140f1c08040c09021c022a030703020a0312020705011506030615020703060b061210030b0105042d060b0a0504030309051c0312110f0909070305 68
    0x14003155454032201c4142141c41d000c11603005681d05100700300e01000300b14150728001c00c0c002800d401181d0f01d020400440542c01840240f1a24004000200d004d0826944c121900740101503a140741d20501e45034204950085000c1e018408144c09410006a00e40c4c0000c41707165500e140d80415510700346940d28000d0b1200100168031004130f40c00044e109110041980c111200c026080503200c0c2c0e40d00d825140e072481d4105118404035001c0000c1503050051b9002003030701c07041c03d80070403072030100081d1204a12f01000d0034441e2a800140c0711a1980c00444e1081581803840b142c540c144401c083c403907140c80b84819200203880d40c001040500c0e2900c150700148407104450b054050111894110303001c09070201c2e110155840d42c00250b0700303140400801e4084403a6a03131595660540ca80a045046550003c501a43d0070b032440c2e9050307000c240a420b2000c0d82600300076140320302c485c3c2d2010142059134a580d04000c2c010444811843d20140605003648c800c6845001c0381d038070504c08504445045400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 753841978 1250 753840728 753840757
    0x142d0a060504180938070503100303080415050a0b031216030e21150f1b28170604140c0d020904141806010506040b0a0e1305040512 58
    0x2d1202c40f8525500070450301d0303c03c2c0ba0b8a0120a014a100d0001400b9034510341110303003e582c81110320401c3c4407240d030350014890401c00d045003800f10000c03207110981c2c0001801e015034000820244059461114003904a40d075041c00350349401d035100009080a400010301a105005030890065440ca01383c8040700c404280705611183c0365142181e0500007045140d03005221040c80c181c01c400c03010b40200420314030b4001000c1c0307040030390540034a60400234900300800200c078013400003400e40c8860003002d0020703c41c40642c54441c00d011050407031078000108401c00d406109409041c0e90030070310484807007811256102d0903551b41c605000646817440d481210600351440003445090500000c0e00a90303034031810041c2858007180c04a0f0840310702402504000c1e00e4081001490361125000301c048528240240a140d4942804502280114011941000c0c00407410501161042c0e014054080009000b00c01c0150800050700007020f042d030781034a043c0200c20000003d5005801110b03c0d00e103140381d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 753843228 1250 753841978 753842009
    0x10e0a030506061e040c02150c0307090b0a0201022205010f05090d12092705070c0203103b2a041e0e070f0909030801142d0a060504 58
    0x1045215140d525072600c000c4844c86003070783c032521140300b44c3c0310500b0990002e0030032414100b16030341096001080410241c0e0200204207e080e40114044110360808200c1d07621040c0112050340a0b001d82d828080203803201d1001c0007c8020705180c1401294000c0c0c90302c1c1c01444001c0b100711054411802150f400c004d400e0b85810010300d074404401126119840c14400f1991034030b10700c1c41694980c40c50a07140081034000421401c4691084a4000140303082c0300c0c0e803101d02903002c261289000d1030744400365560b5040e40111414008041c100c8281403d1395110304030200d41c8114500c2040200307541e181c0c82003450724500500083c0250310802007c41d15030307440303422a00400000d031a071004d1094680c1000b9020300341440e0280a2180e02800900260140303d0500903401e14596482d4000f0b1819400c01d04007102003a0810364181c19a1541d50101c4401115080446e50640d214a0000400c40043c4224039007a0203a44142d800103074100e4801d0305003592402d08603040c0c082c500824010011624 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 753844478 1250 753843228 753843241
    0x1201091109040201090e0f0402011808060f0606090a091d0f030409090813060c03030e0c06121506031009050903030c2a0111071112030a110102070b070e010e0a030506 73
    0xc2260b030107481450840ca00c1a220840c200705880d0954400341004059000c0c03004542e08850411426540d81c007210600c0c41c81e001245a590101130280d031001d140b101d0220343ca03a100c10003101c0040c40041d00158800d41c2c0c0b032242d440141000d04620000102c13201d1a8000300038089031000300c00345241c004504090401c6803400c02000d00090803120403000300805110b5480c0140c0c039400804c2683c403400411001800d001c2e0640e503402204200076000f80080d4146545c8000580712101c0030040d140503140d94180b03102442c1c26440540b241d21403401300800443e03a004118600a03a10b00c0c01c0c0a1049446003483c0ea5540e000c1a08c6c0c01c0d1000e00c0038441c90300c0c424500010440d0441400071000c0c1e01601c056403460071078411040c01041d0900c00240740e130600000c8400d441c50403a0135210071200308a8107500765140d002c0c0f031754280c08020176120101111603094042d501820381010110f42941007091010b0000320703002002502003050802540c44070710386103081d6030403a81c008000d840d8551b41d05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 753845728 1250 753844478 753844489
    0xd030816050412080306010201052802090a030f0605011d06010c1103190b0a060b07020315130c0f03020a0e13030f02070e040b100506070510020304031707020c12010911 74
    0xc0941208121007440002910980030006480300d50043c40d0455507030600f103000901799180103002c220804200f80c501d215512440311008541c880015005032626a407030002012800070750b01c044d26001c40e0703820000c144580d541c05581200c41c83c0d0140b042002c200f2030700c010146003c0b59460b0214071403401110126000c4442c00c84c8850006050380c0c0400103e044c80410b4525251044d14501c40580402c88c1c5001184140f50181045110a5040c03c01a0f400039980b048440c40c40c5403e0740c1070302b0108001205100c00b800319140d12140e050340360360300e4000c40f4000340c0f010f11050344a100902e8002440400c0c000da52801802d1402c0c10752845809510107a40c0204810310340c40031807181080005201e141d141c0f5040c0240c1c0f0420449805007000400131103105c189030019441030004005210009400040b02c6510351340c00e08001d81c4903626414203075500700b90003220f00d16203c41c601c1041400ca9010400e11081e805c00c440100e0080a03040c0c009007240d0002000804880c040141c5440c030b072030b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 753846978 1250 753845728 753845761
    0x2030108390418060c0e0102070302030c1003020c06041a010b040b070b06030c030d030b0a051c15090204111e0f0405010c0228031403030403090b1602030f15060d0308 73
    0xa40003140c41160084090300b100d10f40c0c4810b50740305940350101e5581903030011801d10003110920041841c9821500003e4a603940181258420341404c010f1580d803030b01940503103089619000030341d02c9030324042c1000d00c24921810301400346211075800200f560b111110585050307a81111216003007903600d0b65660341007040509001c0c0c0c18442d18080c5174140e6010040240300b205196004103502d5810404d0001407512600894426408900c10a0710529040115003416401c01ca42254950380118100000d110458000c0d4201d400d1440b803218136002c4c60002c1c202134080c0c60443c043d5111840c207105803805044a041030258080004210a43c4103a5841d101580028901d101119841d850102144000c6d4802c104400801030700b0000d00004814030905406042c001d14954905a0b07001080d40c40c05004a00d540034000c03407082d1030030a403410b440f11010b03805000c45095000d200001c1d076460017210045d8100780b85650004140b07040502d80003500507031649603084107450300300c1d001001400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 753848228 1250 753846978 753847093
    0x5030c0319090c06030b21060609130b0a020a0f03050c0d090606120b0402130b09060103091a1008010c030603020603041205160605040605090d0e19081002030108 71
    0x11900342d00c2d4003245030724401030018407140e2800501404814180001d00a4106c3c440c0600d01c40310715483d15041c1c0c0840d0599001108070380c68806641c40c07107502071440c1c561340c10242070100d8030b40030031181e0710480d0300500c1a2400e60715400a900d40841040b0240e074030403100c01c90b412000703001d5014400c0b81500106416846180049589902c030201214440320fa100c098801c0491142800150305043c1140c02c0000c124403400d025810064020030103d400c0948001d04055480c1800c000388200461260813000001c1c19002c0a800e03e40050403a030300303403402010555481c080d030f20009280a845070340101e0341c2c050038071801c60340ca644401d458405002d0800c0f090000800c45940c0340c02c0c04004984025200d246c00081130b0030035082600031140010f1824460f07920404040c45d41c1500031100c01c0740190210352815041010121039040e40410358020140c0d8894448401d0f0300a4183c4c0145060b2001ca104468981d4403003102150344401004006082200051031f694400c4480401c0446409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 753849478 1250 753848228 753848231
    0x16030503223c08040e0603150c0d0612050106060806010c0c140a05030d030c03050c1615020d1418150a110714060708011a040b07020406050406060503040506010605030c0319 76
    0x144140b980001d03101a00c2c42150019400030301402410143e03402c154000b00160020140b0740001304c441b0020701409000b0142d2101c021801c220b030108190404006401c2510314000c4400c224688280a8007050080401142c0110001032680d44500012014207804c412a82d00c941c1c42c000c03030021480c0442014a401120980010810742c4040048144554907036800180c40400c00740300400700d030006481040218000c1040c9801c8495001c0710b400d509820110701000003000e2141c0d000240301c3c495a400c01141003501030a89a24021f80751440b601421040034032a0096807030181d11446490101c040c4107a007007000c960847c0c4075074422a465014034200328a40a065142c4c094074520b2200030f00c10f107034803650401111a91042441303004101043d840316141c42006000c8410340104e00440d030341110081103031810f40d560b541142c4010a03001d0010030285480e1800100907600843d41541d09104040000550394807070b02c101c1c0e21588141a03c582551202c0c0d1000c040d120f800b0000300c1c00d45 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 753850728 1250 753849478 753849563
    0x90318040f090c06050a0315062c120d02100509070e090708100204090f110d0b0105070c0e04031106150609031f05093903031603050322 60
    0x10003d1844401a1240380c84503a112021860014290b0b8803822141c1350220051008104043e0098000c182007030551008a1070940400b440c110004984407000b80e200d0783c22161101d841001048610301554140d0a660700302c0000640001035403000d0b01d2255590384000001c00c41002025501a04480d0144c20b4800040e914110b040c6070001808040200a0b40000e0800ca16026407180980c400c1400406000c0c3c010030a25490050240ca40d0a60043e503e403100321039a41c0c4200222500c0903404100710420a4071040d01d04007640040320210701003418500110000d9200058413442a00f08144030711529081c0b44c140640c90f004810443c1d0140304a880074007a1109228103000742c00c00c2d88038002145e1908040461030051381800407030681301140e1030303441d0080881d480c05580010f5102008920b041980c0403a146108000665000d682c0020b10a41095400300056005101c04140c100300f030390018440c490303c5406070038010008081c02c00203001e030f1841c00700302f1130614401040c01c5c0441e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 753851978 1250 753850728 753850733
    0x41a070b1005041404020907050c030708040b090102010c1706130b0301020313050d0c15020901090e070207090f0203160c0305160507090c021c030f020906041d090318040f09 76
    0x4121040c1da03000c0c5a035203034820510040c14180f041ca440c415030a40100c0c0d1900b0180c002c551140c3e00a405c1d50b003048400101c108c001e100810460748055403000c021643c440c0e86103200301c0f00340c2201c50018019401c0000450b03040c1d100b0b01d151b0407120340700c110070449134503880204404185070300c0010401a441c0d1103e2001a902032010714410240491244c2d480300907860010b0031318812401c60414450340c0710030031004c52081402d101d03003034442c0305006a81e401400c0c010386801401c1e138070a1060043c0c080400891540c0070800c4001c0310034050041c0280d400c0500359406901003103400c221641c4050b180b80c500ba9114091510341d45000f030030b00c40d20b440c004c07540c180c600780c04010040d2480e9000f4403040204e20281d101d05040f0341c1c6144007610a014100016426508100c0300307807010151a102d0035100064039604035101c41000404c42d944e12642c0f994101c10340101000783c0316119180000040d010706000c0110f410070501840003003a100b98040c104002050044460314009a80d0030743c0400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 753853228 1250 753851978 753851993
    0x106050607150b10090302010c110603041b140108070e01030f06091d0a030e120723271b070b04050c0a081209010818010504030509100201060308041a07 67
    0x86600807110240b2400b00090740b20181e482400c540c50190854001e59400c4a03880000d100a491782460720010980c01c82c10f0400d000f12060600551000300002800108500c0c4880c0c28600024210f01c09241641e81d000c590172104000740c811301048602e000150150301c5100c1125952405050004201c41d044600380221b40658100445450380d5000c880c010003410304c0c2851103880d00000030140030305103940c008c0c4161344901700c19004000103950721050001c1400b128018011401ca410f60100c00c0c4220340a8190459903081c3c018400301c05001c00c0042c0c0c40d14022180d68525901c0c0e4040e03100c5011110720b0103e289480b0006a030180102400141c40300791960243c1d01410003400e09146203004c0050010050f40301c2c0445034044100e50340201500c0d030a0394110102424101003d03615041c601501c11700e03408050b9240e528041c00c000c01c16800c0000b8000009003611030308540003010905130308036451408060000ae0040c0010841d445158490308442e04030743c0c0c141400c280030b0750b40305e14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 753854478 1250 753853228 753853237
    0x10e030307030f15150215160f110c0108071101020f090f03031312030c231014040f0302030f0706062306070b1803040603020403060b101b0501060506 66
    0x10025080001403000881d898002c1d210352002915040100030314180c0030403002c5074944501e040c044040002a00018000e0041c8501094070040b01c1d4814940b00f070012000d00c5941c80d403280856000485031000300e00c03c0c08090807040f020f01c000c0507040141001075030951401448641000b44c41107100d1328044081c00a03042d803200da0100f6039141c54040b8204001c1c10400184c580c080c0c2d006001840141307400c1c0b030400c400c407400700300ea03c1902c0e00780707060031030310001e40349409042d0320003030055507443c0b60055403403803c503001c0ea400303803041000c08604c00c0e01941d6143d11403104440008002c90b02044100c24401500d83c07080c0107c13481e01e500c5008040f03264112003c19500c0c995a10b0707081040c482c0c8590b0401180501d03003020050356022100140f42802480c001812030024900000d552142000b4280601d241c440304a90f00c4030303520813004010b54400e0000702c44103410000702c104541080640e600d16842c0a0b01c8108100109544040126801c5042503c480d901c070789000a20ba140c800c000d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 753855728 1250 753854478 753854501
    0x1b090108101703090a050121050c0403020603130210031a13060f0803040611010621020a030b0c0c10090309230d060614090114100207080114041703070f050a0c0501 72
    0x15515140800208800c4614071b502c0035040c4a0004080080f10100c1c91a403441000e002100062075202c0600c0385c891409150002900500c0000a220f09140010601e140c48c500c201d5142000d102800d01c1141561040050104006039040c001c1c441d038a00070610b0440100c40071000a07000e40d940c42001c1c407010f20340d80b021003540c000040034011503900c004464490803200c8024000503140c912101c0a0b12507080c01eaa036500e212802e03413000c560390544e41c40e000355085109195035081911107031107283d11401101e0054407504a03072100601e0140601e140c00c07509034445038035445c40c10201e203200d080f070300290f502c248102800311582170380d82c07200515941d0300a1400282e140e040c8030942e0034a400c01c03254507214180c2c4c1c80041002003801d0041c42d210000603102032030441764056007649410001c3c0c00803000c0354203240005c1042d0500c1c81e200e910a0380201c8450744000342200385101c5600c010307180a400903130f0b1010300e00b1165000d00018400b880403403818800042c00c7c0d440c1c1c00d00715164003010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 753856978 1250 753855728 753855733
    0x110c0616050a03110f030309120309010b04060801020d0629030403110a080d2a1112070b04020a06050304030203071b120c080607050f16051e060703051b0901081017 72
    0x122500c0131041144601c01c01401c0300075880d50902200f282e944440b2010940803001c000000185410400c1d00500141c500c0a00107214854549059038003035040560101c606524082e00014903d003061a462800d20b8000d1044000080700740000056030300041045c0d040c001d031503c21903000d6404000406806003c0d0848545078000307814644299114043c2103551081c03021030000b0398009034000780b81e00201900b08000b01211400d16203040001e213040c002c012030740c0419003a0600c00502c05061141c0d20071030303040d24070b207488400c255041d0109880140041e481071004800213605031086006118400c0100d00c180c031307601c0b1b900a285010101c403c54941188440c00c0181c1c6d03c0030420383d03410038a5810100e045c880c028420340914020003003081d0711800580116410b01000b071001c041285018030f0b007000c40b200081e0303816503521000e460007000a0300d4035000482820289611200980003040c1c0b0320b00c0c1100242c011a0003010291500b034040114000000e110340d40c0b0152a0400c0c03104101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 753858228 1250 753856978 753856997
    0x608010e0a0e0d0522150f180b070c0b2704020d0c02011b030501060c0201200d050415081b1803030a020c09011a1e041508040204050601110c0616050a03 67
    0x19110715a0360003a5840081d8000400034800b4030400141c00440084070b00d003211f01c0e500640e60444101080307980d140700b00d41000d8804504118410000d0041a0094000200703241da110b8590800340325010703144541c442400d2400b07000030407560341418503000081000d42494400250a8111002c5031a1440585c2d9034440c0c116000c0c07181c10318186441ca0505040100d5031502001901040346840c00034104812812403d00007150012201e91051b0313404203d034404c1c61201005403d641c464003403008071855407101d44c403149200e55030b43c606c90121050303984507240c09281c0384240781c3c00001082046802201802019440400c09012002c28560042100541c6001030100c2c90300c040c3c00c1100030884043c40c0140e44002001294042c82103c81801007080c2c25403945517190049400001640c0303c085038441e011903100c850300b40558000c860070880d50321a2001941c2011145900c07019941184180001600d0104081c09201c550540481210122561f81d1420b1214403001100400d40001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 753859478 1250 753858228 753858247
    0x8040f06030c030e0c061b030d0c080612010507090b0a020c03060708150d0f11031c0207150503090c010e0310050906040b090a03020a0204090f05061005030d0302040608010e0a0e0d05 80
    0x1d480680004130b015107010190500400c01c94811101003d0386400b081444010f44117040080304d0241070725100800000552000081c00048141c668500c20050031a2800400d20180709450040c80b03681c0394040008d1510401d510b15410000141d01503001e070b68484943c581b0207202451290400307030755070f400030f24228443d42140101c0301203d0f40114000d1854500050103000c8a041450300142d6002890401c04000303071070400ca48803080a04022402c0140541d60000b8020096038201321688440303040715072088030103000888205d00e540e840254840c0c03413035018490800402c00017070143c60500e50201c0550040e24419500c1c45280d0380f00100708828400b002e100c0f6504190180044e001022054400a55032140204042c1c404c40c2c3c1d8040d480104121000b164100a51007020b030f4040b0715000c0d0402031110035601c070b040d00038040c0404003c0610310074400c49058401d180c641190070303400c14403070034850040203040f034003041e684207401c203844c9404221900d40b084180d610b05907280b1496 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 753860728 1250 753859478 753859481
    0xf0603010c0c0b0a021602280911071502160c080c03150c0325030213151d0d1703040c09090f02011b0b090c03210901050708040f06030c03 61
    0x1074038008100020581190001400c01012a800840c264800760f00d8003c078610400183e0682d140c003d42c404800c0c800030103003400180007612106e03249184810107582d80c101c82c405403a0075210380380c0450401c025980000306102405480f100360703a4401400d1082c0d4146150700380310300d042d081d40d10a00c05081000701c01c10401803c0c2d2003840950250480d07000303807001c1400308600076040321400389001c000a1408002950f800900200e02c282e0b1550041c41030b103010703000790720016801e40e81845221000c200006030004900011406940354080826685c501c10005540c800445602481c0303c000d42c4003040b00d034101244000c210b201110b1383e03410545800c12204030340d9070004030600c0c2403880c8400428003035180041e0958080c20144424441001d2060501c01515402801c0700102c2042c07103100b901c001140342c8000310540440303140b0911030000d0344c07070700c60489040e0501d01400c03c00301d801e9500c14005041d40b03a1051240f18141500c3c2c11005082c100c007030708a1800259211010003a86915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 753861978 1250 753860728 753860741
    0xe010b0409150819030c0f03090512010603021302090a0b28020601180b210721050712150f0f06050f030d0f0c0b0901090201140c0a0320060f060301 65
    0xd241c160300d10380f03241814041d116481050942000c507100c020a00c1454042d030341c103024040c2c0c041c0403c4a6018146030241500b803103400354a01880800c01e10841c1e08030144286000d51780c008141d082011801404940654003c1d0303440d54010191b048001180d03003100c4041c1461031100b000058564850b500d12003920101c04039508210341c4038000400000605291304010856480404503031944001b011521714290000140128a94842d409049200c04150b010540b1825107044005450018407882505405100a0010b070813200c800c00c09402175034240644c45128800010f20780822803040c0c01203482926042810640742d1004903e10b12180c4180809400119207445a00d8204404203984014500d84401400390b205001284140908a40038140d81d000360030320018501444014042c00a2090803804290b038404034000c00c000f80ba0079550407003500002411220030a0700e088440f601e032440114100400e04035408075102e0240140d502c526000708403030007681000b905040c2107854 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 753863228 1250 753861978 753862001
    0x110c270a02070501152d0b0c01060504060b070201050d020c01060e181c0206040b07030204081e01140108030711060904050f06030f160b0c0f0102030906041106040501081f0e010b0409 80
    0x4400d2014451b0018410700c0340c2042c07001c150f414180b10740c000b080c0503a040180d007200440c440041141414041c3c150440c0003511410b0702d09101c4030380d40307280ba10224000d07514000d0200742c0c01e000d811030840e550b5020b89440004403001090103640c5e201810101c62080c0d50012145219100c0c4001802e07040003181c05100200090700500381c0c561100a442e04000340000f81783c000507902180d1072500c2601664050a0000140c4032403001180310070f0450030112903051a254203000d030200d130100302e841105040b1880c00c0c02462030008540d4034a03903040e079140c80c1e40768056400d225081180d1694070810348a200f010301c08191509214080519108508075046102c2d4000d1503600040f1803808940301c00c5400109500751502d400c405e40c1414280c00e8400004d4541c404000c03c01708060026000e40254007507440ca1340f500f10100c0504c4914810381c040c042c041021320010410201301100019491003a0007203d450341515004e154001c0e00b42a400f028021002042c1401041481c0c40f410310341c0710 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 753864478 1250 753863228 753863261
    0x708030306010807050c010b0a091a0d1205130e0114181015120c0f1e09030201080c1c020a12020403020a14150d150501110c270a02070501 61
    0x2400c5070008110700c0c0002d08410421001259405035110250403a549a41005105260243e11804108000d018000c000494044122500c0a580c00c004030600c110701c1e04144115000030900000340c6050b44500d41910448440b0a0300040b81d0010440d02e9010342111545c5102040c000030412410910111110343d0b803040003000e0240c00b41c088484901100c0c00c50301c1c111001a40e03564140c902c0a500a9000c192500301192200c240b580704800004010140d02d420a402072080419540d02e26640f080a0214090798000e10156010350551079004030b0b41800b0518110090b020720305410002c00382d8604042d00840c01c80c040f183c00c0f5541079090410f485085041c0351440d00001c049240c0c138840c042c00c0705440400400e01e500e4500c0a014070003010810251788441d200745400041070500517004e03040042d603001080544c818802610f507060550020881f034013003441080014400c18138503924900c8040d0000c0002a8401e1105114030b1100c0c00041e1500c54508182d0300703540c2c030316a444034501c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 753865728 1250 753864478 753864481
    0x390910020d1706180f010503070f08060123030a0b041104020903030d09060e15011410020c130f14040c0b0705030301061101021209030c0f010b03030a12090b04080c07080303 76
    0x1258000b41105507032845041d54049602d501011819410120550801c00c100c0303041045445490401d1541c100c0d40f0641c00c40e03000d5030742d84402c3c44a102c80b50244c8015a001840100300006128201804907244400349060200c4410006407820b80b10302012611185c4040070042440f10001141e502c40340103480c1035107030495820020b501c1e1700c64001d402840c4e0b591a40240f05000282c4e0010890408030012030b00b100111806192410300248611015045c030b948240c14607045c040200c002c2841e064004008a40f400c0d030800ca070031540180011f0140c1d5840c011044800c405004490411141800114090074a0304050440d41815000070084003010045900025000412281110524905421b03500c3e82c01504a0191080ba80d1041d0140c0800707050043c0780801100400450084030110380814856440140c00d03a4200c40c2c00e6940f5400500079052003900454011600c20310004001410040fa6528804080415201076640f80404141d1001da46001c0040d400074046800086040d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 753866978 1250 753865728 753865753
    0x27120b011e0b210915060609133b012307080a09050615030c01080105031c02100507020a0203070f05061804090f03050a2639091002 58
    0x880c0042d01c1a0607050b140060300e24003042e03440c5842c080a2001d5a0b01400504082c801143c2e24654004441244a000e0001c90140e00e000d800701d4200d110007030200e1171745000001307840c40144800e4081c1079440e050000c103c03108a9000c80c0e134406c0201c503440c01022004180181c2402c403041181030a00e0700c0003506182d45041c03100c1142c540c1c00070745890420181ea0350650304001415072420000e0203482050107005098241c210752903e40d8000707500b01d807486100000112440c1500780700345609174000c5204041382d8011a608195190000c3c0101e4110501450803202114021907410b00160401c200715011407034180720404c020b28001c202040c081b4204400600d03a4822909403035809061a181e407007160700c55800c9100b850b908400607010048041c00d02904942c0f004010f00f000a0280080101212000442c016610f42202d031114440c0d07100400150320b41c20501038802c4400300d01e9000041c901c0001e1314480d03500804840281c580c0d000308140800408401c074001c0030354002d41c120810 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 753868228 1250 753866978 753867029
    0x405030a06051003080703050901030f05061e0303120108240405030909040303181101080121060e0f060c0406031514010f0e040f0e0606031c27120b01 66
    0x1000c0c0d00041e00180d2a2034030a6240c40c06002580010680300300841c00a0500d0307080800303401d054030b00ba00c09014290400c0c8c890011990f0407509142e12400c8003520060b8580d1407100040703000d1000c0c04a07450302ca10000030003c00d0000340d00c0303a5a030b40d00403c0850142d026500040b0300b00c8100440307140303039800c190741ea1503240d00034824240c2c0100c10030000203007814032a0b000b4051a034850003d054030000c0c0307400d102c2e1400c5801070307065020074444d000009148040801d500101c1d0b4050260110040d03039a6500030140400c050360f04801d1044145e4140a030405004184c02103150f02d000c02c2d915880c100000c0c1c2500d2110460000d01800f000c400c10018003004061581d04000740b80a21201850700d0054560303510200344603030410b18000030024803078056800340c850000810216000340e0f40b0300040590740c90380690041c0e01c50000003441084503000d02e01580f9020f0803030380c0c00900b098400c040d81603103040562000d4041b2100c41c0c25481030043c1c601000d400351422284484903085249810072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 753869478 1250 753868228 753868243
    0x6090a0f150203010e0703050c16060f150b18040207020114030720160b0405060a11010207021e010f0216170f1027020117060d050114011a040503 64
    0x5068000d0003a004041001c50007048001c40520036046490396111825062010400c45508000c03e1030500814a00e81e40603056034505690524040d00f9503c0e1540e03828094030b080318a0160850b01e46191440d20b800103140302d4058940e03488455185e150010070341c95120814007109000d00d104010010140c0d030300805040106120241d481d5491300c1380f4004903140e102ea92403044c0004003e80a820310340c10085455034076802c2c01003603c034a00c1d07100c8100381002e101f030303204441d807200b420420803641d03e0044900c0d4840c040c1c101300050600d4031a401094003403414028000714207080ba0007180c030941c0c01c01c0d910804234580303200a2400301c0070403580c80343d5030926000d20f9807030500b100190b1a4800c0d00300000802c090502091b01c5020b6511303003015024020803074868181c2a10b60010182041c5000300102020350165512801d2402c049040041c0b04005001c25420180002013640401c50900408040154015103444558135148400803203110501c00083d054504200400540d81c0001e401d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 753870728 1250 753869478 753869483
    0x60f0a021201030b04030239010518040b0a030f030503010501030e15220f0b01081c0507060f090605180706020c030c0907091703030109140601170403050405060d061706090a 76
    0x480985c0301c0b4201645048045038504e070714441c4554409811451146d00040348150449441522080d4000150b645000728240204101010380c040720440c80c041e00a9440408090041564a07407a51100184041c01501c04d402090000004120075641849650100c40c0a54027812880d040a4283c0480f044081e0846591010300c1d0884003002400310701603508030358040c41c2d414200709145410020131800b4440d42060340504000310000042c540c45030051010b45586003071500501d0380d5270030001d0000483c03841440d035803080c240001a500e481254045d0483e1200e078051050800303620392924245401a0046400023003e0540e2034038005407a01108000315035480099441c98421119464203178400007034810044011440044080011030580f40381100c03d00840b130b4619900031542c8826074156000232074103400040a07440f150308581c1c205d0311900c0d1251800341e071000002d0858001c040702d4020740d90307206020000740d0302800403900c0906110001d42507901c0c05400e000d40364410504007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 753871978 1250 753870728 753870743
    0x21060608060409150216062307080714040b0702280311030309031c03060501031406090411040c030605190605040506130e0709090507021c050901030b040e060f0a02120103 75
    0xc0108009104503640c04004c140c440843d1942da0100080911452050050b220f103403a00b084504c0c2d901240d40c28000c1e00b480000c0307103c070b01d03102c010080304d01e400300a000208000301c102c070300749400065500070001441032110041d1681d00d1401007100c0c1000d0003081c241c061556086446007020096031140032282c12649210220b062070380440d08500c200d85035107031b1600841c680c0c100b0280c40c0c8a0890f20074001a83c0030811a41c80c1d01c01941203a80404034030303584202c10320000c3d0040c070303110b00d16a074840c0c80385444410300110080424142e0380548008170109881f00b00030b100e51b00781034540e40081061001c20411007440c081002e40507119500846004400002c3c9603200b0a040000e45402044003042880c0b8515020700e008021681e14014501160304010100c2c2000d80b0000d0115080c06034442d901e9500100807400b965140d0059400c0340c10303d51109040109541d0b14480c408500c00d002010b00603c0c546242a1210b01100401140b4024414440c0342e55034484181900c1c19294170083c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 753873228 1250 753871978 753871991
    0x105090f070f110c0306010e22170d09050d0e010216240504081009120f0e09090f0718060e0c0702010c0206070219030b060103020a0c0f020d05060106210606080604 72
    0x9201d801c149516804c150144503580c0002510800308280c00e00c40e1000e03040017803a00180134869640d201030020017500f01e81c0130b0b008840359541807500503c4088140b80c000a05054544d948509189612403c0408907451b441c40006a58050004000e581e0403042c0e010503560070b107400070780e0440411040292841d00311140000880c040ea01300c03806041d249044420402808000344054044104110382a039400c03440c2c05030450192280070b01a1099440c0c8406082603082400303200382000f081c04455105541f801d0301040320600261024083e05180583c0000d842145070083e295550300c6401c0c0000190108030403500b00c8803d030341b400390742441d040406098500008034070b405075280282d03000c145060402d200c1c99100e90790f401140c1c032951225403255a0200103600b00e016240200d400f05085103000d00c00a001d1601010701e851005000300700130340494403142c1c42e04100f40c0200c030104aa6080060b0b0002c1e48001800000c60141000d11580d0309100004140d400003601160040c0d407201c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 753874478 1250 753873228 753873257
    0x8150103090b01180b061918053604050706030203101a0c1b060d0f060308070b0f0c0901091e08015013050a0b0105090f070f 55
    0x10407188940e504500000310b15611191440d0306107410300c07880c0320700c2490804c07180101c0c00c141742901e107490080551603080b400c4c41c59090307807802d1001d04c0841b5200e14240c404681666400d80e4581201051405030400d010646192490001c1900b07500c01b00d00b104000304400036100040070310654000d0319001d6102e44502e5020018211290464542c01c032207a00f84441c941c6c10f110290074580ca180040b40c283c03256240600507000d266294142c2c10280400c80c0154820007504030114404111400181d110b1703403510340091503000b50a04880c80d5007248180b06428070000c1e0030b2508440b40514403482d00114100280c41114a48a032805c03020540c020080d5451424a5403001090880000d0155200c3c00c1c17030940503115941c010361481e000044c601a4a41d901c40c1c103040309604100c8541da550319042c10240c9130600024440d0392642407a41450001030000d1000c0000c09100b201c10040b29418030041014500b0024034000d08000c009081008859004c088001160054244007403401c6481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 753875728 1250 753874478 753874481
    0xf100201020c0d11060a27020307151e0305090303040b0a09020a260712141905011d0334020306010f0911071a06010e09070305070e0a050108150103 65
    0x20b0142000e1802411002581590840c0201580150302c0302502c1c0c0a580c3c3c640d2007001c42c0c00300d1340e4140d580000c07403100d42c400150344e41d603008940707000804a030015a03940a1202d850b02107072501e0740009400d000f5502da201d00608488007110100d060a2000307242101805945e404001e102415880200020814202240d44845800354000d0316003540f9585171000301c444030400424180c03121213a40c540050440340454901c050300d27680501c00d201d4030855110480c4c031841031281c120071402101e9070404111075a180b0080b40e0b920440020034a9403820501c005516100700b54401a40c00401441c3c040d0841c2102c1d07860a81c0045401d1150340340745008994005c440044002c0d05071166900110791845020102c1c0200e030a41902400359144019200110b0b0040b4080101940282144800e401c00e02c41e00c0680d1042c1d061410154100c5c0e041d00240c000740f8207a448001091303a680507c1005035001111642620342515002d000390b01d0800020a440780c0206282541e4840c02041007481c1c0c8039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 753876978 1250 753875728 753875737
    0x20303150411220f0305030706050c09030f070602060a0908090904151802090c0a08010320040c0e0a140a120809030102040f1d01031e0203010902030118030e040204050f10020102 78
    0xd2102c00703600e444206032142030711807608440e52260340200740f000646074003080c00c110540c0d90041c05141010000c1d5242009404098402a151a0180400c01494034100407600c54000c2100007085454034020000e820010094002c017103240c141001e59000c2840102110908502a5020646030b070301d500300010054000b401c4000c24030b041541a8060300c0e03000340d0031040e040c001c4544488503120200303026507510035046240b000c5803d45004001150b2000c00402015950840307005c41480301b81d00140c04c03105245410030120321000601c001d01e0800c3c01c0500e019044003480312003003005500005d0090b02545c42801c01da9810207001004202c1c0d508180c03510034001800139503c030f98172458041a0b180403801a03d56005a054185d80704614440e10039040302c1e0401c040402ca40b08201d00150854200e000a81c1c066403120a00300043c0c40074491000b102c0703003022a0312542e80e5a850003c05075494030314014401c900621081c0907079904e000800600d850300700d8900c17442a410003070686c00b81c000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 753878228 1250 753876978 753877001
    0x4140f1504031b1512180b0717270705062d13030618021504090c03020c0d18030c080304050f031902060a02011104080f1c0203031504 59
    0x1222008469201106006041a00d10850041802c083da040c07007601c105000303105072444101d0280322400c60364081d50765000032500c1d079400802c1d1280f41c0ca40c1e031032696900000860344030401402304200d03140d0007198000c400160720000051401c04007002e03074400407602c1100ca02c0d0150703001c90304800c01e010000b6170010f00003d04020b450300e00000380101c1d40401d64034600040303015107002c6003142080c101200d60940500c03540a0a442c2103403500402011505c029541d0324a4030030040700541c2c0c80d07400c01c0c00e1801040c0c0707070587c2d9142454100416034018078122003d02d4014001c0862483c4003050a80c103203400307464405003415043c01401400d80b510341c000ba2000b4201c0401141380c51707021004005440058174110780780e502c048281a030700e040400c000c041e03140e2601d81403001450140002d00c0d02118520005c10708042400c0c02d8806075215a0102c40564040003c071410301e54184100c031001e44450049200303500d1041c401035120300c4003c091448043e80c4e20200c040d195200c1d8408002c401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 753879478 1250 753878228 753878239
    0xa06141b0c0c153c0a12141006052d07140a0204050c16060b01020c060d1a0a081005060411030f07030b03060613181a010611070b04140f 60
    0x100b003c1e035492580280c02c2c00b5008408600c07507059160202c80401d8540c044004442141c048200b41001281c21090405040280041c81103134501ca85005483c031004a15a060b0b40e01e00308070085040104003a40160140601400f0b148602070002180f140d8188001260381c00b405440341000c03115110380707103004083c00f40c079a10840b80b80d800001c200e00458400d0307408026a459900c0041c1450246071036a107147c0b003d1411400008240340c0113040800c0040c0112481101c4560000740c4580101c15100300599644400d04e08140c65540d00d000380d07101c20b6a0380c0c07511901344000b694803080c050060300341d119100c80108a140d00c6076406001141441e42e2a95240d08096415001501c1c0075200031001070300301020000c0d07034500840c40724006c0d24018000c01ca41001c1201e080b014209064001c400c005102c0001030104030703019000c1441a10120300a14103604001010f40300d0242400f611500ea400381100f440324820603400c40d4183d9101100c111000b01080c000682121607016600340c220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 753880728 1250 753879478 753879499
    0x80c010507143f070806011d1210050a02070b010b0315010f02030405030a122c011b02150a020d0c020a1802190201061715070c050f070303020a06141b0c0c 68
    0x2c0e40843c4400e8010306090b5528200c3e901c4003c011282684250b08044842e004c903046000c8034545203041c034116048080540d440880c80d02800d104030340080700d42840c1203400246a80811415000041c05006012000d900714204102000f6107084500d446d00d0601c00040d1822040900230001e0790300400d001012a00082107524000000f00304112004010a25880402c13080c002d42c5482416101e6200c003c1d4000500700703400454680c0e0400503000f01c80380c0180c00c00300250f16150260840300981030b0700b5a81c1d8010b9088000d00d000e491880e144104051188954016558000240304689440201040310004090600001d201e240d030140035060341e510b0120003c54040d00b0404c02c88100c041440b81a000d4059030b01c0d02c41e40400b0508290000b000700103503866004242468046002d80f080301d450007a01038069203403600c680c03c1680507034842450340003004507901406040e019080350b04451403d143c494403179915004280c0703410001d0081191003024400b006480a110801000c12000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 753881978 1250 753880728 753880837
    0x20304150506030f030a121d120307030b0303120108070605120609280b19030c120c1d010302040b1f0309151e0c0203090a121e080c01050714 62
    0x203030404040f10070301c0c0300d06000b150700e0389645800c4070342040540230015141e410000d280c10001d030b070310041c01c0c00180355a90385c809080b070324100058420000d80719810a0070354140801c461900e4200e52121040080c1001908003480c0c04444e055000364064418070401d842e004000c000c90010342540c0500d40e11507091103124487c1540200b2034070807055501d0000c0c0c145510f41c0e4184c403203080c0806000c581c1082c40401c408030004154030205030240d03c2451a854a0301c41c4080400c0c8411014000400c03000014420b51500b0b10030b09444c4041110852500e15100c1a488024001008036106060707843e0750b04018040c1d5084005c180000800c1c0c10001e198000b1083c28920765450511820103103031032103007035016000108a03030055000600c0c805c005860031140b03496698203081c04075054000e2100e980000b00c8203400202e1110b101d80314107501d03141c1c0d0600040c01c503040249014200940c4282112010703003844d08946026441c10000b20300c016920f0500c000301e03117016040001d8112044001080d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 753883228 1250 753881978 753881987
    0x80f030d0c0e04091506060f051b0c090907090605010c03120b18100303030f06060e0904030512070807032f1b0f0d0207080c0102070e07030e0a05070612020304150506030f030a 77
    0x61700382c05000100306a40d01c522003240d000b81e2005842e4040b6104015855120855603941c1610742c00b0802141d45414a290201d148288241e4821106502040090103000c80314002c19010300001c0c031f44401384603903d0300c00a10b941103034100d101019513503040f40100768035848841c0d003226040c2c0d16100c400e401c16069412080d0000d200641c0000d01c4c2480c41034100203a401044100d880e81da4600e440d80c030744101000301040e0302400c02c4090103020400d0707034015501300060b1446031440b51260101850519809819500c03595940c0da910500c00060100c1680846031414000c89020301e040d0301c40c1c082083d050079002c840c602c03018807441101c4002184440010f1038000d0f82c2040e5081c0d801c0d1a50301e41c1070319590315071810600c0c00350700800024003580104680c40c6900c6203180c680402c070360515000722400c15008440594498001d5102070264339000181d216102054400451551510342c031032000c90307100e03011809800e0340c0780c0d000f00b0f00541c1c040240c03401c3c1020800940350b42d002038400140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 753884478 1250 753883228 753883253
    0x60308031006050906090114070606060215010503150c03060f03030f040504110a0504030201030f021209070603050106020d05071218270603021f20030c07080f030d0c0e0409 76
    0x700d031035070880c60102c0c502e40f1580990b446540e0203048241065071510040d80d2140c800c04001000340002d203e000301080d56401124014071858015001d410446e002084203018141c10242c00380d444140c842140703c20040c1d0351540008005211601d075110300000401c00e0007038103411130303251001188000c1d048040f140108112042100c01304040c59504a440816004240c1d0a6010400a0204002550194000c0300e5050b80c10440140b8080d0f003600141c500510030348111041e0b80c042030061040941600c82e40b0301428860008021440000100030315910903441d00030706084503280c0c1d652059000c0d070300e00080c0b10f0202080310344964441000c1442d142d41c4070b11206030342144602000381710030b2500c1104107607071700503102100e0210035036602c00c40341070b81c0c83c912000c10120118aa115010654044001c0d00c0c840000c0e550354211701c02c1070303450600c060708403001d290051049402e070007000000303c1d03441503c87c80001c0354011400e070094600f00c1d051083c03150405e050408001c20044139400d070b00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 753885728 1250 753884478 753884491
    0x31b0c0d1a06040b0a0b07031205040303020c0f190f1a091b0f0a03060902030c0603070507050c09160c080f0d0c08070201050f010915081504020312071a060f0406030803 74
    0x7810030341d9840c01040103550400302d04c20b4010303210a2041c094900715000a00182c0d000341842400299543d0058045450440d030540001e54082119a2100c80901c06260070600410003040c181c040300000c0e0711002c4040f0001080c80c0341d2000401e04003c14041820070034100d4442d84401454400002503e46580e089004c00d81010092030030054170303040b550000401805048450141d0031171351400018040b12400340ea00d88210302441c00381e42d035800c0055215030f284e55a0a91580c0e043e1900d0362410300740d510301d1441600400c1c10024440401c4d11f0130801d801013450f0001400030035052115451003071450a042401000440000d070100a030000745e11140150f03180e8096035103107001242203d0090f617030024945124001002901101d401055945680318242c809403582c0300f41175484c10f200c09161f442031445540030401586024401c1d00108020100014038000407503403068078001028940c00c0044075045d010a25684a403100424070400c0513204100302a143e0500b0305241e04100c610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 753886978 1250 753885728 753885773
    0x20a030c080f0d140c0313034b0c0321090b12180102090301050109050a0e030f0738040b011a090402030901090b1003170c031b0c0d 58
    0x80840c030820025140e040c40c071442d610480d44041303009401441d6405000804860700c0240060040c60803615003140003107120391401d101402440c0406075899500402c00655950140822100342c0030754412144030180108100790054224500286200c21039080a0202038101403920f00c0703e9003103507501000700130075200d403000c19035540308514540c8039581a0321012003d80001c1216507404c41516035030b81403450700140c18208420702203401c41c0d0f0b09901ca440c0c1541c54070244021141203114000181d90444051490b01c50008550280c501c61420700610b2580040310714680c54004050000c0b48005000e500c0e05805454101c1c00e000c80700954040c0d4100b82440b00006211904c501c0301c80d1032103683e96200d41000000410031000390001410354680d5521010303481c0c000380010f4101c80c401c21500d1501c0c007049042d824034440007058049441e0703516104211b992141c140001c10740d01c82070032400518541818240c031450600c0c917a41c07440380e017140c0103409460810100c00444424007404950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 753888228 1250 753886978 753886993
    0xf030809011706030a14031e09120a050601060e0d06090f20010207030f060212010f030c0b03060a05040f0902090c0c06100b0703120b0d0605162a030c020a030c08 71
    0x21290018003d80359154164001216000080c0380302c0078a40c5205182d1051320305008800d121381c242c0940c28815040c3d5440d00140c00d02c250b107031007010810084000c000510300010550b8a2a544a1041c0541401d1104a542c2c40029075290f216003004d01e0f51101c403e0020700c0701ca2401c440c0381021510200e5058052a00692000002c03981e000129841640200759651440d1120440090603c0c0300360782ca66002c00c001c0071805000c400c401c0c0240041c40100e13840c01c0c40c501300b44540401ca03400000e181003040083c404155250f0b400d607801c1e00e0046400143d21004203810300024642c84500941158030074003000108402d6401a00d14202600300760b551543c0e41ca040803401f00300c40c1c015511100d0091080c480030900c90381c030031801c604449100207100340841c000107220405142048500c00d8a44041205880740119888498007440c10450b010703c010f90340c5410034041484030464003541060030401454407031072142800c1500a451502542e8a81c1000c00300d005640c0103225640c0f02e03084 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 753889478 1250 753888228 753888257
    0x9080406050d05090d0909020a09050d0b0402030609030c1b0316061d0301410907210c03080307020115080d0305091c08070c05010c0806093108040f03080901 69
    0x5100c5c2c0c0006016551411020305001c0401d000750408860f44041200c3c0000124031510b5400040c014540074106201081c0781c107104042c58548000c056a1a9400a01482c140c074034000406407039101c0c420310a0078103041480080386c680b1808510a18031540700034030000ea0b0f40c0d000214100b016440c92189074040810300141400d0307401c08045404031030000d0851007a800c0c0c1c2d21711224229444110404161000d1149900500000707443d030020f150030101082056428207015007100e80101000c1180c1c0b4030240d160700d80c40700102c4c4009000c2c02d50010000c0c4d0300501c00c1d8030020a203110807841502c4503460300d8810f03603030780141e0090602080c0340502150300c0407000103299004185400e5902501c68103105c00712910701d00540f400c424020004420b800084003070103001c07a80385481d5980741081c5855410444001000790130544408030114500001820030b0000d40c07183c042500e4100f080001070726261000b407007a41d02400003d0b2603180040304000c450001080d03480c1007660307515040030568 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 753890728 1250 753889478 753889483
    0x1b0c2d150c02011b0203181807020127020f0409110303070c0807080102040b0f07020a2102090f06060a030b060c03120103060f0510030605190c0906090b030115080a09080406050d0509 80
    0x800e04e8400742e4818000c910001e552000b070104004006041c0c03010310355200c0203c41f0fa0a03800d50300308000d42d4485500e1051107503000031401c0e807000d0082102981d40c1854012607254142c844109000e25110040d10050002480000c50003000140403a60744070041e0134034210b241e4042c003031000d00e4092001c000404075414001c0d48d094986910341c580c540b00048803005540c0c1e01502040b0b8000580389000100403111124101e8103281d29405954031500034030402880d41002405001c80d540d902080c0619034850f03030181e402e011124140000c03d0f03280c0c040060614091064820198800082d00081120b52a03941c58122486858140311840710890070000744c40d0300721058924220300c44001c0000c10810f8100c1034125080c0b041681889850b95901d00076201030283d08030114800e40307410858ac1d070341300d40c488006010140829046505100010810080ca2621401000814000700784505443e034400c658171503205440e84d503107540d100000b6040d600504c5a9104030303807030440043c040d240003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 753891978 1250 753890728 753890771
    0x120706080f010b040501270b03040213110a050706140403210905030901031806112104020f100210140109050a1803080a060302090405011b0c2d150c0201 67
    0x854001401c1030300f170200450b040b1041c41584803401c0584044c001c0101071070354440011b04001c0c00303850b41e245480d00500600e2082640c16580c401e1900c0f481e2415000200c068602030040d80c80c00341e50721040b070304240c806043d095680052001c2100c0a01c4101074100c0211318254421080010700e44141c01e5902c6c0440d01d0559020f80780390004c102d0030540350310aa01100f88044641140e05400d0016122981240d151209140d03001d2800a1980c01010b21700020401403800e10108504525282d4041100c00d4045005540104203580b1181c056500a1040c41103441c0311800c07c02806041e00f8003927030260001c1c46024031440c40d04010562240c003e015403c080c0560880b202c4070b204440d1340407150110020b05107d16603641c1c00005c801643c0b6071f00e02e9030080c0c0c0220004121f508000c6a4010b83c0c11045550905201c40c0812100000301c0c41180444800440c3c0400d0711400300e032103007541e0814481200200f50a101084005080c011940240c030707030503095070080150111140e400310382c1541c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 753893228 1250 753891978 753891989
    0x3030405010e1203011214061603061e14010504051008010e01120b041103160b07050c041509050a020912252114060f070e0a0f06080a0b120706080f01 66
    0x200300010701032a040341c106c072440340384903520050070303805100015410040240c54036400c203a110403a1301d40803503040c006c1c000a0400000343e5040c010001c010284016003510403003041002004040d49603a0044007030b0b4004001c06045a100795000240007003021038240200440d81c076200001103880c0d4090b040850250754440b008280c0d6480d0b5843c1e0312049260010595454807445005404943e6250000320040249041003501d5170007519080e8141000300d40254001c130302d01900d001d4440d200540000c111019241c00248039282d24200002034814216125000381d2915011000071000046018103960b982c0714150050004220252140c046803158060314244c00003103400145441c40c0300707035800e1300c1000ca01c9043ea0f844c1185904200c0d08550f0008118446810061146d8020400b115000b008031102c3c0102c1d42000452402c0270b1071801041c080010f500d000440b640313041c0d072105803102401400c0840120740700841d2952618a8021400001d1a460114556107032001c1068107849 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 753894478 1250 753893228 753893263
    0x6100e04080304060e10020c070504020c12250f020102010c0c1101032c070f0801020c0a11041e02180a030209041e1b1a161b1703030405010e 62
    0x1100d5403600045600007420035221141c1e11514000800001c008016080d0381000c00076803a01d8155083e50305104859110601480c0104a4101c04105c0070405504046552201d15111600130024205180da40c01052070138261961500ac1400f0400b20440c48591003640203205608200c4000c466400c035241005280451004141c2d0445d0b00942203c1401400032080f08564402c080c8050790910701008142820703081404103001506100381040050309150b4025858682015440f603580c16039008064a00c0c890700002d1600c5a507030703070402c01100e409010a00c0b10590440e40c484025031000c110344c041d0030f14100c000030080c2000d5541c401102e40090840b800707030781c40d030326840c110048402c5643c410001c00c29407600054650b488845101c8015000c0c4510795007400c0031040b122598041034003494100303100b001240c040c80d1201c3c1d810b50754000c01001c185801d9400304098401d09400007280e90540c080391070681344001001c4d602c1280188028808220307032041003621440c0303580210001e003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 753895728 1250 753894478 753894481
    0xd060801021c0203070c021504061103040f0b090f1915031419150e271b01030f020403082502010f0f050d06030b040b0a06060c0314070c06080906100e 66
    0x6600a40c007450780040142811421282d887d0f000a82c802416001c2218050022400b4006298051031540c18464120019481c0508048420b281c03000148581400c415001035080e02c280c07100344942c440c075000a0000704200070240706414600141e030207204461080c192503140b890b07102c0e004030b0b030342000745500e441410344032071301c005140c0600381960a1080713880e00f08648103442c1124014009000703020007140760b401c09040d1751a200c01082c1e8a0b10100880380200491441d001c01c10003120520384003c100368180b143c0c01038018005204080022910104002003403050540c002c1056802a41d03407801c040c01d140f080c04041c00d44811000c1c0c00518407504221f030b600e0241c801c006040307220b42030a500b441c00640c00a002d88000f50022540c0d007850b08207120811081215103078010b0803904003444100d04140000f001e0222403a030182c01c0001a00e40842d10007901c40032a404160041800450992195005050a0401d45215102d841440002001403420a05d07120540c0c00b83c0c80030305000e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 753896978 1250 753895728 753895777
    0x301050c07060b06220f06080f07030510030510020409061a1e0405030712050f01050f06010c02060c161a0304050a0807020f0d210e1807120e01020d06080102 69
    0x40107400180d41e000301c810080810f4809441d026000e507505c2d08500038420324100f030203d10b00c0354216401201441724140601c400040c0c4102e0240d4059802d10f000074407075130b402200c190004000d40c0b025080b80142100d514010310300d60010400c1e501c04510620840b070b6507020012001d002c108060b10b6548003804400c0102100c0c1a824644000a03401181455202c0d030000341004400d901c01c8040c1c4180e00d242008000c4e0900450421002800007008646071001180c0c0392208010311003410010069090710440d510401991250951642165000140c1c0c859000c898680d03401500c12130403040c1e00700b029980401003280c1c403d681c090003401d180041940c0d081c6041c0c01508080381e01c0101420751b00ca0340e0f11000781500e9154055410350070722000301400f201400010540034410884000c2401551b512945c0342d42e0b800c5100f00a030306d40c03555102c5000702c4545104c80c0100710507605060f1030038502c43d0150050107610300142402c00c4402d1b0b0750a5805d08030303ca403006104402000e82c00c060705 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 753898228 1250 753896978 753896981
    0x3070302090d050d030c030f09020a0311130513050c030a03140f0418050709080f190804030c121505060d170906070818040c020a0f0201030624030b0301050c0706 71
    0x4200101400e1214030b0512641c40f903060100b22100000020713921218214141e52501600b00142401c060401c41009c003500403604089036400041c062889040100c0c58681f5410801e513000303075008004014a0918049207803003c0c0392424151101c0c4202d16a5410380d02e00840c07809030095050312001442050740c005078546400509008d4404442407000181400e0840000c2c0ca40400c0e17880005a1460520406032040b4565044131185034010700540d009a140040c80340d90060202e03000c1c04a504c0c071880c081800d84076a0300b0081440080d94030000308510120309a04030541700305825016900f080c000300007118002c554065104009459520205514800b850f20180916482c2458411003801040380c0c2c2d03000120440f042000095414182c141d04452240e01400441c0c05000340c00b10454029035900c0d01030005041c000c0d01d110031600310783c02944481c0080c140c4184030014a9a40626421140300030564070010904000600c207080c603040c803c0318400c00e08284043c0c1054070780d0f180c110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753899478 1250 753898228 753898237
    0x9060509091902030307080f09011206050d020114070f03020f0c04090b0103080703020f070620010905030f0f04090501120204051b04180f1b1116030210170901020306030d08060603070302 82
    0x4d8140c0000c0003001c010451a034010700b400e1542c24052a83e07a121900010301140102c0c4078210981c0c034040090015503a03224032522080e03024a402c11502038010242c4d0035510405800800c014804160001010740100300f000107403030360500f5160b00a0020b0140019140350075402004428082c0041c000510410b01130314890f03020703104030342e1000c1c117001007945021040e41003840401c1c0302131054401c03182d00e23000a400c01d2450000900c40c035401c580d01e1701e03030340d008880840b62280e5000ca604c0048502003012344005104444003404656500c060110980c4500c0740240d000d6402c201c0000da0415540c0820010502c40400307051801d86040d052000d010b013900c422400017070700d90030280d0152040740a004240101d81000348940380d0140e4010345030703e5482d03003030905903040300c0a0700c1c1c190603011504904aa0b016941401040584402203405400f40c2d01d060341700d1500c89042c003110410541c0558400c043c02d13005c41c0d07600708600ea801e8442000c1181e4560f48054100002021244a0303005403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753900728 1250 753899478 753899483
    0x1c05030a050a1809060f050d150b03030729130b070e06041208090127060309020f03100b10020a02060315010e2205010e09030d0e25090605090919 64
    0x1003102e00d03e07800e042d0746501c1e565402004465110101403100030201400d01d402003500310f4041c1c3d20a003065860b5918040d81c0015011030341d039600d8403240951014400c441c03a195101041140005c0f61424170500c0c0c90250803a10030900c040800202813105480b1240b52041d00140729084c80da4411000300c0e52045800d0036141c000c04180800101c003182c0300381289620f88903a1446031280050300c001481d000280320f2038800f1902c01c0c00641c00d1078080d9600e8a0a843c0e45140104541c8000d0020491120034100b8031038240c8030313807020035185501c0c0b80d12080c1c1410f0300b1641a030710110f441808036a00c0030300400c003039030001c420070200c3d807030a20400b0748940c611410305103212070b200c41100064222000300400c400344401c0121040c440043c500c606405030003407403800c40c01410041d00e8180e490061400784140d1940c0d903c0b405030200000c000c1e28142003060360300ca800000007009503503400480707171040e504518105400860302e45031003212a80306145440040c08080b110794980c800d494100c071401e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753901978 1250 753900728 753900737
    0xf020a230d090305010f060617040c0f09020307031407020c010c06060504020f0c0d0306060804061d0106140f090c0f0f0f1317061b0a030f1a1c05030a050a 68
    0x69a52a02003400145a19107035515040c007510310703509101e802d50303541c1000351181500c1c0c20001d11070b0b06d421040000310100346540108082c0d0f51854003500c14012a0001d440801408000140e000030640040d841040580c2e4284404000140b00292441d02602c002000d81c115440c2c80718954810707004c9848143c00707401c0104102d96103401042c100c2e030003400164844c10700011400600f90381080010354185641c40e003000a245484001802250040c20040140c0e40300d0011903440242803035078004540000d0000c01c182940e0b01d440740100803408642c01d00032303030003020198058a40313030112500c02c49007040500d01c1c100c0020441c0090758400703000d200300b0302018404141c020f001003000c2c0c607011054107c40e00080c0d0400b2000a40039005100180150340000c0410000d40b144004490040e0880b203074040d22460300d01d00075005800c0241c003a2a1551401c1181080c0c0c811501401b400300406a0f01a100b03840e07000080c43c0b81c820132040190250f0f10400010100601c644001e2004800d140751 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753903228 1250 753901978 753902033
    0x412051606050d0902040f150f0b0a0e061602040606080618010b091014070b04020f270723030708070203070c0e13081306020715080402191706070e010f020a 69
    0x2651030840b000090988c034440091074061200c148080e40100140c621901c1150401c100f609001702400794900c4024001c160128a240407030381c0302e01c148101554002c1c0244011900c1d83c0c0010104102101c1c501d2180403224661030003e668a000d1a040c0c4000c00c058510b042c01030801d12014540b6059140c0400a0350030180600701440000b03882c280388505601c1c4624101401003100f8524416249c910940302c500c030840a99180104061294140900241c1c090303903250010354002e000c815441083d4141c5461aa00a00da0280114842c01c3c15807151b40701c0d510355010882c0d480c0140780780101024003c000501131000e800304915800724071400c04040e0440507036580e8140360840e01b070002d02c02003005810710a103901403040c0005008004201590b9080103807000b051902c005e400640140701c0300000030034134414a10402d000e403a4110305007500e6071024034056030f01c00c0211800f1002915002c80030003070f5807141c840700e090200f0b550b0045c101c0000e651613045100c0300c1460f00074281d403c21075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753904478 1250 753903228 753903251
    0x1e1803023309010510050109050d021221030f0a090c0306110d1a09010b031e04020301090807150e0d05030106030c020a05070f06030f09020d15020706020412051606050d090204 77
    0x302828880c2c0341420004c00c075402c2c10782010702081c60315003080b03041c800007400074405a01c3d003000c50000c0c02d0b011108020341c0514050101c2c00d0501400d02e0003581a281c0c0d0325051043d02c21401180511075006101c21656141e10111040f500044401045101d507010200b001c9207a070707000503c0506a5214051030701d18842d85071021689030a001d00140060f101c03a500603450200c0c049401002c003c100c1d05c5c590b140010b83c3d01c084403403019109914034400c402050640d2000d6214945032039101141c10741c1c440755030410580d024190400581c9407801d000f410300580b080807492401510f00c9464481c00c50b400c00350706802511008618904500c5800c00b40004200204801d40082401c1c01400c3c0c0c0050500c000107060b02c0001214010035400c0004090058440e4420329a04581041406040440a404a1000c3c0c07050720405007059002080104024540c180e40c07003941c45c800c01c01c5503801e6610811025200800d0710680d00402e00078045258698050381001ca541e0384018400940b114800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753905728 1250 753904478 753904573
    0xc090d02060a1b0c2d06030e030d2d090210030b1810060908030903070302010c290f150102100c1b060c0f021209010f030f1e180302 58
    0x8002c0c2c82c0d89804c80320401241d03e08040d41034801c600c003100034040c0c06a501549856070321071b00c180d0781056500d000b88980d4440510540e031942000e0030b414072514090070488441d100d114900d20031003501102e20f00417854164450014880e80c050158114465074180076002001d0310449142c00c03400c84010072451000c03414845106803441c40801d1081402c0c00c2c030042682616400c5418a07510411440c1307822fa0700001c041040f01d41c24680080070440701d2a0002c50344c0300c065194840c51115071654684040500d0b046489007010310101c0b10f0660301e140e280301c1e50160f425100740c00b40c0c10254502003e004540c01124600e40c4a00b0840342880c0446030920300e0000c0302c1415079001e45c0d1341c20350843c80fa520103c08985081c0a10041c1302d04c502c403001850323071403040b0f00034103050081d0f0006903412580207030031407841d1104aa104001c0707802c41400d481070b1080c042502d0b00d561440d02e50001e8500030f858100e488200d800da40141260840140d100f450340b03610324007000843c0d52942082001407400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753906978 1250 753905728 753905777
    0x71e0c090c18050a0503100507050405060a0e1f0c06050a0e0d05030114100f030b0a03140a030207050a08030706050402030a21080705070317190204080c090c090d02060a 74
    0x10b80d03640d0000309010342d100004504180c0042c1d2180c2c1d09041c00b00015500011341c0c8081900c14403000880c0e03102c3d0390043c1d84a219036848541c00c41c5022031524240303508480060b901c1c401c16280240c80f42c0b41c00b40055100b803043e964460119444800201c040341c02640090f910601d4043c00284401103041401d14182411881000240e400401031000300404030110880d10f0080c0da150104440c01c01c0040c0c18074003510f002c003041540c1d41a006146690315401030000b90340000c41d080d041c51041d03003a90749030300da6480198003501c621400040c00d420300300d02910485e20399002031410020705d5650f020140c203002d4400e0b0390503c1090030702c101144440002e07000003641c0501403c030f01e03008294040c10202000b441c4600b800002c0c00b844d00032030b4200302c0b03407410740301c00200074003003590340c40c07859842104d024041450462000c2008104030708009645071240000f1070321101c1ca0b55507500d100c5c0245c890310207929002802d803003e000050800710080c0011002c00d0810b4500d5100c900404c0744094403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753908228 1250 753906978 753907001
    0x507270f171b01023004092c030d200c0105070f14070b0c070f0506060a08160b070c0b0a020703110103140403050a0201020f190e0303071e0c09 63
    0x4048854286075142000100040c48509162014050710b41d40041c0d200d018840c103091101c507401c240c0d0300300208078618500620b000700058a449945030203440000709000540d844020541040fa45440980301e80100c0c48288014025460040410312000151200380300380000304440d03451040d5650700e81c20190032075003800c0d40001031071315110307600401041d07140350800b0911884508207180b0410060450755031329041400ca07244c0e61201090170300705115041e000380118041010070010010007041041c040d000840da2091041d032902400ca440c0c18907921031050800e070b052400c000c0c0d200d261010b041900c1c044c00342042c0160307490a0710155a800200c4040050700803120900401000703202c10b245a46007803030f04000a040a60031004120703400740018050110105000c03c00b14400d40484400c0d560288503991140c442d400c1440381c0b01000b092510200e181800003a0345070800100760b400e2903811880a401040840b80400720607030031000180d6030094110b03808281901c41d4040e40200c0807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753909478 1250 753908228 753908249
    0x60411091f1803081e0408030703020f0c0a05130c0302130306060504060b0f0702041d2e05041a09010f020705030a08010503070b09060f04030209090d0908010507270f 73
    0xa4004100402000b101c00040e50780c403507803803818001304400340c0940d41d00054140620790b41103080744a401c06800350341d1000710584070009100040603804103940c540c1d489280f040791220300b20070080241d1740303060380900d9401611980074001a6100703604030712030403107a5080051404034452582c0700031060980055600eaa11a1130070402410640b0601c001091602209402c00c0e407a80f03402d44452144940c003030302c07507078440c00203103040c130785031015030411090b06401c45440c0c540070b2030b2084840a40c0012081000408480b841c0540124025240f00725800300d00840d500c00e460302480030701c0201402100e150b640c0c0d074040c110600418030041c2400c5000300000c45d1241c00303014008103407940c142c0050740070340c101100406c48100210140d0394034802c01c131401c64840000241b9a4024041d81d80b001e58055808002d0140c0040085880904041d26540304403105032582600d0303003a21001c1c5c2d00400083c02000070243e05031445220081007810707000c42c43c0c04031940e802c0da1500c0320781c1c0354201c0464032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753910728 1250 753909478 753909529
    0x601060e060310030b06040b040615020106140d140708120306041d07260a24020a140306040e15060301060501031401050d151415010c0b06041109 64
    0x1290864685040356600311200342c50b5241510203601d0341a041e210082c02143e03075802245542d030b595004081c10000180080140300c0d551f02c06d040729015000c046502551800d0000305d002032032141c0003482040042d00e500da85000707030b9440d40b88600d201c0200c120305014003a4049030099003444254402c0d18617034038480e00ea042810411044036030f420440e56403505484458a280400800c1d036034203d951b8450401c1196120001030f01408407003800c211854024042100100022242e9070401c40030306d101c0481c408000c04016408a10900c500f000100d080d01445904079480300300115401f074806000418041000310a15161529080a0700005107c034020454141000d11030745008000c02d10b024000003251201d0b14000000600499000b908801c05401c280007a10082490403940d14608000810400e403000511070019204a8004031208007540d8696210707964880485800c240c0018481d2140b80802000300710800166102c90300600441c00d1984e110304203103d00c14074400616404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753911978 1250 753910728 753910739
    0x12020c0117060306071407050102160b07090e160c2f04140c07020105070b130308010e090312070207120c15020102030f011404065f0f10020601 63
    0x60301d0404440d070501110480400c40640e40005580b41c0000c002d05111100c0604251035082d94414820050003c1d8000624000034a03040a20302c035440c2d004146580e43d503110f0315001c03a1a1500c62080030640c0e40d07100701088107a00c02d0014025111074a0910146c000d406944803180018140000e01d50040c540b01c10807041d101c01c81c400c816080085400300001c200389070802c4100b0f2800780c0061a446000702e60b503421a401a4100c81c48103400c00862400e52810311601102000300c4030044000503864000000c0f0b880c14250004e010f00c454101442c1031001d0b110310f1002c04071000300a8021440b0309a40010701ea4404a0310383c4942d03000782d4030102d10a0610010504546410100c5011603204204100e0041d18001c00e00b03055500310f89161a0103101e00740000c0281000d500914400d90080b102d001c0d048032617680c01c008080e40c0c0a10a8441d10400c0010155220040d00303501c406080d009204011000003102e01c8603001e4000c3c07840352501c40c540007044010010005000141c0d00400042c001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753913228 1250 753911978 753911987
    0x70c02041b030b09090706143a0c05040311040f1d06130c0b0703140d05150a0b0d150905091612120503072c1311040e06060712020c01 59
    0x8903010a9a6020090403d00c1c1704950303540540c440c102c01c10410100000780385400c07004892800c9800c03420001c0b011605070304100c214007240c2c1c1c1a9074000001d80b8140071901700d4047c0b2514149161038607414240355441d54407419001a400c680e101c0d035100c11082c0b054082b071081400001603035503129541c0c00e0b002045842c000c0003074440a0b507110441103400004142c089030800f03454800d601a071300ea00b00d80c503042c3e034010301c680340044450300c01003903800482c41d059001920a03130f00070030407043d0803611b0004d005404c4070314000d0751200c002c10455240b07120125000b40e009030002044070385c00c243d650820f0200315034003650405025080300d6000e248001240411401525101d200100d21101c2582c1e4080c5a14030704200d0020300c00040300050320640101080750560348000040c141c0303041a94000d01034039213a010014800e60381c5141c2102e200351180302d089091500c2d11212440c0c5070502010101c810710051090703a010100b0000e07040016001c0d81e44003c1c0f000c40790010481209020009007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753914478 1250 753913228 753913241
    0x409060c02121216110a050109020f041506030b030a080706050103020406440109110324011a09030a0602040801061203170a24030b01060207030c030605070c02041b03 73
    0x80818200303101c00380c503402035401c83c20b800c100629501444d003024158151440103081007601098010b40101c00d05000d0190410b415031482100e00720020a001d50404c01101d0108984555468282d84240040c600035440512001c2c4000d04440c00d003001c603900c400065020441c02c4507550380f0346004200318245806904040d045003814803a035421101c45418100340e41e060103060385031105600d2449454144100c80c04c005e02c4200074080c0e14500c0c00d08440940071000c3c243d011303200d8181c4982c200b41c0095070402001c000d2011000e1164607080c4030b0a900800c80804a01e40b800c100100070072980c00304010b03441c1512031800562210700d030520300c03421240290320420051138102e00e04800281d1002d0080c200d000300c00055440ca848402e803441c0281174044074400b90801c42a12108141c00c584c81c100d00701c9102c3c000c10709050ba2500400ca849501e5840000c05607448114240006205900120390009240c9040000c00c0003540002e0151417014945003010688100d10000c203607031501405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753915728 1250 753914478 753914503
    0x3030b0405060f2202070c08030c0d09080c1513060c050d02070b1c060504021804050108010905030906071506060917010606051c0b060a0807021b0d06050601020c0409060c02 76
    0xd0b034102c0720603c00719607074031651500c8a18900d09081305600c01000d80d4155644540c00081a03003d2584403d40380341e50750710100720100b50303120300c65410b80481d121300902410b9039650005849180001014000540e00d51030542503000ca0600104d800c1d00c0c0610a0b84000341030380d9480440c00e48550030b0850400c0010114842190050f4209100080e010011140c4050310741405481d09a41002210014a8140c0001e54414000a10840d02d410114036418000c60700711030400050341c0e036101e03007030880e444d0250041c4150003e100b009641c0c5042e002810046004842c44807541c00070702c441c54222a01500510081400d012061144000350000c440c6540340751002084240c1c142000540540180034070014038805012003010345214680014101c0e88002d80030588a44c45204098000c4208441102c018481c00d28005000440541024001c4d8005440d0303880349052030f1030324406402c0013851207055100b030801c07602403501c2d148901d4000c58054440021284440c9500a04200390300100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753916978 1250 753915728 753915739
    0x21c05010501090e2202131a012c01080910060305100516120b040e060408090f1c080702040e060906010305120f16170711031005040305090d030e0d03030b040506 71
    0x800251760800c5c01200b00d91131038075440700b0600c0707280e10015022030350090074031003240d0800e0300c0142c4002d822020034001000c241c0707d85141e0100c00c5114824000c40c040003010300b8025500f100401d50042d41066009000b51090b170b9041e550303e901100607034025a004541e1680444d40300c1c12207551034822103030841071128003264041000040202001c40350113107203480f160b8903964110540e6035940304002c0c41c1071800680b0000d280c10300b0b00501940040c00c00c640188460480311107940b8043c09401110b4410100400350340140f45c64601e001d0b08642c00498125030b0b0388642401408080010300e216058950041078598110310b405420f0142c2c0301071180f05070300103000001052340d007101070310303018100c5c07110311501c001c503500b0f10306d80c6a42103290000421000107100402c1c428401c04490120f4803d40854500c0f01002c2c104c1c408494049402400084c402d00c8070754074038500100c405001601a1404d02080604d40c00000d100340f65451040b8040b81d91032001c9a004e081500406a01107400c50340c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753918228 1250 753916978 753916981
    0x211e02090403020d2d122403050106050612011a070804080f0d21020310090c0f0f09050f060901020c03031c0b061201030b07050f0f0d050a1a04090501021c05010501090e 74
    0x81c00025042c41c0148000e02200039603040404140da80032141d03180714016071f4501451010a0218941e005010a0341d4950030508041118101101120045025000002150380c607110241d04408400548115904002c000200210304650080c01c0901100c0e0050001550403000580c41c20144000181c180980e01c90272101c00c45081101d1490410312610243e07490755241e41d00d2250203855004071100d6841c280311382da1300c69030042c4103540c020032075203400003407820fa03a2013540d40c3e200505c589507010404c80b60411040c01c200b000703401c00f0007041c011034104820000009086400101c09075010821800010700101590300500b0761141d025205586425620030707400040705014000940112044d401041480e071059044601d0000c0409840c5d40342c802052000c1e401c0d61100300e62504840c1080041502d08200d40b042400242d043c210340c4204020220a0202402460030180d070742d551309211180e4201c0d51300c402d041c182100b0550000d181e42c105000074220655a80140100024031130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753919478 1250 753918228 753918287
    0xb0108090f0715120501060f020f0609122107050c0c0a0305150403110a0f0b060609010f030509030409060e01150c03020d030b0607020402120709211e02090403020d 72
    0x80c80d0701c03e0b0b03074030f001d0b006140c02c11800c001d51382d158212014000e1203142500015019903c55803a810001041d42620102c0f011181c0042d61a0400c0d41c0003002c641040407031708501c4082c40020400c0c0303400c0391404039580142403520041c80c10304842c00d00204500041424403810107204e0440032000c102c41e0f503807080c0e08680390195290300146045010080000104050600410f1fa41e03000e048600308a59a0610903d032000000c0d07040c100448480d101070b40407803218034065050710030040c1c0c181d4503031080001e220000c50251074060058081400100804601d01c03c1740d0280c503010b4030030a4542180395241011408115401ca003401302080368400503800020b50209072031b414414940303004a07003041080006041d40c454040000d6000d40300242c002d82c100c00507a2050721505c8552a8544500d648084d49000c01c013940300c40c40070f15808040c42300d00142002d100c1c500d680d4404141c1600c90340701580410034144054a040c0c000d071740802005031005910002c001601c10401c0001d2040c2440c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753920728 1250 753919478 753919483
    0xa0908131e03030c021201180f020913032c03240c16080c010605060c0f070803090109170106030501062d030f12110d0c0c05150316020c0a090b0108090f 67
    0x508000f0b2207401001e5a81c040c1100035040f02380c0340348460400c61881002850000900d0140d2402280940c0603040003454144a809803128030035055100d00c100c2000e412842809802035504011200003400d680299588080204030004200200110303000c40d400c2080300f655035030042c9600c00c0640d0400a4126a00ca8000ca0700742e52903218040710303118aa43c0f10b640303000d403059821942c1c0040021540040c00f1100080c040f403e1040e075400e46030481c2c1c0300e40f0700c1922403040645a03400704109a00c1007000400d04c40b03d017403811444c8000000c0d01500c0b42e480c0382c29511194812004221140c0300486003e800070895082c4030a10090000e489241d90b840142c010342000d00079000c14100c1c6451443ca501600101c0918030300c00302515840c10107c50702800349a1882400d66604401410100c1e8034140a04092094020201502c0c1555542504100e41100310141103007107010f4070305408030307a40720300e030340c00014043c003400200b01d0030060b900040500703500400075007183d88000030b40346045002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753921978 1250 753920728 753920747
    0x71a090a03110106080607090509070305060319021f180902041503020f1614010b0d05071a0f040303080601030b0d20040e03030108011a0102030c0607080a0908131e0303 74
    0x10704101140b20300b0401c030140180361660002481c0c0c001c003405c001d032459004449000b03030741e03084600c1d02c500e1301c1711841202118001c42b0044d4250b840402d800000c00d030340150b0241014402800e4419495009181130000d4a2100c1e8581c00304800c218000d80c02d2220038090806405840000c5041c20301c0c100d10280891051900030091680c0000d41540100380079044505949a04195420b0750215182500100800d43c410f07052652030180d01d00c3d402c3c0350000c4000c21854000006107000e90070551050300d0316104132881000006c007003194400201c0b0b00406000114000d4694045a2034810009410b86000c401500d115109901d90315000441c40070300c02c0c00030340303d841c04a804000c100c0c0105004066480b003054a610000c400066884415001414941001c0c81e43c0b2200108034001640c4e24000ca0404124079005403001a8529216543d4030354451284a40414228403684510203244d0041071082008103c442040c0202c19109030222400030042003800c0050746140c400402e039024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753923228 1250 753921978 753921983
    0x6060f1b03031107050d030c03020a0c02061810030b0f010509010c170c0102070b190b1f03110304051c050f090d021215100e0115120917071a090a 64
    0x25261031801414400d40c4584a0040500c8580382d6070111802c029989402e4165400b00217420201240090fa06c00e00170b903082111243c5603c0078140c91682044043e801a1540c20b0400d04201500942656803010709524001c90303031400100300581c10306200329010072100345818400c04002200113661302c580d800a0045c0c204450700041803400481d01d07000e02c03611440704510f40c0003003125410310421000d4140141c0082c82c221409605c603036021802c0d5030402100e20750040141314070888034040e44d00c1110b0740c94100d24001401040c801d400074103a13007050b80c040d1280c0e0320810345003542e4a5400b00c1c1c03205440f003d017001400d00720158070380131403031080000c2e81e409044040ea10104540700c0500356001c0070101010340e04ad01c4040220b0f6441c180d0300702ca9542d0b43c03800201c0300185980d000582981604d0f002da100c2c0c1e0a4038105081a01c80c0d00081403481d2019640381400004541410b01d5030b40c804503606810360b542c03191401c0a4000c01c3e802c4002c0c4604c00084030500c20303000000103010b624187e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753924478 1250 753923228 753923267
    0x10608070612180c081b03010c0504030308040f020a0e0106020d0305090607110c03010509010b090c070f020f13060308031801060f06140f0a2105040f0209130519050106060f 76
    0x81c1c00f041d40078071240c50b058004001200145000c10040400700e1041d9000c0c82e400030a8140119100c20942643c2c0c00025220104c2c00811090021038450800c2d11351050040038802070580d202e50100d410040e503548401d01000c04000140100c65060002c0c0340711413210f01e028001800c1150340a500e5200c041c207a0350900403211754120403100c0500c61000341010040007005189403070800c0320701070021005224860b0121600148644252400382d030110f9030003031400c0301400120360034040c41c0500c078103078a48c0c806004a00d420042d01540181c4029611a031446078aa0406510540403000c449820352801d0f41091014480d19040000407005c9521031700d009001081c0d240d0820b0360521407a01880309335440010340298240d0000503031440042a001c0d2040c3c070b0241002e40c1011144181d030300405000d0002841d4025107480f101854010000b50f220188000305c65496038504050310180c26140d508104514050100a10617030000300411704100244080e24070000301650b6600d100040d412 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753925728 1250 753924478 753924491
    0x7030c1d030a02120f010501171c031e060905010609030215220303030603020a092f13060c0218091203040606030210050318030a050a0c08090603040b0108010608070612 74
    0x1076404120b08918150081c141c0f000c0700060a103680d4440000340201d81c090340c2024000520309901c803019128a80c0d09102800e01c11180c00344800844c00300302146010580c641c1760543c0002da50070544000c5034460500002d01ca844c00c3c03100b40c144c0390b050303004c00140300395098100050b88134100349081d8503c000300744a54400c5501040d42004441c601e041081b06900007000c420150940c0c441015203008030384018505941d40c0303015058480c070409c405010084290300d40381205040c0240c0300b60b002e065102c103007000d06052110181c2d904541c0300e840003c81d0031172440250b04000072800c441204400d040c004910700760040b80c1d0744a01e10342414542c42d00000010782400781d03980c4480b001d554003d04000b124440c10703500a0060f00161034804810b1034008210f0151400001298403110082d21568286074070280250ba070702c02d02080503a030f04481000348a420360b0380c4c9001148503074800c1c1c00d00380d0301e541490102400c4a0b00d68001141c1130b802101c00f07101c2c450308000141543d034102c18010494 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753926978 1250 753925728 753925787
    0x10504230a02130f030c0b0f090906130e010f150b0a080712020d0c030b01020705030622060c05071202060c03010b0d0b120606180408031b0c0307050c0907030c 70
    0x28890706810391038400803004041344008001307900e82c0889018010090859440b4610380e02c10344644a040e608280303080280c84454105100070300c0c0c0c0710600500c0c03110200412140d2405480c9000b001021596413100c4801e110300051080109152061026aa04030305055002c4002d01c21440f44400340039090380007400ba64401c441814180d40b0848066444003040c11051014080303950207800400d0a0070000811035200003012800c03100014014412a15400310988554181402c00050290388144680c0030400c2400b542c18560156542d1550300c1016003401204409510310b20320854200000f40040b44800e0802c0d07038103664070f0744a12503880da40c07030300200004c203d507181b580d4200c40e412280c10b41210010446620a510540304800b100c0b512070800c0400b1502100c0082c00b011061020455500c0080c01ca04410420540c5480c80c000035244401d18640007400201c40300d03804400c12486500f09194180d400a59030300f01440721b480101005801c00174000c241034101101c0d81007480700c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753928228 1250 753926978 753926981
    0xf090b0913110d090605040308010b030412030e0c0904140c1807140c19030e04060308030a1d1509160e04060e030f0d0e1b1008060406210b010504230a 66
    0xc00030380d81c583c02c20104550380340c4040a080e04507025400300c4e01600c00041c0302d02605003201d108aa20140c640004002c400c0305030003c000c2040d25440c0b0740704190903c101510380300c5c051801b4a01a0001500c00b8407007600c01464030703400c001e201c0c1c050318621848010099158207007540208085c141031461380507420440056010318042d00010b403003280048090742041a004189960081c0e440d5041139084005002c103440c91803100800304082000020034028107507210382d00c12003284c0080442680c0c844007c6181c2102e842c041d141d2840c40c50207101c03d0083c2001780550521030344442000041c64851081d991000040001d404140c81d0105108408028401c5940c0107040e00102c58641d038298208000404080300305480900c107513000f001d000b61000d070101003c03080041c4080302c030400d1114110703042e24002e054660026140c000120745500d42c5010074520040030391844000d1807030342c20503405008060f071045000b035241030344c04204210170a85152801c05407c2d4404c2c0940c072170350721300b10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753929478 1250 753928228 753928237
    0x91c1a0403020a1a0703050705040f0920030106050414030705011b0311120c010b0f2d03010c0c0204050a0b0307090c020c0a151103090612130506070f090b091311 71
    0x81001d01d0384c5550302248041201c02e540126600d64040006503103031a8140e5461150380180c41c0540c9070903030b04120130007007500034032040c44001030303d400745080b0050204041e410a03000715010541c0401c061040c001c80650440c402c0d00c080780180603444c54a07001801ea40803074080c1041200c004030801e01892f00446114000010744022a80c04003100c22090030b0641020030708003000d50a00b80c400800346850b880d009001e000c02441c08100419100185102e028280e09142a00c52010391000f8580d40c2845170705642c0c020354075015a425294410401140d0000741100081450002500001c2d140042c244c426141c072144001043d5001a00581c5840c8030192060f80c04124050301164081050704092901051034035080f61500003030b48003607140d0089120315504000b046c428404542a079410481e00302500c210920b00e2003040d078554905000c02190742300041a4038607884441030782c1c04400d41c402403005018950a00d10b0f1400050741d08007840f011110081d813034040c1204a07072444001c41e03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753930728 1250 753929478 753929483
    0x143d0c0b0a1d15010b1b10060905250f020705042a090b07021309020303160b1e04023609011b0e090a1104030503091c1a0403020a 57
    0x81a40c0350030701c056005860a5410040c030300c040002c0c030118034080040c0c45440303420350218a46983c0c2c20300d103192600382c20003c42103034001e84031401240808402d10540025071400e017404924241050300c0c280c180e0360013030301c2c0450504005002c14103803204850075041044852510a1443d10b80c01d02c100d1074034038240c100d2940103250202c4115a4400a0801c6488000001c035003881844030280680d041000351040e112003c07800c00c0000e005103000d031485129140c0198000440b03003c241c0102c2d1640c1c10054000c035494480b02c0c0c40100307203c20600d503142c4c4a03811410b07006007002600c503000c0a13490b0180000f80038600603a41d01c500000c12003051880542d134850106208648052004d24202c000c4c0ca44441a52a1420189898035404c42c1d4224114580e1503444480301c1e0350f400e2000c40c0d1002407049203416654030b86aa0044110300061000b1800b44008685402c0c00004104100054001c1c241090414010749800500340da00d5002036481c80010041d8160783d5403c0c182d0410407101c500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753931978 1250 753930728 753930743
    0xc0c05100509030c0d030c0b0405030d020423030c0d02120a08072003010b151308010c02030705060109050f061c02101115091b040b040204143d0c 64
    0x328140d5540400a01980b10089088568159070750f4203102c1e400701e0880d0050002600c0e0384102c00401c070042d52032340c0c00c144070b24100e80ca801c03241c110910407038000d600710414030100c803441c0000b4051450400129500c048010f4120612640001143c1800c0c8000003400b0709409000c445014100303010440d17103207400c281c003a6950006480d0214079002d0400f958400d8844881042c00f45007414400c8100d00079000d030040342c00c2a02e0503411142500441780184101100c0c810200d2580750030b00840744401c41c1c0e42c0003141c41e001c0318a411303403c0c04816003040d40020300d400104640c510180d20030381c0c0c010100781c654120400c0760a41040c1c9544004001035003200c5680b030340c1003200f64084184480b02489105555050030420010f510f401000d9a802015511901c21151074025900045402c4403008000203031100502012038140d030031542c004d12242c2d440e249199903070704001c5404009400120a01d8658440006140c1c8012003880030728100f0320034000d43c203034003a8090b200519065402800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753933228 1250 753931978 753931999
    0x705030c07031407060f0c0212150115020303060f04090201090b0f0d06080c090f09010608191202031e0a0905040e0d0306090c3203010905070206010506190c0c05 71
    0x301503a4612032880210341d01119440d0890b0480300c089041d40c2074030920340d00d00c5076514081da4100c4191003800d0045c0c0c0d001149800000b428802048040a80d04242810308800d42c5008607481320402030b1780c155025034000b04108007081e83c070420080c0d03a011049130000384d900c240f4001207a20025642001c100c0b8000010030329030075040d4402400c1c075100459006c0c060b00740c854049a8a81a01d0107101d0b8000381c800f400b04402c0f1140900b0140e00030311400c00000c0d41c0ea51a10202d2500c403100481c0d0504c00c02013444042841072f5400c880e445c0e50751500085107400441901c034424442041b1710010001c00206030220341c64030811010004000050040c0000550712034407039100e03c00e60307070200007003490084001101243d82c000c6e09181c403820b4440c10100000c48098101c5007020403000154002c6489803030030f42d0203000015501a18002b1000540d07403030521340203490928107800143c454541440b000081c895024685c008500791441e20944900b000e1401001503105a04295405003030201c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753934478 1250 753933228 753933247
    0x501060f0f030512070206091212040303050c10050f16020c060304030509040f0501050f090c0408150108061b07140111040914150901290703030c0f0f0f0c08070503 72
    0x4607040180e81c0100c05071007444009503885016841802e9000703410801c180f003645058034040d50580c95800d4a501a1459281d0450380c21a0942c0240c1044003c00d40c0072640c20440b52040207081d144154128042180303081c00d11801c420300c000101407161502358080024045d84c401d02c2400d20b004000f9010640b00d051510700a415034000920141c05285080303200302c2c0d800203a004282c121407020f404444000300003424007084c1c1100504269200b42c0800c00000c00d190104040301481c03200c0210005554140203801e4107124025181c1c0c0030702884140c5101d00c640e22501203030002030b4000180301400e50b120040e2405804001707101381003041c0201c1d0000710700d01e0303c0e0005e0a941e41d11494280d42a52140085600011400c11840d001886a80148412050781c000c045107440c4164080c05210000207484d05d260384190170071000203458845150b92a500003048210850035030600039950b104100005007044101f07aa0303201000345450480e41802a4041200c4190741c22a0a50380d803201000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753935728 1250 753934478 753934499
    0x3012c070806100201050c04050d211110050630060a020315030631060f090201030506030624010912060203010f080d020a0206030c12071709010608190501060f 70
    0x21141c15002c3c011090841d08018410301c00c032441031680d0329006052a08100500018402d5000203d41c0f4007500c0780c8a0310354140d60b4064084490903540e03102c46000358200e6007400d00b960110700440c02410b010a00103141d4541400010300031528003501c5c040c03000d80d01d078501d0f0000c81003000503140c010407060164244071900150b200e1655000b400e40c1501e186018155070341000c94144822302210104130000074940d101001c40c0108403011410a45440d8030b542c02110b2044070b140420f1580c0320300075011540c149c0591075128070102c0c040c11035450030660500c040c6102d01200b080c05401d001708243d0a03170107902003001030302c2eaa400154042d0601c0c542034000754001c1c05145524500c056000030f40c0c03400002d1044180301150302900c0222225801c0c054150005032110104500601070316600503210784485100c0d0385103960310480d10030407854151040002602c2d90010341d0411005001c05840001c0100b24840c01c07505503610346101d0f0070410300500c1113030012100a040c10720000382c0f40220 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753936978 1250 753935728 753935731
    0xb160611121006020f12130510020f0709020307081f080a050115050604030201020304140402041a031501080115080405010906180b010801200d0902100f0908070b03012c0708 76
    0xc05888481c0243c8900f800e0b030365204c0e046a12209a071101200c216044c0c501e50143c400c0030803003c001e04645881c2c900040513840621144c000503401401041074800341006090b004080c611011440c1d42000440100445d030020203003404030031040c1060b188031668944882c000c0100c4400d403600440c0c1d601e4240e000c1c1500e0700107400d0000c1c0000022a15141200407642200d5058001314681072510346041c0c2855000c00295901c254240301c002286184080c400d403891b205100065070300d00d410251907100d081c41840303036410003582100603c0003003121650440300240342d09264642ea940c6160031809041c10410041880313081004052000240ca078040900500c5815219082da8075204002c0c00c0b903240081201156120140c21102c00d03c8203001018001030141e801b05010b451500482c111880e500780850000e041100842000b5500590b00c1c4060700301c0c0c2002d4a092881d01c0380394103003800107008200e04d0491803003080c0642000300b10303010b1300021101640e0300c1521748218040e140510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753938228 1250 753936978 753936991
    0x5271003020f090601020a0b09010603080a0503090d230c030706060b090109060305060105073018090902030a0602030601120f14070f09060e0a091103090f06010b16061112 75
    0x12070002d42c92858002d150520038901a40101504c3c000c585941c81d00d01d4000d40200780c29541e551020000c82c01400051107206100e854043d27403803c00342040c40c90300c502c02103110f0811006440403140c1001da031160300d01c1040740a111a45580c00540e07200c0c00c51040d010010501403502c44c0000701b40785110050140403100740c89140e029980c419054090300c01c200e030326034001f4004002ea030001a000301c10140440c190040030118412641c01008918600e110421010400c140c1d280c0c0c4001d1000e410a0014000441c000c1c01459a5580480e507190304000004001507004800219203900c1707020030b44180c0c0e84858003800044001d1305210300402203074900300c0c9010a072400154481d40105a40301d00002940d42c1c0e42002460039508503880c0c954180100e501400b2424005482101c1c0e000e60f10403241c64905032541c030300b0a04c9501e480c04500902101060b00500e004000810b140c2c0c0543e0240781c1c0c00450351445102d646041402000009000d0600340350120300e1344940d5060401c2640b0403503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753939478 1250 753938228 753938239
    0xf012d030606060908150c07060207021003050f1b3a090b13122a050609070e070f0e041104080d11031606110405180a150f0527100302 59
    0x64660101c0c0307491b008480d1036004501200c3c40401c0030f0a00ca9002080143d00601c001030521200d54001340c0d0410000900d0070000e5201c50a010400070b00024098010000c291000d208114113812544076000d04600781c55050303002103850701000814100584101d03080c41c01c0b041d2200139412910b0060802880903100750560400027401300e400c50510401e0640c014161136845c4200d0f0b9012030300d0141403000c0c0c5c1c41e2003c40d50071501030841154155400244242c000d051646481640d030340c0382c50400e074402c40c400148002488120794018641c040700048a1501c0810605000c01140c0a480e443c444048101c0000600081521001c20981c28121547c4c0d10442810080c0340d4203581c0e401659110580c2001030742840000a26035400900310400022400741400e90303950009075a81030300040100c6e207501450802204503c548501c80c0d0b08076031200002d4649003089400c0c1540c4500e406803a0240c00c2e103140c4040d52200710640c00c18507000d0501f100406140c4a581c0c43c211035180d200132401703103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753940728 1250 753939478 753939497
    0x6020d030c020d1403040615080705010e061305090c121602190209060409030c02060d0b130507020c0d0501021902100c0302161112030d0203071101050f012d03060606 73
    0x150b2010407407018642041d41d410103005a0405128004e0b88084d100301c800c0c6a40b000404400070049182a0044c100398000e0200c0a20302000900408840c0702e40911031078041210304100821482d4100980d20240e03000e811954078100e4041c01c0d449006001e140304010715041000c8140180204507820340142c1c203641c42a00c603038483e44052081e2280096102a0340343c0000d00b1400d095000c00d00190203880c01c05652111138002c9065980614420310505480e00e001040b40d0034000c1c6842038007410711000b0816440c1180d8000d446203061811584100c01c04001d00003070040035015202107205820300e008460748040d0010b50f8401031603401c501803605003459000708500910907190300202a100300c40c5149015601d400c05103103210600b82c1d1002c60f8880908444070100064000060500401a6242007850000e040c00d2121903080c40310341c1c1004100600e0803000003507a41192901c5004d4090f085802040c06140c1000c112001d484e243c90342e200009021154101d18111142d035100e60203103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753941978 1250 753940728 753940751
    0x402100f12050712090c05030c010513360b1302130e0603070305030307172d090705030a080405150325050d0c0806090702011a0d0c080706020d03 64
    0x62800280c0d054000c038401214922076100140c2041c1d40c0034000b40707811a1101003a610700d00c01c603003031104159252070104c441401031b07007400c01c400351151000b428640c1c104460700030b02014040e000c0c09115004401500a03902e01c1e00c40b8110f0311400c84400c500540b050300104000d00c000d05000b000b0a101c0c1103101c03403043d4800380501c02c80d201080074400407c5002d09080c40c08150602c00b8048540601c0360002c0000030031030501c050350248913565213000d0a09031111004507114009006643c0c2e03428682d00c14142101010131704c0c40500841c140018283c0d4400d014581440b4065102d107415002c4c01d501e0400704032174040100f0070744004a03200c5001401c4280317110319038001240e1300d0003555610302840000304015118200002003510f0311601c0c142d500c4003020213031070a043c40030010030001700622041e8a00451441d9020303c051000f0489010b40d4600043c520004001c1e031406440861881824401c03580211000341c81c1110803107a0307a82d640d107002980d8411886422001a1810582141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753943228 1250 753941978 753941987
    0x60604061703071121030a02070519060804020a0506031801110c0a030503091f061805070e0f0303040b04031a01080c09010303120e06010801020d0b04020f0421080c06040210 76
    0x10300580100950a0000c3c50b9107006500104000b0720754403082c44000c469400c8041e01c0b00b0359402ea1a00d028646030b1040e503c000e49420642c8e00618441c44000c2c030401040c8140c010791008894192030000b1030b9490300c0c000b0030b181006582025400c20000803c000c1c040c2c5e0203905205510300420001c100750300d12541402c2150207285070010094001c00301c4034003c684140d000d942c000d03095105407200388001142101d420301041c00b01d01c040d82c4d10350008000002e000c24102c10342410300d4406200074a05482c1c01450407402d4a6858440c451302804a603643d1420819107001d0310048070350707a0b95103880b400d001c124801da281805c0c050300701c000c0010810110120320b040f0075100c00b900c01c81c0c80d6421940c081d00e0190f2407419102d4525640d845000701508208007047c000c080c0c010005035118038144500c01a5454510b00c41d000c2c500410080001050001c102c80c00ca400076101c900c0e542c80b148142140c60180390b02c1c040e0504401191a00c0034060102d4281e010f20300c200d610600b034581c5918280d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753944478 1250 753943228 753943259
    0x1503140706090305061518090a02090601020607081f0b030a0207140a080d091119050a06050c0c1011030721030513020409111309053f0409050906060406 67
    0x903c0340d00a1790100300c0c0700d02903000c042d210385001001140150529050a40048412240b00000303501000c064415402d1002c60b00f6001002840901004c0c54005070241c05e0640150000c2c07800752801465060121401030301402a1258481d8156603040c480ea2030f4020f5002071070240c2c0d580255a486103038410000498012455010b41003a040134843d482200c0101803c9405440e501000209900113546615036a600d000070b84c03a00840c000d00344000d0140207250740d003140c800d1000c100540301e18004000b480d1418007a00b03d5400c0000508401c08444004520041c541d480c4800f0800004003c440e503000800d00f58528694002c030100c001c004c4065a405550350101001e58031076107000341c2031540107002c2c0d1074099541045c0b010380715004507103054030b5591a4010383d640c4190001c2000820311044a0980d0403004035209140c00a08a60855041c1a04149240d410140b0b00c0c500304c040c103060300c6c010b200200080055292201505495842c21143d0394840c602d04500428000c0e0b4003503111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753945728 1250 753944478 753944483
    0xc070f0f080304050d061a0a0305030c01050906130803040203030d060b0c10050105060d15030b011508060a050105032a040b091810230d050a050d1110020a0315031407060903 76
    0x44003004280c840d80d0003442d02c0d10465000351007c950200407600c0303a4448100070361040000719683c0c01c80c0c1c050f81d400c540c8060110010350301710a040c09280d0649a01c00c00007145c000c1043c0382d4a0b01e541c4006450340c071a08040505580c01e001c07000400d044c01c00c0142c00c030030341c000c015180e51740402e204580446200740500d517801503060007800c0c1c42e140e0700c0c1e20400c0c40038a07080000001940701e440e4540208400d9000d2964820f454050690301c4da070002e03803a03803c84420382d00310a00302c0c20000060454000101002c02150307000c05041e51020542043d0f1090080f6524035540d80d03a01c0e48e108060a510070200140290000c003a050320042d10340890360321854030078200760040c90900b00c00b000100300703121101400c0c2c550780d440f1a600755212001c9030855445a0000c1c02c100910349012800e101d01130a01c20180305000d90414103140001c180c040d10600038410044c2e03150101d44080c0c0041614030a560385070250045c0101c10000c08900b0341e403503401c0307582c200c0d901c55a40305402c803010305017030200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753946978 1250 753945728 753945739
    0x80106051204050f0f03030a0f0203190b0a230909160b220f03050c030d050703030903140a031a0307050109170114190506010c05060402150c070f0f08030405 69
    0x5004400074006281c80e0018403c0d0141c0d0211081d000105261480d20400192250800014425040303280d110702c041d0900038510035410b5103070140118181000a40504400b581c07a800c6811003a40d0302e86000b40039218840700d03c015281c1030803446044080030040c03940201031302e40104800c00400120781c0b016107008106066090300f000c05c501c1d5250003001d65842d0000700b640ba41c03041c016180a4883c050099140550f0001d49141440d620b07050b5040b072128069004007210000e00d50b845411141d0303264050402140080091804070798041010700003c0d414600400d0080e8500e034142c0106014161620b00740c002e9450080c101511440c0500c2118003040100c4c10400c482e0070003c440230000014080000b9044803420b400d0700d41804202ea231800300141e0007006d0805113549110700d9802160a180402032040903a503019510b60000e000a031080b11200d0720903056460a00c1220100d0541c2c41c20780340c90a60740c11540b908548240030300700082d038150001040a480002c16142150402041c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753948228 1250 753946978 753946987
    0x909060a03020d020f03010e2e0b010504211e02040c020f1005150913030914090a0e010912020f01200f0f070c0b070218010b18040209040c080f0708010605 68
    0x13085817544001140c207400d9525a00005d00a07031060000c3c4001c0c44440081c401e69205a840070408525601c180000945c81e0410815459900c01d00b901c042d904032005600703151908105a20490101000c02440c21400401151988070b074500a08200c5209850134000c111084030140d032a00700400b15100164031240707000b42c1d80c52407900301e1500320f00312460104200c000c8502244007201c1c00c03600c3d00c002c0041c24036148105a400086c80c001015840507034000200d0800014400c020080d02d04800c2c161101090359985100394486424940c0c4a008a907000c1f02c0c21a000e074072007400000302c85581d481d042e07600c048150202c7d1580007400381230b4249443d2200440310070320140c00a1903180f40c0440c090100400041412219401800c2c07480e45940d11170313000b841040080d03032065441810722a00c11004002c4c030b02e458029980007145a580318000b819100c4d002c100240500500c040d03000c0d04000c074510311550000030150141b809044813035000d60701e00d001540c28640038403035003000850400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753949478 1250 753948228 753948233
    0x603050f070e0d1401050f0702061006080403032d06080709020711011119051b0301020c0a0602030c12010e090d110601031106280207050f0a050d0c18020909060a03020d 74
    0x1007a00383d0041c40b0322a01c82c60250106a1103003125000c03101451100743ca24140005250104902c0768402d60aa401046260421034000c0c4150806840101819107600c030b003800e1401d940e1415400c4501c1c00d011400407113490058a0042e00c070510950181780114600840d4450b1103000319840940c010320070704141d8075001c00468195180c4127a1902600503408500b0110003c9e070559503851b402800100390b084080c2c0200c1080006201c402842a071040100600781d600100c4c0d608a42030b00003600584030307500c00c3e000340160300c20000c200b40903581c00340000c40c001c203483d50403a01076010081120002c94120106950714050f840e058105980150010000511f00c071001d01450312010b004141403003040e270706c441c1c04e82600f159003d911213100464011100c0c0d0400c442c000804080790340320300e0440400c02146500441780030380e43c0103d140031807040621540034803c20041c030040d20030241c0c804407012010020741022a40b64420440c0d00d0200d0000d00e0040c60f00c5081d03940082c070301c1c0445040d43c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753950728 1250 753949478 753949489
    0x181109060c030405060a1101051602060402090403030f0213080c06120411040b130902241b0a1a0708010914061014040f03110915090a150f0603050f070e 67
    0x3a05481c0d800d00c400c101c0403a040d11103401400301000d00761620103a007000030356214256280101900d01514a803070740d0603806540000c0c0107403c03d40507180d044507501c0d00c0c1003c0b0013078144002282d0545000140a1103880c400b10b540710304a481f03e40036940d10a0440c0b042010502c2280b902000400142e004100403070348603e940d01190b14020070004007107840f4000b06501c002c020340403064030703941c440148044d07090295800002c16404456042030413121410303440e40d800381d4003290106844001801c01c01250030001000b5164200400e055001d41d4220890b601c01000c13241c090000710100000205014603019585120300408910200b03990b5407002e00a08000003030214007004100710b20103031948002c0c402000038200846031040958154140340c4840121981e44030f000c7c82e40c0701c04000c080c18001340c0c81501808104c90b4245180c03640080c2e10080c00110004400358000d200b000528640d6698840080368510340307061009a4a0341e45803110802c1c1110340401140011403d0302d42450107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753951978 1250 753950728 753950737
    0x602061f030215071101030608030a030f0b0a08030319091205031e09010e070b03040812040201090305010f0b0a14011e0c08040e040212030403030e190810050118110906 74
    0x11180104060395032500054010000c0203400b903041540025404144861180306543c0d00c003007030030207110192601122699038450360050a0030181c1e100145800103280b038108020001006042074460703615100354a8803644140c03503c0c00d100140701c40c10300e13814000d4040c0122081e0000c50713a03008203440d1f150584503548024140c0c3d1001101d0442a126000380100050248224400004004111700180380c5040b40682001d0403000c018400c1000064a590481c1c180050300713030100c02c80752568401a1840f8615800c014410750803c44856160386c07a560011068510482d851b052903a90b03000c0c80903040038000b86050001c0c100d440f20850030740070b020718101401464034004140800740c0c1c54040750798001e6003000c10500020f00500041d8500300e404840410014070240d0314081c5556000340c0a1880309007002c0c00390740084242c010348420343e28410002c101da0025030302c030445a004410020070090241030416072064902000740c16080c4900361441051100301c9240c04503400400400d03801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753953228 1250 753951978 753952021
    0x2d0b180106020d0c031e17150901090c05090619081605030f1504020a0909050a060b03071110050f161103090f06090418030e060a09030308100e070906090f060206 71
    0xd00301190301031140a504581104281c940d9a1f20314049841800b0a81890281201049200103885840541e84142c205811220b07602e0380040c404442c05404e82d030318010040c2c581e50044000c5809164050000c0d0b601c600e49205a6901d0140c0c1d550758991030040d00f500090200007401407000075500300220542c00c2c3c002188403840341a5890302c1001034143d0307000c00c00150005058800820000929000b144d400c214542c40502c00c41d030400510007824003000b80b410040018031107a00d06c130722005010501d035041061006010314070700351201c1da542c0d15003580c05011607904d520141003880e03c01c110164217540d003500554500201d0904114105040f00c0d80517a00c9601001044070301e54443c403030304210b0b1500404044402d0720905002c1e048000e020030b6140a1a402c007d12000558007142c003200fa264075081207003094455003004083c80e03030250000c0e004032040b401444103450300580b40208a9035141d5039102d50a4640548a042e031080d407192101580c018400300300c0c01207030b407d4445c11005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753954478 1250 753953228 753953237
    0x70f031b0206161403040305030910050d140711010b0906010e01090b0a03060602070603060308030703180c181d120702121506120609102d0b180106020d0c03 69
    0x1055070300018150383c4980c0007052142c00c80c0300390808100784100d1860440c9a000c02541c180781c615112642c880c4540c01030244905441600c4110384c0d4014801da454090341c2010400c201510b442860b0810b000a86075038000c100e04c44400490841c050041055030311000d040c1c080152208801900e040d44020142414401b01e0070000c03401511080280c5800306041d40e02140d541c0c540a0060b013815426009101014241383c0c3c10b00201c5d4200e41101e400c14624940092040240e81ea504202c40791180c0003401c82580001c0060182c4010200d0680c7c0e038000001000880101c040c8002a403011900e0051703241c1101105200107440d1802402000e070011b40f610ac1c40ca01035000c2c1c5800c0072151102035000d07207025005d01416060540b16a040040c00200608250800c480c2081c1c0c2d6641c0d110440d15080e80300d240c031b12440c80381c00c00d0308000184204141c0d01400c800034883c00280c404038055901809065882d01d00d501144d406c01030480c0d115401800654404140465030349100c407000380c1c03d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753955728 1250 753954478 753954527
    0x913020a2325030e011404030314071208010302040b0a08070902031b13080d0906080f04261b0a080301140f0a060c02030d020c0f2202040e0108060a02070f03 69
    0x22414a11503114100a07501c150035000c02c00d28003d0010513654405604003d00c4041606852aa060482e02a0780d0141048105a80c40003d80080c6100b65480100550f0404400442060304102c64074141d0b8401c40301808030038180401e20000385102e2080a0007076010700401c22010249600458010000d0145061600e000c1e145040d00d6a00c03a5154007540c03210100d08110b842c40621401c040106c582c54010f054038038214005044090140c000b0b912000c0c10000b0904200d00031180340c0c0031035600c204148128080c0c0f04c01414942103042842031001040c005140d400300d001c10342807110380d4003058080c2540d0034120503024241c411024540c0080700c00c0c0140c4850740e26001300c44000c011507910101c25500321b1041c141018119994801994400d01c2c10401c60f81d201000909000015140300d0412950070f1980005011014000b288840c80064046842c58001d9032460680d0110340440304261a0740706440101d1084100c05802e44505400440c0000e01c20441c0489800b00319200c49481c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753956834 1106 753955728 753955747
    0x8030702010504031b05031605030610122006070c03210e0d080415031b08010f0b0702030f0706110d180b0c1509030913020a23 56
    0x29110b0501d920307040170215148a130052600030210b030f4040450700d0000c5003180e00c500410703000740680d01c0004c2455020031140c0341100c18001070450a0500b81d01c0d41c6442d0440c5829070708105c1000030100f030541c2e0342c1d107000e400c89038020010101c0c820318501d071065038400b22824181001541408c80004141c03c400301d018455000d40c0c10043c5c0b4113213840d1000b6a07204903003090704909145d0700c40040c0c0c580e040e8084054a803a18015a010042d282d2054070000c1092007038022144400205001c840400005828418800380c1154400d0710712400c050300f801150b821640001d464001c9502d11040100691400a40c90781000c02c400002001816030503600350040014045001502040202c0c4c100860580038002141145150070b0000e0b180c0d0700c0c0d500401c0c00300e100700700141c07243d0f011481c64801c891080b445a02e510140044079005000310350711001500340016001d01c080d880 = true := by decide +kernel

theorem cover : BRFrame.Cov 753776978 753956834 := by
  have h0 := BRFrame.cov_init 753776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753776978 ≤ n) (h2 : n < 753956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
