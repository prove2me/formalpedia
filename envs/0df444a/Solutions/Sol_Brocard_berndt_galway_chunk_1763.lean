-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1763
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:35:19.993399+00:00
-- url     : https://prove2.me/submissions/33ab130c-3a09-4b51-95f5-528730154ce1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316906474 ≤ n < 317086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316907724 1250 316906474 316906481
    0x6040e1c0302121f090c0207152102130e100b0c0a0302060f0106080f13080c070501030f02092b05070f0501080601080c090103090c0f08010b01110c0102060a0906 71
    0x18451034000041605416036016405060010404003603d4038969585000c18a0401004100382d0321070258601402014040c0e401800380505900444032060748848414050a14926040740080d80009402c0006043c0d007801010328409501c0950911904401d280714402540c040d06400010480c0003403041789540382c042d8020316071071401e199604001700c8182d4a071080b10000340d0151050501203000107180002e450b0407524555148a0345031074401c88140f4803003002d407240d0f044012032161200821395003002000d601608000400802d4503090016066400400b041d0040c079106100400d50b50301c2e03103109481440c108a401e0010911000c0c180343c0314808982d0041c1c198030074460301213030045c41c08201c40107a902c2601c400843c0d90f5a1401110240f90484140c51444001d00190189500a4228400702485000c00b076a6403615042d110345903000c1c9601c118001e039112a201040c0756040100c4c1d03500e000c0c520b00135003012079088001270345d602d401400400e003e540e84c441e1001131068660 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316908974 1250 316907724 316907743
    0x71e120209030c04090305040f060912080d0905100e0f0604050a12020a06050c1c0c120b0111060906010f1203051204030509040903090806090c090c070201180909030e0f0906040e 78
    0x1001005805c2d41414000e101c0c0e0410b0140c405034120529000c03c01134090125041100c03080e0740304602048296849041c1a0810b0385820070300c68580d012500080c82c180300a031258140c141001034210340400c8214906100c0c0d030303255025504480d082c03001041e000300701c0c10b29164101041402c1d4140000782241b4026018401910b01c514220034003070b07008070410080c403020042103000501f02402458802c201c1e10761603592004030b0855080d0369491801900014821030050400f600c0d041c0c0303813401d002d0900c44100c400c040c03682c001d640148522042003d9402c05480048904c0d811a03146030341c0178240f4400c2c0754410940c0c040c007400003010144503404031610080c001d0400c0c0100c03012482c0c0a0040006d5000d090f40e2802803a0002e4000940010555082c01c4018101c104030780310803110f501c090703202e480700b1b0741080003020325401042c01c40040c03a40285a0600002100c50003070078014005c42264109500c80c840b009a81e00c5565075020074203410001c1224009240006100c40510304070104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316910224 1250 316908974 316908979
    0x10c1e05030f0403052a130b0402092119081e1c05070e121209060903011814010606120b0f09150901150206040b220b071e120209030c 59
    0x280204c204040460003592402e0518180281d071002190401c101c082038082958004000c0c040c05144e0900d140c002d2034030358501402c01407070b290941020030035640e411148014041c5000684159005040104c520a0ba0000005282c2c0003810340d5910320070701c101c003914180031140d021400701c405c0300c032400c841c0d0705410300c1d52400071500c840c0b4a84004d030508807149008100c3c0021110440e0602d6203600450444040c050000d60b00040403291080e045020025000a4281b0101c221514244240d0349190b5459560300c2d504440380c6440030303110620f40601e419590400c081001510340080c1941d81c2d18000c2400418241c1701c80000c03491580909440642c04444e8000703101100c000c40e454091264411b5800203030740da81f1070b1101015106075040c00e00c01a40a80c0000c1e02140c0007241c0c0c5030300130701c2e20a5085125514421101c2482903824016a940c030007030014001039580141e030741420700001410f1950490b014450141071001032089800c24103800003400189075034240b00f11042204d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316911474 1250 316910224 316910227
    0x3030d05040b090a0201020304170307320109050304030f0503090301050408040510020a020901050603070908030c0319020c2214010905010501230a0c06090b040b1005010c1e05030f 79
    0x1060060000d00000d4505450020542000c20910301000c00c03001c0e1442d4042e00103501c0e0614000e081c802e51031008038009840d01041c060040054118449645d41070101d46290309201c12000c014a030b030040e54244500765a24091a107800907202000303071001c880d0031440c00104400c0da0709211f41144125141150305500e020304020030482c00c60003030002d40702c00342e0300a80300c4102c050050340e0b1060744000c00382d8130981d500010000d07480d05100840e0702c40c41c24030f0f03d401d800d6031b03c0c980e0713510b1070b0052140d4944a070400b04501c04e60309002c0340040a4100c15200503c804e4100e540070440103400c10030012840e0380405403500b100c1e1110341280002c50320365134110741c4030760351140c80030010304083c0200c600040c0554020101080c00c5003d2940c0c1c180103801181c50409070080c155200030321420110b4805881e80c00c01000700f0b0b9030080c0680304d6801207002919915007820810001d14564204a0510503a04c0c0080041162401e9540c035801e40820400700301c40c01c1d03081c0246103001351003a0007a049070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316912724 1250 316911474 316911487
    0x1104090506160207051914060c0a0c090b0d0206071203180b090f0a031e0c020d06150803130b0f07060e1606170606070309090524040c0509120c0303 65
    0x20b500c08220100b440b00d5090300c2c180c40d26542004002c10406440680070414500180403a40314000302501c0c40c1c031700511040c6480c05000c01e1500b45010101b0640d0303160000c030390800c42c40501e40034030080c4000c201d984100d5203c0d036030300052190048800c0039013030110160040391031034065031003000f015020300c2c0c0e00b03400d4801620b0180e28950b000c036020381d10341c001d2028005882c0b80008001d480b080d03150b200e1b00088101c9507821802920340e48940e00400c85a400c0e0a000340e01c03803030031041c01d5034058040401c08006200d11148035001076444003c155004100c502d508544000748002902c1c1c0540c05e09a441e1500f030002d0300c480c0282030001d41000c1c60f105090041080c001030070b900450118101000c010380d21201964062480750848254008003800242d451500c20014043d4611170305040352125140d529400c00c80306c003251201c4a13100440c0d20000d2005514464000b00c500c110740500c0344d0401104c004003a40140355029000e0b401001403c1b00142092014402540d000340072242c6030078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316913974 1250 316912724 316912741
    0x50a02071a070201112703010e07030b091203160e0109031226010b040518011a030405100f020c010b2409060706091a070e0a17070f030c0911161104090506 68
    0x801805107038038401c3c0ca0001850b9420180140401c412449d0b0240100e54910380720149072030707030052034041c1500403980d80d40010104030000c0c5020f59948050359821400c12035015180a0700403241d1418040194400c01c001001d4214250a000c214904400e90440c408401c081143c1b16400b001c0c0c2820448001007100d0380d11202401c1102d404070b4100c0c0c4010100c448100180f0001e02944021070203500f02d000801010f42d004580192250045611440c001040142101c2030f40c00c2c003140072900011300d1103440c0d00900680101c50310450304031039403c0316801a605850743c41c0301814900c410100380001541d54004c155500355401480502507c00700346090f001d0341510103904903608070181d01041216206141c807001c480d9024150b10502030030101100c1904e28450811a080c2c413071036034045006480da01c581c0c03004611481180004a0030199102c0580740c0680d01800418403e102100000400003161400d03d81c101540c150b41c00d02010108000c0c1104000140040c81184280300a12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316915224 1250 316913974 316914007
    0xf020c0307051203010305030901081e090606010801050406081e0f0609010207150504020d020409050709110405090912071b0b070f0c0e07021e190c0801050a02071a07020111 76
    0x45225030191200c0402e4510318003e240401c0c00003030a5544180200c46095020341d0b20140c114010801c504e108070702d01c00085040000440310000c041d0404400c0c0300c22541c0241c0020301508040314240415070800c0c0010355242444000d00b92641d1510301880d0241000b40060030482900300c0a440705844c140405070701070760044808a07000110b201d51908000f82c24464503000d164010907000d01c114440d020400078001810f02a078041c01040380005000300148100c00c40b80000d00c01c0039072114500700810121410040114401e40c101090300744000c0248400c880e00e00f030b13029031008007000c1c50209260181c9100c1d01714001c0e083340081c2c1c4405010180305001c0c6001e00c00c2803078000c2141c0b103100703c2e0b2007000b007075961001603485400720300320210b203025071b0a030f204014008070741094030f041c1405000c10340540d070241e81c424000d100c10700012100f0301640d540110900d0301075281604a554800110529010401c1c40004013000308803c94400e421128040e8600020180c603074501c800002a10f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316916474 1250 316915224 316915237
    0xf0e03070f0f08120121020d080d14090705011e08061c060218100c02030607050c0a020303040b03161707050d14070509010f0309020a030609030c1b030c1e180f020c03 73
    0x12803286246c50000120b00c581b0040d21300b40e0141c041120315180e55920300c9030b90050a482d800c5540c5450641d6203880b80c082215202c1c6040c4070082095915020000d400700c2c46060f00e82c0903032807015070703024000c40d04030320b8841c3c1182c01a25110011100e01000c403050000c1010300512442c00040d511034031902c6a082c442d49000c0490300341404141c000720a0340c10241c00c00c0003c4d095001107000030f030580d000d440544500c1c2181010380c1c01d0541564006420355215400910401101101b88159180b0346000760381d500d1010704082c4580c4191500754024107400a281000708140014104415200e642081c44207589500607525a424900f002030000c0c0c01c0040607500140707019103850340d164401e00851481940250141c0011401c41d1a100040cbc584800b0960521030300300201c100241e50b042100710351045510120081905510342908002d84687c003403140059044c60000d2200381d00da0701181140c0502140c0c0b18030300c11110f00007028081060320125024408103444510100200c0200f00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316917724 1250 316916474 316916489
    0x2101091b0c050d030e0a021302030411030706051206120607020705031212060d0206130e0402030705060405061b01060f0303090806010803040810051306050c0d0f0e03070f0f081201 79
    0xa48011004540c485400100504140c0c0146040c0d07200d103000c3d600c6180c802070f40a01b90b400d40c184640102e02c1c4440e804070012049035000003004188060708810656046041b006403580500e8880018124000c40d58100300d200c8041022407200c0e600ca008101c0a410300400307461303552400c8613004c1e45411641c480c460181c05840806100a00e612044911414a60203540d9847e15160148480b010f4000b6040307803c558204000140211204030b08802030900c0d0840b0425403070980705060400f81da0760312040c01038070148810f00c05503603000140c031411891109021140500c031142c0c10301400c030507408040030700700542020050560014a4a0941e603042e0100e07074141c2d0380c803500c00e41d03203105612a0b0b1420350881000c11081c500c8582005402c6020700103c02801107581d2580e82c101c41e000e460214903410002482902c002d503c0c055883d00a04040040141c000c100c6599500da209607040104052022040c41d000c1203455821455002c0d0841d40c81c6495101305401000c451307000380580c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316918974 1250 316917724 316917761
    0xe130903030b04020c07060c061103010f03110301050f04080d0b04060b0a031a0306040f15050c0d0b010212220b031e01080309030a03110109020409060c03110f0f210109 74
    0xc42e00f094000c48020341010070040041e00c0c41c0200413a144400740c0422121191101481c0f075000303801310302440c06070003080d9903201d0452035807400921014456070041d0003a41441d00f040018101c0324410b580c041c0e0420401d590381c1c4540344000d801000c42130003259115240c0b5901044040040e4007400803001240c8040124a4001d04030300c1000510140c0c459144d40301400080005070741c10300c80700d07a0728422401c1c0307850f203035400c0c08030026104110764040c1d94400c040f4000200f400076005054242100380013404980c1c81114001100c0d2268000101c211a03d0580000c180e41901c2101c0004140c044201c0303071a42030841308040708508d84201c0e455218606000420141c02c08002c0361003c50317004004000d10513240c0da00781c40d40c10b01300075115a1550780350152005030301c1d0b6004040d402446008001801c410310030000d811241184200e03695010140515040306032182d0803204141c50128201c0d0310b5480341d070010340104503030b410321240f0812920000140b144144d00802d03000c020012642c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316920224 1250 316918974 316918991
    0xd030e3d02070b04030c0819050d051e010b0a0207080102031e06030d05090d030c050d02010e070b1e09041508010509070e060105090108041b031103010606020f03030103060c0e13090303 81
    0xc006a004920b40034103021500b2001c900024000d1405d6a146031280390403074284056405c16203030642011011001240c800981080311500d50720820303600c80129000c1c90140580100ca02c0f03024081409807401407a0300107105030788039000308039501c0101100301c001c0d9500e01c1d18080c80510f80d920300d100c40e08503a0402000c20b0b40307031a010804010020080d542c140c00c100300942042242c201001c01901031260b200e81d9400820024041e60b0301c001d0f1f1540000c41c40e510103030440c6192000a911250040d00103020100101c0d9202d00316050b0000d40000d4252620019400100104640303ea248452603150000103020807064200ca88160302c0f85080e10700c015540d0900c600c451104031042c84c0050801c0090150a601810620f500280a601600421401d41403840541301458109a4289012039402416403070b00b401290044e1000e84007074041407011604140d80c1e8007047c00000c215984a0b5802d40802c1e1084010405007180144ac40c0204a841d9240c40000c0491003415000241441000f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316921474 1250 316920224 316920343
    0x40b010e030303070518101d150d02030901020f0423060f0f03042102010204170d021c050904020f0c0c0d021309031412010503060a05010303020d030e 66
    0x10034204440580a186583d4070a02c0c00c0300c2c01d038401c0031240e0380c2c00040c80180605803070707202200c08807084580303c0c032a050b003140384120100c503c036880c02e0303111340005800720910683c80c01c00d40d0002a6007850150f100d03124010301da400380c0601c903a142000d100c041000a001016254007100100078642c28515007400a81441054861030041015080701009903081c0c007141d95008551142c080d4601e4a0720300340d950000a040b0580751051001130f0340220b0144040c61040803002c0b40c800c00f800060184080e203a001070745a030704541000074043c070f040300c044883d2400707141141c000f420024002c568950440800040c283c0040c0d240205d10312883c031050015043c503030192003140703070000c16809103030a600640d440a4079404030304808111a4040d000e50900300c0da030141140450299034000c966041206042c9032035001010010010305003401007010940218810750480e40d1071902040404801144501c1d20b01c49103c420310140450016620300c80301004049400540000d2258014044200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316922724 1250 316921474 316921487
    0x6170a03081008070b0d02120f0a0608070e06061e0316090503030c1f02040513050406110f0405041107120909051e060d0201030e0f030a0f1e08070923040b01 69
    0x22030105500070710040c00008204805403070050071a24016103420882d12a40e01ca1880540c0e409c2411054442072100d01d66440c020203001e0a0900001d03c0d03010700d00010410840405030425010b03480000d100c40900408503860030050300001c01c05a0350b81080c64040002002913501c6200240b030b0003c0204141c50003100721010203c50b40c00400c01450003c1e015540110707281d200120b506d41c2000000703500d0701c520562030000f00000d000040d0500e401e091290035201102c02215044500700501c40c0b16001100070340e030a85400380c400080c0642c2060799a991031261550280c1541010801d1201d078541c40f1030742100341c440a49060125841d141d00e00e400500c144503804180700c2e0420002406402c1c4650040f08850051601143e2102640032031400d103040710b81d100078550000a010a100d90f0003000c0055012100d01e419514a10a00c02900c1d0103001c925904040045103000309107100c2c8242c0002003d80740301800c0341441d800d0700741e22803055a07140f0815805a81480f10310b4003158000c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316923974 1250 316922724 316922729
    0xf030b0609010e01030f350912032a03040e04050102130b04300c0602030301140a03080d0506030f190b2d09150712050f01150507030306170a030810 65
    0x1c0c6914010030036607201f00c007985041c0d440c442840052442c40c499442000900c481043e400d00980c0e41c1d0f84601d1040c00740380b40e41040600381c50b91082000d002c0d02c0098001e202c1034004041107901250034a042c00350300303610841c1d0018200100f84002c3c0000d0000640c02440d4100c0800c41080c0c00b01d54407088090300780100d101c0d000540000d610311610400da00c02d201b1084c61803990780500000516519803000103450342000b8010392011006202d0410791b05c0e810803800303e08980400f00549140e5a0007814811040b41c5540103407181c01103091a14100043e600318005041555a10b510070711480d070f2008a001c40907510080e82101043c820303e1a00300c81d40c0c00e803886109004840d44841d04050b684000a405410b5920510307541110300910391040900031412a61024698602d004c3c5003000ea840c06840042c0b251020b000400660b4200c240345900303105a403e24a485141c54181580100081e500070b07065601054002c4514103000305058940e02d01c41d03142c4040507214004150b142d1001070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316925224 1250 316923974 316923983
    0x30603080307030c200d120e12071b08160509040b011e080d08010501030507111005150d060e0f0604050a020d06021b0d030f090305090d08040f030b0609010e0103 71
    0x1c1011030401c600c2600814680c4c080b6051003040c0c1d60346a0b80c82030010700403940c6154a50480761403010301340e91000700340c030040003242000c0c40341c60006a010380d11503c03000c615003010000020043c040000c08409881824010100c02088903515032000d501d920504c1c1541c40c242d0300b010310201741440d00c194110700454000c400081e80b6802c203581311654820911891142074046400015408410011001c0e1218113030b9400303000c0d5150400140c03c1e2000506400c0a00013607007100c00d0400c1000407506c68101040c040800d4544800e5060301c000941c00074000d8010100119000c14002c260f00400380020382c1c4411079124805941440e520b501d400d80e0000c02d00d402030070400000d0701d440c3c1e0b1660b00460050000610b03040a05014402044400103001100c0e0003050b04408980d80604c04c0c07842c00c00e004c8205024003a240e03a80181680300f180191740c407030740100b9400030030700462606580113804544003001314141c5034101880c2c1c4400466100744110104800800d2050600d030041c2c2c105d0394003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316926474 1250 316925224 316925227
    0x6201c090801060b07120e090901090b062e09090e01020301080706030605060406080703270215180108041401021201030b0c04060507300903030212160f050c03060a1a0103060308 78
    0x39901c07101500c10700340c0c2c12000c11011f070742c440015035240a1001e001c1e08141c0c0000601d40558a015406e1517070050801d0312401c001d05003440310b10344d8a514014030030603854030030b04001c0809030265408503490f000b91014501d02411103031401c10540c000d5050360351701e4040f00e210643c0d4510032016504940600c0b50001801c0c80100403545c0200002504a401814049031003810f4003018407024155007104410003086d08901e0041d4100850322303810803440548a180f4000e1409681580b20740c200241d0b41c1080303a50350004042c408040d8000120084480003956a20418202c040c06058280004e40b4030716183c0011560701e044c1d102c221800ca64113500d0b03a5080603801c2e00c40080d521070164a10700f4040c503108904074805a41440f8400c012201e032200c4100c1030550400a1414001c5181d03000304450410190108184485030082540c1e4409510385807030180c0d20f020f13030a005c103140000d901803140c0c10502003104007a800c002565025030541c104001148001101910303802d10020700103420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316927724 1250 316926474 316926487
    0x50916060804050106050d1109070c030e1c05010504030807110a0201090603020904021b030a030b0a08060f07170115110d08041709150903060708040c06201c090801060b 74
    0xd0300d0356a0b015001c0d000009485a0341d00201d000350408050880360f10581e241c15a01d00d2400803e003030f1f001401481c0c4520108025640640b001c1e0b120b5a00901c0360306030f8a1201c80012a4000e00340e8910750002c002d0110781130529010304029020f0702d8590119500400d80369407051300290401d040380d0143d5504c0d900742e03c0c0180590080d1701405000c0d070819020000c0351480b1100c1802d000400c0705c4140250340c0c44041e8003000301203031542d6015500c2950102c0c0c0400020b500010001c1d00300040550360f01c00750f11900016104d0300d48607000502100001d80000421500184003169240c24980b109080b4044911005440300041600c00012880c90000f04010a4422410000364002e480031103280664801c0080c440784c2c802d200e00d402000d0300040c142c0d070f1401c09110b038030b4101600781070080d01030919595181021603140644c904001414444031424050322081508294620050f90181d0781c240c411070b034a0441440030200840c01041c1c00090360f550512491044a240340440c606014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316928974 1250 316927724 316927727
    0x80c04031104020702040c1101150f0b03090a1b0501081006230408150103020406050f0306130602210402031b030d03020f0c010213030c0e0f07051b03031905091606 72
    0xc012032076410036070900442006840d14407a5102d400c4084d202c04007805070809503a401d444100c648100c450700c40e50070070050012201c9040e4147e03189500c00d0754403681da51481d94580115400041c01c044046d40704c4604c0c94000708d0f4a4400d4550aa80e420082c0e540c4800f2515034802d244140d02c0021914408440c00340015180c8d03519000d108030700c040c50305a85d1240ba178900401c65815000040b080c600400c214030b028401c080003000c0640e0f145040300d0401340040c2e162040200302001700e11140380c60404003d4994100d6505514010f08210a080102000106000200c4049020303120b1611682007a500008010620b0709004000702a900500007049000e5049080000c005610134000219103407020b00203030919078044008102a5407460078030300b442c281183d000322601c45850003400800540003a005034032010a0405076074554080c184d440520b80011018082c6020100c1030103e00340300c450451510b4000000180216100d0441542d1200e0b0080c1caa000d291344401800c0020301d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316930224 1250 316928974 316928993
    0xd0c21020a060203010f0e090712080d060b120702010b0409020307050d020103020424090f14040e03070b0708060f090603060f0712050a06030b01060302070b0103111519030c080c0403 80
    0x40151040d512189407503610141680c000780c01c403401242d50218203121000321420081e900c0b207004001480d9003813400401c2c00d200b180000e00a0411840029104240342044c0c00501c01400500045a91001c2a882201d1104425030300c2d80f0043d400d20001020600c2d10313000e101e4495030003c0207055501d18180401070300c0004030504905264007403200007620180c081c101c00c01180c0e260b450079406014400020b100100581146c021044003400a000c00c0c0300d611100c0789101000c0d60b00080b01349120b00454658081c1c00380c002c003959044c400304034160368003e41c00c074000c0d1429908500c20000718020070a40c19422200250560310400c001440b2a140004194005900b4100580d400207403010002c141c40c41190548003581d1030380002c2082041107038a080c014040f6150450a050096466040c1d006041c48080c050b0f811450350b0307032820340d02c216080b040918032440b2180c0c0c941c3c0c3e0b50740a1100c2d0521606c0c0001082c5030207160501c2c2d0f03000700b880c0b41c412008004401d10305411a80d401046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316931474 1250 316930224 316930283
    0xf0c030601020a0507030c031109010605030f040204060312020d12090f0b040201110a050a150203060904030c061e051603110715090b0a09110f0d14030708040e090d0c 73
    0x110f20444400001040c0c042c007520b0b010b94010014003a0050641c200b140c20041c0545009004070b94440c01001031551090584c4e0300301c03100c00700003450f5884a000090103811140c01c05012911500c80c0350000c3c0750000396100d008005615120651020141c8100440700b80c100302404d800c450045100c0080c0384080c02c01d60041c4141401e40c1c0340c0503d440c1c064a45000c20030300300e906d5402140c0c000117020328480100c100b0381c0c00050a510714a030042c007060000710050001024452704180742410040310380c0289198010142051b0200036162585001801083c1c485c007803400b540100480c2c281e403281c040c07602c08940d00c0c600980381c01083da4484910186092127070703003201e80c0c8002050000c3d8020b00d4990184206110100c1c500c3c1660178101c260341210f07400076103d00303030550348a0310740d80300d09140e186d80c035800c2600401c400c1003121049007944146503009200480c0010045100c984185034a809104108101c82044010798016900c9100000e00544510704469000048100c41d07401b2030107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316932724 1250 316931474 316931477
    0x206040b2b0213050607081e070b09030a0c1415090c13020702030a1b0b1b0c03010c020d030911031e07150909050403111605030d1404090c02160905070f05030f0c030601 74
    0x150031000988e14010b410503000140f01d0110016104044c45025004203411501c008061840c0c4100f200000e44100c50080b0700400a500a0030510900785043c00000b000302140070f81e4564910f015858992110382d46a80c1912401c40008444c0c00e0200602c00d80d01940e41c0a4010407160565448207045003907034038403528491110010100d200304940001d004400f2204101000b01002410030501b40b09200421a010381c0c50001c208550f6a40060a20101d8490b4140000c40845900717110440c0801c0062250305881a29141503061a01c030346000400c3c1010400e940402d6181c3c120001c8010ba8081008009a600c410a0000c41143d50040f80c206101e414803c0c002d00d00700555900f0248030740c000c0445007441000030000390030180120070355044245840c0410395503015030780d40035001d0388c06605901c69545c803070103948500810080040080207072080701d03000e43da603071108081d03d0211150750014029007215841c0714050000c1c1d9020703c0b5895a0302c201641c0340040c40b589908010420f60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316933974 1250 316932724 316932727
    0x2011a040e0a0c0303080a0506060c0d030e0c0d21110c1918051f0810021b1002040812040501050901180b04030b0901060506071a040206040b2b021305060708 69
    0x5000500f108281c0000758440d4131018458506144201c1c02c40310014059402078104200240d8800e00115107080c3c00d8045060008105080103941c13460300306480e048541109603842400144400c0c1e80b07031075080100703443c903843c03201d40e950300e0403900011402c0100445078010010801a4544190203a0702c0000035941d0310000ba50382c0d180d15084040605407603051698440502004c2e40c1203120f0030700b15414240c1000d0720545810a910b5407140c0450209891690205441d11840d22118180701041d04032001c440c40c06c1c2502880e00000d42c4248100c80e0244921840f20343c0ca10040800e42d4125101611a0790400100000540c0c45c42c562400c100d43d90f0390070f410082080c0e013030003002d00061400380e9100300584c90110038480c00c5400c20342240c2d01c6180103000d142c0011b000300c04407110201c400011013089465500c046003650003135030440d2070701c0d0324046003800d00c080207034294844419000c3c002d480104007126010049128054003451070088011050000f030808500828655200f100e006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316935224 1250 316933974 316933993
    0x406091721090109080313030b0c070204140a0506090105100810080f0721230304330f0807030b0607020a1502072301270f1502011a040e 60
    0x840020514500741030103080c003007807900d92075901c849100040d201840045180c400310312485050b080191000801034441c840024505003400000d50b00c0859020388188500b40403004400c80a1504440780201146480001000ca15025800b0b604a41010b000c41c4c081340102036044503a42002000040c500c15810000107051000700201044402d049000d44000d07410300141001b90a0600d04068001c040d01c030001003c81c200c09855600c04188105030a46203c01400860841c0a1944035410342400d81c0d41003901c00040c10341c114035004618080207203450350710b030007a5400e540c0000300a0014a00ca40000c0545000c2c1d40030310ba9102005040c5800c0105660010303001422540140c00d0720a2802d001c0d19085d030701048480007500740040d501000814407861041c000e403030100d81e2070420007805c0980200e00090784408891245140c0380000d01130311030380e098403241c10301d01c983d604001402c20b03600d0030340c0c0c418030a8000143c1368149404c0b00d00400c030100000b0b481c03844d984654a01405142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316936474 1250 316935224 316935253
    0xc030507050708070906080105090d050703122301080307110103050a270302062508040602090d0f050705150301090504140f0c01080714030a11040b16150204060917 72
    0x80310300420b03c5800a0052030b0405440c00152070b00703917112802c141e04020038003109010110352241012060b00c1c001d030300c03061681421184403414046684a081c5840021403d2550320403c0000e801c080c0000e01e12140d0740c402c4000c2d6284510800640702038001c40500b00ca544c880c2d00800d402a40e040b40120b10b4003030424038010f070f801d54070203800020302c1000c65075000c154052000310341c004020704151000903035a06c00010038031b00e0a041c0404201b0350341c00080403c540e69041c0e480014004e420000e01e4a814031700300b664030181c503805840b507103e00000040e1514105a5058145074801110790840e481c1c03803078440c040d040203042210140035070310b110160100c041140e800c5032005640100710080002c4000740484401515100420031b18100c80c82e103801081c0e003200c0e0001c2d004500042c01041e41c640d80b04250007640c1002503083c00014202190454032441c40e400240541020f9400c401c0e00304448040b48264820b0b04042205054100704113084408142d00011910303041d5101c25451401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316937724 1250 316936474 316936483
    0x1005090f0f01051005010e091303140703032004050a03021e030a080301060801120218270f011d15070c121e210f020d0c05071407150c03050705 63
    0x260026991241006003020114801c18000e043c00c0c04c20460707ca00701d0005c141981c1340144914100c8070051045020140b190706c10250356403401100c15126031061030002c0c06400c2001007241d01032558888208030fa806213003101e04594004290342013051031035082c031003012808407820480c1403183d140541541c40611108403e24070950101e5900d40c14020041c1034008180c0001c02944c4c1d41400203001070311040808012803c5642c0420381326502c84a6420201c00c04600e449500740d00341031418148038000501c0b0301c000090800901540c5e65800c40d90b030861600e1014490103030301c0b401d0054403811110301e07419046846031501c0c04069407980c607035250490100e425600094140c0302e000c3c0312600c1c40c51003e100b074000c40c41c0c40c0c1030754400a031070348028104075031038080b0050340c6007452807003210541c2c1107840588849006200700c00074401c0162031030f00701d031b2819903440703092912520700c0304000b060075019140c5c06401307231201c0c0c8940101121182000c800450a1000400c28640840c80c20003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316938974 1250 316937724 316937743
    0x70f0201090f060203041a060d0303020304111801090e1609090821060f0906010e040b0621010608010506210601110613021f14030a1e0f0b010906021005090f 69
    0x243c00340c0d490509103411925442c01040c80404560410b060107015030300c4800460038190145009610380c0c4490074140b84082c40a955141c0c0205940c1204c0c610300c1000042d94121b408a42c0100700300c4200c001480d0321762221035170b00c01c0c2043c03480e0024040b40c0d04680c82680d031503000c1e00382c0300e0034460340300034414941c016401030089042080d01041024644480c2c03c0e00c1030f0313130190307244561400e18100180c4403110010702c19105036150010300c1c1e5030340ca8601c00d07108001c0c454010b41004440407805c00e046c0440c01c4c040d03000002d60341030022a580c101142180c001c050b11008600156564003458030703ca09014090b14100083c100d01c0f003440180400c59075004000041c490003904015204000d04960400c0e0308004145095408204458000600301c000e48806440701d543e070b98074401c074040140400d410180c40a100460824030600c1c00341e0181a11a0a10404200b06c0c0c4a02c401902c0c84034651040c0e100580c07024000d0750008500f50480b94000c1016012294819504402d4608010303c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316940224 1250 316938974 316938983
    0x3030c0403150b0105070f020402090d111008090604060f0204050a0b0a020606010315050d050309040507020a0c081b041503020301050702011e0b090705030c0705070609030201120e06070f0201090f 86
    0x30406200b886141010320800d80d15100c000c101041070500041e00c43e000e51040503201244409100042d92280e40456034501801400c03440896910b203030070402c4101606e05a8081d140c0043e2201e0840d0160707240301c0c02070300c0840060100c1e6032607955180c00b420100d481c10f4110b0740c081c0070004c1c1c9078443c4490540580060340b1400d480d80c2c18501d00a01d04800200003e0405060201c420280c001211540c02981c01c1078a0b1003115400c503090107840d6210301c1464580140c034140411481540c041180788256200b0402884186d641313440d0a6991380345c0002040140d40ba410820b03216240951240343c40401d102c0340844190395940000e030844000700d41d244050f035102e1801000403003070a80c0500c7c103c0e1091004200b010440c80228043e40c1e001042c00043c0000003010442107202042035811107603202e01211401c603154040180880010307c801c901080c0014004c0100454078041c41c461680d24030f000f04490341e10f00101312055403420b44c01009556131903d440d404a4041c002c444c140e207006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316941474 1250 316940224 316940227
    0x403030207261803011103040803040c090506100e1305070509040f1a0913050d0509090f07082a0d05070f0503190b13020d0e100b0906120c0303030c 65
    0x1203040407030000c5448220050024100c5400c1c200b1800c1007030070f544011881408507040b0415810200e4010b03e0703c44400c800b0003102008010400c007075400210712030780c491009003080795035810b2202c0940354252082e03a4425400601103680510034105860700c4000101079012805c15100703008110f03001540e0020005400091660580c1001d00400382c50308800f00301009003449140c08000c1100b11100d0f894416106000860301c5640e0200390419202c1d0003009035500e0051242c0c025200d0350000c00745602070b051220001d2000301301e86a43c2d44c41100103032550241580c60100b0f40040d010042e03107034440464000a580745018103071018103034401c00c07510001146d042100340a044810408180020010300300700700b02d14503240040f44109424005404142c1c65840b000042c90141030380d202c03540d010310102e0302d6144082e0b16003000386001c1d070742d0f0192024601200f000034243d0748040700c0c0a0300002d0010100e462030500c070846a8250100f94103445060000e10f00280c19540180c070003e071048030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316942724 1250 316941474 316941487
    0x140d06210c0b0c0703110103090c0608040303140402060a14130905090f24070311071b1a04260712030f020316030e030a050d05071a0105060f031e04030302 68
    0x40000c0030080c200d400302050828030302c3c441d41a42d13848640401854015007007a03164807a40603411880600b540007d072007004035222080100b0b800b00854007900064101910040982c685099160081c0d401500580c50a01d002100b560b500f8403082e00c40300e00b000100911200e400100d00450081c0c480540c011409050450f0428502000c4286030180d0b60824401e003c1540e80c1c2d0340360014909500c09c074000d0290707181441034008080703070700303075495108000200f55042100b400401c21901d042c442c0c0c4404555213070072072504500c41c15a407086651800f00010301a01101c0101e0701d1101503010b01810b541042c07030800d5400c00059500200c8264802d80070401016003200446409102c14402142001e03064500036130480041000502400100c028841d0a1789090007105035140e0440100c40d45212180c03802405c9902640d0140d5050f0b25007413428607154a0109100c5c100c0340b0090004e8104219108021000e44c0064240b402103003c49000d644018801c032034841c4078a009031130040c0c036a070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316943974 1250 316942724 316942733
    0x100f090207021203030907060c0c030c0e07020609070311011b020409111002031e0a17010b0a0f0314040201031d0109050c0f030c030601062007090b040b10140d0621 72
    0x1a1900b094039001401041b0684200041c1a030480d41a403034a10504851070408081501044e040079040380b40b80803000c91101c400031000e42c082c0100760300300c81c0301d0f40d540301c5406c0c1c40c0c1219020081408004540e100708540c860100c00d19203080724003201e0000856640098126100110100c4804d40e466516951301c1ca00141d602c103a240301030001d0352506030303400c00c00700d600c034000e800342c0b41da0450209131840720070f218071001005090550340680d8217584500c801d1a4603040441e0443c0002c0d281c03854500c02c140700780100e0300340702c0301e10032200c1042d200c60780190007405001d2003151224501c1000ba20000720240220b52080d40620050500c2400748e0051100401c085210341d4000c0c1e0045050b441c03580c4000410030b04441031894446609124400100300e28200d100c00c9900340e103d08880468854055404202614030480382001015403180501000317031210700040f00490000340041d404100140d000b0241b10441d00400900c0603140c0c0b0078a041e034201444e42d11402228401c0540401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316945224 1250 316943974 316943989
    0x3190e070509180d030906020d0207030806030705030706120c030908040306050f1e040b06030c04060303181509030611090a0e060a0e13030e04110c0a060b010f1403100f09020702 78
    0x1101d80c0f04840120114440084d500d0034441d044008040d51402c0da04d09001440d81a5104090412002c0d940d4801500b00245004002d460440c41790003556000241d52800043e880201c81e50760300c0e44050f00c5119800003004101909400301819101e0030300c50300181c2204018005188201c400103035a090a0180031841940103114048091444107a0a881c030004d00c1c039180d21980c4250030711010755645000c0307414000c030030036030582107810810003000b0036802c04100b40c00c4032816000c0708283d560b100d800d00200700d01c072507546020804000c07080c070125225402464104880c44407540c80c0112180c0400c0810400d80d00081d40d40044c10240401031504039601c400910500e403200d01603003011101c0c864075543c1d050000701405184924000d85454a410000903903265952154842c100301000d00c2d116400784100b02c8d1041d140251802d160f601583c1007021100b1260b48071407091132003901840d5a944060100044c2d41981000080c89424188109028040240c00942c0724072091050090741c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316946474 1250 316945224 316945231
    0xc01020f0d060504140a051f06020109020312030f010b0c0f0d0809011505010f0509301515040c030219050a18030f020f0112090506010f0503031e03190e070509 70
    0x74900700712181143d60300d08a03500e5003155035180000340c7d41d00d54460100380e1124020341d24a40c103040010006080c1d40642c13000c0a041c0c02a410f50b015190b403000a40305512089030b0000132007080b4001030140d483c148c4013500c142c41e40a42265a00c0314005071040c90040600c84810002e5014000c100e0401400e0141048009031188c01d08a00f0f410040041d02503805101c3c028100240451540180c5d501c0701e80341e0540c0300e0580540041014483d030320010041d9041c2a0500310311502e200403808450495a032481103000c00d1803040404a90030400015010404107070b020140c007403200b4603144070341034403000c400c01103516074981d1007000c400081d00b01105010150303071117403011701c0420116280f10603c0036601d5049901401d115040001aa80802c01c56041d0015174038002c182c50400000180e454181d583c003980858006a43da0704143e52441180011501350000301c2c40b0311600d00080d4051600300034214404c0c0b5603015005000811a1020a4512825400a141040381d0706160250320f41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316947724 1250 316946474 316946479
    0x602010905060c1804060902030a0b09011a0706020403060e1e01060e0c0903190809090f040201120b040e0f06010f14010516080f0711090a0b030a0204110c01020f0d0605 74
    0x24285611910b4903494024200e510401c0c002580741010350380e52681803000200104100300c4951581d06080c0250411188903440914040e8002102e18040780114100c50241c002c0032043c00300003160202c940c1200310200c0d0001e800344804400940540a0a55801c00800082c0080854107220004500151a8034103960345803c1013440320303200041c01150b00120b8811061355030464540132a107040100e24030222200d4107001d504013041030f444010210340343c00311400070079138464103c1049101c20541d002804141c1184480c40c0d03580590300101c001c1d0900030400520301114480b242d040c2000c41040c5001500008014840c010140c149007000d0000c808040c541e0503511170010b811445400294018022100b07010000c20084600700c4010881200d0010345440c40341c03030001405119000f85500c150710381c40000760a01d00f42c0c03140d4207620750010300415805800d1f03020b01004003000c80ca881d0703034401c04016051080303400b40010300d003ca0306400756aa45150b40b07000c000c00c4a090390402032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316948974 1250 316947724 316947731
    0xb0c010b010504120209040807140607022505010309060603060f0b01180f06050c1f020c060a1e020c070918050d0c0803070302160c03060e07060903020603010b0c150f10060201 77
    0x101c1103094130340c04040360b41614203010f04d0329142001c00f441d0007403040c010440740300d030141044010404141103018143d1034007103400940e100d40140041044e541d848802d01250820208101e40c8030750003140c6040d0240b000000d14546030303101d54050701d44032a01881403c0d00c489420399a540d211249800d1407840042200507142440310491603010280b003448100680811a000e40700410b010b44240c00f1014602c103483c945e51014107a0280d0805407041d180c9001d130f18002100d0501ca8011002d07400b51681411a1005080b50402c0094016851881188c03241200100348880c1ea0f20031704038040c0d080740d007080c1c4d9081f40c0d29080d490202c44244102c10005044414170020302c040055036048951402d001d4ac65815104900f140c01c10040805030881c145030b1800014001540d1188100000400035500020346421084c2c1344451940302c001c2d00000c04100410140d80c01c1c6d000f800901c0320b81130903500c584491a00140c619001030350499180f201d80c8044c0180245003101c03402c003c0c032090001b407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316950224 1250 316948974 316948979
    0x601030c030209041a150405070302031306021803070f080f0a1a130503030703061415040509060414040b0105030c0108070813031b0606140a0e0115030906060b0c010b010504 76
    0x3101004503440000d01035040350001c00d0800c601c402d000c20742d803207000d04000800d25000b501c1c0c02d4044290300c0c405004514150110700020b20a001b103d10036000c503807080442c13a2481d5181e50003980001078040b5a14400040481d031a40c051000b07100811010515084582c01d1901090506440e02f80e40f90165000c0490280040e040c1203121102400a0a1030304040d95008104021482ca2010040071408000200f218454241d0300200a44890220101400c040d2100b0310a03070108503c903001918000340300802c0607162003803109520010180000c910207200345198419000c0645049450058110040c03040d4103040101c501032600910740031303010303051408026001c49400f51240b40c2401c011a500720905000790520448880c0c446c11845c07080c02103042035002884180100c10f14012503450760711080c6861209042928108c0e04005001c1e4a0038905013201d8800480360424107031208001d4000c1041d03481038074000d00c0105d28003036561041c51501821078a402c20044e041c40401c1c80709 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316951474 1250 316950224 316950233
    0x907090b0d082508130501030c0e1302040b0703050c0d0207030201210e0609070504050108030a05191404090b010e01030608030301090902131503050616021504020d02040c030b010e03060103 83
    0x701c45002d4015001d01da446011080710483c094280707181d1071501c1c2c032801841c0304200c44000200300c0c01d803d000b00415090380340c1c40110300303546548200a000428091083e0030350301d040c64821b011168103440040c0790a03030314a511400d5421202c402e9011030004218007680076828410001c105241cae1024010303050450340041d0101d01c2080400c0c10304036401018803012105a403114103e4402c1d02d0440d0268581412101d9407030a031406014000c1e03040c0400005c0c3d4590000a46245020540b00c55080c2040d1201000a90041294200401102d070400c180c101010f03800910140c00d6141c00400da034605103001400c0720615806090405103040010002d01d440401628151518124081942c1c160f900014032130840132505203a0180ca00741020111500f071a401c482103a10407000d6480590f54000e00e00c400c212143c100b400981c22102528000c12081e1006680c0309100401c2e00500150903004035007141d10508180000c00d5488032096829038020960801c9004100d004140f10740c199030b207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316952724 1250 316951474 316951489
    0x613050f01140d05100509070609080d030203040c030c03260304020a0302060d1e02031621112205090117031206010309050327040e061902130e0907090b 67
    0x1903280b00345034150002995544501c0c141000310b4004080b80d050003419041c010003010251441c101074030400c103002545901034080a400c0f9070601010b07000c100041071050300a9440104110381c14002c4e5800800060300402401c070107140660700851842c2c05040003400440c0048540000c4040c09101308401603035100c404c0005c0c4ca45c181c42e169220322805010700302820026a5621448140c083c9000c444803c660240d1720480300c0c04411a10407051030000e03141160483c01480700b150a00d424a00382034451380241c0c00030070f08000e030399161018003000601040c520104002451011000030016440e11040c420f01425136189542c03008128513088170380e81d1042c12091500481850005151603000323602c44c98009400809981d6501181701810340e882410900f48100310754140034422241c10944107142418521100410041c0c4608400c2c1e01840d0319a111112400e408102d010042c40c0c01416100c010180c0340c681415505150840700d05261080d00114040c0746800500100317940c5114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316953974 1250 316952724 316952729
    0x160506180d11010b04020711040b092e0306091a060f130b1f0f090608190e0f01020a0c031211041a0c1209120604170c01091a0613050f01 60
    0x800c01c000b80700020055000d010100d020590240c8085061424814028070903a884070040340c040002150038000c00084480c00c0d034821020710b1a21070160a010a1180124194a107a07442c81600c1c1303075a5985e0000b641c004400c01c032400044005900c05812840441582001c000c40300000c281003401e0205600311010945484829150000c8080139242c0c1402c1c0b0181007011039010708621541c40c030140280d00c1c4c01804800180c0c20150005150748625181ca00031800700032007510b4100015240300141c8502c0d200082075000d09510b519182c0c80903c001d03c00c00784507440e080d6000001e403c025040310402480d045003181040d09140c1d502c2d03551800c54098500c0c02c1642c41e8075400b181030020060280400013410340c42030381400e011809103040904400da208030344d500004514050843e41300d9000f600c0050000e0050201c00c0c21000960b0090028100d107003000084196440e291070750350b0398894400c0d0b0f100c1184241408180d0030035800b4680d0200103003400740010305080000140202052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316955224 1250 316953974 316953977
    0x91605160203070b1207020109030c03080a0f05160f080408220b0726090916050706060e0105030d02060405190f21260c07080708160506180d 62
    0x2285980c1810304146880a160003404803500b00d40c40319500c00c0345a112403401c20b10012aa00092016403050240301e0b080c81e0301d60740b00b41258209580a4880102c058105030030303c0d44501513005465040d11503030344101d001034520041114603440c051b00d01c1003500c000c0d80410200d0020400404c0100d01201c96880035408604290000d8180e8070075441c406420255202d036000601d102401043d08400814202d001c0030590b9002c501000c2c014544600c5010b150001d21a10014080711011428030841011a050551034081a6a03500d02110306580000c13502807040401405541010014242d03511003d000a240c5403e203615280c2c0e81d4007903aa5142680741c07101101d0742c01c2011030918100c031075034001081661500141c03507105a00750052414000500d0040000c040407071000c15100141c0501c2c4200401e40d101c5c5000022141c1c08420f0640f1280020417010002071507000091804803543d40000c612901300f890311a05050f006440600c441481c141a000001008146910100050f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316956474 1250 316955224 316955227
    0xf1707020a140d0b07020703061103131b0b040806040b0a020c0616050d18030f14090d1127060f100302090a030605150307211b0302030604061a091605 66
    0x3420015011404082006140c40c03200130910140a8000800c0b0050364450b03c014000350960303810b85401804201c45030451000c604071243c01050710818082d02003480814002c1708141c50700d406418940c0541d0107940721381d11400821041c0010300f01c1203500100784080552418800141d0540e035014040c000620384c421140c48601528020320490b605046444c80c02e00c14241030106003009548002c605502040f1149100c0860354402c0300703e1100580c0d40c501860500441e48180000b014210408032030701004185038070080d40d12071648590303641048000e040003c0220004415030321015048a010b0001210b4180390b5039200603031314001040c140780040c1c903991004002412480d8952000e0603940c500002d100c41900c045000c4050303450107600720340050f0758a07c01101c001c14542c0f541e140b40c00c600c2811b180000c00d43c1c581c1901c0c40300100280d60040307499800090414100392070440c0c6a6654a4a9a206684a122042500800f1101400c0d50f207482400c40078074003101c40d9503c040120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316957724 1250 316956474 316956509
    0x23060a020a29011205060f060619140d05011505040f05012d03061419060e010c0818040f0902030705090a291f090303180902070f1707020a 61
    0x10b20800454100b8a00a11903403960b560418908891040038207844900820380020746011001c0350b00d5001e0003014100519003928240b0001256540030180c400700400c68410852640307048000d485400da007060300080319454010200101401003a108080c048240310400841aa8441c0711040700c1003800c0090f61142502c240800b07400600910f1911500c0510320300d283c403076059000b081070b00d80da1841581000591810001c4801071480700c40c5070410807006c14401c5502c2284070f00d00700603060611403400100760380d910755142c1201c902c1405c81c840ba884210f08070314090080c1e21074036141040c108101005500070940720b0382e040c01000e004285030350200f6210041c5030b120708c1000c450043c1d00c00b0643d10a080b07000301101600c040c1d9209500f1003008604003400d103c02000321011036222085001c1ca140d405840b4a10b183e0003003c0300110820340003030307034130030600041441501c01d0803440a00e104915100c00b41c10724440c6005a107040c203116541c0141c813003580100546043e02040d152031034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316958974 1250 316957724 316957763
    0x1a0105031212150d050c150c030702040f02070203030c010e070905010b120702072102041a01081f05090106050903010c082205030702040c17060603060d0803090a050723060a020a 78
    0x84a543c0c164000c805a030b01401402804202c5044109046590300740d0b030400c40500704054040d84401060640040201e68014a00b81e8001040c5070341c041405030030040b150700003038150340100b0381c0c3c10004d035150310a02c152402e0600540300070340f400d40c0c5d0800031541030407044422409610215403502022070080f680312070080084000420f602c503011040140318402c400e0a9502d8200124092420450300e4000004100e0341540d5400c410394034034402e40e071221220b204503000b509130302c6403403120100089515261945168040c10f035a4a850b90740342c00d40c03070516007101c43c40216842004110400e00c00702d0344100c1c039200e1a80c1c48400840d404100141002c50031441000340003903000d0f280071109802203400449000760ba141d035a0039041e20b95141c03400c2c0301c454072044035250780c40509100a0f40000703012401071a084880c0d0800c442000c0004e99445e45007000b40d0300b050b807000c40f101c4400d59421080c40300a16208409686044c101140400040e540d0310046c40000e09159400020765a040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316960224 1250 316958974 316959001
    0x30f0309050c09010b0a020c0d02010804020d0303140f01050108090d1d01050c100b0307060f090b0319050a020c0d03150623130e070509010e060f0c03071a0105031212 73
    0x8000401010f880d50b961200441541d000d20b592001600680c0b40034441c911700245c3c031070716407501070711084c407155615400c00524036a110000c509040e40c2e401318404006003107000d948519400200b03041f5950500c400500041e900500a201c03036881545c84405456204e2806d1300012400d4102c22428040341c0f006035514003900320104024403e00512246280180e000100c80840980548011a8903160700300c1d0f051840111600106201081c20028500300b00700555100c050004980001e032a0800e048043d25819602205455000701c1d8074104154244025004500c0f607060070843c40c0e8403490001242e44e2030348602000c1c40f0b084102800c11a0200c030010300c40804144aa980c1c03100526031313194441c0824014009040c1301400051f03400c0340924100c07124000161516988110900104002540141460507880e00144181c1181113010400342c90094490b03051418100140c1c01881f04001c01603100c0d62290388405c8900050b10303080b5045884650380030200e80c056681e481880000c0c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316961474 1250 316960224 316960243
    0xe06030c040c11062e0806011211030312010e010f030f0f0201111e0d090503100b061c061a1215030c1003050a060611030a081905011205010501080a030f030905 70
    0x12070084a0410001c901050364100c03802010040d121178104012084815041d014001c44409512400040c0320080f9001c5a28000601c00c1361043d69058010b80031034116084119039030228000c0200600003125120000341c05801030740100014180386454071954003040741c00c064100d0007400000415648540106030783d4004500880c2c54a2280d0a101000c000164801c1000340c00b4001100c01c0d62841601080d0440b0130007401030400c0a20400140001c101d84044564002800c00000b100801941c0c0004002d070020030780050010b01e043c0384a16051981319681c0342d5034204111521301c0003818490190800c4036407401c0002134900c0d402081c48e0500d0894202c5e4040c0c0210384207400c0c1949030308098030440c04c11a0a02040342e54280941d0b0104043c84540c40035001400740c4602248590700043d0b21001038520084403000075091034046650030f802002403441030030800c809002c03007401540d00401c1003030700911581100361402002c2c8610707220904c0406485070401d206100e41008070706403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316962724 1250 316961474 316961507
    0xe0c190305030f1b071508100305070b0426030a050304050a061409010c020115061d06040b07050f030304020a23040c030c03152418120c0e06030c040c 66
    0x40c2c891011503c0d480b281c000d01c005507919050b4101110600301d0200d9008103c1d001002c202d81043c1030200c0076500c42100412124140d010702d140007001c0b490030130000000301002e600c4c82e031b0740350b08206280204907912000c00e00364104540303958000150010031075448046070719003140c803a140c2d45407040c14a928100040e00d603d00380030301c9001040440a1060040c1da00500801040410100a9003030b50318100a50b20380b40301100301042118082c0030000c45010000032912003940625000419a0300150090201c0c000042080f03001c0000c100300c455150f036080e000031421403400350700280241c3c89501030402500552640078040c09600d111440040400400511082614000080c000d10880c0c11150002c0d040820803820441b09c10b80a1040e101c44052410725060700101da0441c602ea050742d01c2e010000072810102c3c1c440200c1000d88068281d48407091210121030400100e2050390b5040b00e0701044499040c00420313031300001c05e4111480246c0700415803000030981038a40d5806400c0307010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316963974 1250 316962724 316962727
    0xc090414070324050907050103050c0c0a0c05010f11100f0207050d12110f07020904110d080a0e090c0a11030d0905010e1b060d200c0309090105040e0c19030503 70
    0xc10000d454030204007010f520f1200014040c00c9503042019201e0540360b400c140d400c240b00c240000e51080c1c00c40c99010300741088e854542030440051602d01000c50300240e078250000c8005004540e80301d40d01216100040c64801d0007030310041e002e0b5850320400c1080c450400c1d61904c98401c0810950191f5403c81e0b000b8061724620480f41c40d01421444001c04129056485c000c501d003804071200b429290907a11f00303400a81801301c59402d024070142d02901c00e5950b0403511381d0759100e40e6521018089103d20130203040707889500040c13024140d030140d0882c0a101d5842c401c100b06181e10040190b0344440c03e036151824500310030204550840c458058110580c81c18069984188501500011704c01c030740d56000c59105040c4440d843c91b0701c0c20b07050070355035006000b004002c441c5040751b00418090b0204203181912000c0034080803103182c0c000311106506800100700c4540502d03111103494010a0180d0b0140304490f51001c10548400c0321044d40da00c00d00c0902a0300c20740d074004d03408036400b0395400b1040700e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316965224 1250 316963974 316963979
    0x250f08030c0c160b0f030a02310906052d0a0f060210050717070905060307120c0c0507060f020c0d03092d0612150e06010906110c09041407 61
    0x803455120308070b00c405a10541044040400d050f00ba00c00884190451580c14550503c03a11315655001800d4001040c0c1c084c0070b0390228008112203c0011500d0362a0b5180c13080950924198000f000d51003104005d181c8603040001d500e800e07510b921f504106070101c40405e4005003000d00100580f95905030094041c40d03020590000f075816070803e44030550225036801c105001001d003075500803224000042c4800490380b8908100b0662650070000c141040325006450700003003440b6810403203400c00021410b01859410365120300c16074403036042a28049803013040ca5182d941c0d41d4801f5100d40010040200c030b00c0110b0714401d01220360807105c024050300025010307040051025400c3e00401051040d07504010300d000c100d10403c015180714000d40c1a051616100301910b24003154000c0c030a4040e19401031420b00c0d510207030280060043e0221104443c20403030001400c0c2041504410184184a046508600c03c0010301007403001e42291700e090240e0b514903140440d28001c090301c001b54031652101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316966474 1250 316965224 316965241
    0xe06060d1b021e2109060d090303092d0320160e010b040812090609041d19020904110109030b0403080a0c0e01120f0b0d0620250f0803 59
    0x580c54000b109202110503c02c8080c1154864146010300c24440b00807a80d040c0c051350f9584041c0801c20002081d60341440300042801050324a01c0004070700080c0d81c0c0c04030004100c0c00c4449010601202c0d40311100407041401c40d151010b081180c09001d020051940c185809800c59a18086002c081c09580503025074081901510070715000e50040355483e413001248010411095a0440b130200005151004085109007619072000482980214040091034010749a034000c0d010011078001404441c0d0f10900204c508018100c4100c0590030721b050030100150761000c12203034110b03070003013240305010b4000001030f551840c2640c00100101d80d031604200601da003001d0664031910101c0c00034404108110011a10150b2142e052808a683c0c092109a480c1072940030919094140d2000243c2c050302c000000ca200024030802c9035915180c044c1d454030b8041b80320810800d202c3e243d14481c2048240c01e8103c4822041c00744054001c18030198a6052080000c1c9c87c68500390000c80f0329a890609508 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316967724 1250 316966474 316966483
    0x61c0203011503060906060816060507261809010f17150718080a0b04150f1a010905040212060d0618030e0916050313030903020901060c021203040e06060d1b02 70
    0x1c1c6d50180c40c0145c00104003001251801c40d11000c000921009070410b101a0340b55008051705580c01d81c1d80c0101d55070015041c01c0000d118020b80e540003512400494840e002c80148510124002d050150041100c500306908240940b04240e03511040002500701040c0b0b880d4000302c44400e1010038800703011840742c102d4581c9440c649440c80103080580c491090543d90892844010400145900014041445007000208040380854080b810b20706841000050751a81210350012145a2150381e03055a00116800010482690f0030343c14141502050079240000414250041e901400000d04011050344403103038100d00f813090600c6001540c240100b08240c203512180c05005c200006c50b44440c0541214000300c592603403940d1071591601208270741d8507072401e0110700b8040801d40c00300041c2c1c6c6200180e40a0302a90340c9000c2540d01c0c0b0b00401410b00340e0a006618143c10400051005541581c1c4c403584c4003605542256a03481e00003400300040010700d07402000c07050f21380c1d01e0705c80042e800f24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316968974 1250 316967724 316967741
    0x50f13052701050103020f060d090c0303050a0e0108090a020405070207030b0c04050405181e0a0b0a0e0105060a060e0f18090d030c02010e1506190603061a03061c020301150306 77
    0x50035444100e8441070418200c034070a000195109141c114102c02a1414400502c10403a0010b80411034014680d6414030603c15908124040f03280425000d80103640040002500942440e04010a0608911094031503c0b210b00290056803101c000407602c90003004400c004590040c0e080386103240403040b00c00303540c105014880c0300d28100ba010803640e040d070745103420260704180d015021031203164004560b5403124030841f001034003503c1b8000c40032410074681580704194403600490341e01079032128142120801401c040c8104a918000d00803107520441c0e243c0000c005541146842070050300040c00100c0010900700031a20000c10082c180c0c1d004103000e212031409490034000148038000070313420798607a86500c0c0a103501090f2151903540074001501c1c2c00c000060802102400a00034100050f44180c00850100e40c5a8208004822002550f0003141c040004801c0c2035040c0000000c1a40034402d500c60898001c48286000350f613029070150402860344100c0544441e66403900f40064031016 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316970224 1250 316968974 316969021
    0x3090a0f0513050c09121e030c060601021204090b131b0806121002071b0f0f0e07050307030c210b0a0905012103021908030421020304050f1305 63
    0x2442407000100c0d29000c3c40e4080d8071140c00c03190500e582c86080c405030a10b20100e0000a1040c0e10000e1610404030a004400c140c1c2c2c2d00255030780309040f401a51a01c440513048504650103142020001c40300441900c0c00d489240b000441c0c01034070403000400c1d55003a075040302d00310340c0790030746030f800040005901c03545840e800d445010382552410100000c20002030000b1415401c401070f00301220245038001c000580c81003008080c0d04180803010108400203400541e5000c2d100102444480e04294120303005020010003104d2034078200704000c0c41c501001d0704d0b04040c5070700c0705d50300420302d0b004000f90303401e07114404007107100c0c1d0301041080b0300a4801c000700203000f40344074030780480d8002240c0107d9044c1c84441542e01c9650b00405900c3ea08900045070640c00c40c0209141e6854848451001c402c8480c010500243c980c2030508000c0541505507078101c4006000d032004506164022054900f10341040b03951543e2013250344013003400391080081010b12549440c00704020801d94861050300d51403170 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316971474 1250 316970224 316970239
    0x25080a1b03020c0105060406060909020f070b1509010e04110405060607020316060e0a03080406140c01020c03030105100503040201090512030f0f0703031103041106091f021b0301060303080408070503090a0f05 91
    0x141b2083c0012070f4443d0052500151400006216095150300282070610030700040031304c0d002d660f44610030040c0d801e46002588034403101c42500702c1d01d0000c0115014005400500b01181815510102581c1b0f10469081c02281c03a400003520954401c0c0c10703155010740203000c0e2001c85d45001012020083d0034010040803c1e04a00500e8490610300001400d0b00c0d4469a03461134a4180301313094922502001d01303d4401c44080010380d51010080c0060005240f2070310040d80c0b01c5d4108020004000320722210380040160500400c40541c2c2c0c000110002c0f02c03000c0d2454110300e420484054207500c07603040b90100e0800002030b50344e0703450b03210300060008a029640030800004080500032541c402510f0240054040304040d800742e00d0054010500301030010100010000307440044013002151101c1c05001da00030000c00c03811418825800239007208114000c10415041d0b980160044c440940064500c400c0810242e003080801c0003101d010250040070911029902c0e583c3d080c0e04003841c016139001e6001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316972724 1250 316971474 316971481
    0x20d11120606011407052a0d080309010605060c0d0c11060705150604020408030a05090102011e020d0b03010b03030d0b28060306060f0c060e0a170903010525080a1b03020c0105 77
    0xc00416a264a1b5026018000c074061889404010f5400e103107503403902c1311403001e03082c8140d41d174010541940351094003040d4403860481c0070035007150119400b040c0150000c009150f8140d902081224505425040240f0380c00f001c5d05004400d8482c1c2d800c01c03508084000707103032000e0000c0001d2804002d030004500b5103c6564240500050f8011031280700c900c2c2e0f10901405080030701030320140c081c03a04d0610001541a51059201c00c0005011120f4040190700050202540415014aa040c5141940240902c000d00c50100c0e80e2131298140c406a90780d92141840842e9a1340e1264107100c0040c4004080c0d4045080300802020255110300400b091400d1070009200d401b604020090200d01d860b101038407074254940700d02402550391034014500070040705200190440c503034081014000c0b8422601d8803021400d0508488001d00044c42020080d024038545a6076002c4050b101411071a2a81d03407a01d81841e80d001401d1207030020301002c0030301c1d203850400661640c05001d0840d2580024840d64a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316973974 1250 316972724 316972757
    0x31315021b0a230c0d0303051f0e0c07060204030605010303020102040e160206040803090a06110318010b0a03020105281e0806030a0201080702120705070801230103020d1112060601 79
    0x1071402c00c0c01060f80250f07031a4a2802c28048540e00032540003042510f0000d0540d0300040d0300003144140840103c1e907681d00748800c2808181400017280c80c1c01c0c2c0700d11000d6041038580100004010320142c54450300142101c20401290140c600940d8068028070a958491402a0107500103001e826940c034124400601100c9862410704140b0280303070040c14654070380d501c50300340c0313030f84002d0640321f2030320aa0030303080c0000d0414070410440c52240c0703076403546904108600700c40c005601100b16105038141003d640a42e174505000b1070031a070342401e010f5900c0c07000000744903a40451400d4980c8200c2403040300061240c01941d11440702c40780f80f40450580c0d01d05102620904000e440030342d01503001742d402000650140000f00d401c440603004807200150751200805e4030b070f1302c103d03822a00758011041c1000440002d001e00c1e64101c044600381202c1443d42303110905134010500c00688a41d06000610040c4286850132107400e100144c480c02e800c4000d04402e5503982c03000c0d150280002c01c0300c0740c50548071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316975224 1250 316973974 316973983
    0x120c06080721020f0906070c050306100b041214100501030c12030e12071203050c0607050903030a03021827010501080106120b030111040611010f0c14031315021b 71
    0x12401010b0b414140000c0907600000d40021240080381e110030001e031042945d0380e2001c1c0546a104031800d00c480c504007800c1c54200800641b003020440c0310810207000d6040e0340c0382920259185201c01c42200804d80c03c28502003410a12400d6090091030482da001c4502500024142d81c00b40821100301699038040c43c0c1022401c0741c0160008031481000b00707582ca41800c800c490b068a1000720f441c4c042d15852600440c61103000c040300400d100051320740b1450800d1000e80c3c0c1c026528140b0606094600300820348900c540702e808010190300144012048942c1e400b04140d42c44041c0800f01c0c141034103400d0075500881e04915800d070040c6a00006020740c41220094182c1c0d03000ea0300c480602000b050203a020b404800031403541552640b003031200885a20016000900f00c1d5603400000c6440400c159086482181071907440906018201406980290030b03541d012414000302c558941d11421082c95405001c000100001d0f1500d0350075081034000c1c0c015010100100180344202c441914100c0e658 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316976474 1250 316975224 316975247
    0x18120801240801210606060e03060a0506010e0d06020c01020301090903021504080a180509070528020a0803040809090a02090a1211210d0f1409180709120c060807 71
    0x1403244005208510400000640b442041c424184c1081025034075101500d80c60f42205000400319041c010345842c04200c1c058001c08810410090b41c103003e80001d10386040d01d03441500409440c80080c040129a604071443c20340510003c648a585a0b403503a4003402c16240107400511070080c6013591440061403040c059a40071a10620342008424142c80962560b040720207180210f010004a0781c8a64050902c5040c0c0e5a44440e625150b80b6400c03c011292181c800d0b0301c0c000ca10100c400000d40000e1300360042c580206100d40c50303035164680480c032071164180e8660050150400c0c81000780c40b03038000e003042d510101c1d440104035460b4501424401002c52024001c6010811090114149020719100f80100031490141c40b4a507810303078600c1c01c5c4010007410006007517501500b40d0182c3c00b030340e2004002000c5000074688035075500000e1021100344604100032181001007008075000e8580700c00240601c0440c800d58011505100218104038820203021401c0313500028a514403d4590010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316977724 1250 316976474 316976477
    0x11202031005040e0a05032d0a09030209191d011a060d020c07050d0b0118020c0c0906031c1805010905010207120203120c0105060f0616061812080124 66
    0xd00920301401c003c0503040110560441d40110079000001c1041070004019100f021281261221403004a400c80d180c50f0405d1084005e609018070784505501c40745282c00c40b0b40464200c10540c403074007545e41c1c01c80c2400e18006481c0d1b10300050200480204c07415602c034154284020819168180d0f5040001d0148001060340729404200060b034101781540034058042d00364084540090310b80c40400c6078002413141c1034030f008004000400403202e084001340b82580c2210820360610244030421551400c1800744c1500c15031140d8002841134a04000e8803a1a180480c00c42c91359150241000d040e90000032043d07210488a0100401c583d405410a00102d54042c1e005084c0c80703181851a4100c0e6186c0002244d15000310303c101040401c1c2100649074040f0070710b000091a09095041001c0710191060f6035010300c07801d0044040e031081800e100e06015070480710208110f0102141c80c0010a400c02c801805204081c00b14501a64804076441c1a68480300c1084061101032115180c00e141e03180c2c0140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316978974 1250 316977724 316977751
    0x30408070302240c0a0606120b190e0304121109010e0c070501020f0d1d0c01080a2a0509090702030403081e19050c0c0607050c0411131401120203 64
    0x801420400c0300360324242803c1200088010501c8040c40c840d91100400403c26480f030461031052040902c946801400400003160010a0036a1102c1603030070b00a150030641017213a000c10180c400c0540020310704152540a41e942c554031a129011610061901500c00c56440c801c0c3c001c41d03080808425040e648a101007295035a1040001905544154400ca4481d5000e201300f05170f20321158003802c0070300c1440b400402c00c01c0d503028051320816140f03d001007041c1d220740d030109400c0c4d03045014a9007050320030002150b01c1180c800d58024865101003041c0c410b0044500d20140198020054000e0703c00494030520f481e2a45a4200e035a0b0189010103040b511041182c0200d10858070460301a8120004000d810103100c0409076103500700b503d01840204a0014020340681030a00c207810707030440d0899085040041d03644601e5034071089504503600507961031500c00c49d8502d600c002e88114110303016045003a9500c1e90007601d0000341034551f403400316000c80350451034400c2c03038000e684c41900c600300b244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316980224 1250 316978974 316978979
    0x901050904060603200f18121c030c1704081809010941060d020d0605040c0f06140a02010b151201051807210e0115060509060319021902010c020105060303040807 71
    0xc02c0000c141c410a0759221010300d43c40c00c4050018003281c00d55027030146c695080c3c2c2c1c0494002400350f035691041401041200c0d0705180404806030a034940143c1c10840e016201c064800901c20b1095900345034650101e041800013400d400e0325008504000045454141808140c1500303980c14841d00382d68203850480d05180b590008601c5490590298004144402504085d0041006a4042901a03841544880030032003030006000d9410000d0124652085129140103801000010740100f5991405400140081381910035001400c2c064002080a800880401d00110703247c0d10000c2921054807060000045519180d1102a40782e01c12100000d100c1e03031564000c03120a0400c1c48404644060041da52141300f880e4070451048003240c800000b4443c0940403955902405075000c1020800f041104001940fa2001580c0e0400b007000c070740c020100350360000d03003002c1d004800403082101500385c80700c580a61305400036a15000c80390000c1200c2c1d11035a0606840b480381e401403507050b07804001c0c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316981474 1250 316980224 316980247
    0x10804080f0702090a0e0f0706090306152706091a040203061201110a03153006092f1005090303070605180f01091203020901050904060603200f 63
    0x3000001e241d01030341da2410320325a000800048003910031500495407a4078441c41030204105c81c04507001054001c0250501c0c1640050607160076000041a054540c070b800e611589208040c00042d021401510b0640d101035100d55880c0301c414040140400d041c81e03000214085144501d0740c440700354885580c20a4a04028000a540090040b44d0030080f015a1103109141c2072144059001c80001e100ea6201d070512001810746d04001c000780f40d0105098800c01c18a44000301c24881c6c60b03907152511180740d18031460010909802540030304440d0070110030f03408204002c0c1d00889034004141c0169031246400b002811442510903100d600075842c0b580f4142e1950241024280c1d00400404881c80c22880b5510682643c0042c0c4408445c00c9120200c14a0404c05119040f101980700c00204170707600183e2030303400c14401940c80c04411700d03900003a003030000c0e4810300450b64441000351003071048582e2405d0080013000319095400c1c44e002510b0174840307d44d074074204403500d0445c02e6541c5800c01880104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316982724 1250 316981474 316981477
    0x106030e062205120309070509010806060409030c1208070f030b0d081c060801020705010c1b030806010e090f0603011107080915041212031109030a030e010306090f02042301080408 79
    0x359024629004040d00003c00401c0054001c20b070b5244880d4817810000400d52401d01c407500400c1c4140035140061000b1000021041da09c0401110081070204940c20191440340d40c04402921601030342a2160b4842d400c0f001c2e10703009151350380c5c41c144041d046c00c0c01242129030302452546c3c404d5424442e240452109000f400d40c01c1000d00c50610100000b81c43c10b02103400b5580040791694010400c0b5052010030710420417180784a04180003071140c0f04904410302c40c021400202400305010100e40c46910418400d04c42076000780421031141000a2030014111086809a10071340c20840301c82e08816601e01030303071240f903071244015003004421010003c401300305944021900d20300f0312000401e00d00c040c104032030ba05d0050111520311b4101e80c000409a406a800c10400e0403010801068170b5100080e000007000d0301407070091940b000e2440104e003c0c02c1a60720410031241003100c3c010303a8540c00e50003481142d202d000a003d441c0303c250040c2c1c265400819200340032072104400140420309050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316983974 1250 316982724 316982761
    0xb161b0f0303021606091208070503010e101a12070f0518031009150c03110d0216080a020706091e0608190908070218160c08070c0e0f0106030e06 64
    0xb0050f00304480d030f518a15200c88101d03c03d45246807034800d02c1c0240900c18441019001f094a00032045160540e030250491006200307415180032075000042d1500384c091031071805000c0121102c84190b141d078030341e407030b440e001030400b03441240b400b502241201d400b80040555081c626120070382803083c1c00020420004241c840d464050040c4800424980d85912070203d0803446031441010300c6a40c03a8225003100c058444110038180b0f0802c9541810704420103482403400700c44000f690320a8900e1043d142d20101840040030020086240030015402080800c00c0d03c5250b5542d00d0200e985a8001c044140c00c3d042604140a0001080c00501d100300308e181d901c806840c009d0f500346c840d011544011989407640c140c9200b1400302d005021032410103003200050720070140004030b500309540701c4440d221142d52020103108441048508009171101518096604101c0418001e56202d0b9104e4134140e04030f034081050311048002198103402403284a681080c10b10041c41d1a66445200c240320001d1030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316985224 1250 316983974 316983977
    0x5010b0405061f110f01050916031e02130e0f120f0d051807090605090601021f020a2a0605090f250e072106060804022403040b161b0f03 60
    0x11980d1408804081103045e1030304402600000361823070f02d401c199080c0500842e801c03000024807034080002c41e0140c0088903201c140c045d02c1150440036403000802803080144c100c1c078014108000c1c84075000c000300f002401001148151414800000c890741c003d4803035481c444694101c148510040c403000c60b880f01c0c3c0e000d5080280b55420104480c10640f40600940c08105041c0d00e50105100c2e60601d1008907030426002c0c001401c4040c04044455201294045a074850315400310714074070b14034840c11180400581000084082140c50010384d000d00c04080000d803400d505000c08154403510015810303000c41c402c08003404036008222000c0300806459051050031510380480407400351613001178103000b4000c0d6105c00f40b00c510a2200207190307114204003226102e00d0310004001c1981c1142007207074415070464018a883c139448600000d810fa90900000e80007070702000b0402084010401c43c3e015a9100901a042c0c9000c02012142d0300014462040d10400c0c00c0c00060005138851040d491881c4039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316986474 1250 316985224 316985237
    0x1803010204080610030303060f050108190f0e1507090806010e13150b0a0501050c0d0509040608012903010507090608040203071e17160303110f0d0302030405010b0405061f 75
    0xa0b141e2891a04205540d12503100e03503941005c1041507018400c040050500942d203c9080b0700d0b00c8000303810260000d0050031040b50716042d80c800120300c1e502c2415410354844003002864959598941d40b010300081c40078102c81464003142d40c140c05188118100c59183c40180208d03030910318030902409010f0243d820a007500749040001402c1c10320310088000044100041411a80c4c0c2000075000e480d034040d9042c004100884000d4180c00309140100d11060b080040c1d4840d0716001280050036294041013140d40b900c0404140b13001d8081001c0441030380c410400401941c540201400c0f544240d541102040e9407620070000c250090a00301d9106d4002815501c2044d07540001400c616450070032404140d9100805000720070915012120a03510b8800030890380741d1044400740e010302c02c1d000c080e06020900c4a0200d01d580c040220b01910b1481f103060380c0341c203104850301034081d40081d24204c4165080403a40740702c0341814419188104c40007010902d09900760790400c020000044441002c1103031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316987724 1250 316986474 316986479
    0x1003020412060b1c080d0b1201050108030c160f090902040e0a050c0111010203040c0501180801020c0309010e040c020703110d0c080c040c0804080904020307031d071e0b1803010204 79
    0x3001d003005011405120301048500b000707003c02428804980d49030a0080b10300b194640469441419520704680d00080007541e0102440050300c2e00306202c206e01019800c10001040784c0c3c101101601d0a000160200d0307800218140e070070341388154603014904d02480b03000e400700035103842c80c1c0041030543c1c0054400202070404540351402c05200c41e00a6034554040c40300a60b21303581c882d8241035500c864000850850415588880344c0c051584103180c1004060f000e10f001056542200c90010991b2000865440200c0001075841b40c00c05001c0074007203641d610003035030682086c0c021071032200480e601030054242543d40d010211509400d0054225425407080c5001400340d421100291a04a004080b0f610034842080240c401c48000d0000b00402181070100190100040e40c04001044a025849640d0044120028414110071000850100d64007507841d58000c20083c0c2510041c2c4060f5280750342c2e0702c0c0e08039070200c0c8070302ca079181c01e10007040900b0030320307003904480301d002040100054501503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316988974 1250 316987724 316987739
    0x302070611030f03180a0b0906281a060d0c0e010903150c05090a0e010e010920250308090601081b1207050a0303080a0b09060108040803061912060f09020a0510030204 73
    0x180108002c48402061406200800c0409c00c00300f80d00c2843c2180320240c4181c142c00301d8000c011403026844900351500b800f0a0000035100441c410340c1e04c06005a03442d056000e4070790018041c40c04d401c1d00401c085817500c2900f0b521920005055a410500f4105601240710954000301030000300c8604010b4103106070201d039550050396200810741404c510602d541040010055280c0c1a0700c007001861800321440c1c81c4494080b11503000e60020b840460300d032403024030074000c81c5583c11100307011b04c40c3c0c142d031a6003010b03042060503000300881344c100d03040c9a0302c8070021a0f070340d1101742e680f40900402d000e0000c4d0a140ca0900c00702184480b509403404145e440010501d4421241c00031000321707220204003d0005441e104a04030160102c40c2e1500c60f007400030010b0000c8030f014101808074000040040c84540303c058529040004046095420994440014118103500c0d8021503600d8189002200d812103070307005034843c65400504009a203440c0104004590180c1205039060540a100004640c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316990224 1250 316988974 316988983
    0x60d0510061d0625081b1e060f040602040b120a0e0c03070b09010c05070e04170a0504060e030a1401020309011d060708041a01060f11011404080d06050303030406090302070611030f0318 81
    0x840965819070090007140c215040c03444899850000080308412810341c1030001507001d8225809c1030118540341c032641410310180c4526000181c550100103081c4441240301c07402c492048108120803c0050b0620401a0712801c5549696a043c1c0c80510188401880340005104e229014100b586058000e9510941003080035401030503480124003c01050084440d24814545980c1c1c018602d084801c0d040070b0154051070049504200417210b6032219a1000c205503a0081d421414101c441c02102d0402d0b4040d600468141429500b8056480c0c00318400311411840f40d10346001611095403022000c88881c0340040040d03d485580c1041d89060518964405028143c00c3c1d840c1ea021085541d000780c16424000b1300c0448982c034010081400000000b61035820681c040bc256a0792400c00c0c040c800603040a4100a605000c00814801004015131024980702c0c860740030740350710b43c1d50360401303484400c107c10380a00181c1040040c201c960022200850303000524001c0422100000d05455152 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316991474 1250 316990224 316990237
    0xb0d02070b09280c0902030c040e0a0606090815011a120712060f080a030c0311031309050c030402030604121b0503070c05060c0a060b060d0510061d062508 68
    0x710340100042c051516460300b6100c0126000e5071591041d4086984c0b2205800498460514010f03404404609000c03071480c1100e009101e032003c09186820010701c5103008100750312500d07000c90380301c1000240c60400807034203d96000c0d4294485089a1030480340e40c441c118500380d0554842020081c07150000d4040008170701524840d503691048009101d14482220300b03035001811010940c1d0020000484006121030625605213005100c1c80001c0c6011b0300d204400d481e01c1c0c105400042141d070f00044000c40c1c3e4804854404c1014041c0c1d4440d1035524100744019200603405030070010000340456400c4204003010242491710900840905052100000780c000b0100d4143e0000034480040c0820310000b14084e000480386c0f540f41c40000c01c9107075520b0807910001081c0580b5100c4105040e40c0700010340380104403078401440b1303d00e045102a008150315028041c046501c04099843c000f2445103800300d074503400740c9994600b0030008101031040d813450401c0100004192850300001c0d400c180039224 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316992724 1250 316991474 316991491
    0x80406090e060103021602010e15031f090606140c03090409030507021905010e150c0604051e21070213090302010c0306240f050c01060e0a240b0d02070b 67
    0x280da60910044009a141c060714540c1014014401141c110100030903400107a942420f0206059030808040360500701e45041e001c2080602200708644c51714030310101d000c003450b41000081d4994aa014140c00c03100d25014a40025440007040609185034800516040c0a07201c1100d040c40084000981514441c210840006d4400700b000e004600341066a6800700f00c0d1a0360000b052424070000034101c40403c078015114080b1919104072502c10a0100c9501c20b003041c003540c20910f80350421558914102c0c0019034040a172400c01c2c0b80103000440c804107403040e14030300c00b4508180720100c0003403900304e00da05a0744a4000c1002e04841c101610a10074070504c260000300b081c3d81106001f9040312000da00c0101000d4610852a041d00a0440311905240e10ba0610038101245142c5c1140c0c14000d8040000680d880d2803408941d80700c0110105208040300780040c850340c020300c003515440116440c0c40408540b480b00044c858140031030013504080c0e1340410014107155083d00d9001c68143d05440c0c191 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316993974 1250 316992724 316992737
    0x15070b0106020a020a0b03070f030f0b040603050d02120319090206040815041407080c06070501060f0609090f1a04050601030b060d060503100509100c09090203092a0105120c07080406 80
    0x4110704100150f080200365806d842401c2d445d007a840942026461401c241c20036075181d0101245050940c00400104070250080000a1701c82c60016a00c07000303c0c07489805849209900d41c0c40c419800101d03849415001054086001c082024a0207440340e03810403603008806000c0814804410004130f415524491800111424581441801c02480c0b42d842d80840d00166000d0103010b0000030b01900151301914185e41d40c40c4542030075401040c0070f80144080709401d0a002071190703400071103001501e401c00c000304a104106184481190b8000304000c00f180d0880207440f10a160030380c4659032104042c1804102e544c81c80d0001017650380a6848090016983c56091000c0e00301042148210401b0140400c501d05002101c1d40c1d640541540a410301383e12211003000c001c0c405c0e40c1e5500200700c114020742d12410304501d119228000520400010a155414400190506100d40c0b0140c1c006844107403401c40101500500000001c0289441c00d00400540c0d00180c946e5000b000241103c1d544e51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316995224 1250 316993974 316993993
    0x7020a0306050c07030f05190c05100509030a0e01020c0108010627080a030e03060f010b0304030309050a080d0b010905060f0a030207050d09150804080307050913090b1e0103080915070b010602 84
    0x11b840405406000e008001c01880030f184246e140c1e09401440000c1800c020191002e5445c21134035024000c080510a6428a8103000348004008003401206400d5110b10461500030b4004903504d14a5180c070a00090302c000040101501501138480d004020780a5102e1800700101059582c030f4a80c1d0102259902203a5006c080c540e008043c40c0e800c0c2c00c00c0740540038500b018501400b8203401030090103581c00c4008040703801c0501903070110b24610307030000c141d40304502d1500380b01100da04030581001c191401c0031801c2d03500e90300c141c3c080b00075a200280214100215030440b45115008010700d0010726034200300d8130000c2007040104c10000d040c16501c40004904003030190000b009d65510075018450764200344400142400f099980c890781d07501e8200e884114101c00070380700461004204a03002e10b840e0f00c2c40c040c03143c0f9440340c62180120040903c1140c00d022003891500100b4800a014210148008160742c03901041e040000d0341350307003521070810720641c59014070f0350400c1c0c0c0030002582c040540b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316996474 1250 316995224 316995227
    0x50403020307020d1203110c0715050705071806050301050603060c0a0306080a0605010311011404090b01141c0e0a030207030f230f06060a0b030703050c0c12090f0a120807020a0306050c0703 83
    0x2c00350f80d844003c03151410801234004581e507a10b0640219160b000102d01c00c202c5440c454800d8a000c640c2140032180955901d80c0c504007200501440c4145d17184c20018045541d0505004407805444007a00408842d030b80c1807a0016a40c000764001400c0644a4000040c1c180d410020780411074094a40080d15515516186800305a001600c40c14000b03440480492043d4602c02d407421101002c3e80402e0000700303000100e07084405002c00c0e4a0581021407040030550381c01100b100c7c6402c1d401c00800c00e0000400f20302d5a9015040f400030010791002c0b80c2400020b56482008404c1445086c5448110384161651102c00c08080c2c00c001284c0d01c80c5043d00b080d41d000b00051078000c01e09a03458035010742000c0c01c400142c0300040c0f00c0424552a00302280d0030324205021140c1c00c01c5038105552801034012500c0043e41e0000040601c14180d441712203103540b4241c0341e80c40807900103000a003944812550703160801e82003c20180d07482038006a0000100700b050084a225070725a03c280d9558031520700c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316997724 1250 316996474 316996481
    0xe0a050409200a030b1603021903020d0b0f0a0b16060203070206100f05060711030a17040302042019030e07060801031b06080105150d020a0305220507030204050403020307020d1203 79
    0x10b00d2407089503009000c10224013044035094000a0310102c142401410140680103881005200280054984200403286505a01610001140340c109218040071401000004442c42861542c80100b83c182085042103500040120000726800c00886148075190181260000c6441e54096007051040102008054003840302400030701d41805d021604040108049028841000b0300f4011481b4400e0070a980c00c100987c0e506500c41120901480d00b40f2121400d60010710040b4080d50500550f0248511003899880301510302c41d200d5410700507a241401c0c808052454406c0a150f0380310b0301c1490240e4184140000707072500b0748881d040c651451a080c100c5424400d9108403a4244032021300c00140d002e800581140c82c11148030b1005d888440031001103216042e0260041440054080c1e25070ba00f40d04004d100c2c040c0b0551454020401c4101400c0411801e840105030380c00c00a02840140ba159014a82007402072040f603041c124550b02140401c000c00c0b04c00d503002a04908142c282d15414003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316998974 1250 316997724 316997783
    0xc0504050910060806040b010e1302042612130b2208010207151d0609010b191401082d0108010b010c11211209130b0607030e0a050409 59
    0x103500c445003d00e8107100814949015007880d10464940d010f154907031f84601d1255215a60043c2030b840080030010380c640096200744295059103180c0741c20b514038034030501d054109504420700a040411510140601c0541c09680204403d00301c8000104401010101a0491101d0342c40403605150301c40b01d05030340c40a8543e010b00d0b6103a00410840f4002042841d050021011500c0040b8100c00340050104022250004002c0940300e0581040303010003054126501071803042e0b64a980d498103141421035111024050140c0400310180c101c00301c0d51064401550201415110082000240d40c0f010903d4010241000255070342000610a4540a1040b2459240c0c242000300d0101300941d2070b2180080c0e403c11040c4154074803024a001c074603400301c0000710b19400e14241c5501c0b1110a44031011900940300150081d02c1d001141841d1100500c81d84490407801800d80341003814554040310345542c05204290400411940080d89071039078050300d92440e1250000041c1e0026459408550f0920b10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317000224 1250 316998974 316998991
    0x1f15020a0201080c07110d020a120302010902040b030607020a031206050a080a020307060509130b0d0206120906010602031305040504110405010b0a1701030b04150b0a060906120605060904020c100c05040509 90
    0x1c20100300080d52020511045d59410f60300041b01e20700d08c2c00011850301c00f5030b0040d85482c5514078803d04043e0b065004064003442210100321186005c424182e070344e0342c110f0700200568008030300e0344003080c02102100440302c084030010549503100e0000c21101d102c540d0040405a10400030b070b8045140038400c401c00782026207807031030420b2507400c001000c819900100500c00c0b651917a4450aa44400d80510056030300a03212681d42e4426400b290000c21085a0000242c055240041541d80c03000c41101d0100e07607013441145d851030510040000038800030b4400c54070321000c0249172a09403907601a0a00808186c10301949910030344038050700030440c1c519280303c1440d5547c014800241d512000c290065001440c40a01c03201708064032004100c18881070b5440349038108005032443d8071081c84401d0328880da49035011030900122071020f4604901070294410001d11103203e039801c107a400f9154010040c01203411480d0410364070000c803440c1401c000700065001405001c2800c01d6140707181c00c42d20a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317001474 1250 317000224 317000227
    0xa020118080d080a0e0c061b010603020405010803032715070c0204050a05071d03070911040305070b0d0b040902010c15111c060b0403030906180305010c03090606090c02061f15020a0201080c 83
    0x6c0390025070350344511100c90700903807030100a60140407002d50204014582c0034108100c2540c54414071552034004031506030038088008018071441200310101110b08100340020011841c150f0341005c4014401030200041145098065001d0b07036a90051030700036140710b4000038690410401c0100425240700d88051980501d44020003140ca0000300902143e0310003400055401000e046e01c9810302c240d80c0050312510942c0d80206203105560000c0281c201c8051003085060680130501c000d94440d00c802070301080014050001141a071018221100054140003800062503e000019134000d1000d46040344800104821210028490103001d0701c10b00300000d060030301d140e40080a40f000c07802040e0030400c1411240c420b50401807500320103180c0c400300a00c0228000000100100b603805d6065400034100030700002c0041081c45142d43e13809159000c0e004c6541d500c100311010b90041600840c0c01700e2548800646010b030907002c0e0500102c55405800c07509500d00004104e00006840c2d034150020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317002724 1250 317001474 317001493
    0x5070e0a080706080c03070203130308030a0c11031206030c0a260718090609060e06190204062a050f0609060f4f0203100e0a020118080d080a0e 63
    0x2001301c54654441e0307499921550769078030303150120705500440381c03414408200450007104012001015501c5520004400c00681410980441e41c07002c1c2c041c2090034582007000f1754003900c4409580c04e6480300003c2c00702c0d04526010404038142c1c1b4141c0d030041654041c43c443c4400c072881120052864013040b10001d049441c100311880345928a410308190801d5941c603802010088030760804081c082c0c10036410064044681401c40d140c2008494070310300307410904041d0001003803e01c2030f1415a145503881c00051102400940e0000c0918083c40700e080074026440c200203036040001030701e2407514402800351400d1410100b4502a40a003444e4001582c010802410105020889000e603030703026244660100060001110742c5214500c0d8070045001440310140c45545070101d16002e4403e070110742c5945441c0c41810200c0b403001d240c40e00d43e40c0005800304095031080160441c2d0b0024825403900855940e00d020340b400b15107e10071004120020100914194a0f104811000040e940600311184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317003974 1250 317002724 317002727
    0x9011406150412030c0203011b020d030e06070f0c050111040501020d02030c12211609050108060d0215040e040f0b07020c0f04020c07050a080c040b10090311040e0105070e0a080706 79
    0x30b502a48002110a00a41007414403480d5a82100c4e50050b008100d00a10310b443e5040401c1003020700d8015110305280304001a200c0d2260700c036000d002202a060782c1d152420100d07003480c2c0701c461000400c146e01b01d1404c085902071040c007802c0d0400e0203c0e40d0361240750500280c2410030203000c810030340d00700340141c3e00100d00c08074130454250507604590f03644006030303400c10201c1c07242c2c42042840c1c41ca10804226034991010810002c800c060703110f40f0728680d42c41004460303001048546540003002c46042c0c10050a20303010a49160112091082c2855281d160341203130400e0448090f650342400b000244240041400030a4009082d480989404007609000c903181c4680100440e005644c00960540c000006001030800307420000c0002c0c1c0c00c06c0d501e47c5100e60300c00815410502c994a82801c4c1c0340c00e441e01c0b040080300d142140d12000e6195155846d08800940140c1d0382d10340080c0c0ba5140d000300b942d001e1003198405c1c1d8503521840d103146010418070013444000d810103410355003c004207000c420f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317005224 1250 317003974 317003977
    0x180c0703030902150703091e030302070e130b1905061c020904020604082b0504050a170307170d0501080c0616020a0e04050307030822110411030901140615 68
    0xa03815040119452080c2e1000c02c1d000d1410030024411440003003240e404169021640c901151580394940051115240c01015035a0181c40003c0c0076030300210741003003042c240a034041d0740440d51000d01074002c0003548a0840d060401c9a20081d1007c4e000301c1141410900d05c103d0343c2125080d50303001050f11807103540306906100c043c4064807130000103000408541d2414110740c041c1c02e1910a5461648404080700d280100751040180c40d2a12442801e054a200700291411030720000d048a883c50b240040c20101456a901c1d074890a0104200100c04203060404c01540102ea50b21016585c1f5414500c0d601110410703007102400c3c0c2c001080c1006940ea5060a036078488096840c07401089c0510700c0080c1b81382d05258801640344591030704020038414044084e04491307000ea00d8610b00e640d103880e4846503e0201011080c480307405015030201040340d20444107030005d00904005020042102980416002100c4080d8a40c1d100d00d45112047c80000c012900414162185d0351000350180b00310307429 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317006474 1250 317005224 317005237
    0x528080d031a180a091211100c0c08030408190807030b040501080606010e061b06040209091204030b09160f05030d02030405060d0203310c06021501090e120c030702180c 74
    0x282804030022a05400841d80b0110201b0340c80700340110414109078019248486484601e0120f001d40020000249a0342c0200c0041280d955551200f40c40c1e503541d418001e0704054001e6072a03110074840f00c0303000e0300002040b0700c0001c525120110140341c100e5008058400d002807880c0101c0c207001c010011000d000030441d410038424207040080312072803404a1024090392204010b101c0303212084088649002c14054010ba0080d00c80741419581c0e5030b50a40ea4070754081c00400062000c00081000c12a003420351500101680b0a840140c02c00d0740e191b1048610076041140a5080c08604100310314041003552108003403400a142828940000505203004c0c1441c0c4100c20364000001900d04407240d1642c0c0316060f80f4010710707140f81034103102103040017624400490b841c0000e103002203034403400065944031400341a070b481400f5a080290110107040540c40e400001d2041e05e10001c580b0000d480649150740b203000003140c42d18168010441d400000070312180c101e580071018007104100c4101210750 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317007724 1250 317006474 317006509
    0x1c1110020a050c070906061806120510030f231b060901020a050703060e0607030e100b030f0304060c060609020703090603180c0e04020f010302030601090528080d031a 73
    0x8a40203541002d031154856002e080d0324900400d035000c81c0e24800c035840401555141ea460420701c00013001d20000214643c0125004144044402400800c1c16000290300038186007100080b81d03034079501c0003101955980119001010261b0341050700c0e0340c40c9000103078003e00f80001c08515000500701e0700d07000b829150290113520001081c41c02a4000c01c104ac820380c0c0d00c0821a064a5a0303814880b00500c05100108018000c0b0750114842d94428040d0009038400d5074050f0042c1c2d00f91000b050024401c1c101c4298150189245420003c04e040c800f510087c040d40d140e00008441c80c0c0783c0070040b07601541001c040d2030301c140300341400310760b124680700e042e00c80b10b050024040d0702c20080161022800c000c0205244900c9102240f49840440d04a014602c01e0380c0c61011940c50324015810b80c08221045400144860b20410051401c0c00094120050030a09140d800f0000d6002d4002a0001e801007a00c540c460011044500d501d8172903116520082c2540902d0810300d00c00188041084884814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317008974 1250 317007724 317007727
    0x6070f0f1709070e09030d11090604090e0f0f0309040f090309060507110a140306060d2001051606060302010212040510110309030f060105040b040902030c0d0816051c111002 76
    0x3040700d1000c00100c00944104c4003d40c0a900e040022550b80b0340c84103441002c4141001c0d41d00704400c904806581544d00001c0070b00d4105410401c80000601d400010202544545c042e100070301607081c81003c906003089009140e90710001418001900e8100c5000c2148601d06481c50002c2640440e07500305444041c6000755039001c0703d04098a106a024072403642c0107415990010344843c92200c0e546c5400c405800741c9186595410412000010415002d00f660003640e80c0a0079240450b05c1d45074400313a050400c0d40c06c01d0010440815026a4100d0440d0309641e1001e0501c1035680400401341c0c2011001007403450181480040380c03444000618403c180094001c00d440c01e000103000303403981100042c04441c84000b07195101130340d8400c01c4c404e1a000d1854145240500d04250250f600b5154000d001400141b00c11018072810700b010760b0041d07450400c280410803445000581c80c00b0964021401404100101c074241d004028400384000203004ac40b00d0100c160070f00109100301c071401c0c400d0005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317010224 1250 317008974 317008981
    0x1d0402130c170702060403030e16182012060307150e0109120507090e010c090314280308060f03191b2402010b181003120206070f0f17 59
    0x984034002d0640c1206103540142c1d0400110135030014009105070302070740d802d0010703000d400e407900c0d02c50142444845980b516500e06029501107140f400c01c0b800d51101000030b07010352030301611102d1450010f50741401040000c40d00301070315210646982003d000c402030300c0c0092400c030468096140450b51a01030160300000e00155038002e1003108020440e001c1d00320442d54041c5042500d90f5054040e011100d0f103012a405029903051003440d0007485c00d80c490303018450441c3c40c2c00c0c003018003c3c40d030074146205018101d0f001840200d020321a48000e07440d9125201c6041c038010703003440002000113000b400150100b001680e400a1601542c0114140368202c0c0305503070a06d01541c0d60b607408041000620781c0c03400a0f419a4034646000422400d90780000c1030320b01382c901282a82e89000c1100c4c2e100e4800e440841c4102821501c161300491310740076039420300e583c1c0d5a0b8403101104a80d030340c00141c3c111008000d0301035088617603c0003240c00c03454140d90300340d05030320080d105480c8045001043c80c03041e17001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317011474 1250 317010224 317010227
    0x402040207020409060504120e0f2224060c1a06030a05030c030403171306080c07021c02090a270602070b1005030f03210402061905041d0402130c 64
    0x11260082c0d009042801a605a402c1c0712001e80720940d001c90319904461142450f81d4454094000c104d000240303014071100c84101000000940c4e1261040d00122031840c00f503100d44c440c0f00e0310b8500d950003001120141c1840100d00c4402c00e00d54000303420b12401108100015041821140b0a4005528404415100d5a001ca440c000e040d640c01400c40c80000750004082e040000a0001c59100d41403400501c0302141c161165802400100c0f903002c5091130080c40002e0250680303951052420903184c0c1091400c4e00001d51008000c0041e40b04540d086040d0015420306d0f0401c56070168101e1020f000100d00500c0880c000405149810903200c0c503050200c0802c11950125191a40c01800150643c14540703891804d40d800381c4122842071087c959450200c003008410344605100d000c82d03001c1c41da0300249489080c0b00e0300600c2241d11031010031480c0c111703c0e02600c211171a9200d40c1e03200c0c0d0303d60f814441000d40701c80c0303c2c41401c5500c103003800030400143d4510300d10302ca04c4c0b074075600089000b03100790343c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317012724 1250 317011474 317011477
    0x80a02010213060305090c1806091f060305040c1401170c090409121b030203040302010e0a0e180c030a020919090b0405010219170f2703070c05030d0f0804020402 71
    0xc1c00b0b2200300d00358100041555142d04201d014080c5082a00c440596070303000c11522240d4129440030300000c0b030001494070700d025400305a0024424480201c803420310b191105020340381e03401020101c1e580754140402d00030b602122a02520b421140fa54000e0842000138100341d02c008101e06030a541ca0700060800d0703a10304241e40b040390010f0020312601041c0d140298440d081441e07420001001c20360409000d0f20315401280405401d50051887c050840e00119082000c08e44002d03007080707503c07200045c400841c4000d42d03c988034103201e000009640c05852420301c0f140000030351080e840312240d0801360303a0380d00c181c0f604580c1d00318011401050310803210018006400001d094901490104002d1000640050611520b1842200d10740c1c400480c00303507000503024418440c865860300004203107102000c061600301c07004481d4144401e440c5205042200e552080340c00070380c0c1010401e4401c20481d440c900b4081c0c45d00b00c0c054080c0128401c0003c24920300c400100040115000100d020345d05e8590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317013974 1250 317012724 317012737
    0x8071203021903020c0f01050402011d0103021908040b06190b0c0c030d0f14030c0a0e0f042c0d0e01260c120604090b1801150602070503071a07080a020102 68
    0x140d950781c04100c00080a002900040d100d849207001c6d04402d44031400062140604c251b605841c1ca0850400512003940142c240c110798606055023081110b20004840041c100707065900c0d03485c1171491515191a1005a00280095006090f010702c511491840030850724255100a4491b50711f03001110102c2d841d21020702e14445d05800354440440c03144d6817000301c0000854041c0c6424030b1100c0811400038482c0300480e03101400d144103000c20041d481c80340702e080041c024001c0c11b0384400d00311f03100010704941a04105241c054034000710362018907042c0508aa1001101c40906461704003100080c0c40b8030003150300302d410498054144840c4640c413481010101c001640c40704418501848084199800600d0065241c07000e5000910245000d0144040140d070026804d85030b62510318600100c118008a8203889540303400c50440001050040403004101c507600503c140da140405040c1080802e80140300d0105022020f6080c890101003120110b680c4034009680c0d603054810102d00900410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317015224 1250 317013974 317013997
    0xb090613031a0103030215070e0103021602130b211e0a0b0a0609050c07020a05010807052203060b03150115030e031303060c0905210703080403120e010c0807120302 72
    0x3860940e0030078444078003190590388a5022902c0b40c1c40741f03080e060618003088402c0750006061503103808155220b50041d2503c8070b107030308100203d03914550016034044103541a40b034a10342c0c0c0c0c3c0c10060040c50100b02c084c0d003941120104650300d09450701d4260726408513406403440d0888011122401e04c104014450381c0c03603004600041c441c10030f060b04c68040d000d03c4c810b02e040d441c01c100100e1440a00b6000b11644558000c5c140b015a44c501300042d6050000100309806210050003108207050b1030703001003000c103108a2040b0754054254078101084842c0149001c0c060f030f21850701508103005400f844d9054030010462605420710700c18049028001c1c00c40c2050075400042101c2141c650790510780303010303a441503400307100180e4078880440f01200c5a108440d1301034101d90290400c204c09610740e40c200070706442500c180e6521307900c882042d980705900403a0f031001e4139086a003665500031272805054100342703051122007aa540361b02c0443d000f101c4010b0700006a40036215003280c02a8119441c81c20301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317016474 1250 317015224 317015243
    0xe04050a0f0c060305010522110d11070b10081b04020f0d1a27060402090303030f10080d0c030509030a052e0b010819091a060414010b09061303 63
    0x440c42c00d030032450070600c0f031980840d050000100e06807510018824800005100c800d0034a0000501e64001c0d251044100c2180d50040107650a03640d031a0040340c0b40d070044401c0076652801e0501c1d0100c8103501c02401080c0e08000d8880600440402245510520404050051228000c0c80000300213100e0307160612500d810001e9500341031642900819042c3c429090080c0c0c2c1c4500740030a11031144089210207811042030350205140d0100d1a560b01d400120143c0014109941d18000c00d10303551090781d03510008010b00e0200300a5190510301c4070b0141c00004043c160b12041c585c80509411518400201406004100c02c2c3c143c1e202000300404090b008000c075080c0800400040c6000b100b503c2d400031b40315101681c04c02d480b600500640340c3d0000c040c0e42d41074240d1740e00784684088880080020132540d86030161503000c11070384080c2510b2810941584046824030000700012944e031880304e00f10f01e00e20180104207c0e90030074240d5500840c00c0c0c441c3d550700c86d250349056500c2e1403a900700a148030070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317017724 1250 317016474 317016503
    0x10203071403120a0f0507020a050601060f020a0c0b122404050411040911010f09080c010509010210020a030515040c0c17040812030708010512070909030e1003200a090e04050a 77
    0x14181c10010100e145a0410041601e81807c12a2103019172280074000f98400001000024480c42200700004403904c10759030400c20b0380e9039004400722251300c016000d10003c00c6001450401210040e0040103544a03034010340039030602c810180c4041e0b89080d11a541c1c4800080a00c11001c4440c50702c040b009204106202c01e81c60000072100300c0c10035003400100582c0a1200d5140581c0d8100281d8803403400900950010600441d81c41e0b1014003441c2c1180542000c0e00c2c2110000e00143c0710550045d10049020b01c0c3c403a85201c5010819000300b0b02c21030034590740010035030300311941e012641d4010b02c105000c050301b80d9580c6154803c031362101c1c601c1e00c61a40f10028561711000954050282076070b4000442e40d8030000c1100107148480c41c02d0b00c58112100400807580b5590010060f1440783c205103400079039010000b4920048422a0004a43c40f10710032003070f0041d6450407010440c9454030703550074608041c070000d215005901880e03040c01d01d440d020405100c410046011403e80c0300111240703140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317018974 1250 317017724 317017741
    0xf040b0c0703031803081c0b09010f0315020708030604150f090b13050f0a0b0a090e030a02010e0f1f0204050607030c0c060201020f030606071a090123010501020307140312 75
    0x39020310043d00040c800c0002d0f005145814102201180e400500c500d0600b00302e01c1000c2c1d007940b000403c14a04607520442d40e0142c0d119030800d00e000788030741c02205400307a24604090744006071400e05d00b030240d841040843e0019100009503504030b6020703640041c41408245c01d13421301c85040d4104c1a44880e5800c000500100079411a080d410000e81d91400c15280098001098031001d540c071441c03181c2c1d24000640f0100655000840712500107107070300c030305030343d18400c980803503404c4038140d0207940000a44418813a0240101c1c0d41940314280244a401035840e1026190340048031844e94043c0700c200030a44d01c0030990151809010001c000c2540c5191030700c0d020304002c04c1e120381100e6903444168002034040c0107100391540746101c140c0d00c034039590781c000c20030015500c8060110b0703140c4903000440480b02c65030b001c03040c803618030704000186094502d461380b0003825100060058106440300148902d99010060754501c0d030740111180068500040c2c0b0501b03501481140c10100c0002c20200404035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317020224 1250 317018974 317018983
    0x10c0501050c0d1104030c0b0d0f050f040302010e0a0210050a03090c0602010204060f0206060603011710060e090712110103020c030d3809060f0f04050903030402010206010602071a0f040b0c 83
    0x592a400c00c000c0141070b114640c031a4011440098207e103507035501049100c0c8400010a40c50b02d01701ca000030000702d5003002070121841910641d903ca10180100020540c09101d002901640a0003c220800451740025952112450420104000404d8401d0054000e800c031109032075216006080f42c2d07403607000c003e00070f400c240701e2200061550f84400301c41500206120f80240700140503a0318681c246107410291003440c85a40c5440d1040c4200c003000c8010340c0c800c24010b0264002540ca481c102480e401e03251103065005214404007083d0f007207000a070340c50001a0184005e080158840061060030b6080d03002d01c400c000c07101c03402c14000000c20785900381c1c20121b451240304004188040868500c00c0080c40300d0805800c01701080201d007541c5030507498519604001400500c0355410f01d8080350642c0c0c001d5404013000d52012040c84112b68050190ba40500907502c003c0148034500172100310b40d0704041400d5003420740002035100c0c41e100d00408403400b070074240760402d6641e2281203460f0350f038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317021474 1250 317020224 317020237
    0x10e0613150207052b0807050a030c0201120c05180103180b06010305010902042313110712020303040506160c0c060f03060f05010917101509050703020a0c030e010c0501050c 76
    0x601410101160624044154019941c0c41e0300c2044811039900446417005c8030450800c1e21120020f10100c03001a80400c1100c103018829642c280c005150b0b4800540050418041840440d003480380c3c4209017940802503038062124405002040e0ba542d00050b001000d50000010fa0016540d80381001c2c00301d8051316900a81d801e0760200001d0707a0380d45401c7d040303005901841031081100d8005036003060f19001e0b4010941c05c004d00341c68038400c594030110110303400614060907110020400409212001d040032034103440500246146103800d584050311101e00805800100824581c413088880c8a02181c80d5129805907107041490703100c00740a8000c881ca040c1030400607040c40c0010468030000300f62802140c4c0180c40b000e5020703013090000a55a44c442c00001040d11a000c2c129130311040034020000c060090265410a950402c03c0314001c0d17440061803070040c5401005248e04c500c0c1c1c8001c50b85080d0307405240611034408414012103403442c030f0030340241c407035800d210900002e41e02e80c5008044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317022724 1250 317021474 317021477
    0x30108030a1715090a0e0601080c0f0402040b0a05030c040b120a0510030201080c0c0c06072307061409031e03130609360e0109150218010e061315 64
    0x7082542c038030391070000c80085800404501d54151107030310303d0030308000c2c05401240707191001c208107020380c450515001099210001c2e65000070440d10040c00c091341c0e00340035014180c40940c03030300c0d0070950451013511402114a0800c0400000601c1d0007465505a80240101e02c0c541e66a800342c408000c44403500a541c0b80019502e0240411004088a0b603850100d03075045e102e80c174041c0d030b6910401c8007640000002c159907000d4001044610b039200700041c038407240f08280901d0070402601c00c0301171000300b02d0305001c03480d4803188007445122742041c00900c146c00e0340d00c0542c0d601c0100101082c00c240391211b051030300460381ca4051060340400b00c050942642050310b1900225036609044601c00304520441107105070510120000008441000001d40c50301690380100d0311025a66408640d0030350560030090350740d41d910000304000c5c0d028840c4028000e09003076040c990000300002c840c804480c4494180010110301030401d40302c0b4829552184150300e40c0d446074075038404c203070254540c410001c00c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317023974 1250 317022724 317022737
    0x5010507330609090b060609180103050607030c090803070f02060d180b0604090b162003070308070e0f090406061802040f15091205030f0c0c0901080d0e1e0303030108030a 75
    0xd143c0c00140b29411180c0d801046480036511850140141540040d0005400408903801c0943c156010f106650007544507000900842c6082d00005085410a040304010000c10101c1040101c00c0002510b0305d00da0003120036500c1000d60710001d0560304c2002000d0410b5424180081c00c4a1950100d0441c03140c01980580d44640e034040410007220700c4c4d443c0080c0b12400307200219a103080c003081e10b00070710400b030b062070706400141d1980c1141d07075031b8401d40c8100f00e584002015403c0590120725960086a44e0601102006c03030000054450080c0300c24950041600c4400682446600e4200d1002400080d8080c486800b0048001c4042e5003e4020005100e400f50000921000f911105d2006101265070ba0301e5100d0501c02c00c00c0d0200703030327290782540c00d44802d0101c1000c100030800203240e446400c000510100701200284550040c1c141d001c2d1850783c101a6040d48015000040e4400c0703500120b50b001b0300400000d0800f86505024541c903901448088004161010000020101c05820b07071681c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317025224 1250 317023974 317023979
    0x2030706080912030405010e06090a060605090606030408070501061716140d120509032410080d121104030602030f130f0f020f040e071a0310050105073306 68
    0x81d28403180541d202c0550b540541c0369082c1e140403070000b035604603105500100300300081e0222645800f00580705404503400c5038100d002006890311a0324003d150558000d8114900000043c41e140401403018145090004030042002801e41c85030000e0002d0000c4803102c00c003410440307503645000445032440a82081000300d02040c0c0f140484501440050240800c010a40e80310030310a1141d40010307040c00000d03c111142c0d9a824040c01d41d01c0c3d00c18408903a82e4003500703041c108100102500040300060500d40c203104060010854041002850400d908400d101c48080347c000d10034103001c050302c40303008500402007002c2600114000c4011100c00303c10764507000b000280b48044568024924021031400300c000032420f1400d0b00b61785000030081c10610144601043c02d0340d031486181700d0140c0000340e00388800000300003110842c0d048122000d0862400091103800c00c1c41d1030080905001010440c54108940340c5501500024811b110705044000d000d921810503545030079220310340e400c01c07401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317026474 1250 317025224 317025227
    0x90a0803040e01060c0203160e0f0609042121020403050d09060f0c110607110a12020d0615080313050f0618010309020f0301110705010b030307021f0207090f0902030706 74
    0x980e025502c81001409040e464000d0a0742c8907441800c0480e01030213800791240310091001c95402c0140440f0310017400e5450500c0c20641e6a000044c403503840741c0705407401d01001c0b5041e440c100300300e0000c0c8440f42c006c1000f482c10035205000001310704c000c485080f0000d14255503c0e80c010304110307480396085070140300c464a000d5994142d140104000164a98184215184140c0d40c2401c0c644c007400050001c421484086030007580b0001048d11000799a00d90b090103410940400302c024040d03480d011003c0d0f80d01d0390014003022001c14001c0d01d015180d08090310000c030f005c0c481d50020600201260341d9901c0703034290400f0100b22441858420f002036007035921700782004401c40302021441031a444a0a10907001035000703007400752050303030004068581071100380ca00f481618002c21400b2070741e5032a41e410346405403d403008404107600a41050120b03a00589410080c102c0218a441c0c04848901c01c81c00100d00e00041580109246400c240e5141d246051951007a210340f4004e5041c1c0c0c2046483d90300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317027724 1250 317026474 317026477
    0xc07060e040629070309050607050a12020318040515030d0c03080f060604180603201c050309090c1306030b120d0207050d0203030903060705031009060302060304021512070203090a0803 81
    0x911032600d040f4064001c451031200720040c4003840c401e0502c5481951a8404034200350815601115240c2c0080c03014400c0c80034440101ca4000498801503103444900750013100100e10080103540a280c640020544459519a40850040d0301804481c40401c050034028100c00c4030403029004240349002090b00d03240b02040c0c240c413440f8048d01c41803030140b900c69080906480d0148500076035603510030100c0012041090b8103480c40844101c03480a0441404009540d414802409042040c80002c40c00081c008010b54465600c1100c21065030b644082c0b80d80021310800d620f5041c0c26002c80c0e80842c025070581d01c003000b4400260389040340440002d02c2244d94403c0d419065015a02200c8c04218600d40b0103198804a0300c0541902d082c514508082441c0c448250341c40c4c1c01088021040015202c000703113070100203200356601881810300e10740110f20703148000303840603000701d08450b0204800608441200c001c01c400030f1454407680f60002c130094a80d0000c0c00c11034400c250404001901200000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317028974 1250 317027724 317027759
    0xb040302030303060906011704030f0f09120f080d15180c0c060c0507050a110301110f07081602130f0f0213050d060e1006050312120601140c07060e0406 67
    0x2001036146481308810800031000007014075041048002d6060702014840701c0c0d10f03014900c01d40714200607010208001c1c140b181007803034400412041c40420401141c0c0c6500c02c01b0400c0d0008280344406505041c800e40f688241400382075503138204070004001c07000c80c0d5013080444c1c0d8104883c0c1044008801484140d80301c04210200260b40b480e01c0780089600c1c4d600090584000c2d08016103000c80554481d401d042c6219000c1d00c0c068640380041c403007403c0a001c4c00717560400c3c00c0c1000780362020110b445d00da14054048080d12003c00400d640c5411050503a008c034146400609880710003281d00c1c4118045c0c40d05100c4070890508104080c81212894000e4614281c140e249130628103040030280100c01004500946100c0c0e11a2050b2100c543c0c180204603c5245068001c21024108000d06282c181c0400f1103030031120007000f007030180c82c91030800c45420020900c1e2041e04420b6403001000076000340c0f000c4104c2070182140008107140c0000c0115001e40c01910203102c05a59104007420101524 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317030224 1250 317028974 317028979
    0xc070e06090f060906031e030c060702070605040b0921030309070e100306050a090609050a050c0109031a04050c03070b04030303050c070809010809071a04031a101806030206030c040f0b040302 84
    0x5000301d80b081c602413030001c1d4060005800c444a40c03000034005900c083d42c0003101030040d0000141d0184001041c0030103544001e10740001c152075450184e004007031b4450707031140041040000c107440c0207981e0740d6403903191224600bc0200c03200c0000141c1c881e490303a00c1551842ca2520030040d00107100c10f40c124605228205200b1080e50680c03035070310303440d01505008199505441e515118040040d4441c840c0d20b5040c1d00520003411a01354505e405494010010041070501090450410000b0001041e11451101d05500421103440780d02c0d044d841c00c0342c1002010f03814010841c1c040380d100021b50147c000c42c6d01036079042c001600e5a412402e880c4c414a0300141c040d107002c002e0403c2d1540549101c07500030000d04115252540c0e9084500c94003410f05041c02601240002e0420a010001c8081e483c102d0380304050790b0950034140711026845886224856050cc10900c00c2e40d0740700b1280d840302c0021034001e03111554034640100c1c4404954490b01a0015041d11000085034209200c81030b5015254007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317031474 1250 317030224 317030251
    0x60b03190b19060309050102091309031403040b011511070312090b04080307030305040206040e070201020a0e121b060d020408070302010f17041502160303090507060212030f09030f0c070e0609 84
    0x810000301e02174554414252007640d000c10603400a900c42d052140020900391100144002051400910648a002c500a01c2c1102031040c080480d07043e0305131a04444113510103644181c0d814006541c0540300e02032210860051010010911071800d41288224074295180300312261070700d03941c4c542c5005900455001c0c0e8820300c11480002d000380d2000750814001001181401d603034002c03844a2507130444403100140d4012420070411500b1404202c200401110154018040280440d996040020600c0700604007034440c040d5540b14a41151405402e1074000d41d80c4584400c8181e58a01e482d10040f4001009803007039040e854400c8144a1316445070f1044001103031140e84520540c805034449070314440e07508009803469040903102e8074161911070f40f4049484e03912030800300c0c1003003266800b03a025034221410142d40490700d5030031694011600c0e81c11040d90f8542c03070742541c9140900c1c01a03c615400005405640c000d000590100301ca608025210940d5110400d0052501084d80c0c2240001007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317032724 1250 317031474 317031479
    0x201140f030a2d0c020d030b0d0201030c141206030c09160806060d0203043002070303050c030c0f15012301031e06060e0a0f03020f01050d060b03190b19 67
    0x46030b000204150b02d00d0001249150303800e45035810421450003c1540c2a41c0c46500c1a92550140f100e80d0b10001a801c0403c0b03c6905070010920040030b6050090406540e18003800105001d10807190301d01d01865202501ea0b015903103240c01900c0c0942c2c07a00d21034800c1c88107003c1c142c907120452a102e00c1520b02b5407800405500750680e00420701420703442d8000f10612050a81200c68030145d48114020200314015040445219140b044600c4001d10030b0360039440c0c010031031500050210304407075052502c030f07540c3c03200c00705414254040c0d25040c40c150b000c0c1150800b20340d20005500c0c0304024034210003070000d036070b10512800100f50300d5900584040701c6540d980d41e0b44d8002e50003455159851800743c01d0280451315854102c41c44c40d080500482c6070030070400c0740748c200f13140e0b0000580702201e0300e412403d05507000174001c1c031030311000541003200000d501d00c0404a1030700243c0043c10802c40e910f807a0700f0510030030b40400c09800a050f10701442c250f4418200c1c68003090001c24400700c209801c442a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317033974 1250 317032724 317032741
    0xf0e07051f110c0607150b190501050a0306050a030c1d040209010608040f0c06080a060512060103060510030501110a0e040c080106030c02120325050301032a120f0201140f03 76
    0x5100c2600a90b140c02405960842070700d44100410109120315600248060710641c00340c00c403140d49407280e024624038040070a01c0d201764500707002520710174200341f515500034001c201c02410881e00300039004128080b002007042182d0b4016230a41e552000c180144a5903030050b061000001c4030041d520400300401007005902464147da00680188034100c191041612020481d51040e0b0011001131080020000a05082c0c4905000740030221452200311a4401c21107a403140c0c1800083c1c1491307510000709025001001c40c490056a020b4001d120905141112200e143c0121f11a04042016001080401d10f454031524507a05c04a840c0c01800c0d0f400c0240880c0200312032200441988590394030345e804014814061072048264221088a1500511420303c0d91000e4101a00078040d05100502c0000e40711152503100c800c01c068004510041078144d1384154806a20108030701c02c1c00d02e101e40c2400071244098144900030380396510441543c480488452003510056180b0040030b2010030f5900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317035224 1250 317033974 317033987
    0x70818040b0415061b05060105040518070f06031104060503070f0201150f050a0609061b0c030c09020706050f011d06040b190e0a0b0d03030e0a060f0e07051f 69
    0x104405000000c050070200049001c580c40140742a00c4140c28410810800c0d50040300022a4481c2c414038200700f2840341d4541d980c0b00301c180541841551160700086130032031040308401c0c050301d4842c00c41d4034683d81e0302800c8010714028084c0600183c1045414110f11101e441200c0881c0c0055071418915512501c08980c040d0884010900f1552030b10110094169403000300806003a4204941241c203250404010f072056550b80a4004e01c02040c000700708050704003507000e4220741405a019241c1142c5d10b4034111404164200424076002070380c002c264400d16601034040944a500104016294113030400f1084509110700004003029100a840c6c0e0455084002e410410141020a101d6031200c0040e8800c0c60720b141180e42181040403c0001c01c079400905504210b10210801004010102140310f40071048006424035840f1a2441c0c0000d4080008861301900074108000405102000740d0140100500450140c82803074004940da20701800d225203140c00c120b00c0055000001c1006440d503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317036474 1250 317035224 317035267
    0x70b0a050a090803240405010509010611030c03040e2e090902030f010f020a080708040b06220f0e1b06160f0816142e020d091401060b0708 61
    0x1c0d54641d0701180c0050042c4000e14094061100508a1585504141c2840400b080911032044c0c0c1004010825511403c0c0e02a05495483c60005444a83e0104141c907610031403401030740707030700c00007a0001c0e50702c14005031103000785254122042d00607801d0241500e4502c0341d10351100b40030546841086900a20350120b10443d00c06400e540007120301d90003050844401f03403d444512a00000c61501ca41c0d44407032050390120244c20301c0c0b9034a080c543c548a00c6040010a4a406102d100c0d00b082900300844000620010225506110b0b40240c0c10480c8054003820345007076941d102d005140038490788024608044e1100141182d8286440c1d0041c0400e44280b2050503211120101c0120703020440300c1c0000e00e00b0060218a00000c0741c0b0500d00343c0000400b014201600f5000f0b511030044802e4a0203c01400203c029150020542181c00b00340c002c5c0b2640800e01003640c07408035544100001e0091110402500c500200301d450741e030300d044240c288150b14004004c0d4504110380c00140480e100d59404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317037724 1250 317036474 317036491
    0xf030c030e03040905151207050609060c0604050709050c0412110402160c05100801080316020f22111c021c1805070602030a020c04180c060503150105070b0a05 70
    0x325541610042820360f40305030810a40c80ea12441007280ca00b00201070f50303100020a84000c01c2c1c400c941d1a1050303c4004078014188207910003c2d45031815500d41081c0d4048602000c02d440c82414140b400c0c6684111a200d0f141c000c81c1450001144036030060295030840e48944046070b070070300d555a90f0340c5054401040803903025900b032003990b05c01d03501e546810388403c1c03045820480c02c41c00d0900704019a00c90b5000f0504020395540140580400801030711510784080380b0350074001c00c040c400214010200d0040c10380000c4140d000241180d480050008403481d1404100560f02010300b1501d000d214554040b0213007540703000c00841000351a401010405055414105c80401002903c81038503410642c4042a181c1000310000307000d000e100e120000e01240c00251b2400c880000c02030340301e0b460540424400c3d41d0752000e024036202070302001c022075a84411000b85003921020054410341041d1200c141d0840380e0000c9000550041e002c442d43e154016040056503034500e9100b801801c4020907640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317038974 1250 317037724 317037731
    0x201080606070507150e060f090d2402210708161b03030603030201240b0a0e060a03090c0f080a110d021807030b04060e012c070207050f010507030f030c03 68
    0x4003240d41413044c1d4000d01070a421a2030a5092000000c010951342da482c540314810070049000060310700400c9404010f8284c0702e2405060241c1402005800310901110b013441200090314040301d52a40108802103484140140351140c041014421000c11142c58000c1603003200841c94200841d07843c1c1d81603c032285010794003208454040f403004820303801d049000c2601d030013043c010550203000d03e00390074603070420b86082613403c40150125a40e4500c030781c80300070500151034600c1d50302c40c440340052990007504450f41d4a00403a0700078010180e6004c01d8805501c6010007080880100204401f21252140108034148658039201d450040341305682e03500c428142c07440310058660413a40c000c1c0d480781e40d003049100e2920b91400743c140c42c1c0c540c0f00700e4032603440c00b1401d0000c05403031b0303000d6810340b01e00d1078003483d241c6004a40400460024446c0c044000c0c4500304000c41c00740d00203000001c0d1070050f200e203076049081c0c07001950103002d008802004141c041e20352180041c400d50082d40000c0c070500c0e020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317040224 1250 317038974 317038987
    0x1202070b01090e1009030905151e090a050d0c03170309030306102006091006080a0605040602070215030402100e091303051c0f05070216060311120114030c1c0201080606 74
    0x10703c11210700005c02c03404548552010001446c140745241c0d004a03040d410641751110841034044104c0c030701c0411141040d0042822080d54442801c2e0401030034000c0d14000c0007a402d8144051ba0800c40c5c8070445181070a00000603500fa1608160380c06400820019030070341d11408200280791003100e80000801039140308404808401c511200b200d81c045a01a00e818101480c1040c00d001e10b03200102e0901d4101001002609400140180141d81208000407140c5462500b00c0c0a03206202000e036015008020182e4460002c0c002540114400c8031075111854181b02c06550070070b41d0b0340900d50301040d4080052041030074051100802482840c00c0d81c50218417800c002e00c07014900d2542158143d503240e461820b11440e12905822440c1400189044117400c0404000c1070141d005003001c05450b4010b9030a20b03810001910304a81c5a504060391640e15548172030100140d419443e071203481031043c0801c060030506c401d110043c0320081c070441590095001900e440c80d01901c00c940280707040201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317041474 1250 317040224 317040253
    0xf0c0504080d11010b04020304080c0f1606030e070b040b180102060123030f0d020c04060b03040b01031202010204030507030b060108070309020306010b1b0304030302010c1e080a0902010c120801061202070b01090e 93
    0xa41c8200d10840ac0720b0f071903d0f00c122105107000c901c20131520940e070040c03607603c242002050600c070480380203140224150003041c00d82803c00c1d010354000d86c90071402107800300302030b0b4516020f07103003206043c4021844012101d004a0ba40e00c020b01c1010382e4406029042201410a4042031080e03580203000c4952001c10906c161b0b00e01030804c3c80e00f40c0141c000c65100e0200303160070301400700188143c0500505604054072907525841042c8801030602101103240d1003424000e40642d4001c50300030b002c0d034a01650f0790610220344007040b15150300240b002400100c81900074403030140207540140041c051a801e000003102d02c0e9100e4441a4214600404c00080155080005001540c402d50000c10400c200d0100a41100d240300301e03501218170076242d61440180e002207006d5122a04030b01c08201070f551400181c1d42c9090181c0050910a90150003088481d0041031641c1206c0e26662062101c1540764028012070080c84402412224810010010100d85801ca001c0600c02182917035081d07a0441c20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317042724 1250 317041474 317041477
    0x100309051c090f050409050c01030504170304030512070201090c0b09040b0a0f03030201050f091915020705070f08031204020904170d050103050c04091a18010f0f0c0504080d11010b0402 81
    0x3004000b030b00c0d1000c1444000d0480c24140e005000c00c1d41c060240881c196161500c4481110b0840e041680e1180040c0600074442c103a00034042106042503642d00b09420010101d41c001007140080d1a900808903000340c4c8140b05003822031b90041e2072040076900f402d00c130748079a41c850140340e0350160301c64490240aa45000d00c0d400140903038180d6150b028907615001e420349400a08000a00c42c0400c200328650002040e0010a036000d01c0b80792452003502d01c0c043d40d50a1807451801c0035540b010428108005000800c031082c0da49218202603007958a514044d540d00c1804000314400300e035040401c00504101036510340061180381c15085282441c2013901c010b4125880001120341c444004100b8010140481310558505a500380f10b15405500c0b44070a16990090841004010078002a2101c5880342d030303804540000c100074402114903441c0301000e07081100841007030515000625039858000e50843d030456070340f14041c5c110000500000d8400009007211500d0a54844c03502e0310081e6601e10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317043974 1250 317042724 317042773
    0x801020a0504090c0f050f0f0d0c080406060b0306030a062c07061d100f0e0901060c15020316081008030f1809091b040603050a0c080f070510030905 65
    0x903107880d1140d10703001400c2c003a01c1c1002003940c10700200103110b086a6510408131038403c09110803940d565005906039111034801d03508107840da14946004c02d408698040d075418083d0f40149800e018042c1c070b074091810644400e96190754981e1040620900180076034001d40c4480c900041160103001c0908044106001402d42a8009030400c00c0180034880d000070001080407090405001e0012401d0301040009406140b001d040c0702025034010b030007510419200c151444003601c40d409030b580d1035001401614246c0001c6580410904000d1108a103038420340707114180107a05084071200000c4140d40300030b40544000210a01e00001240b1044208000c2064a18241680f0b80e2020040d6070596120f121541803482821000180100d55100059945000201d0107144030030440040c002401880d0030350000b0986e00604d0030310710038490300151120841d803034201a1000c220413400416210001d601a0310381c45040c425400c070015200b030340040082c40c440c1045695600310320344030484990148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317045224 1250 317043974 317043977
    0xa150c21031e020f07061e110315220b0303070c0803040f080d02060604020306010306090603140606060a140a11101d010b0303120402190b03061f05090d08040801020a 73
    0x4900782690150742c0a07445000c2c0004040860400c0c01d05022420b0521914201404076505d4485103281500c40640403801282c4004003003000c1c15501208031020b4004580c580205203108690b80c465041c110203000c407103002c82018410810120708148028141c00819039018407007032000344009401c1025800141050b000210703211031801280c3c4841c813103644c100703c40c0c90704840f45035140c95800084185c0c11100803103015840742c0c3c40c1f00c0102c0040006500821700c09052050010501140940d9000345101100540d03040f41d8604051001c28400c4e44510750009043d03081180ca40c08580c1c010300941d0106160082c4c0d01e005c10780588c1e28010080240e50446682c03640751724031118640f8101107405240760000e0042004e124000381c0c0701d0250f5020450500e40d907900080455981183c840e820128003079400c46011b4660303a5800003a041151107500459100b03ca1120304141c2c11805100c010702c84d03556034500040c110500c8100d0b0f4200404544c1810240408120b043d000e002918051003103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317046474 1250 317045224 317045231
    0x170a020708060c09040c0521180d2c030307081602180603060f0c120c0f070308012d171006120501050a05250e03010c0804050c0a150c2103 61
    0x100d80801c401c40c0da842d103106d41440010070000920380300c0c040b03800c41042c1a82450301000d50381c000da416944851902c0001c40b030302402c8100c006184d08030343c00f85804140040c3d07681031101c111ba4102c1d0b0f40c0811460166059209200050025001000a0000520130584c3d0388120000b039001c54071b4000401201c21401c41c50000308015410100708640c0d0180103080220b105c0c1c14542c4154a1612a5011606880e60b4590010320019108411907100d03000f0034401540c0c0b49803a04004048400038043c1c0042485134420a40c0c2289115100481c0345140c0d16100e0407641c0750002008410496841081c0503008a52100190406920442c402007440340c1210701e030a01d5038503016003124801421884030914103c140300100d4010300f40703064200c0c2d05d400c606030f2006010b841651410341c1c1c035a0159140d030904000641c6264462807882c0250703c81e4040704d01c501c1e08078041150004103800b071a455120b6810032004400d200e008a410160b026904100303100146503640145610030305c9034407010984 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317047724 1250 317046474 317046487
    0xd06020c010c0206040c050d02010507050a05060105030f01140a050a090606060816050403170309030c1c0e01020c011211070c090c0810080c011d030a121b170a020708060c 75
    0x100b03009000040340c2d148042c3c40c440c0350a031b460000d14101030040b5405100002c15100459014000f181c088a4000c2c0403107510544618141d6a20743c1d090054500030f00070700342d0300c0202c0c00050140c50146220040b0f0700201e552148030b600d0003001d00034042c000c144e03101e210f10380200303866108403406000d5070380d0f480c0120b280c00b00c01c485042d10000065400c1050801c8208003203203520f41c4101c0521100c14095642c0d0b00c54030a00d81ca140a21b5000404901600403004d1400840c1342203c10f29001580f11314500c030b5555401680c69543c04801a8007040c03803281526441e10300d581c048404a010000380307a0424003e910703031810703281558006207038282c1d68200008402e0342080046901540c13842005201505022010380c0318018610060f060cc407510300401d030030948001c44030360304240c041d0481c0c0c2222035605040c00400c0581d030464000c2150580948460309200d20b0040308076400c0390074a01e03429140d0100081607401b2218000031402140e201080303118042c0503050069865840c241e407600d0703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317048974 1250 317047724 317047747
    0x6041b0f020d09080c0f1216050310020a051c0f0e031b0a1502030907030614040332090307050a030308090c0a0e0414011d0d0206010b07020a0e04060b0d0602 69
    0x100301001039007800340d0f40a0070000468009001c1450160031b03501c1d14082c41c50080414010b901c80591407140d4000c0c0680016128402c40e01141114000c404039054210004009400c0b4403a0007061030008000708031405035200301d400c0c2503c1c1d0040000340050340d0000c804000084815005c0380170f40c5900300190018080c1e4801c420004203603805009012080441d955101100c900b1300c440286c115004400600300703043c01d2198000445d0010410b1020030001400201c0080d42200c0c01c42c00f00301d20701e0640c041040c2102ca00021101a950004840c01c0c0741c40e012100303900281040d517814400c3c4032000c59a40c65039804c1100440c0302e41c5038406c42d41030201203141804494401c071801415007600070040115112543d40e04103070084071404040c00c04444142c05042c103044025075a07002c0c010001c1c1200780000310740840355115030030358469036218003d00000d8481e8200195000e00c0300d08003403140b09a040030007600320744107540000fa60720a400109060415280c0300ba02e5490303000c02d641c50480e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317050224 1250 317048974 317048983
    0x10509060d0b1f2414090409030c0b16021932070b0a090302060f2a010b0d0f080f0409090c06030b010c0b010e060f04050901051008030a120506041b0f02 67
    0x28000c0e0500b12a00c01c01c1e6041407000416003002d020308101030085d10700310441d1140101c0324505c2010b00103220000b6581800b42c8481d01c002c10407544e1005010001d80e48400300710700684c400d4180d50181482020490090300c6c0d1140611054540a041840ca505c81c8061070030441480c078030308104510400160020107041c9a95648007250300603080190100580e40001c0c5102030f01c1c0c0c100d070107070b468500200d82c0d90198042c0f0f8902c02c4c5040d640568500c03103545402044030016098500031701600e15a2000c0c0020443d0158000748283c0d50070400c0710006030b101000e03207000d00d04560f520f8145071f548c0c40e45e002610405a015120050545014084643e140c003d09010308400e080c041038059069a911840a10510030a003071800010007240c2c550303445c0301c0c20700c47d403440041080c070041c10001d501c24000c140958907998000c5196400042c808004800e981c0841202e40f42c1c0c03075001c2e4410407110082c20703008050030b500603540c44442d180560210720316021185e46903079115203035403400300c0070b85070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317051474 1250 317050224 317050229
    0x5060a08030a09050d0c030f06150f051e010e09010e04020a06300f0c05040906050a050d06050403031503080d0507090b1b070521060106080f010509060d0b1f 69
    0x60700100981220b0541100104084030001e9a100c1d181c0c400c5802c00d172980e101e080c0c000410707111440d9030000900030710303400c82d0000504a4008010700e030360700d82c1401c8105c2020b12949800200f80129445040443c044e2001209418140540c03942c4401000038071080098001c0d0424940100c140410360920b000c1c0e0301c018200300d007015650702030511102c039900c02d046114412000104138074141c02c042e4541186c040b035030504409101080000001401982060042240452808900152625140c0c450300100ca5001e8200060003442d5140c2030081e010040080d0141501e4550400541c208000c0c0340d00110b0003400069252420072a00b2410340301d0103006101008401102400079850780002c5501000e2010300c140b403140f075008007850401d0000e03440b107a402201408149401080340c110450044100400d03a482d0343e80b0307103a095406410558800096100610052141e410400a0241c002c08004d0650f26628855568000800301c01c9480382908081c04080034058040e00980034003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317052724 1250 317051474 317051489
    0x60506030601050a18090c060203041404180825030f030c02070f120c05090a09030801380d0f06053618030d090b01140a060f030f050103050105060a 65
    0x1201d525201c00a014440340f8015400c07120240c03020204007540700e6200e0040b90f43d07c0544d0820b103a960300c0d0040d450783c0051040d0305840c0c04108103d00a40740500c500c000701c41d04030002015042c40c40d2941800f81d00a018442c030f140604800b520b80e5000344445502c1c0d4640300ba594686040e1110310010140c44140c40c2c0c600940d0711184061143c2c0320704020389016140d501201c5404501c15040465050301d2a0307101c0c0e03030080c1c40c9000380600a03585401044040b8042d4942000c1c90360b8407049520b151050000c201142000060805040c1e14080c100303581c980c40c440080d81c2060655402c1c1c01c221012542c0da13554039551140200a40e080030000c086901448080c010001c08001c1c00c60540400152039542500d5205d00c001070004207820814080b41d22031404980d1110100d003840d81c024003169030305a440b840c4400000584549142c044078103a40041c20b180030f200e03c0c2c00b40c160390700300c040851032052546a0071084003c100074806c07980254012000807540f03003421802e00440c2c0005800005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317053974 1250 317052724 317052733
    0x917130f0f1703131502190c0915080304061202121024080f06011701060903050114240301020f070804030c060206060d0308060102150406020c010b2704080c060f0406050603 76
    0x10f14000105600840342440c0c090790300f201768610101e0401d004480768007401c0580c401030f54240901100c00c030041d113144007408c21081c031044030040111040e921801d82c4c59402040f09100051086040703100360048444058100104014200340031a01201c40000c50220f48104126950710038126000c0460403980e0072054140282c2c008019140c001c0840b00d1070401c030004100785900c00d946032030550860314032011403940c48000c02449030b44607201c00e407030a60038100f9030805455618190350141d5100b2903180b640302c4460352020064001d1501047e4155070070301c504c03030b864642e40004207856885500580d075590704519040824401c0c54000c5007c65000c401003094540fa8040d0789107043c0c2c1c060811860310790714000103d1074101c144108200d003911200500c002c20019030042c1412031101c0009101402012082c00303200c2c0d45182001c0144100381c0080000c2200740c4261f690424011a5030b01c3c41c0c03202881013246096019590a80b034800210200303c2448220312a0a40000e411800340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317055224 1250 317053974 317053987
    0x90c030207052505040216060507050a0f09120b04060b09070c02040e030a050301030b0406020c0109030e100f0503160e03070f05010815090c03070e090123040917130f0f1703 76
    0x1074020624010340d0b0117030b030340055400d19000c01040742c480388070350001d0180043e00d4240f42c02021500004152301c0490101691458601e0050408600307481c0386c038918070f600b0308140d00c3d400f0050301d0150094031055514052035607035403a4004041c0c0328030a25200c0250034a401e01c1440212000c00f10b070107500f500288080000c85030701c00e048030704403500448010702944481c00c0c00b000038401c420b101040e642ca0303d2625000c1540000280f441403c044030500d00d1106114400e891411403040030500184040001854840152159203901d031140e1400110702e21680f00828030303000254000500c24006440f0400196901588040d80405207024070b62494150714085201140054080381c80010007200150850307104215015202000400c00103c070f594803040c0000308900c000601c3c1c420084500b15491070f0506014401d9555807203240659450380740c0d1703011400c94000a64035420400c20300340002d0a102c243c0e0442e0040c1c007000307900708074252034210f05c0c219415125800301410341045c00003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317056474 1250 317055224 317055283
    0xf0c03060106030c142a030304032708030426070303021c12140106080702030c030304110d0209070305091921050d020408060108241f090c03020705 65
    0xe15044807031500300894101e803244815550580030451800d0f02c6400402c0c1040400c8216400c80c62602e04210142c210240848215460b4801140d000d00460414800340d520003c119060442c860441134126000a032034280e094195400340e44904000c000860440602d0f059624410138030500ca407000f8001d051440c0d0300a9115441c0103400301c5a0301c500d10f62607251a0107284019451115000d04100c10441e00d0381124582c0c20a00406002510602c002501c2500000c1100d0041c4242d000440c116074071a9110310784041041d1b03c5035000019004128016290031b04802d025032200e403000714030b515101e80b40e00d107080c11995403490903407113007103401c0c011400c903255110901d000c3c6402c500140035000e0094846115807960665481d10000c0c00142090001c41c41070f040c1d861500580d8130f40941004032030011001156021090a03612004c50900c00f03034880040c00110100e1600e0300c0165075403a0103011100c4003401a40481d80000740301080210920070300d1400480b0030b1010205c0b003015150b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317057724 1250 317056474 317056483
    0xf021c0905070902130b0c01140a020a32270306010b03040303200414040b181801140a06150f020606120120121501050f030604020c0a140f0c03 63
    0x300703e4030b1030780041c040004c5040458003c000d00400504103540d2951044001d00034080004154039400c10715000c0b55403031816001320f407004030155803000318130800d034101d080740f203030075040041c100801d034642c03405035168030602030008100720091a1028400c0103030740212103ca1107400c0e40c400d070000401884502800710550f03800641510b000164070842c0091910600300250001c8841640801c0016103a10002c00c03c541c41d0314181c5040c41034a800c4024044000c54800b8440d490307103403001c005407800d20461005464404c01d0000072031a28414440c0c2d01c0c8901041d246020450b44404061041001401c407501f804120341c03400321880c10380810003c0d2074900181100e031003589010a40d03a40e0f40d009411194801040035030382c503004c203a41c1c0c40c0a12250320401e1300c0e80c1e0034520301001445070010808800304420068580c940381809044a4000e2a48018041a44035a00340030740700a640040100351032103481040340b05601e40b03900d06418a04110300e10000c455174060801080315840120703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317058974 1250 317057724 317057729
    0x60304031b0506011712030c0409051306051e010e040b16090e0a021b030c0604060b0d050f010b190503120a020111031003020f0603090307240f021c090507 68
    0x75054090509010708500d16440c4084081c00620509001088a02c0c0c4500040b205843e54030454440080c11049510306000480340900f0811080c0020018105503401450b488042d014007503c1d402440e0381c0d4241103c4003aa176400c1d0234041e244403160341c8c0704203403d40c0c1d016090f05084c4880d5440e00381c1c1c9426040c2070081103201d181042c1c0e01c40d4500240030707014600c040d20240089c1305240c40d1440c2640c000b07411481003400491141040120152000300884220602d183e000c1c0210b42d4403501c2e10409031001010300d80d048491640c880b400301318113015840080b10b0702d500115204141404101440d0103940c010b0b4284491690200071581c2d00250f40040c581f0590f5801d0303198490b44038141d004000b100c01e80702d0038035000420401c1108003500b011007074070f108503100140704480c801402a10f0000300c40720305c0b00364400c21155000c9071491031500c0004017807140c0c14140d82468080c507810385041c4040391102c2e80c0c000c950107540d2001d8002249000c1c003951410481c5102c140c440d6a038503105803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317060224 1250 317058974 317058977
    0xf030b010309150902030705030f030306040605060403210e060408150c090a030f061104030b01032a060810031b05090903090306060111161203080a0b0a05102c030f060606030403 78
    0xb00704400031901d09007d20381c01010002c00748c80d820006404c4803130b200e61003240e55034031030380c580040070400d49081c409440a998021859200c0c3e015414111005801e0307145007001445090440c20605079604030041010f4a1400044d0860803800e2000000c01c000c082d0610550380310030311131035032311741c84040c2c0c080b00b260742000100804083d94100240202014081244072207030020300031083c80003a08071507040b80e12400440f1034040c14030013204040e031941342940060316124101000f01c070740326102c6290004849800c010b046175a1381e0b1100007104008180c3c03062851285010003041c90500001507205400002852070826500300190b1a0b030001050241401200c11748440922000c0025105607480540c040d000346445044207102051440022030014629400084241c11540a282c07400072028041041a80c01c003410424420007441031101009013021824505c1b40007228644001d213101142c500f42c0030040010706052450b181c90144c03055200d034060100a0321420110381e0b21a03010b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317061474 1250 317060224 317060231
    0x3071d09010308190306090204120b150d12020309130609110909040b071b05031c09110907020a05030f0403050f0607080109050a0915050609011205060a09051c0f030b01030915 77
    0x604030145c0041a06400058003544041400729107221400b4100030418004e100c809030507a03071704c521002e100100a107245e402805810981001481c94403c584040c201030040d40d09184c0103001007002111903800c207020040e105c50081180c00b016104128902010b00d80c218508002c4030701149007813401510050442010f00006600e0510600c1e518200e2950f0a02482024680342441c1d6070300e4110407207880081c0e0300b07802c0c082c46045d954814019070580c04030381c072a840b400c0c0400700021107070001d1103602540518015200000d4040c0001c0060b03140c00c4400c10b89440c1142010352034100c01c1d01074a011640705805000659030044142070450700c02110101d903607074544103808064500c0440c020a000d2025844d0380c8014110f4014501c1801e050395405003d0703981d05200481d0700a0381c02c1c0a803490b001a804500d0ba4050368101961160103503003102c0c00441c4908609141c0070002441030005060075114605440d491f000d1001466803d20741848654000d8403410907100c0c00e10000410150b0f07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317062724 1250 317061474 317061517
    0x2160312200601450b0a080619020301031a0903040e15040f050105100c051c0c030201111e130810020403060623060a02070302030303071d09010308 65
    0x81404041c81120050665240800710000341699510702070207104004482c4010000320144507403031000608501030744140d50910b01d003011405141004200100c140d4840019500d1526004005e0b0000d1080310010304103131130f140050810034624051201d82d840d004100410100d0141200840301c490001d003001c080340c0743c07108014914440c59009000140c15801044040441000a01070a1300251360500c040708500519808603402401500d50186800440c02d81e064030031618265024400d000302d5a00c440c3c030340c80001008100b4007020000442c03c1e014602051760a0141800c0c0f154141c0030382c0d080070641e40c04400e0417a40707090b07010321484d0045040d01440006105480062007140c007079a11a07895800030741d01035031007808140d40c0103091500000360b66185404100082400080110041070f22008010300d5034090340c09601144202c02001c005a5800d100541c09801140c403000300caa1248941b2410011700303180da651150b00311b84010004500d040c1c0807501c0d01d102041022070b0614 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317063974 1250 317062724 317062727
    0x10f0509040f0f050702120a0e040608060405010b0312071211030d0608060709051f180317030f06100905040509070801180201111603020609060d0c1e02160312 70
    0x90011120703070103802c00e0003540d50400603034880880348040f07a41c14440c5507110602a03036030303138243c1100707003c03424080114100092281c5241b5880940045c004a1000d03130300c500b014070b484402d480555469540300040381c22031500304816903207814494182030a240700c548464207072445a1210710103000403801003001101d0103004840034400381c010b00308a6a5203480c196955100c00b21051404154054000305a03450a0340c03201000350b00000c00c800010001400132181c4222a40c0351001a20388228048001440d000e203c0302c0241c0c00000c81078a0b03180410320501a13207000f0346040c4c0911a410012a011070f40f08425005a46d8169070200f003030780720184003903d05a50340d844950300e54602502c112201100200b041315007030007640e030614140600d020540d240c1031104014883c280c519042040103043c204040e00300030600501150a0506880300c040988203441030100014004c50307152241c036271030804c500283d03e449100401e00408200810441c412079800082d0221606540305032086 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317065224 1250 317063974 317063977
    0x803070c0f060e0f0d140f1312120e04050105030a12020f0114090d03111803010204050d030e03070f083a0f020f03030601090b0a0c081305010e041a010f05 68
    0x6a0103501044501950001d02e42c484e130000104205a0145c409030941446c0300c0d0708968a8243c81c20516842c000c00035000e040d0310f0303000b525001e60541608100246462545444030801405899007401ca0300d6400c100801041c40140050b200d20320341801030045403000904140354a80c80703a030441d02c40f5881601279103070891000c1001200d42c2854088050042e03080135940c0603019003811103440c00407440040d419a40c940f94a01d491110a014902c1908010700c03101c2a143c1015000618154590020030502d0f0428181a40442c2080210010f5030400b040158000c0651220708401182084901c94070b6002c040c8484c4640540503840700905c0c0c8020030003104421442e203100080d03400c101d6000d0401806244404094000c141e1030710104400441141d100314416961505018100f821090851700b1085000c4100001d41341c4140c005424a401041d0303004442c0c040c0701c1040d1a1000060107525607008150240d030a000c2c05010484443c3d00780ca1343c0c81402d00304424402d07180b0b401102c89 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317066474 1250 317065224 317065253
    0xb0106081e070c11101d0607050c130609060603050411030703080a0c150c030905150108120d0f050106120c021626030a12110c060c031515130f030803070c 68
    0x80b40522000346905c503003003004c0484990400105a1101c451b020030800306004d1010701030320940000c013103102c840c42c211074209046e05c5003180c0040d2061719007680d41c0880e03107160840360200e0380e510f092005004444513440e04200c1c0840091220b281917541e5821280504110700c02030203c00b48039402002580100040a0040700e8410030544403805c0d002000f8043d41803045d40e450260441d40010120b5103e41603041e6010341e8014412501e8038980742d440f035070005442c0c086103176a071203c651500080f07004150003400f4503580d96040d14240d100f00d40c01c8941c0c500c40c15041d5840661100b4545812031015000c640e040c00d50310012405614041840c00098483c1294a000010740484010340000307240e0001d00100d20100941102c459004841d40314045007601144c2c00840040d036a4a5044000d5500c1350a03445a070400e8035099000c9480c010720321030340f812001c401140250711908407140407001411a00b0090780000d140d52034000951101034100801c118440c00387d281800008207071003c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317067724 1250 317066474 317066479
    0x9040e0307150516020601061805030a240606120e24040b060a060e04090203010b03071d0a0606173303070b1c1a0a030b0106081e070c11 60
    0x2920807661070a048980902e2955051007442c00340400c80da0b452407100f61070f214840c1d0700101407a9080610680d04a180e0071b49100d0b0710f03200140b000ca4036840503c00d5104a40c452140402050044c01200b2442c0200c0300d001b90415148c10400c0001e0340d84021802c0489892030000942e620501c0c8a69040c0380c50010199450403c080c294a01c10203030311480c522071405250124100d4070307910104588104113228090004009a0585102c0d04d0705070302c600c00640c401000019032000c150f003ca824036081d5881100c401e2a600030b40200c401d01c5512a692044070500c0400515041500140c42d4400c2000001d00507240040025000c14800510380401160f06401003510011814544200024010003a0081c002e03008002094141c0c003003516815039503820501c80101c541f6110b10002c0090803195060b103109001e80c0c1d03410b030b00c1e0071842c0d4024501404140c001c540c102240030301382540150640051000715081034040224803490650440c0c0d0780e140c0041544c0f46e6041066844040c02000c03035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317068974 1250 317067724 317067727
    0x180912110703023d0212130e0a09050706020c0a14210309061341030a060f060602060c03010305070e0c07140106050a140a030206071e1a060910060509040e03 69
    0x450040200b8224078411140e402c0383c05032403440201e60098041c2ca40c0361203100d40ea40e07c051003000c12820b8030355448025144001101d0046444403403030100c503030348914003603046980104050f0a0512a0342c000d01000e040601e411250400498495245400c001c0c3c04c44050101110101034240200c48404100410f15501c50030b0400111a00c1031841c070841c11520388199000440007462040507069000c40c01c1d80c2c3d5610f25204003840c1c0814203c24406916000d45064080040d100344159040c4103c49107000a07510304105019180880160540c03013110001e1004100107500050760409641c1c11060b41040d5440b4850500503034000c003500101070000c994200010044150b201604a0380c04651901c1460b80e14102c400300b0341520300c00d10f5000a6a2102403002d401c10000030028144250fa400b000340070608528548a802440116482421052000030300342c9040720450f005401116601c1950400102888a040e494415002848804291510750f955154004203180040e241540d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317070224 1250 317068974 317069059
    0x3040905070e120f0a0212070f0f030c2310030e151005010c17030c0f0301090e01050711060708040212121207090e010e060a18091211070302 62
    0x42c0042038058070060040000840340f0751081c41c002410000742858901400d0819450303000c1c0040f00100c2110722070944209100020811501c6040c0c800403c0712403900c101003800d40c40d183d0180c13840f0b41d028109502c0c000e540c0c0780d01c1103000000a54016400c03a0402c110034007403901580940060b91080c0d0040c01451130250303034001c2070030b00107218822900c0c102c2900f039143e00042d1040c4161100c00760281095903c00c40d00c02c07001e000119004040c402030181000c01c151103da80c0382c3d200760444401d650315a09400c1c0c040a0034040d107500840705080c81400c115002c501c0c9a0b0310f910090207401000340010104041d0b440c2c5900fa03030b800e00044010380d80000b000290000d407a40c040c40080d40544554000100c40d544100d4550003a6404821007440d9646441404145404040c00e030560242c40100300203401031840c2c00b0024130312207100c0040351070704039400d0503407280c5503601040083c0060140350511020b4089040d070190307941110308195508003013142d909408219114400d00d1018020390 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317071474 1250 317070224 317070227
    0xa0509161e06020d0f1215120302060901140a022b02040812030412050d0204050a0f0e0f0411040e0c030f061909080f0d090f030315050613030f03020304090507 70
    0x5107085005000954445a0b480b20201e0f40d03031403403005501c0060b500c042c5100d02c1c14414015100755400340d00010600701500e14100183c4a0b040d0b0210000c1c0c072072410202c00b019010300038103a001c1d40040003000808442907880382920401001c03c01401e600180070b40ca5000040e6003520800260a00301c0d95811015004c0402540a03004000c054482e0170b85101444902004883c460741d07010030080b02020400e6000e880c0303038010505016074243c007031001145545410300c1c0e0000820b1811079410b800da00c1c6c03030070320b40c5060b00280c02e40502410079020080400c400540c840102c0700151000941f1030b502682207410300c0c41148009916000d200c0d4880040790f000150b0b2130081420843da03e002070070300c842034030865222590050110740184210350b5900e5a070805003607071061990340807514440701d640d5a000c5804102c021008255109e54607a0207040050b020400380405452140c43c00c17003c000d410500031442e02c07008055840030301450080510a20030780b0000c0980c0b400500c07650074407010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317072724 1250 317071474 317071499
    0x141504091a0a110315060307111203010f0803070c06080901060b21010b0705060f18010e0601090b150d020928080c06212a03010504140603060a050916 66
    0x2c2d00c141450800b46141414000c03101124084e0841c098580d032071340c0c080820f1006c0343c1c20040c070745400d100d00d0800020500e10240403604010035880c03001c5071380b1b43c1030001351014042c0c1034020380c0c2c1d540d100303019043c0000c8005105005441e01d0381400205a52200c0d0624090980e6401200d0185d5000c1046220343c0081e00800d0780803042c4484041e5940e0300c1d600030291074002d2202c09805988400040340c04044040490b58100d012551184109001151420f003940c05141c12950150310aa0040080070480d104441c0e000c00106c0710030ba4091a01c003101d0506014030306140e20303c59400900701d102540c46c0c050004210a411301c00e45240c2d0aa0407124121140b544241402070044022a107024079000d01114504140103040411000b000700c421290203200903c0c01213001c00801010190812181c140f003102c18070346003a13a55170740c1040300b03100c2500c885d8030301541b54070702103000d0120680e4086000360780014a0b0314001115601e0790101480c1c40241e140118480c981e1100129100340707001c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317073974 1250 317072724 317072731
    0x80708060703090f0f03090e150405060603070f030b2b0501111215012d09050d081b0709020a0305042003100b120d080108060109141504091a 62
    0x500303480c02a52042000c1d001d03104858001032801c4010422540041e0411400100540c0249040d408181d15015213000c0c6100036515280207410907181d04031249401d0042e03e41c401c00580b0143d007181812040905407884942c00941499180c0070580010703190b01341c0c4441901290305041c507044c0802000040400c000150541e025401d101d0f041c1c1d90a0504000c07038035045554100d40c2480e80e1026200101760140004060400984e00c1031350103443c043e0180c11004038079404420801180800c4040c0805ca920762107a03014140000c0c002003c1031011701502e41d0030b901000030700c1032004011080e034104001c1b80c01000b000e9101060f903400c015410790001d4419882401000e52200346902c201c02c3c8404414002945070380301490210603003205801c8100e10610141a04080700030b80003200c1e0a2a0060b000200010b080384010800721800f0080d01e4010080b01d141008008500d20310300d00c10b00802400c1c088031007017044142c081501d83d80d000c24035560700450010749051a40386e80c174561880c181e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317075224 1250 317073974 317073989
    0x2031c1106010e060d0f0305270f030f030703080c07150c0801090b2d09010e0f160e0108040c0b120103020102010e0c18180f01020a02011a1c1104060807 67
    0x80700003244000403481d00034050440284840c40210141c1d942110401c5100b104500304802070010301c88140404454182e240300d00100343d07910301010811f10046141c80301314188682d10080544440c20808070807a000581c1500d402e14280e520040300441c40d20426100800340811410004030091403540718a520140c40e83e544020f03a640c89200000b40c691850340c40d41d1080d08034284600c007190005c44c034000300c80c280c0c015483c0814040005030021009a00884507000e21104000c240181403100300c1c0d004d618040c401030001c42c0c0c2e040050a50b5540ca0901e070601c0b9150000c1014082c2403540700c801008105012655608161000b0040260a1004901660a085103c80600804100f00642c044090460151404285100a14180040c044440010540c42c292401e08024014460714201c02c43c000750356200a80b10003401c540e03041d0241c0781c540c0c0251000e1a0300c6d9580030b044e5103100b41040082c08034022075040c055601a40c024075035a020b450a100020080e0000c50000100c5460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317076474 1250 317075224 317075233
    0xd080106030501060e0102150604060510080f0601180902071a01170c030d02300c0d110c0f010c060e0105100905010f050109060f050403061107110109031e02031c11 72
    0x35901301340e52942507914420701680000303918440f00c4202c81c450603803000e0014808a119030765240841c001e01d060150b8580052103005c20400c80410540742d050700003c00b0310b40030340700c1e0040d403911119105c402e004401d03446800140c40c0c400e00400700c2610860420511100c40c041d6503990188984001d241b40c641250f00481020027554500810309070008032a0b03401500b054180703400c1c003003508032610b6907500051411401d003000860b4094003802214080d40e0080001c5464000c3c00780070800003a0440d010303540485030312100c4e070301c41e1405c4109210302820103418141c0c041c40c052001d0305403194071503450f620f41020803520b103041c1100c51040b00d00500b01003005980310910101c1840c024000e06020030704801d801c000c418841d486440704881146462402c1c00d4036503032140150b40d05407815200c0300d2400b1803541c06005810140e1110b50100f420200207103071640c2d0f9403084d05a0401c01c6003e4004201400c00159141803050a44015040316624555030740c000c0081c2c11081005d0081901e80306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317077724 1250 317076474 317076479
    0xa06050f0906010f0f02030c01021912090c0b0307050d0c09150207030b0402240c0d0905030f0601060509030f060901020c0c15040b130909030c050d030606120504020d02030d080106030501 82
    0x146920075034000c42c010b03514140380307161440c000d64809191004503000c51104102a502d181c00038409004141055804a079010300d0765800105500c402030034070b400da140703015003100008040b15840303801c031601b2161040e16a0703201041522107004d240b405040703080c10040042c2c60981d0128a6406a4003014012403016440c07401c12a0b445c00d150000400d4400040b02240261600b0380356082001c150480c0a80c00b110709c040303000d031690040d0202004ca540010b145810540c3c0040048028100c01d40003051100c28401c24680d480b0410311840d418410001080e210740c1d03e01b031004049000010007110007900b0b107140503134000e6210780f50b000a81d009040841d403583c500200034107594200d51146078145418107d501c4690361014940f0794901403440c8001407030042d503015003400d040c026103e0942124540c14668109101004d0310300400d480c15005000054000b80c40c040c1e001d07408000081c00d40d031580f01107440c3c030500040207581032180314403403034426032b2100900e4103842065405004599 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317078974 1250 317077724 317077729
    0x1209030b010f2718050c150c0303060111010209032a041503031b140d03060e061509030703021801152604020307171006170d050d0b06030a06050f 64
    0x7101030040b4194050204905802d01c54441c0d1445a80c2c07001c800002100c10070003941d5104c1132900c07041141e05400c85040915145043c150f11000c0c01c0391440198a8042c142e0460382c0c032403100800a60600c0002207500e000d02070254143e900c01c02c3c0140884a407142d00301000d0440d0503d0f40c16400c03000e884c0030422740720307810319015800b05e26503410552140c0c40c1c00d581d006d5502c10080d04462803d450610310900204d4640c1c0c01024140d400c0e98050721174080d4050008041e6441e54021407103900e0001e0030700c5020f4596a018004103081480b2540d1524060030000b0b04000f03c680c000703035101685a852100c058806d4001c6812550441d01141060000010940d2030145906101c00e80e94441c650060a042e03102041d594490720050030b480302c0d640c962203051418895480d40103115880070f800d00c006c04844d4820711014101c03a51000160041560982c5c2d62040f1360b181c10403c021000c50264491400303601b007000c00030f0008010035143e18040100a0080107035205591164000101c50718050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317080224 1250 317078974 317078999
    0x2a050a170601120f0f030c050a060203071e0f050a02010e0d050310151b0f0609150f14010915080304031a060d020f0405070c020d060b01110601060807030b010c1209030b01 75
    0x9136441a61007801c2c03078440e1500717114003400000590a1040300c03018a4000749043c054202c1d424464200142c407800d00c0f002c01400c45010708400e4085030740b003649a650040d080244000b00d11100d1600395941c104c0003400724090b09582d50645d60b18480c0c01440c41d10780303402c1000b035845403410300f4001d000382e80d4400701d0343c0a884000585101080d0842e01c000c0741d83c03541c88240300d03030a801351141b140488115680c82342201c000309025251780002c0801c1c2c03030581c07002e8000c2c0000f1000c440030900c001141550b22990207001032003890303000b9964040d0007410f460310701d100303500400c3c500d025a0340701c959a007080c8070181c0c000c003090500e000000c00000d1941c501000455281078020b000040b12a60310420b0000818002d01032030300340031030318800b580141c1c0d0740403000700110721800d80440c64070380034000507101c07c0400998181a42000c13006201c3d65a2041c80341e45e0207000e503d00441d8078080750005aa45812283c3d0280c00605c00703c101d0000130380c0195580c01203030310480c2150344a80e0390b1403800000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317081474 1250 317080224 317080259
    0xc0709060815010e01051c0b0403020604060e030f16020a080f0a1203020c1c0905040c090305010b01090503030f07020a030f0f14120d02090a0f1e050d2a050a170601 72
    0x51541e61307001404503040155403a02c07132a006260704180110f05440700d54010904072401c40c0164065010001081380038002c0d05501c180e00c000550a0400c40c071030707e50740d0780121035a0f40300b000c20a0500a05551754010342d0030040c0301c064207032004074000c5420aa120b0710309203401c1da2021050103404044034820310803a80d07043c04100290500341000c803050600801d50340c1500e42007241150001c1040e0360366105142905810b81c481c42c503218078510b40103080d04d00c0590040d0510058640c208105d8034088115094010f00d4005140d8a5680348006141c00d0940d13013000e45800e820742c9011080104800b40f5031100ca0098000c1031040c540c84c40c0d5103603a4041403100401441d420b2100840c409010b4000d40320407040145a140c403d0380310040b66080c0041c036440301460884001240c2c006007101d4401901a1905841860103681c0f00c0d1a003010142000c0641184042a985186c000e45250113264015000c0100101c6c1c05554614043d5800445c1c0703941003510f03009013000010f030702000c246181d0300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317082724 1250 317081474 317081489
    0x50304020904030c02030a0615061106040203060105090c16120e0d050712060e031612020c090f0606092805030f071a0408030706061a0c1506060c070906081501 70
    0x703680c0d40e5030301240d4600801c1d001700d030103105002217500000c1081c010304000d0f1603a031040289540c60020010032502203849155100c1d08036405000141e02e0205085065550a0742c0b030380b4030b07030302e0700b05015142e4070610640036500304104819108100e03040751492030706074159032400283c4c0060410800d1480b2440402441070b03000b41010400d524000003543d03906030050302e00040c240034051780c40d401c43d0f1001201072468100c580140d8104111a80304882d82c00c0640700403c040c1d5007440c007003003070101d0161a11602130040400a001e640d100c404565942d640039000c0300348480100e13a620a20280c1440d0100031191881010400307007000190b20400700207440040c86410314103040e003415110180c0c00b407030a0407402c02020800250030801000190b00c2101c00198503441c0c00003540d254400309c0d4400d1610301d400c0202c10400c040010390b0790320640f007200c1d022500381c940c030300084d40522882c1070508842c040e11100040301c106c9640180100c2d00c0d10001e5039401c5811140c40305c41014240603151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317083974 1250 317082724 317082739
    0x30518060f040312020d060b030103170a050a0309020d02040218040501060e09040213060812030720030d050a020d0f0b0307050402030412030e07030221280308040f0b0907060f05030402 81
    0x4000c070340303c4d200303101c0c821441c14001480d06048680b40e609544068021504104000004200308039644550401c1140c480522504140b580c80300103115103d00028401016202c215080c15944d031b880110007041e0380140308559030740800c1442c440c0c80c04007049841c8140c1c81c24000080c414080c0c2601584400300919042d4a030751158200540c8072801101225141d0390782c00041441c840c1080f40d500400655040242c4074600b5940041c881162140c03188403206584800414104001080ea500c902c42484003242035a9050140c00090046074090f0181034205041c00744c0c040440d030f200c491040c8040d0107031071000b41c0711018001603110a803402000942026202041188207074403418030060940151050381d0703603c0c0c000540d1146803d4851200110780c8030404100d03481000009240f030911580071700d45108100d10181d04046181003d01440380b050001000c0190804503100400c0d40035440c0007050404103580765403040f45000d404013161882240c190a81d0098050700d1046e0b90040400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317085224 1250 317083974 317083981
    0x150f1418071809050304050909030325120507030b040f0c03140c120702030d1b020c030a03090b0901020a02030d020105070215190e191412040f1707030b0106030518060f 74
    0x1080200340d83c00050750180014400401c0658400064a0180a50384019916400c105484a180482c803046d02c40407841007036010820140c12900c051265407507100001110750303503108203030040c03d03141400c20b0384180b600c0e0000c00317401f100b13500c508059401c175074041195145201404910400c1540d100383c1c00c800612520b8024121360100310b902086510689040c003a00e01031100603514010601b8903004481e44003081b41645c100312001d26100118010800161070352009082000381d8042d00046000010702e4203201d074004c012300803900c2d03805000c80320020601c1c80001d000341003e0750100014041e00c2d41e201048030401c00080d0298210f49800f1404494240301c0e980117058400c1078644030300600519410b50b6a0f040039590748240640214980c5e400b19180c030070308041d4844420814000280428000502a1406035043c0e4003100d082d205540440d0b42890b18000261344010b0040c440c0b60b00105d030700382d45504074502924a4a000e5142010010070761611500100c40e00140b006002000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317086330 1106 317085224 317085269
    0x130b25020d02060c0a020603010b0a0e100f0c020103110c0a062714031201090e07052e110a03020a0b0601030e0a150f141807 55
    0x11502091a5000940c54091120060302821010409a805503400c000e002940740d001000b040d00c030341e51840ca4864551100403020001542c07503018420074204883c0400c00e0311003d80307501201c0b1400c080110342c51401060141d0405031115090300300710060000402c000b8140101501a041c0e040c01c00000b502c1c50b0503014242007201a01c00310400141d00c0e541424194442141020445850102407440c05404a408502e9054400002d400d9000d07038880d1100d031410300260340c140d41d901c100300107603803255030f1405201c410288041540b01000e00311081c480e807607600707090044509014405241c6420100f0403009030f0b200c4020102070050041140c0e9000c103091030280000103080c22515101c04500308001c043c0b0a05a4089049000b40d402110601c00e240c0360800c00d4401c003580e00c41001303a0035500c0710580701040030f44203480b80c0045140710540d00c10300c012440310098101ca = true := by decide +kernel

theorem cover : BRFrame.Cov 316906474 317086330 := by
  have h0 := BRFrame.cov_init 316906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316906474 ≤ n) (h2 : n < 317086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
