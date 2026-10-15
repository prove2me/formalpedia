-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3859
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:11.098327+00:00
-- url     : https://prove2.me/submissions/d87ae582-e82d-47d9-a207-28e895143af3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 693884892 ≤ n < 694064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 693886142 1250 693884892 693884909
    0x6020c030304030605130213020712050c0616090504061806060309020d150b0a03050c090c031302010e0d30052712030313050c040603080702010807140d1b0801 70
    0x8000d0000030a01d07003080398050003910200f06d084026400140c60400c511141449080c3d0015040c0d0a10100e40f038108003050031810300f149032084208602d40d64890041c118220700b807810b140d03042c1700c40c414004d40008180007001800910340342c14118425000000803280c04a207040c900252040c0640221004160001d22034a04049262540001031000c084010000c42c0c0e521009032141d80c5221042000d14041d0004240e101d40000900ca010031028120102038a07084c820800e005041c0061403402c2582860201d840ca039004001c14442010034100030b0542c110000b40b0304445d07141c883c260341200301c10038441d592184850002d441900c01d0300340403240c4440ea296a1040c05d02c446101c80b44030600506451560110107590500315027040e00c0c907002d4010000b503d6828024100000741c18001e04641c01c002d440e25656415100c0c2c82402e02c020305210b4030a00150045000703140c05480905c0040840796184400c450460080c54110782c83c0c0c2111b04400740719000180b05091860503940c1c240c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 693887392 1250 693886142 693886147
    0x60801020c16121a0705071b18090803070c02030a0614060a0909030f11030c010f05070e1801091806092f0904060e010608070b0405041404030203030609130f15050106020c0303 77
    0x948144c08100e200510311000d00c2403c0015600080981c03408000481402c010460824107000c0c104d038001d02c0410b038000c003d900f440c040398040f0301d17500200e9401c6032090500e0907110800d48042810b100c01441c0c090110703440c0070f02c05042ca144088114bc442c040464038040a5034680b20080100c5e503078941c0140016443c542d1078007030390f0700800540300000468002c0740c1c200418000c0c031b1421740303982603410001941c455003484429600030900c5140150100d501710303071201810b81000400c00051250082c06c3c0c1c1c0b152160f034100c0d2a006d0706244516000302c001c3c06040c0c402d04207410a0030f800c41015045107102c1201804868600010340c10000d0300622000c000e855980302c91014140d1100401c00555075400d0000360040104200c0c4018540407002176201c038608030400003140c0b00c1520f03c00400461100b04400268003000310ba074003c400701c400c0b81c0c558859a000151850a411000381000403034195030091018000480300d200340401d43c140110307a21803074200d0f101d003103802089401d903005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 693888642 1250 693887392 693887423
    0x106050108090a0b06131b090f0b030c03060a080a0c06020c06030403081f180f0c03050402030a060213120812010501021c08040813060c060b030102040f09020d060801020c1612 77
    0x4202c84645c21078001010b41c0c601e100364096131811030b002c110501240d44410352109940c19040420030b8010200d844241038028600500c441042c032004000020003140000002d09656449489101074071140088400b0f00f18185007445200c0c1c11030040001501c1810042001407a25000300d07841154190342c0d40c0b4140e1034041e4219a1a1400701d040a402841034001140c0c0141c10300d64030134402454880494180300b6020004221801072050030704042c2460200030150701d00086125940780d0008006aa45200c55903c144105203601700c0e440d07004511000009110080c4050701c921043c0010503421f9998500069030784014090706910414054008150024041c111460f40305002d918694542100d124504580c080f50ba0445400318054030913000030b020961066a941c241c0a40c001c40c50b1509200c150754600040340b160020307868001030103040c144447d800c18001460043d00a6483e00341c008906900d44034800071529410490035000503610001788031010102d82c005940c000030b80103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 693889892 1250 693888642 693888653
    0x50c070b04110603090d0e0d0512070f02040c0801090b040e07061b05010c08100b030c07062403061b0314070e0a030c0b07030e12100e0a021c050106050108090a 70
    0x5009442c00d402c1d024420500b512058015841100124050032000b000e690000d0420a4042c08a5028591040b00880094400201c00a101090260003500c504d450310708140324140d034010094129052400900b90b841d0004601030598965040074040d464641c414802100ca0140d410b80b01e5a006460400c0315501031800843c544280d07511003014181291985401e50381a980c0300350004801604000f00040aa401c08c0050050513500c6461400c0000c41e9024600034108081c1595555440b568006045482001001301005003d500e9265481c00c0c003400138400400d000780366580040d58003810301d10a120380500c004c52074042892a4075114801c850240014a0094100a8122021000c90320115000c03006054040007541d40e48410b18004010f001c107485c40502440742d45a045c01194404104d0700031080341c20400180c3d60960f684200e00c3d0031400d14020b50032021001118041a24008602200b6401032000707000c00703982e4200465001e0300c2140c0100c20b982100310003030001107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 693891142 1250 693889892 693889913
    0x7020f010f0306030c030f110d03020601050603102112020a020604090203060f090103050102091c081e130602070302091f270c02030d110a05040915080a080a0210050c07 74
    0x50030b4640012042e480f039403102c4034260b507900b00740c3d09034111244240800c004c4182982c8401400c1d964404034440c1c80d50003a40c2e500042c02003500c12800400003030541c03400409a000240302d00e119440b5007940e01d02e10f4801215000300181d0b4403410050381103504500004800315603980c0900901d181929000101000f9000a410241d2265202001009070395410442c54080c40c02b40c0001640c441052007005400450070707042c009400d6500c10401c0204414509580050108203803082203402c1e001c003000c403680b01c0d4402c2e85044164103100400d20682c00511203003924800d491070b50894880040480841d426120044203512071404144803900c0b05da154440b40031402c9004020400b069060303001a5460f0240c0c110041c2d00c08990000e20a5580c01428105204a9100c0d8a000d81101c2c00030280d01c6540200304a00b925140203400030000304100100410421050b40c030216441d103002c8549900482451006110760a60030880311054480c180c083c0760306c1e060041c90308206a90b03002c03501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 693892392 1250 693891142 693891167
    0x1312020307090516081e1f08070807090f05060d0f080c0a0605090606040506090711122a070501050d090503130906090e03073903050102130b07020f01 66
    0x500640200042081c82c5010f907501a41203181e94205010010f000140b4550004014803071100c1e51050282e0f5001009407030300d1f0400c03980402c0b81a111a4160354040000e1981d02000940c0303e00800020040300c0818050180c40101034140090604a19040c082e900f0a49000740e1003645002c001c400510b0b03204004508074803071140f180c11b1401f80c1a6050408040c403d041d42c00300d0315a002c2000c0c02d04140440d85c0d014400b11410055420300c80301107000440001c0158091110a0080d0707603424004104c2d40390305003001481255100c2204007a621100041d9030381c0c0452040640d540c03120014007140200c1540c0060391518280101405480054840000240e449020030420082191180701c40240a410080000324141b46000c0da41b2007145c0c41d00c0030302e1815400030300245000400750400e4210b181d0034031030440c4d646020360401c0c041d003482201001c0d02e42000702400004004064002d0420000070075079400c3d10716a514051407007403045880c000c0d40a20807900000075580120051107a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 693893642 1250 693892392 693892399
    0xd0806182403150a052e0b03090a0503040306020909090604050a02061308010c0324060905060c07050315041a04020d03030c091d0118060f0605070203010b04140f060402131202 77
    0x6041d40c0c3c00301100c035507009440268070952960200040000c07013100d09001c1002c0e16107a15003a411a410050249466010720307480d0460000210b40d0314241000a40e00c041e4014058a07595642c9291140c000d501c400e900c45e000340300450000310000f02c0480c140d44210382100141040402079820400b00394008000c1408201003540040f5492009102d015002c66290714001a01d07011102507454550811007200c90410501d0f02c144500c2d81c1c8508128100e81050b581e07a40c4840d030120050b42050300a410094245c03003503100301e0640c0981c2460305406280200c8450010420140307913400030605c1190080e4108413281d002d003000a1003580701c1540800389151002545403205801070000d0110207242032550362400c014402c4419142000c2c50f00c0c00c404070200700140c5491403212034459240700b92402e000c0d0102c0c0e80010b5440a42103542c02ca40c0080082040c900300b80004034141d9030965050680f0085c0300d0010741a401c207442215821558400c003c4003031840d0080d0300344484000d6004981 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 693894892 1250 693893642 693893653
    0xc100b122e0504080c161a0f04120320030703080c160c080d031803020c0108091207201002071a190e1216050f0d050d0806182403 57
    0x3141c0072520036203002d00d1141d40c0071580c0780040000c0d00e20300380b103d007018050201440300404c103030a103502907800f41e084a10420780d04d5007017100c040e5000380240e91103451503802c0720012008155000240600389500c880106c6450342903200c0d030b2590781c054030384014049069003012403271041c18240580043d003600c0d1095070740c81855989900b800c000c20b07407145520340d00c00c010700f80550f40c0501540840001035851007075188a1520f00a42d00d581d003030b03002d40c14070202c000031070030b8050144441d00302c1c140c1000110340d44c3d0046107801c10201e0281c1d580000040e01c2c0403004543c52502c50180040c1011a034020100705003460303164650400d0030001624030380c02c200844c007101c4504d00007071415100b9030303100ca8158009650074400700400ea80302c0404c076600301da5603600c1c10b50031030030030001621025501002c0c410864008542c01c0161030101a10900c070702009080c9483d404101144504e1041c0c40d40c03400b680e10120461010038055605400395911107451200140060b5540c44000c54001c00719035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 693896142 1250 693894892 693894973
    0x2408071b02130f020315090f0112031b241515020c0d1b0e070903030e04060b070605160309051c0e06030f0f0f151002010b04020c100b12 60
    0x4100d4889048611540d6004010041e02c044401c1b250103110f1000d981c00c48043c81c04510680340c0340014003429076a00d85a2609106051058260700785048400307a10014a40035810000c0c0a620440010f0b0500d440c0b200404006000c640101c280000382641e1510070541040883c0a50842c9021407504521400070986c506070f54158054030968000d6a580c0d176054140b03040c90242d00b280360406010501c480d002c1c031500b41e42c8140303508101c9800d40b414000a106c10310008001c0c0c80d551380445800100454410b040c0310865020764011880c049143d0f54804171a8415810740d42d407030720064900c0c0c01c070706c0c003040300d240d020707103050500c4201c52614a160000281c001803964000b075610b106958400004c010400e5030b2840c1030f60300145a2401e1011620b01502e650b030740720403154403081c0119220000b02c0b040f64001d401c01600100010015074403400a203441d01d40d00d201403215099490304101c4054060705014040201096900c0080c1500f500e040c40b8541e50b10a11900403d10a40c2014214 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 693897392 1250 693896142 693896179
    0x50309040606050304020a0f03050d0806010c021f080702070807140301061a0c0d020a0b270106090e120a05090108040f1a06190608070c17042408071b02 67
    0xe40120f4440a480742042e0040c8909480c3d960004e01405503400e5090011900000b20030a0307c00351454007481031350324070b0012100030b88100c5c40250440747c00390504a08420b0506104448449541d07031110664440f8000c0b80d0710111031080404c960440081800003d0014521045406001d000814030f582d6540000d2188803d070f04032102540c0c030101d401d040f80d0358140108614004a4030007041c8010b90750304c844005100c050704500700100c0711943c1079448190b82007a03c1c040840d031002040103030355076011b0b403000d044a40382c3d0903c580a15520340102000d035005440751041a6075895017090722030801035403070603c09002039410000707900030380b40003405a00404403034600c0c4804849540c00d250302401024045402c0e0300c02d920002d0101845000d40c03040040b0381c030040c00d103042116105c0c5400c0c40c0c5454902c1005041d201c0a00260104041c6a03400442c010012200018104414094070440380c6010581d0700c0c0000803210320340100d288030400c0360b15031940d00003003c0014680240a60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 693898642 1250 693897392 693897401
    0x4020109290f12100609090504050a0b0702030a02160e010608130c080106052d060a26150105030118050a0f0c020105100f0e2d0c092403060d05030904 66
    0x2110160ba10005810341c01032102c0c0c0f20141c1001040501c582d1440c24880c02070403020440c042c1540c0300e40d503400002d05200b0208100854950842000d500c1c40c140070340004c4d180e5000000c0c00780544100404030081c3c520000d800c0e0212210070006a10726424a44d00703d40c4800c003d46181c2c20102c40b040c4003c0400c0d007041c96400280300410001030079501d08014055840c00290035407184614002c0d04e0340c010b4400702d95542c201e060849074196103410f011800d03516044280d0248a0002160320f08140c0c04041200c024040e81404007500d40b60341d54070004442501c024018002418094524440d4505103a009950450703240e91000c11001b2140c829001110311180308000143e4540d0280052400d49581d28030152a510000c1c00c1814104000c032921407201038081c4100b4454040c0b680d0b65101c9182c0b9400025480b4094030f1030501386040c403128981c005015280c800ca0b658516414881d4488001510504610b140e590a5544031010003583c0840d40700b09030b940380810002c401941c0e4841c442e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693899892 1250 693898642 693898657
    0xf030c151b190b060a050d1101050d06120515070903260c030d0501051c020f06040905010305070305250b090a030804090903230f1305030a030e13050402010929 70
    0x102404426541002d490000c3c01901d01c0d030248116100a02c55500c60000300301055401615402d104c56212004950520903503e22856051800f0b4010030000c41408000152034040d004032880010034a0034100d601100351100c10119050b0403040002800070640700200b07140100c802614601001d01142c041da000d2828400130360000201c1200c044254480da0340074050030340f150415480e035020307482c400b0f400b054800b03840b5100300c2e070b40700c044e5650f2101114041c1245038800c0c08656924603180b03035164103500003103805004555012800840307100c11a200d540b00460843c0e000e51400600c001c190388107004a6070000207111000c0045142c0200a1009181940c400240080c10742001032000c40c1d000c0120844000b0800e401c05045441c10a840d40104004a2103586898140b800c409404c40b40d88065098054a04e140041c1038002251070441d54041d10194041a00c801c02d8204480003114020f0201e0070b441401e2040d101c10b102c0d01c2d0070340c3c03503089488804558990588040c64203d0074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693901142 1250 693899892 693899923
    0x913060c0f1701030803071b021306210203061501020109140607022406100c0f0b060f090f041e06090c090615050301180f1a0f030c151b 60
    0x8444000c642c0c00300681080200c480318680b42541166034000c500d1202800300700800c110207410481e01c25640d0004040c09500620385c0c540d41c20441e0000000d4142449031101d1006003900c10a00219800d255004099000f40030340916543c04101158100c280d00810341117658450540001030100c149a10440d081d2a00a240d549001200249440009030460401c074085011109180c80175184658200b803040340c602d04a005c1c9003e04850711400180b0182094400c40c554005003c00020390a0284c80c0640310700c4100290f0806110085a0982d0120320300300101d0001008030782a03c26250b03940c80982c260000d05407007038407508142e501f00c0e941a82e850b00e241c8000c200c00d03401c91060308010100340b800114040f051000192090005114804480032803041284104060354400b2140f401800c80c2040401c408905c0a088003004074000c6002d10002e0704411018603001a07540401d00e4000c10b4800b402c4c88043c041ca019402c21158000c0540b001295405040f03007e000d01c543d0050282e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693902392 1250 693901142 693901157
    0xa0504050d080d0504061e091109040206090d0c050a05010e09070c03200303181612030507140318030106150c02030705040c1214070806060c1005180610140913060c 72
    0x418445100c6089001c10f1300e11f8910700354000700041d4009140707280078802119640071f145d0b211f0010905610034000c0b1698007501421095041041c510001300075104191049801640c58100545e400c10340b50402c0c030360100c00c3d5800503484074803d0301800d10661280c42c1c81869040040014803080f2a03a0387e200c40282c00220401100350300da5134010342040e1218000f44040400355028503801c031118000c8843e40c10243d9032110070300d1300a404513049150b100b00254170705610448055202e4101d0827290400000c0801e1008441c64140600c1c0d055684554060408030709400040d00d01a604007230890301030260303c2f0009143d0390303284a5841480c015840d404540385081c01d1500480320303200e0140c0c604000100c1400309599103c3c03500ba601400a848032035464208020041c5000300345108925070504000c100250060101241900950070408403222038455030000e51a03400c0a009130115602d2075140006c4038900f031760712a074003d410310284402442d0745484220549a103010300f42d0205112 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693903642 1250 693902392 693902411
    0x2071209232d1e03060a0203040b040f0303021c0603122c01090b040b03040308311a0408040602011a06030601180f060c1104140406050702070e0109060e0603030a0504050d080d050406 80
    0x61002d5075000f2001d46c0308625500d416a10304403195009840030300001550040c030f43c00c15000c3d0341154151a2803200e45150181e9810308000a80b4140c0801c4a0b9200c4d4128118000c0380101c9044149068011840c12825500ea0040d410760f0700d1940c12a0400410002c0003801c52616401030000d005034082081e92442c140c2030140503d180a052007191403a0b80010314500d0114404510300d501c0001d803001c01c988414142a071120b401c3c035a214041a610354140020826044000c00440d40d40e60024840d075241c041c5401d803041c0c04440301030340280041000921940c07089140b840d02d40c045886013078105d03403100345030044006d007604002d0200e01000c03032141c11b000840c4044a09107000301c1d420f02045050303072a0080b901c1805000140456220408112040d00901040c0040d1100d100c41d1990303581d6403910000a800349100f000c100c0c3d2052408102581804411503485d02d4440c0c0381c45113028a00f0052282c50010b60b6019200f1403c10721084120506500030140928010035000c5440c1c0d60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693904892 1250 693903642 693903649
    0xe0f0a030f081206010504032409050102030709080c040e06220b0f0108070b0403020102100e100903050d0c0309170a030b060403060c020c06030105012102071209232d1e 74
    0x1400b800c0039062180c1841f0400015107000302403c21f2105105c2104240300020070210007410268a009042c4d50011007000701140e0700000c00d00c00c90362400115004805054140000c0360340180403103102d0380001000403110404100040b45044403010b099801350700a840b4040c0c440405d40f00501c7c81160341004101c4904200210409000b107081042d107028515800230b075807600c050140c4c032400b503100c0c00031450080040c0304001540c1510101440800c440e8070b0001c0c0246c1c051a8802c4981d0725058200c44070074424403075510810b43c0043c0400348122415400d95058209180c40c20816854034800f10507610f03004c2c00703000218130821021440030100c00c8040d00b805103002d40036005900a20041040760391109500d025a50008503180c840308400a500d8040d200e01c2d00040d02600007003410601055020030b250f03088030801c410046003230610078142c610210700b4000c00c50744030201c02d03102201031004d01070049903495000149408481004082103103801300154170800058900110440c604 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693906142 1250 693904892 693904927
    0x1137021c02030f16030201140a02041a04140d08041509030b091f0b030c151e0a0f0e120d02010e150408220f030f0210020d0e0f0a030f08 60
    0x1031900195041801a83c0c0a80355400b515074881104000e45801ca01803500039808101441c1d4030340d0942e841c40c50608503a0740658010711400300781c90102018a9802400300090701d040e42c446141b00090100c00c00200030202010810907240d0700020040060b40c140c03020382058180c00552120100c03a03141d4107109200500050001070107411000d462810f801d11504810b03841003145000040900f4a2030201e441c01c401513502d16008040d000400580c0360000000e0b01040c1c2c180000c1d2071045104444422250007030075100c07400f00b405151400900c9005101486401001401c5c1c02d004401000200b89403500000380030026035540c400b5205038013020b01c200302c03a00ca003281c6682c07007500309940c0d46010742c800c100c030f5019254002c558030464004500b1103d0000c010203800058504c1d22404d10000355098408100d118041404d0700d0b150450004c21801c1004d101c03507c2e00c21000c42c0c0c80d81030000e5440010760159011310420030100018900c1c10390500442e01480742940c480c4102c0e01000d90340c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693907392 1250 693906142 693906193
    0x4080613080f27100e012105010b03061203070f0305160b0a290102070b180a15090609140f130e07030203070e060d060b0d020406030609030201050604113702 69
    0x1035080c825802c1c0c03099005100150782e80c5e805c0c0703003810541d04024a511410b20100e152071a4442c145000040c817224058065030003624116031040c08c04c0c0c000414150f681c0b013007034070060400e141200080d0110307001e54080c04205a0381c000c120f076000c0ca140d54800403058200c507101d960f9a942c0310b4402040300800c4a41030358400483c00c030f407940002c0e070700081d580f06514854032200c458000385030002c1201048004e0392901001c1c02d80240c07540c5034840c16029801014640380044c5140b50005601d61207101c0d601e00311440198a24030200d01e000502025410112a07241c00101c1c0c0c1c5881c1203100c0c0140b080ca10501029405002c1039402c5104045c1002c0c131070390107400700000d071405110042d0341e0049803509032039000c100010b072081500c5c045001890f8115000c0d501c246014070010a01403990000002030b0b209a000f0800c0da540d01081000b15000d0200b41c01051005102003d17030325158040a8001c0b504a403208503210031540300412241441c540c10500503000b40d682c0643e51088071038221101c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693908642 1250 693907392 693907399
    0x22031815120e0c042307020f061b0301030201110a320c03062a0d0e010b04051009110f030c190f020a110d0b0906090c0604080613080f27 60
    0x2003407100882e265491229501451050b0381d1114005040b040816051659007440200f40070780e45400311001c2e4859804051000d07403401100001a200b440103d64248445441a519411a401c54004688030f400480c0b80b5611403041c29892408580d1b1840900148840c2c207130030828407001300a440803501c0240118641031391041404030305541e804240745500c0f141038842040c400c0c3e10400c900300090016005081c6e507030000980d803403038040036800280218024200034084205a4000d001c00c403042120b8010750704007400014010700a040c3c00040c089a01d060b449420401100390841c05030b80f09941c017400f019000525416a5108660700700703d003460342d00341690340d0000090041c0d11110b076a4401071101c850310b03c0700081076481c007030781c1000349030441022041880d00821b9143d403070340b003034070b07002420b02c100c001110962400c0c40445003070b1402c0703002408003611200009113400030001c1e42101c01000600140310300244070409080d41c200ca0482c0e07009103006036881a9180010070300e55600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693909892 1250 693908642 693908651
    0x501020105100b030c0f03090a0b090a15020f0405091608060d030e060304140d0e030f0c0328050a0b0103170906070b0405010e01020408061503062203181512 69
    0x103001d54034884140440e40b5861440d0f640303544c1e072001c2605c94440d00d103134181d145c0008010311006150004904442e1880f406000145441c1e5141032070343d448002c4030040054181c0340480c00a2030040e000303000c002503600c1c2040d08107500c0e40300080d030094084a10402904e140060f001150342d0201203280c02078419640f00c00c111180382c8000f02600c180000030f0b802990008003180405c0540c1c1c500e001907a0349003040c4e611742030101d40d0050109101d078101724840e10440d8486106044007261603120808014000c010004448000803010441010004403036800b4044c5107002c22801d0000400e00b81c4184006089903045180010100c5101e04a10641c2002440380000070784540c0110b615031a081520850259258503285015100c14840000c0b95400890b00160b080c00000d0917a0041201e4a41055100400000d256699201b150740c000000404000f441d41e10451580b85240d060081ca400015131007a4941541142007940c452182c2c000002040c40003164090b10581001400210921 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693911142 1250 693909892 693909901
    0x1207240f0903060b06040e010e06030705010e03190f0507060206100603021e03100911070b13080406110309031c030506010e30010e0c120727021218070501020105 71
    0x9200002901008003040e0380d03102e0244c03242d070300c04050790300420f079017100300c892907031940d181e8084681c0c190b40c0c05000b031040d407001060350340c064a0658a00540a0000c2c003034000841ca45144140c0784a0094411110f8201e1400c0443c03814440000640400e40040c40281048510140703a904160712007400c240c41440401355031400c00a546800030100a96103859031514030280f0660035259001900c2d142c031b030008c3c019250701d8903005884c4007801152403241c1641c03401c049024400840000a115140410003806214012200d4102601c030040031030b400c0403043e2012070b2030080c080d0b528541d0024036089207003201c0d80c103001d441e03445602803801740010070710303000401d11041350b00603005044614650b14101307900c000e6002c07140e48403150703000b4000c0c0501c060500381c4416861004074066440d6026004606400082c1e01007140c0c0300ca00744462015801004008400303c0503240c1c81e0b5190200944208640c55080c10303070168a4000a440c000b11102d4030303681c98480175501550643e4100360410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693912392 1250 693911142 693911147
    0x50d060510061b140f06041101020111130e040c1208041401110706030b190b0406090512060103080f0906030a14060d082a030304030203120109020c19021207240f 71
    0x2803d02d0340c3c8201801150f8043c80c02c8141001004403882045200e12420081408012500341c0c0c2103840a80081245100c03910301c0c03040714461016001e04c91300e003c400400c0b20011035080e89901c1406080b4000015440f80a41c04640d02c442c1000c3d942990082414003002c1b6240083c5000c054007402c00c003075a1091100b6060f140d036214460f0005041c3d0310510211940c4403440c04100941802105607480360b1030b100310802640160051000103007401b03602003101e0801d1021181740c6050340c0d009180c241c0c0303580d6803401523900c80c040b07038801e40e04140081119611a40c3c00755000355245400810b011140200c1c4115a90004010912420b2841d00701400301e410002100d080c2080012500da40c4400f00008a0981d640910441c0d02d030701c000410001032543c0030000d8010000700e102740725183c0c0d070389071154416030050404940d91030304462503082c080d10020701c149401a102621030419800b68485071410714001c0c1d4410103088400070607606190000d410310300640051400d00c00714007110744400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693913642 1250 693912392 693912437
    0xe07050d02030c0f03070b0c070e1b0708030c070b090604021005031017240702010c0203090604050103050612072306071a0c0c01050106050c10050f130c050d06051006 73
    0x2401e000d0300c119138100405840a1103000b024040380030159030b0350340f403900c072242e611000e9101342c4014860030008990f82e401102d00d02454180fa0b00e0100341003040300d407141380c600e5102802106c0109820030004000603084540c0c648982080c4001e0240b03403800d8010f01043e450415468000c008080017041508001141c1c0310099841d00c0c1803035048a10121201894485841d050301c40b03418100003c6202c09010980c0325101c0c4840ba07001744580989510141e030740e401900303c0c1c04e511806c18401400340f54429400590f01060050504820b109106c002904090702608114800d800d117135002c0919080d45401c00c51082001d5a0182c907100d015114440c0c001d144040500400e02c40201040d26007c4003c00d0710303603600031980204503a59603210090041d42c000e01d440a0180110000ca00e12404607100e4544640340001c0440b54983e52120300f000c040604413400c81c2c84001c01c0340301141301d455100300c3c5c40000740700700350000b000d00749007840d03800c4489194001e000b002484c00c2602c5460f10340099 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693914892 1250 693913642 693913663
    0x50c12100b03220215070c06080613020315040c020304081e060109050c070b070903030e100f0e040f0e01020a0e0a0807060302070812070909050a020f0711220e07050d0203 75
    0x541c02814025403901d43d034000a0700006580186815010841c4011010013804032a10071402c900c22145d5840b0306850940040703681c107911011124404408030480d8008590040d0313440b4900e00030040c4034000508a460104040c40142e1020074140000d80007085848156092100c1c03045d05d8040d41d1240c0790743c2d0241402040c0d0354507140c50100b440c0c0ca008805649031154415071101d190b01d0710030f000401000c2c0c83d22059001800c518414801030401131800710045100d1365078000000c81069090b520302324030340b80160b006966503000d441c83c03800611501850015400015a0310f480d00d5500418411040c10032920864942400b0002c01030001000e030122131103402c001d07890782c0c014102035043e0b00030381014101181c1d00e501007104c61988001d0715000d42e14000300c2000f40e5201e0780c1010007240200c0840b006101d0301041218042200040500b0203110b0080459074090002d441c2000440b00c0c000c4200203450700d4803500c001e4000b090080502038801503070003000b0300c41d003600042d5440c8980302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693916142 1250 693914892 693914911
    0x6030a150b030304050627091501030902010207050d080405120111121b0406030207030810060c031101020408030c07060908010c05090105030a150b22050102031b0709050c12100b03 79
    0x14400e4242c405000b99002804000c2c40c0e0340c1c0310350202c54142220710001d800000511101d0684252502d13200c04401e0158548190021884101c1c0d4015001880c00d0305059055101d041d10010301d50f80d0b40045000f60742e02c15012151142e1420060003025146c004032418243d0400103c4c1312000c100005a503429401000300c40d80740c2c0c84141844070703100403602c41d50344843c500080c046110b94064009200b12071007555800d1f0180e480d518260391080042c0190b400054003207005801091013050300250036800c0d1000107280c10390350744056146038013013601070001e5005000100180c0b80c010303041c00002d1081e10b0082c004400c040728020610b00c43c1142d0700d41849070100c0401c4c01c04109600c00d40781d019480261034403da886e802104900d03003081e0465070101c040c0d82c12421140781d1103d00581200e006030006c40c01c020759000000140c0b1032404004105110f030240c0001e51124034051076001740c41d5103451705d13920805a184801d40301d90040003074158920800b8100200e4500c0000c4992015000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693917392 1250 693916142 693916151
    0x2191a07031e05040b1506090103021e0304030309290a020a02190c210c0303050c16030b100603050610051804050a02030108010b0a061b02010309050d0206090606030a15 74
    0x40320070340060041c80e06407120800c503000540206042940520b016078025030444040369903205503000c0035103403200d01540068042c4003284465010b600079042e034408020b07034030482a191001c0f40c030864104a50640009844010480900c80b10030258200b100340d81c1001110b040d00031542e2128988041c05c821800c1d9030001c0c40d50005482401251035442204000d03a1141c0c1d80c508142d10b910700180038800202d28062000755030003c451410201c4076a11180e48608185951015070311904400e1a0300c00328024150701c2d000c1c0d58a2070010b400070f1803050a916035103041c0f01d424607103101080c0c3c0041040c10300e010248521030f030f07a241030b90000000b0391034890341e074038284016120007160780b106c180e0704641400c003400490364894019505a5190700000c22a11038288108808401c96100e035002098500d00102103040c0b58000e4031941a0060401080030340c2e542e03a9407440d2141d100e007a940141c002c607040c4100120240242a0030140840c01060380040940707030100317129440001c6040d0203580c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693918642 1250 693917392 693917401
    0xc150f1407020607140f011a061303240f060e0610110304090603060e010b0112050c1b0c10021c030222150801050307060e131b050a02191a 61
    0x6200071901c08035405801030f62a01554900340010414100100c0c5260080e000c80703400d204c905100d100c007110b11404001d40c02c4017540c41440002d621080c0394070541d66120703601002040d080e065902151241094180e10b06d02c400a000040303c2c1c98255040b051400c0c52400c00c50380d01108042500580116007280d0901d21003071003a11280d4011496994070f02004c200042c07080c586a002d101140d001b040d052118000130ba090700d00729003400d610103000c01d6000040c00301103981c0380d011517072040000c03410398501111880542c0300034403c0002035000341d210440300620783c1490f482e17889105004d4001000b00c81712707040e050640c081113010880105a0f0104000101c804003008011061065110502180b5200d401a15080750001c9008010032400b01c00000d203401d000841004442c20b55681d004040102c408000400c1e0620f44000c81031074480800e1901003203401d12007400380348a82c6402d0340d541d8203440068200f024050a2031502c0e903103010b40c84085000300205d80510319400c1c87e6032903a0350f034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693919892 1250 693918642 693918677
    0x40f0809011e180b03014a04030e0a08071203020c090f01051206060306040215090901060e1309080d15080601081e0a030f120216050105040c150f 64
    0x1200c10034a80100301950a8284031504020f500c50840103a4940310961078440325003030158031080c480c0621a0100003180751140c040c007000071081c8440d56244907052400040c0c2d02000148a00409102240310001d1204041d00f08404000b60b040554101c1d090510f07010b090342d00d0b1902ea229401ca101140c1c45290201482071040d00440704d002000048941004001100c0c0c2c003800b40160303400b645c1161011503c2d440c0c00550180319070001001000d19a8455003485400310304d030071000c5001d020501c0104882d940c1c142c0558060203941c2c0d51300b040c6205600c00c01586003044208250b0340e511b0a4002c801081d00141203904004d412440450000c2800305034100518259000400ca07000d42d40c0086034820740420b204038600c442141c0e001c0d0024807810456119040200c00801281e0107c42030540741e4015502c14400c03000705040141441c1044926a810340c41d400000c440c180d540d01c0400c0200304d0030350500805000d004108920701e09030310001401c0103c459017084280811594280340400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693921142 1250 693919892 693919907
    0xa11010908060f16021605010c06060b0c0a03030c05070807020f0321071a0601023a030f05010e041e020402040b0f03040506280209060409020a02060a0c08040f080901 73
    0x20802c035005841d000b406100f00d003500380e5645007407420480c41040e5007480090105001081c841c0400d00b02481d1030019140300806840485846071261000185641214043d0071f07030b08000e00240a03c2e10580c40c0080440d1581105001441000d01042002c00c1c00b81054a14642d81a0341c08015050080c3c0028541000480841003c00f81c0e00000004810341a0203000041e1003468124541070454402034003030b4000300c45884c016070021407004411080350383d400d0740c1980115100e203001e41c2a0303003090722901400110080407a8944d150045000000d100342401401e00324050b5100d420107640d0003d81c2c50120200c20304028951002106550f01c5a04540c020040c1201030340c2d891241d01950404e98004a07410b58040c02039000103100488074048901556142d000c01c108100400c504401c02500807011007500090180004200c148240c40140110b00e05500100441d1411041407020b071000180c5940400103064107010002c0da00710008600d095005511310340700c2e18210700494190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693922392 1250 693921142 693921149
    0x41b080609032505070303020304031506060516060f060f050108160801060513180b0909070311060a0e10030e1b0121150f06020111190c02030a0818040b01020a050a110109 75
    0x14082c2d40740c000301f01130f0004018000c50f481401d1716041081041c000c1000c51388507116440100e44c00700494900a4a0000b0100007284a0f920000d85c1040e01200c0100703d8000742c00040e0140e041040600071903030403100d02e59000a590250f0100341c0c0324800020212181841b604003440340103d100c507001483c6000180207091710000c0d0f58a9000710070781103070203000e0700c80c840b42c0a00c02c404042100c02a01040c86d50940781c00c80100c04694032281c040c0710b01030744012001020041d91103680206540c0d4182c40710030900040d50042440f9201c50078803400c040c40c12249107030402c40340750481b8860340c114801002403140340b541d41948140c901001005000e18050159003400d81d40390104840301a60241030544404c0d5000300494919482f440e180ba100790b000130240703034001803480e0003c1c40c4282c907225089840982602e140090301d9640300341c00d0b003090303000250300100c21034002d60300d050611a0201e920000d02c01400708070003d844803510340c0086040640300380504d95905440380d00544180005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693923642 1250 693922392 693922403
    0x608070e061905070821010f150e060d0b030a11090609040b0a020a030f0914010c18050409020a0305150109052d09011d0115060320160605041b0806090325 68
    0x203100940a229030b106d10074000c00d800e103202d0f0400842d400690800c4000612142c0e04c800002c03144040412416802a486040070070b0785031602c41d0401d860622106440d2842007072984d5200c0e80b54020000030031401003002d8050040d5104010212b20320288644e0032852181c00166140d07a5030b00b040707015219104843d10511f0600c0c181004100e0000c0034491ba1803002802002280c801c040211045040c5026490651030003400910043c44c103644035488040c0700170302c00f003c220ba896445a06041650081c200306007200001004100d0480c0a02d80d849200d0390001045100d4240c100d5012200f5039008108040c4a200010020b8a0960128500da000c913154000407072066000f81e07004c0d02a007031041c3c0032042e070468001039290181c090780030003180301840180ca99072800d0b0500380c960422101c0071903100e41c0d0104000490610302c2014000c43c000d24800c05440701c2407101110321841c41d400f45580d940010100503800a02100340e8000400c1600000e00c400407503101400c088d036800401401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693924892 1250 693923642 693923677
    0x1200102071a070f0206011802130e010e1803041214070e09010c030f1803080915250e010516050c10181706070f17010608070e0619050708 61
    0x1185203805040c0c03446211550f0b41c22803004903807582261102005c8c8607031500101100090380300080d4680181c40d800800016840649503900c00a880e554004e0b400740343e02e00c25510601400001d0000a5010300752580000c519142c60281400074040c285500a0100c5061040c9405c0700710301482071400404102030b80d05d8007030030302824440c028403030040700c0d0300420b180c595001c036004840c0c090034030100e401d420030840c000e125484c150b4492030000c021840602680c40090700c21b03013000f09500d000d820541c40e2f5003401d5180a0040c0d80750404c00100c081488006160850140ea02504440000c1d8001c090781150b00e0300e51410a142c91141000c1035070007051422140c10080d480300e01842d007031800c078010944069807100e2441548410a59008168100c800080c2216010b080102d61352845494800c00e260000180001200000c0e04030000040340402445034066106d4080a005030049444500e001e5030110008a4019100d20300d200740900464074105012a00d0251000454480c6041c2c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693926142 1250 693924892 693924923
    0x5010f110a0609050d090e06132f04050f01030b09010b0904060509090c031603031403100314011b09080601032a060207180606170a1104120b09010b0120010207 70
    0x546800b5511a40d00005d103406c240050040000c0c0d40d110302640014014408103514400003001a000800b015000d0300402c0c2079120080c8030090710140b001000d00c41c0252994101003c00c490704207000d601904050400181404560310b008a0504461800d42016a10445940440d01501190307200c85d501c81440d01c00c2011910000c15142101307030003102030740e000340100c090354081130259000144c006544a40d8501110340310000454108421003413041c002540c0c0d41d11281a1880100d212600b030751a0029225045c2440c0c1c2202c4120505041c070039812030601040690fa20014030002d058181d0010742101c4569100d0400c0c4400e56901e008280080d840b0709000e035696925104030359244072944885040303207945200c1c004c1941c110795a45800000440c0d4841800d650241140a80d01e9580c401401d509411000800091100c02000740e1426100d091654010500600b17860150f41040000781d01682d010810b9030512803010052007030050008511402402805002800419070442d00d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693927392 1250 693926142 693926153
    0x606052205070c0503070308040c0e070336060f11030115020f1204060807021c030e010b04091a100e0f0103050d030614010e06130f06020f01020405010f110a0609 71
    0x1020384065030501800141c440c242c0442c2c580da903891010701590024000340000900c24520550454011020001c0040c1c58500a04040704295240d40110703540e0641c50700c0308c00b5144421102c44c400d0380c40070002c54142c011300e030029069085000306000d0b500c04480441c44083d40c403c00d40709007034401e22078482d80c403040441403094246c5000c0c005882800708240381c0c03d100203021007070402c0b1080c0042c00c151030014250f6010101514000642c02802c1e0440452080311004c406564602d54011942a00e1480b6190031a010740c03140e54003c078107089140c0f0201d071200700e10710071030030f50b50750185459925244000800300140c0c222180a258150078081d03c1c180c6203c040381a40c5c011010741d0500c140c1d550054040300c156205442c1710408085034420700750300503841d00354083c2000e460985040310540e4114141c04081d04040b000502502e01801030540c108440904501a10001c5240504000000c4c2c82c030840c000701e080030040e2100314400d007801d05100e00c0001e182d009400f80583d44032407a00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693928642 1250 693927392 693927439
    0x406020a0311030405011707020a05011e0605060f04031115040e15010315030b131401060806070503010e0c090a0b03070903022803080a020c0d050c01032d09060605 72
    0x150001507400e919580c2c821030100454040b1501611124803045524030400d84055000f000c0b10158081d100c0c0745800315800f030045c0001003130660151080c81c1e40742c0107a102211665000240100000c0c0950510884c0403c219002d4a4100d0445c01c0c125080d080081c1e001044842e844900d26400f040028004007141e41d424000c000156020a0b5101030400440403211452829280e4100e00c6008101003002c03025015002084000580f2421000340c50f03100200404004400150390340f0402044419024495680c0000ca5440c101c3c0ca035500d0149001c14031007018114030a1110300140b0310740365648502d101d10091884410041d103a242c0810050140056444168015865039100900c480b002007504240084c103655a400312506503121001c0d207800c07195144080d8403401c109a103c1e031350b91680e0758516a1049000300a589190800113003036520b2100a00f800d80d201520b90302e001d04451060780140c2108180020b0300803500e0401402800b0154090382e0400d50000c1f1042c03400114040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693929892 1250 693928642 693928663
    0xe01060522050612030703080a1d1b090603060f07020307060c03050a0506010f05180d02030102040f15020a020f09071205090a211407080c03030c0a1805030c040e070803040602 77
    0x401c010664030f00c01404200c8a100490842c2c5030810050301d03000901038040300e5081521054001b6440c421002c03d40d00c0040b82c2e41e04000035500c01c1c850200c211490581d428000304043c0c4d5004141e09000f400b090381d0b07000203000d25010b41110710014010314420802d6914090f08240c091140b0107000c40017400602013500d510808906000c0000c4442d4001c000c2041e4110807079503a541f820003590209614601583c2c20990721050100300b00015986c2400504085e00500c8071240a03185045286420200003030b8a400c155041100040b0150365034a542c0c640000c2f00380c0d1002d40030394400300100c5036030801190b010003a919000c148800c0c140009020300d89140305551103660213410182e440320940310410f1041c0050b540e0104000406160750107401010b1107110b9036800e12403503000003070560f00226990094072101183e184481036126410000d01d42c0e81440400c001c07800c0ca804240c441000c0c0402500032512200401c419680c00c1144600804001c3c065a45403603c84134000d48034180c416 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693931142 1250 693929892 693929959
    0xd020c031c1a090a151814011e0909051606030510052407051c18090b0f06160f2603010b0d0b010e13050f130f060e010605 54
    0xa407a448601201c1c2d03400a2000800180c0325030703a4102464081d1684400005101e100101c000a407500ba00c454101c82141c58800031451078040c3c2a8005400350580c031407800c00c00f50315004020b00d510086c42c641980c001c1d681c0810910800d04201b854808811421241109103007800603505603d84d001600801d0501d41c418030050340d0300f0401501c800800c1500404040a205458000070390100400e80e0610032401d81d4040000151801845c220090800780841d071782c200b0142245605100d1b01d000382107001c201300800080c2c0741c040381441600001c043c1c0290350004a002c4242c11412480c02c003d64041c040d085800d0b09441d202030600c281c00514806c65100c2c043d040c12132540d18082c1d81c16590404031280c140300b084480e08024141407900755040c002e000c9131003030041c2c541101e0414002c500f01c00100c0c1034108031074241d0f8044d2008000400c085030204100c40004c1c45030312011503650b000507010959802849060380101039641c0304907803080452038120200d0b28110400c1c8000d40c0403c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693932392 1250 693931142 693931151
    0x12030b1c05011b051b150f0109060906030302031206040e03070507090f020405030d0f0c0b0f10080d020d0c11040c4b0315080c0312130b0d020c031c 65
    0x249030548050030442180f0000c601d0600001000d9162058803c1034410884210307850030900d1103904040078403e8503e100c010182200601c03a5010500864009201c1180c003085030519685000351030380101c2c90007210300c20010001c40c039a03075565003003808069240700c10384e0b54610b4280380c80707640c50582d481080082400e04d0b802141250551003580e0444001901814400654150480c3c0354807814201009001c949030144000c100321010080c480e130720403007028100d414a0100d40f1040d0445a0004074158401500d410b03109601180d80540c00d541410408180710325440d0080c0788860606007260001d240c1003500c411150311000b4007d4401d80320300725032540b0340b001c0724840d0400742403400c1204518108a10b0340010107070300c1d540c0c4a1703621245000103040b4040e000980005800340d102c416158032010b030458031840c050051045924002102601d4010070b2038408006030818031958541250115103030302507400b41c0c0c0444604152000c1a00d5598220b1702d803100d00c84a0300e407842d03404246407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693933642 1250 693932392 693932411
    0x2090604060b030601110a0b10030308181c02150c0913050108070b03190e060610080603100207031701030320030901021c030e101d0d090312030b1c0501 67
    0xe842018103a60350300c291540355540d034900542c1e0b1000c482c50170548501c204014040800c10301c001860044c1265450b400002e0301c0c1d0705004120b0308000c0d02c1da900020310800b2142401d00b0001303a0a00304503000e10b00820811043d40240d041100c1132456646917100d080c00c01c0f000c5030050340281804142240c8440100c10140e8540045074024015509583c1c4841d00510200707002402460b40075078000c2c10f00703403000d050403501d009031785e8501e401c0d414641c00b81091110300d02d06404498880c0e242440d00303c5052518000003661903c1807224400f820342e0015003a02410f200304005040c08148440a00c080c0d6580d00d8024280c002042c06000c1443c0b001740022807511000c000c0310320550050707004003404400f035030444541840314440d280c207041d520502d000c81c0c3c0780c080c070556043c2c914003540010b41601705070182074546c0c590280d00507103401c002c1c01d6004c02c4d07800000c84020f50360040d801d203091950040050b001000c1115005510910799401c020020310032a0801703402e04d200740c0091104030300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693934892 1250 693933642 693933649
    0x3110d020f040f152c100309050613020d020d0303061a04060e01030c020d11010b03100b0306010e01180c0509040f090201030e0d0c08180d030206010305120f030705090a050a0602030403020906 84
    0x16100c0c004c00610030301d401d41402442140d100702030014204510003d1408400061a403890641c0c02c80d02080d1191841024448180b084950001da216841815860540e0001e1b409001c1028003d102c0c200c00360000090520a40c400340190281d0540c860b0701200d00c1c244200c1c20f8000c1d10a03240001c1020320400115442400b070503900f00c26a400034400a412000240c5002c56200c26500e0380e50343e10724883d41c00c0c0d68100007201456402590010340082c80c0c81c285814004140c01119000c00181d0040054076803e5030314068004005c140022010700803071040b180e912484402e194828201000c5c0c3e1800002c0d0f40c4a0307800746100340c270300700122810046504c0c0c90720601810714012642600380700300450030043c01407464007142d511400307448241d10002542120700313071810b031b00683c8064014400c02008000704907010b050f016a540c101414445142454880140034008005001c151000c00c0d885110b050406080d008020740305041e1200f000942e81c0e08148405d030b00c41c40d44000400c6183c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693936142 1250 693934892 693934919
    0xb22080a1506030804090203071e03020901090e060114030a09051204290d09050f010614130e030703030207061d03031b070f0209331005030f060103110d020f040f 71
    0x35401303c0d00504051600100400a4000130300e06014400820340c030a45014450180b41c3c41078169450050322036403500c5c0010001321141d0406c200d10010b0809102081c1c0c0c0201e21000001c0d05089140d0f903076a01c2030105c4000d01500701c00149181714610090040310851000b802c00c1e244200e2f03580d45041b220790340e5082448540d01d9002d00c01c002c1008104405100c80d0413100085015104070751040c01e200c2001400c481d01688542c040b880e034000c10780c4440c1b40141e815464407080a40c1404020004c42800381c5030300c40c0c03910040078583d00160321810001329411951164074003480903000c10b2071880da2580c40798401c6400700180d140070800c854107194000280d410f01d60708000d0003a4000199400d0022110018146518a078184c0306141503050b070f4030340442d0610b07402c0080c421aa021400070b05c0741a902c000c01c92003d11400388104524092143c4c1d074564005400d18022a40b19200d100d440e60320b21a007071080021600004100c032240040000030011505000300400e09a99201034054041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693937392 1250 693936142 693936149
    0x71e0c02040b24030603070305070b0c010b060418020d09060e0a020f0406031110090b070804081902060d090305160605160504060c20040e0d080703150b22080a1506 72
    0x2455152844200e500f8003001031540014080c080b5140359842e40c41d030300e1401d11168071400030024000794900805a00780124100a00140c45440c01c040c280740c541125641020400d00b402980452460041d00064000344080d0750480c004100c048805e001498407098105000e038080c0c580d11411103070a040c2845507808981d0440c1145580400581c10010702441504c00c44041003604400400d0b8044540c000300071052240a00c4c0b6035691501e4a202d05007002c60107164080c0340f04e8030040f00581c44d92030484411424420b80083c40c56070600c0c05032200e0247c0f0b0340da0071f210112102c20008000c1990b001500600c2621043c54480381c0341e1400f15076501c80c90007031030000f41c601c00c01b4100107202e1100000151a81110300300d003581034840860304460210401e800c0700e40c00700d00d43c030039800c0e08948003540003042850f0a1080790b0900310481c9032001c0038402e60202407070000741c000c4401003221100e0039007040c1d5000108402d0b42d50300b07640d54481034000c00303a9100710420245031001a09102c0d01045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693938642 1250 693937392 693937429
    0xc1407050a0302040504060906110703180b07030c05070b0307030b09011502030909070c020d150e0606150a090f0f06020d0503040c0501140717030a1808090603071e0c02040b 76
    0x160760455091002404018104854058075007034070b0340004116019140c3e44540643c0c40c141c44840504008000c000f82c11400ca0000d240305200f808110204011150038640604040d41c140e113940c901035250140c3e0f60f009910703202010017405403580e415007151094100c211044411a41ca619000c0c0002d0841402400542e0013008608410f060603900560f0022980c00c085010504039004900010b24000048810024032505c0040c2000580f042c50204034884000308200d15104020070040c107003c0070307a00c29003080402c0c0c0c08181c61150300100007400340311599000242c1d45da6100042c081681c040d06003d4001d120304060340314031807825248260342021003080717194a410015101c00011040c5101540d1b800c000b0a80880c03070b0902d110b00c3c61071161051584d2464030b2070900c0c0803201b01303000346490080c0401e950004200e2500584211510440b000d541d00d4481c5c4005880092401988544403030143c4140032007070341c201e1001d4803040c1c001d4a040c42400c00c040c08120044000d034407107944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693939892 1250 693938642 693938659
    0x160f0603141513060608190b090103320a05121305130b040c0206040506070c030507061a1c0312020304020d030c061d01060f08030c06010e0a0207120c140705 69
    0x51001040d0b00c206544040c00c000320000d8101d1294056811642290002c070390f8440c1844094013544048404444646001300700e0030501e50006000c01606203c068846c1600120f07001c85902c5220383d1400b04108150040f924849141281c1d488590446080c2c460380107072001d03c0340d9444030b0070880e0840c0c8440c04845071024100802c00c0b22881203084401e8140b0380d85c000c4072900d52214410410302245a8008105c2d0345050b1030000e00e0040000d0152040000b610740c43e50002e071304501607030141a44460007142180c0c0000c100403102424000c000c0c1d20240300c000d60b90801001c3d03c28030000c640203580d601401a42d501701c0c1426840103880081d0082007082c03101000c01e100b45d0081e8442417003443c0100d1500c0d445001c104990b140c00c044d0308021b03507403480708002103200140d4810092000801640c103000351f480c2c94944906051048070000e9003014001650b00040340e041710810b0b0f50200c0c00c0d2810705102c1c0b0000b450f90078803000072550300000d030750200c3c80680c0018104003200c000a11444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693941142 1250 693939892 693939901
    0xd051b0621060910121e02060a0c0b06011d0103021b061303030b09010b0d020306040b0a08010e1c090302190b030c030f07030902100e040207050a05030306130501030309030210050c160f060314 84
    0x103215112107000d01b0001035814490b007005035214401015412070303a03a101103500e010b40c18100c00c2c03000050b0003941803003110f0a0380c0c6440020349182c100b1104003420010f0710340e80502c01080f0302406150a40a2500589c006c212030038000002003252107020b55010048080d107207051055140702801500c00f03801061010f042c010070541c00456028401400c049450005000801c101c00c040303402c0303004107035150080ca40c0b0340001004400c44500361000000c4151403410070160904145010180c05100a0000140c1c904090303501c0000408140940704d90307a24003011011042d40040c2c6002da544154440401c000520078002c12454580090034600c42070101c5805642d490420b09c100e0360001e400b8032200020540a0141c0010140584050760341c0f498802c00300598407121404001000b40340400601c0441e9001c2952020759506423000c030310141c24118169080c0c011070f02440042d10840400500088044004000700d840d0300d80c0596850352174407000d405a0309209684200480300310000b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693942392 1250 693941142 693941153
    0x2706270705031509100e012708030406230901150602060709261e0106050d110f2b020a090c0e060f160303050105010e0d051b062106091012 61
    0xa50300500e81c0c2084030340d00041d1303c107000d003076443d0341b030341d4644995448105540c0c80590a00c20b40140351401242081e10007550340c0d803c560f000c060030107850755544054000d0559105503042c0d50345030003d00304681074901868594040c0044554041d4803c1c002070300095181d0001902038040d017007a80328801c515040103104441c1c032060083c2407809103a54500103101003000e01001c00000490741160042ca84080303c0d45082d21003a40c0300500803001c103485480401c06010340e0310605801110003000c64210100001c02c0000100b10802650941c0c030342034001c041280ea0b401c01c50a03c2a5a04681d20703903201d21075001c58582c01408000700300c1088512400740342a100400641c0d52100d02141044041c543c0b40e00140803404080300402e40c6c03400103110543c1c21a0030a030703103030b281112060004401991941c0d1100a2000d45030440100340303017815455603c0a040e10a0382c18401e008551030001ea22269045503c2034450034014410034010486110302034200909990002da00d80032020165541e8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693943642 1250 693942392 693942433
    0xc0507020616030207050d06061706010602031815040b03161409090c040e01060f021c0e06030711120403060e030703080f09010f0f0504020f03060708270627070503 72
    0x3c60440c014004081000c1d0381d003070085c12291740a568001a02c9040c00c26802c400c6880d01c4910030194890340041004076030020840300e4000141034942030300c0864002003201000c5280d140200044041404141c000c00a405140300300c079294900146041c82940540e41d40d1800c0c1520400c400d4100030350100c904014010382d0308101d042100e2807820340da401d01c0343c0000d1000c0c0c029000260b41817400003512a41040380c0240405c1d4410404940541c4010260a420811003464002e90012000484544c000c0c1c2d00d0582c030111840a03038103194120344000c291076015000489000b0314201c1c46020f4001e000054034a0f161340340d100d161090711241040c0070b004000600e0301c0301030f40d04c2d04001d88920002e07020b24111245028004111814948104150f00c00070305081402076111074100a201e6602070f01c00c0c0c0d001000284800c00004180300d0081d00121407400e907000b940f0501c0107002c00d85042d100900307103150309000c801151060196885840e040e0758401c1d00d0340765001003006140820745084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693944892 1250 693943642 693943687
    0xc350a02090f040e0d180501050a08060111010e030d15080a060e0f0114060f120c01030e011d030403020f18010902030a0204120b060307090c0207030f06060e0c09040c05070206 77
    0x60b010200340386a001905a81803c0840c41c00ca8100044100078503800103440b16009214030301300e1200c41e041c0300000300903010b241000030420041c140403400503402030350a0b0f80c2d10304d2a0b000a0001c2084024a50b941303520503112a4802c501e031044c1c04804141c0940c1e102c09540381c8002404003040c9540f112809000e01024100e1140102c1d454030507e103009204660300c000d0602044082454044100003210102c80304140c0034896103102c2e60360544d4086880c5104200c04d0130001500e000070200c0038010140000c603041032004c80150040880070020142c0116842100c2011b1040001c9041c40304d00310500c420000d04c0102400140b141803659000340d50f01c10644080142041e0355501e9000a903015205c0668080c0034600900c09103060601208024100f250003c0c040e0454115000307654000500c17020300803140e090701d54010844a6000040207180b022140070480c00e0200100c8096405117603054840d918208184410034012003d480005800405990505804d51103207403d5008460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693946142 1250 693944892 693944899
    0x7050d0201051c050a060b030f0406050432070503150a090f0210030e0f060714160c06180e0c0703122904060f050303071211010c350a0209 61
    0x440da1620640070700f10104540c10324004505410003240c0c6000311900341e04401e000701c20800030441c0341d20804100c0c03608603a1022000406944034104030031200b04140107084e0b00d680e1141104e09803401c096444110700903100c160f0311529520410076a440c1007400708400e00540701c600050007440240d10100c1800c0c018034076914842e12a50019000180480091000c40e41d201034041c01102e0800a00c148840002d00500260801c954060300807c21043c92000d5101c0002d400845509503403020265550b2000710403140c2c0d512100060400100c1044140d403844055100040c080d50291005005480c0084464030740306c0305071401c444100c104e02c904650349481d5001d80f115824010082824800c08281040d003541c0404108000d65100d035015862101c28240284016540031003200c01e4190b0140085011460441041d514038524060322441541703025081d131301040e007008407200e01900c1e0020404880080070b181c10304d02a10400e104000501000c00908645120b80c001e142d6003e000713 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693947392 1250 693946142 693946147
    0x7090815011203120e0307200f091315020310061205010b04061101150b0307030b04020c03030c03130f0506040204060b0a0806040f020909040c142403040f02030a061d070807050d020105 81
    0x4c0031054130310344c843c0d50704483c5021070420780000301038141d41800481c20300f09c811200d910030702e20002d0301202000d00b4051160348540300610402518100d032404d414080c0c00c0c25526480c100442c2c584000b41031050750081003800c013000e0701e4101c42d88285030698002d108090b040a0a14004880c0c3e12a128041c0c0515075851044902185005a070300d0000e00544030700d190340e40380006c4020151001c41d050300d4000c50040c48516a03116020098981c401e02c0b80b00d405850355107000c40d070921265041e4014214003180081d18044c040b0106105101d107009170340c2448425030704c040d150800e11450a50500050043e0082090f51415401c13440d0210700c2c041015082c013540d2000138000c901d05503000c65901c503541d08100031000e89009031000311030044a054244a211001800c40b011488079400c0701464000001010848100c14080e01e094000d002c0b5a8050a45c0c40c0031f030000c05000c0c00d030700d900e802d0f03010b5920301e0503400145440607140340340d0182c8400c1d45007009000391180304440c00c03814850b09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693948642 1250 693947392 693947411
    0x32d040b03040507080f0c0a1202041b031a100806100201110a12060b030108030f09030a0f0b070305091b06030405030d05070504060e03010b011d030f03030709081501120312 76
    0x800c02460040d406000a80b005900e0722601c0303450300003240c940c04520f400c14030707031100c290f640d001e04032044035a0088405280d50781440060001d1550803501468020b44034100c065003a4141d102a0741040c1e000c940040000c9501c0400500c8082841000001038503580040d40505100349060030043c0d084c000403030301c0d880c1490440c500d030300044a03140010b80030020b02030038500c1c14000d0030010016480c803076140d0750401c100d09840b8403c0514100315284001403058594a04100344008941c10504400f8240d9142c070b4011481c10060390980d00003400d01011070b042e40800f180c1d40103841403080c2500c440d4a640414007680c1e400c000d005861b6404240514400e04402c0d000c1e052084282e6500d80795101d0030708901520180044441c1c42c003da1400a0844403030f41c01800d029284204a2500f46821a1000001c3d1800c007640c120141103010100502010603040b8406009442d05030007a5402c00460070794150307004409200d81070040b5101106000402d01070041001b9103010540046800e42c103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693949892 1250 693948642 693948659
    0xc08030c0c0a350304080a0c03090305030d06090510080303071419020303090601061b030e03010902031f0606020f0d030209191206180309090e15011203030509032d04 73
    0x8940380307100003812420b660510603442940a43c034281c00000c25940c03d506103a00c03180454007031012500244102c0d5118201818082d500344401107500c40f0849a03559503140340c52000e0250351040f4100c10741010003281c0c12804103404c40c0c050b202c56100440c116940c10400f298448118982d000707050101300318911030340880b11364428918000750019566030030b00030306052030414164080340401c10504001181c0602e44042c03004015010710302144004603140000b0f00405ea16000203625100d840903050f001980c0000000181c6071050741000403070343c0c0d180240c0c1c17034001d4600c410600380c11041c04405028080d601400030300f04054504001c5001d00c1c0707203064004a05070071925942420a0b0381c0d604001890040052800800c0c0405141d526144c1e005001d6401c24000c10301d48a485120b607a440c501308202424104c0d1310f29035040c440356550a0366030600d003140c80b425000242010002a10400d00000b104c500302101c013000c142c0040c01401103180040c20418050b03100104110016106a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693951142 1250 693949892 693949913
    0xc0b0a020d1802180108070302010806040204380726070b01181b052d0d1b1b0b1003080c030a020106050a180e0c03030a1d010c08030c0c0a 61
    0x4400e000302c200c0c800e010700420081c0c1c0800500b0905440300440103000c4403101040d0300c002c41c2d50a003030080c1603071641000140607000d6604024482d5100c846191146402030000202d140e0b80100507403c60640e0204000551040c1d0340060b1a410303c440c03440328003c3c6204030704046d000301c01c1c600505007485503651082c580c100f80e004080d00c20450300c090030704400904c10080e0001c400d030603445642103148006811750044152410701c008024001041c13a4200081e00502407140079031007030392520011022001408000448099038454220400b840c90040e403c480a04601c803074034216100b02d81e6030b0710903010001004007071001e0051600100017101d000140050600c403901468442c420404000e003120555480701c0d110f1604400300b044400240003070040203482d904400326444613088045454400c14414403a00343c8400104003082a5002d036590b80c00b8483c00c0200000b0307000410044030300380322a18000d001e111003040402c4814807400b0040c0010440300003076424105940d114007080e00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693952392 1250 693951142 693951161
    0x1150b03101e0e10050109030f0501060f120308090304080a02220606031d070501140901090815040c0605130b0a0c15050a0f02180103110d0e010b120a030c0b0a020d 72
    0x1070324114403e000340c03040050b800c3e41c4030b02ca5000343d1300301e1890080020451242840007030004604160b5040c1401401c2d0045800ba041460000840503501c01072184c922030002000d0b40091410004192955404000c0f6011aa035040080c0390588a40d020004030347c0d000d04950345051404100d1811510140c0140310040041d91000544002e1260702c010300740c1c440220078a265004800d05101507a000a01c021030050741543c1d0365102c080d01d00c01a20154101d0308001d0862041a4558405800042e101d030b2041c2c4c811f40b02e92113440c1e40c6403030035216409021804165a0360f41c1409025402c0c501d80640121440ca2500e2801b111003078075044005800204086601364036001084000d220758014603031103c0144a04504d441c1400c1e910902c60700d001007006040640310740c49400600e140205607000f01071400c4007080500c1a6840050080613000080d6004264402029400e104003041d10742e00c16804d130711480d0000c03001e55641001510010032000400f542417026103903500d250f00c15201031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693953642 1250 693952392 693952439
    0x90610110106061806020d02060f061302120703060f0b09060d0209090a1506020a08091207050909011b0c0203030a030b030f03040603140c1303300c020a060201150b0310 74
    0x1803001500c2a1302c20b00b22643c012500b07541c44070301170305800ca50005485a00c1000c1000e10310131742d290000000c461405002100e44d0040c008203c058003081200000c0703004861325202042800e941d5401841460150321a281c9000000c0c08002d80905021000700b07061821000014501404c2500040707500f0000c0e5001303450310f03588940d00e800c0c0003540001a00a88600d000420f003a0780c45a42ea4000c074841c0301c41c80c900408144c1c3c10f8011000c800c100d0307103000d080020303e05401303854042a000d009211384102034840450384a4044141070066070b120100c04d40250140d8505a010841a000340a15180c91030b0944262400240d10341300c1880a00040c002c00c1d074002c80c03030f0560000600c1d40c83c14040d00d111007150b0200507501050021441c5407080341d910801100720304c800c80c420900c0b4985e103038080150001c12401051340003a402500c010b0f5485c801c8541d03040c000d4449500300e08851544c1344154400308070b000b060000300394000c0619808551050480700c0c01e911401000300703010695000804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693954892 1250 693953642 693953657
    0x1c0b0406111b031e09061b0304030c060815040612020d020d0203030f07150e19050703020a03230610050f0d020301020c03120a09020303041a09100e01030c08040209061011010606 78
    0x440014460903003200c8603003813a4440c10190064001012480340c0c411803c0e1010014021030403040050003514011504400300e1410a680d901c0003400000c4116010082c1f240103290100720b81c41e041c4101800e460f03d582c0105803015499007805071401d0640002d07a846000b41d00c1d10801030380d041008040009844a03099100d17103191904441c0030f80154503092159091500c0400a540005040e00c40f6804206005110304540d082c00c0b818840203400107508480d03006070100501c140e205225100358550611192030352142c1a2075519050151803189074011414010070003403400c00301580204800070403400c1200490740c0000c0c01c99100c07101c14641c41c3c00c04600442420b0311145016481a004034003803014120940c0065107038451030140c9640031300d410f01095405078800c01586e201200107800c0d032030b0000703881d0030150103028007280c064000383c00c013440302c00094828041c06004a034081c044094903140c1c03104001c2402c448a0b00c20041100440031188211800d000b80c000820081d1503080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693956142 1250 693954892 693954907
    0xf1b03050c0a051b1c0f17041505130506090d080d0b040219020d05030103051c2606040f060e04060c0e061305090a090b0a0902060d0c030b1c0b0406111b03 68
    0x4515501c084651005c801300c2601e40000c81d0740d60500408055008401c1c0b00c0102020003100b14034001c54101805100f221095003880d15040002403100d0740d50064000358580e540c804116091042040e019000020940c1100000711941c024000482d40c422011480d825003401040c02c81e080341044072409005040f101480d241c06100c892000c0d0051b103041c2f0f1841d8103540318940c1e43d00400c400d00482c2003c052a09110340e00c00c000f00c0300c401d03407101c000181981a10003005800300059641c01e12680c0361644000ca105c01c2403048508480d407030f0300c00901741d545580301c01c1c1c0286003200c80201400b40c4089108041c2c0d654500600b0400c500c10000e455a900780000d214821000a18400501d0710742900e0402054409030794940c8001c120101180300310440c408503029000f40c5016006043c1003240401101d034151304a82c6a1a50070b440c000c046070307013030010780075101c2041002030150302c160000700300851140d0300024401c1101c0400e080c07920204030219034488000720b8541030150400300b500c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693957392 1250 693956142 693956149
    0x1201090b0307030302120a02010b0a1e090507120b03071706040b070302090a140f10110c0d0308160912060608010b010305280e01110a0f1b03050c0a051b 67
    0x209030400150014400039007590740c082e40c1d400100c0601d44509101050140c0c00c64400d4010400307012000e043c2c00503666460100b580b541780313504a0178180700815500030071aa440d0b4403440384152100c0e03a64075002405903058070000c0c404900c0036505401003141c0030880404824003140014015001030082c0d00d0301e4100707803c5c0e00001505020070503004003c6000b041d56201140e0054a002101d014182c5002400064040075560403071071b08400640c40385030740560410344501b4200725800c250344c103aa42c06820000c030300c100568002c010500001c0070400710f0340c45d1000f0442060755802e040000e50303103c460460454030f5614044802d1038440c00148213000081c080c003070f0300030300a080070b00050614072002d001c1d40c0b800740c440c4100c6101041541c1c004c0c03c80341d005402200c034210005c202d02500c0e51407005044e400b20340704d880419010401000d00c0e62192104d003940740c0052880024075980b035901116954059801200207104402060011500030f00c80422002400b0494055040c8240c6c00e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693958642 1250 693957392 693957401
    0x806090c030f0c0a03111305040b0610020a0c030b180106090213092a050d09050a12050415121103090709051e01030803040203012702041401060e0d0215120109 70
    0x40e80402d03082103039030b0f10803900c681e0304800940e540726003140300320110013021a4070110310202c4600c1c1a410001400248401640c0d6140151000e5404807403510300e04100781d030348510000001382440d1900e101040842c010089882e04040245180307070080b1106035505081d16455001050001e038002010551014480c840701c00900310706030f0a10219103800303101a07040e482484140c0b0b84220070205500340500c258211483d41c082424100709041050802a43c3c450010700c08460080400c0c1001c0728442c091700a44086031210410049908201c6e44121460a00aa00750400c2d50b1140380b010408025403001d9803113000c03400010f080301c52400109206403078000d08500f109a000340b08100f05102910f0045054136000081a980c980323031440801c0c01001e28814032103020140320449640d07075151900040a4600030dc5040c0b004007e18102512040d200388942c1000c9106c4000080c1d59003005c0110b4091680014034001581d4620b03034031440c1d00d5000074100545c8180d00001030044600384d108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693959892 1250 693958642 693958663
    0x6310c050a060f02010c0f1b03180e04051213031b090207120e0f0f010302180406030f0512031513110301090e12040e0c130306020430050c010311040806090c03 70
    0x5124a1f8888071010150034034001c200c3c84110f046441800754227160180343c01680320301540420b44a0a40d4803c0c1201c0d80300d006640c12a524014254140d65490600054070882841408861480d5146a41c0c280034624002902ca0981010030800103200d812407016014450203807640c108940328044006000c08041030540d1300c609841000c520003030300d400b500d101d5502c0d401c2c200140c3e45d80021581c100c0c40b941c1c01e41107640c400d0a000c0084108014507d03800141d87c400c8007200d41910b1090004841070104803400c0326032200300005c03651a45409030542d41c50f0f003035002c00003600c01088032070a42d040e0710981044034216100c6c8900d401101d030802c2501038813100c210142e41030a090030007440001354050a0030001e03802c0420211200b032110f044160066502800855a1360340d6120003442d00008829100007105031500d00205240140225403a01c0e51b101c006024014045001074000340000c0c0501042000c0901004c80e49140070004c0e1809019820020185070103000205440c1400010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693961142 1250 693959892 693959897
    0x3020d1508071401030609020712021b06030f0a0f06030c06020d02060103120807120f09020a05041a060a020a021210050123270f01030506310c050a060f02010c 70
    0xa410800c210011801c00b003034a241c1c80043e8108540e03c00100c1c0644280e130071100e10184001510300801c04c50070900d8860181c0d0b44c080c0c5200070000c0780403004540c0c0c10034415402c82803c000040155860300310b100e42c8140c0910300010b01441040381c8404403102ca400132540585504020b01510340c040008910500305440100390380e40c1142d03650f80d880819100c001c8184003441003c660502e02401541407141d103407140402c284085085140043c00614209170700450700399a0104041c1018003900c0169000040c010350541da00c0001e10060754080b840800c00c5001e00d100d10070041c0e07180c01210400542c07042c014184101018002000c4070410390208004c1e0341c40e0b0090401407100290740d580e131188101d50403043c01004040f0a41031400340c04400081c00b650310200b00c04240c58540b682d0580b8060011146e56036a81190b1380500e07e694081100408200300340c01e0ba13405030540d580c50f8442d1050031100380896641010030f59020032600003d011404810301d8500b16a824414154040ca107403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693962392 1250 693961142 693961181
    0x12020a020a0f050c030a1101080c0c150a021308011a120717030f0307020321131e05030c060f070c0236100501021005010b0f0711030a0303020d 63
    0x1001a65800c0303582401416190754010250a0040500c594103444c08090141c0341c03190624a0003c110001800056000c51003110201b4a10f80c56002901c00c445a0a0001c0c82030020707001c80c0800d96034004204511141e001c004414028441e40800d00050030b0500020500e014220014850500c200e6021402a184c41044202040000030780c10125008480c4010b040b5003850340c91401c40c8503455078030180d1680041071080c1598000000c0207088040c03080e400380b401803882000040e2805454007181c51148000c0700d0042102e51512420401e18180200302e1b980156581ca42140c0140c1c111043d90f811040801929811941d942076118145141c02e104000d401e6002036074041c481c00d24a5400c0c40d410480d41503802c0740700b07014600d4101034600392487d46015014403210084d540106401030151010202c42030440c2c0c01207a050301c480400250400c801110503150b50b0300006410b8405505406080010303480038442086000e00a940140e603480e2035220312800e850f42c5203881d500c9884503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693963642 1250 693962392 693962407
    0x4020705030307050c0a05160608060907092d0906030b0114010516020415030b0a06061e052b06030b0c12071b390b04050f0406030614071202 62
    0x40120303948002e4505083d45c5a10b00709601c07a28200545c40c0003491440b44100300e08140b000d0350100003c0716a140d031500000d954403428010b0703440e0113560030302c003007081003d041c003445d081d01e10501c1020b91100c800d1a100c5035140891036614030943d0003510a15a600030600a000c884144140501000060700c000e8004a0000074043c2c40740f070f07002c042c030922440d42c05030455541d50040016824410003031208207403203041c100c004043c1a94182c018030700c0d1440014100740640040003000e19a10003400351640c0c0f505080e074650784100c5075a1034000b810300ca2151489250700c0b401101c0e400400c1e00140b61800d5140004034624040c00806070440305000341c2d440f5a0003007100c103a01c482d080c03801e0004210302d80c2c88210080c81c080c0c07004114502e0014900200790310613401e48400ba450003540e18201042d9005200110200d000748400000b00b0071062085040181100140d450084c0c40041d007943d8a40702c160031140300240f2100361a0004060020140d40180d6200a07a03040f01e0085203840d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693964892 1250 693963642 693963653
    0x22080702010e1203070302010c110d1d0a0305100207030906080c1b010605040216050d080906181603080703080f070c020f04060503030a02060a05131a090f0313080606040207 76
    0x65184024100100700c10001c1054481149160707020b0540d00031030307417100c0c3c8a24000e80a46411210200003591101c460f002c000b4000501b070302101c0245e2100500603081807d950500361400803031036041781d441c02001002400400c6a03a0600411540050702e5030420302c0d00800d81d4246501980410103000140300754440004229815804090403900b008074011040c6170260640e0f038405a03100d48003180a17800c0710303a44030b40031f40043d101c1c1d010303a88031040d00c510a845032481501c01161542c41500051010382604a50400907000d400444400c4400b14041c0e8034110b0b86900b084039180f502042c14401c05030001c80458220b5120200e012031403802140080c50784149000107403085040800700004c40e115588844c015100250550340d4955090902940c1e0f02d0046e5000c0442030728000c00a9514650f8000707066003658454140950031401c0c0d020603107da28041d20820304c0d40541e540d0130035081d00420041118898005900d241140f4001e1403a00b82140140100d000303e0042000c00005003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693966142 1250 693964892 693964897
    0x50301060f1413090e0102070807080c0304030f0320010528021210030507060c020102030a030f15080f0f0703082b0f05150d03022d03040e2208 63
    0x11814500740c00241d25500d0102d0310003510710400100c8003400516540d10703050003031142e010345515003420b1003120010190107080340301d50100941580c0050202400050045e0010405071000804403070905880f070311050380402c4001d0084005c03a451003031098000c024000e0071281e10440e00020415403500000054003904401c6c9400395a0310749840c0220784603016070542d000710030b005a132011203140080f00c882d450001c500069800740b0404070006061031141c11880c02d81e40e0b06034007030350420241d01c505401516170900702200403a11100015560341a640fa400c00910021008241400411541c0303030a10401e4490318600e034001c0c02013400481c041500302d5014450034035101500b448400c004048002c07400c2911003100e800e0000b01032507007406422450044401d02000b88914a4400c10030062405401c0c00070017507049820b41c821483eaa4080454031101c0c0049408410340003005c4d400e003164802d802405013609541c061140200030404040d2110038a11400d4200080303a80383d101160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693967392 1250 693966142 693966149
    0x182202180f030a032613020a0b1e070f050303091e07050d0f110d05070e060d020f04090201021f02070605010501020601061d0439090f0506031b03180708060403050301 73
    0x842c5601c51500303c01c5c001c400f0000d0000d400343c9a8015400c1c56803024074400b00042090340300b03500980000c40e14101c92012078401001c40c04429501602a050120058005500983d5042c0703120010f00d0200d0400c0c03008521410507180603004031140a0194049050100c4c00401d00d940320080c2480141c0756481e2440441c0d82055081c040040b0b24540b03100c0602640040346c0d040787c1440000e10400c80c00050050070b407410041404000d0741c4010900c07a940c0c90008010394040900c0001c0c00e039500b41071380543c10250040c419100002048225072441140d03608140c0310041e4005040401d2143c907214030fa0151109101800c100d500d480c800508003100c100600108000e0007034980c0d8640e4466014240240301540400014840800c8503889000c0400d11955004110101000c1a601c50756410042e40c3c00715011324001803c040622415820040150f082d1100d00100121400c140740040d61085021a0140451140740c920513420a10241e100d220140d1000c820b00c400250030405a9054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693968642 1250 693967392 693967397
    0x18170a020f03030c120a090b0f2502031f1b05030c160c240e030709020c070504060e070f02010c120c0e090a0b0111030906182202180f030a03 62
    0x5030300c580707000904611801803541030314401e038103028aa80003c0400340c1080000358443c0b00026940716116030540c0300f088141440e500c810400005040000300e035084189414101c4c50311a108035502180c500b0382048442c5500718000548010a0b22003401880c03813402d800c03c00100ba05008001c003501074000a000684100804101d0b82c00a07200c2e580c0c031001c81e5800c0700702144559a10b41d40c2c2410141d2040042d0a0311007403200d01c0d503603d40030303118032014444003030300a2000b10b00c1c001c4100000e4000046d0000540201070001a0036651801500c004d480c4000c40c2d440d09042c40500a0140d00031040450156414003491412980d0003100c540448445500c0100f0505c161000c2141c11485909006510400040501004280c140c1c041140084282c0311000c100b56240b02d0181e03640181d080e03296001c4400c2100e901201091200c1e001c810402030032000006000d129188684d50001d034411480c1940403801c1414681500a03000c1007030300980f450800400d04401007500c904045201509 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693969892 1250 693968642 693968659
    0x122e180c060c1b180b04180201030c050d020414030c030601180902011b1a060102030c0303190b0d08030405070b0c101d0706021e12030a0e0a020a0618170a02 69
    0x14400c4100c03c010109010784000007505855904522011206a28201c4400d2400c1d8130003445081920428213140381040202d1850045a401100035111500e40c03042002002c0c885801c03602c0181c0040d1004d005055002380710703030aa9506041c41c2c06000d070724280c465404103004219880c110b8402c032062031f5401d01c0101e018101800181e0f050415403400004121000d2840020301c2680021080c001c5c8040303c0890054640b20012a0b030384c0a03401007803c0c10b400c02c20101d031002c0f0b0703400d0b03040000004e030001c0420b803131507090b000650103103102c4010b450070302e00042084100305040c04508003602e50340941038200342d0140c10701962150f04d504c640610540d507541003110300f40c2000c5407440c1101d90904896089483d5240207440d03462010500d40140c20303450f000c0c01145d40100d04c0010303140c0386c000400e045139507407241840a010302c4020541c10f40076401e180070140e00d813070b04484060044c0c4d46500360b46a03a020110005050b656000c03080d06000d648080454110200e2a042d219404a54015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693971142 1250 693969892 693969917
    0x20312041704030206210c0408150604061d071215090504020102010b040e1f02030708340905090a090302061f05041a01080906010501020705122e180c06 67
    0x1c045101e1034001a40c407101c0440c2c1000f0420091217590500c02c20312680d4041504d424012600500a03805280100d0f0402e6280d111410b41950711560301201c000c05c007040c081e0344c8441c0c0d03000d0098000d070207000e002c5240c020009001c0e00705c40910172120101d2010032500b28072441003949541c050090118507a10307103020400396031003500310b406a00b000600801c0451400e90b140f5554a0306895848440d601e10804148140a0391003641d12500f0142c0310700076140e50f1030706000500d00c10240e0911301a40c0fa402882c003801c9160030b5100388003019465042029050804110000d60014115102107003412400700019601160309504040f942c0c85424200b00d4042e4007103844001c1e508495001b0b89480c1020003181d112000340000c120003130f00c80c4334040d159408a141c46010900549000da030041004000b14188032041401b8804514251007801000d407004020161280b180307c0d62541d022283d08a052440384504c1481c0c2442e84051a0920000d40c2c440b8400308443c0305000c00c5c00041c0c014003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693972392 1250 693971142 693971183
    0x60406050405012d06060c0c090908040902070b220f11010e03120915070507030210050705031909171203040f0803040b0717010501020303061e03190b0702031204 71
    0x41c9610341d02903143c00c4d40e80e09950b800c00d080c00b4590314001c52509261002808034001c402e6054480d4100115108540c01d110540e8050058850200c41c81076081100188404c0f40c2c2c80034143c86482001600086d08141f2165a10b880b60361084050000360b06041000050076150b036a126154414902c03141419510010798403000300200322609401011100c902b503002c1d10000b81740540301106c07040000e00c4602c0050030540030b845001000340c2e1002c603007400546040401e01780881101d2030105e140081c1682c0c1d160450304038440100708200006c0d9002e11050300003600748041c0c22000d042503d41c040800c2a1170756a04c1c40c600062000c000080030905120340c0401525840b43c10256296481c14546080d41c4c1c00b120445091000403041c0e9090828091190311080c12103c0581c0110b023152140403c10032800d014400d5004c50320b1402c222100d144c1c07024855450b01714143c0c803c000301001c1ca070801079032801004002108642041000c83c441180140c2c803e50001e4003c030200407601c9507a42076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693973642 1250 693972392 693972401
    0x90a060807090603060e060118021602270108010507090e10080d11010b190b130e09010e010f05070903030c151104060f09060e040e070f031209061106040605040501 72
    0x5007401607210100d0501034a4010404991240c5000c111410400040030f4031110280912407044c035420620308014a01c07a0040d020341040342c03d008109007a25400141e44840c00b01a642e405e22681c1518103480c82c030422501c2c01020940004c1c006d610340f500f801403030207050b0302403580d0010070400030800d101400c005603030280c0704040c1150301d181c1c1040000f030144211100303881176075800c04c1941c0005041c54840c1014550070098090009d60070100d0440c02500420312020202600c400c0c0051254010044070f07004050680000425038a00041282510542241c2c3d004960501050021780b41d403140748402169014603000084014903c2c04182c108003100c4180e0340a82800c8108490008a8004200b00e880c251500c44071960840c2d000c0c0e80303000c1d0074031030b10020940c00f90820406082c1600702107000d009000540d5007164403104d031600001819081590b45069008035014610380116045003c1d1045080622076200c204041c10f0b41c801c030080004000b10703140c80200b02000001d411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693974892 1250 693973642 693973649
    0xb1603020f0d050f150901060f020319050c33060d080a090f06110c27090102120c0309030d1812121b0801050409110604031410110702090a06 62
    0x707010703941e26981100728080d1005540300c0807a5404800810128014000c0400340303010050900b401e02d030310300401a9244410450303040c00398002002666205050080c00d507064080340d07242c45446580401d1058540181d40114440b14403070450044d811030000103020444004800510203140e5484010810362501c84000404085000c58620195600103901d8000d039212240500480d5541c5c5138126915803003909a106d064000e000c1010260900e804803a5451840b1220380380c4264a414060903100c0084440c0c4640740d60109900801410003510301c7c1d0401e14100c00341c0c0c00e50411000c0700b0b07101e02c00e0421341654280d6400301707c80da0090014a0008541d080700808600124003540a4151040304030807202061030600039081448000c201b07030f0307031030384855035602c01503828982800010a60600e0030ba42054034560428070070303600c2000800c0035511807170386000b913449007010051908000c8900c1d201400d0034004090047c0400005a41348680c04440001860326031499110040c8850340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693976142 1250 693974892 693974917
    0x30601140408060105030c0904021809031b0102130603020c150411040606080912040f0b07021305071d0604060c0f0c050a08030c1b0102030406181e030219030b160302 73
    0x40015402d040414031a04a40b4150103840c012102c00c4200b105a40007254004d5222040f0422215402040840182d108064404880c0740220000d0b40da0b08171640308242e41030303a80d00050202c98001c021500740d0000c2c11541015402e10036058429515858500c070070075400c4061000180a2108140d0f042e080003174040e00030004540c45100003002920704482c0c50744980700703020008244d800743c40308450031115040402c242141c2840d502031001d81c00444242d87c08808081c116003030007500d108460256180b900c0e61680c02e00184804061a480c0d030a43c6c070f200fa40705120800a0b590005d9100101a078066112500d9010311724015110040c1500700c1c5810103412100850718103800801000900c4505040707c0000e17101c5015042c0070b1018904a50042e04240000c1000034041d0b07590003141c40c0880b00d00d212054482981c3e00d1411402c0ba81e226440603a00020001d5040012200044900b1800341100c040d05503228007880701005030400e200805092010b40256219038190346c03007848250b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693977392 1250 693976142 693976147
    0x40f03060e0c0d120c03142107020d0e1c050105010305011d0714060309030421060606110c0f01020c0a120210110a0204050a1e0603060c1103040b03060114 68
    0x80c10440000c00401c1500d2610740300c0c841c10002c2c5443c1c980fa100c84021340c0540140c9004200310011506520054011428840e07406903010151102c10060060441c1a007030a0b8100544080c441c0300601c4c0c09002241076401c25604008040e910203481422400700b5107071001c9000c81b1000e8000d24080d04480070f0b01d25440c110020003040f4043d002807100c0d94980c0b048807002802e00d83c03141d880e1011441a0501030001407892003413030502e0000b0755481410380c000d50381010364030f8001c5004440b1400d840724219040a4404d401c0050078443e074030141030203140101012030240f035915660310007071300071b5845000354000074141c90b07208000043c200032010b0701d0102c0959640381d15007039518248200324440e02e2514200150648181003189840b01418005c0a0890305a000e0200802d400b50185035242d490340e42002c8081c60458002400b0f06103c080099032030701e5401c00070101d0301d1540c1c4810402c061005404400b14000043d5019904242c00c41035a80e1075100c01690ba5204501080d5041c5801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693978642 1250 693977392 693977399
    0x61e2412030c0f031805030309010c0b060f0303030903030403170708060d02040f0c0903060b030307080d0f0b0402190e030606030c040203090c03120a030f020918060f0303031303110c180705040f 85
    0x20400d5008224071300517840109a40b00c2d01016101d0040b98074540c00030303207050365000102f00d500441c140c01c000f010f062507401040c0040800d040d5803044415054940c070000134001010b034801c44c9001550301340300901c03490b800d0002e0001c00149003d0000c5100c0c040c0312900a042d0b60380c0368070000084090410800c044003550402030241c19041c407041d5410b502e8107030199114100070003141c0145501c0407500d850034600752590002030034581450001c10369035900d90680c1d078480d031008004014400c9010310001c542080c000341548460202a4043c0c5c1081c0305000542e140050001e18804003158056281d039100c5100d14075005c00050010341c03601c50300d807042040c2030007880102070800c401e035011b01c5000c00350011141070303100b00013585400c4500c8100500200c50307a206007a270080c00060070807481014002c0001d20b0340e0800d817200302d00d01040040180c00c041c1c0140000054500d60b038040e002c4598503d001920131078000c62040c00c0c015a6070002048288107078100c90141400401000d08140c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693979892 1250 693978642 693978647
    0x3101403010f0f0c26061009080303040c0e100803040b1b070e01030506010905010f0b070303020d14100e0c0703051e0f190315150c061e2412030c0f03 66
    0x104c01640c2004501c40c5032002c48031000078080000100004c5103509200c1e201c82c82440440100401c0758010800e0f4848085909101800298010340c02028050301c4181014003420300044080d0180d145090512010001160044151030450f035031242101d440da0407101c4480b51810b0b0040403072625004d614800300c0d484180c0306c0c0b0541a03d0081003114156a03e5a5001040300c00a0194081c403000383d035000c2022040ca007009140d090701ca0315000d401c0004201400342660b01c0303800c000004c10f121404210882d958010a840101800881c550080c01d20070341e101d600e84243e980240c104500020300302500740500e0844040c0320b104c4004103648144500502995800003100e01301d50b2240c0c038000c20301281c42801400701d1010107213801d40040e032038101d0050b007407200120042d0074002111041404280c4a210b0502e038078018001d144d0822085021160898a40b0f0300c1d105030418100c024030181d40e40d031210101c241d4103103082c01d00c6228058181510400b00c2d0385c43c01014029010400340400d42d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693981142 1250 693979892 693979901
    0x905130509060919080a050c01140601110705010e040b120d020a0303060509090c120f03070507050a09060e190902040c051e1c18050d050c0c0603101403010f0f 70
    0x6107494180d41842c0c48811110340c88590075140030349a075441200c0036020500c90002055100c4580c00c02c20319009030400c800c0d00790f035280200c0c4110001030310100041541c002c400f02508564200203481402c0c2401c00282a078003605100c10301440d560f40f00c00d11140c807810f4015a400c441c3c1012108401d8505200954403071800343c04400107400c06800080030305250541c1030081c24502c010701035061140c0c0501c00c000c0d42d41003e01d2592311511206040a52062000341009070142e406040305508220501511010302e9000e6002c1c41e160040820034031a506405d107420030100c401a198140021201a024009065010394007a1411211001058014005040e0a1440c880a45120403c20b1004003680910300710907482c212003262007401c2e1243c80d40907584803000241d8001441c0e210744c80301803600b00c44c00d02681c0455000500c100d08101c2c00c0064000307100048032918510329001c800c0180e1003980c0d00c42d000c1c0791f800f00305881030769035801e4004030744480c2d50380e004000b103001c80442503000c1d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693982392 1250 693981142 693981151
    0xb06070b01170601030803010506030406091b0305070806070206060d032102120912090402070501060b0a050307110a11090901020d15140409020306040b0403120504120905061608090109051305 84
    0x103110b4070b1800d102c0e075a002c01e085049a8002105600b5a86054184001c03a44000d000301c034082d81c0d8100441c001070107080c0c002044403841d501c170406141949003e41c0ba10100e43c01103a0b0325071040e41041605a0700189059000209903080b80c2e240c4140d1805035084410490321060010311604010a50140742d4050202010a4074950100d070312090b0099889a034082802c422000c0e0402040400d030805070020300324140310b80000107150755110b2001d02142c11039800340000603800418418101d074889420380020400300040e010031070407580c80c100b1499518088034012103a200c00180307840f400390305955401c0740e1640300b44280c010a0b800d5080290460095041452400d07120f140789003014401ea0141c03a03400783c01400c1d10344440c0c641c95a0518014030843c1000384502c2482100d002c540600d5000711320030030701800f50700d0203000098410b1245405c024024501440f20003020b040101d02c080c01c03517400001c2c0980d0f032820305c0300480e024801a0496500044a500c800f010460701d41d008501c503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693983642 1250 693982392 693982409
    0x501060b0711090402030a0605060312030405010b01030b1503071404081e0d03090b01290d2003040f140c0307031a0114060a0e0f090403031a06040b0414040b06070b01 73
    0x55826800801c240f41c1c80aa902a41651114180d40c0000d1943d510071074014000600301d4000b0710100480c4c001d594030444040310241d4503981544055600740c000c000e00120101c078043d0074040200890809400020511782c01c002c1d80c40c2c5048031800c408001c480107401500281c0d00181c4541e118011300c440d0f40907401d0074a118a40d05a007100380321b44030b0324850f42d50050102e40c0a9180100c01c422004082002c0d4a40078090301c00a80c030307512034000601494076107210101d0b48121402069204041409001d10f22480800c100310000b041d10a030a0110b03548126480300a01c00d440c0800d01d00f404900c48142c0621401901000f441201e101030300c00c446c42418502e0300c6a0700c0e0003901c50010142000c1a40002060141c81e0006015124520342c4010291125030f02842c1d0b00006184a18140c900750301003952140740002c28880c20003d00d000c04000d9501c00d01d042e161100c0b24041d80314620071446003505c07034441c4800307583d2190001109036900820480d150003003424075100100c001e1160716071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693984892 1250 693983642 693983663
    0x150605120a150e030a0e0402040b270306040f02060c1203100f0f15082a0405100e1f05130b090112090b0a05060105070c03050708010b041b05160501060b07 68
    0x80c01c02d11402040d81e5080c00790065824011128000e8450742181c0001581c032603000c0c0004205010441c005c1e05400c054500b8145241e031800304880e00c04031007202d1160103900068100804074151501d01e0640e00c0c0c0c166000703070351818049840b034180700c0180054000d24100001f0b102e68003406810903400c0e6034280b1480f140c13840e5282c1d45514101e2803441070003542e030000c0955406450061b400c0039030207009203544410601e150303c51440b5001c5c0981e06034004000200b000e1102e401c205842c980083d03501d041c140e010506101c00120600304254800281841c40300601c102280303e84281c80210810780500d500c07450b207640b8181155045860704a0004408410200b180b400c140902c444007a0009451102502d44405030406440d0062030b80341408010090780000034407040b5000003c40c00703603010705100d50500900700d081da1840300001c0c2c41030307060416005560101c0900e401d515415030a00903907840741100c240200490703032203000c1d001d135281c860001101b8035020014001d441c844c0c088002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693986142 1250 693984892 693984923
    0x3010b040303111005161b0f020d1b240302130e0a09020303071202060f010e0403031a1905010e0f031b030a0804080604030210020c0316021302070302010603230a150605120a 76
    0x2182d81c1f642c4080900405000300e40c1202504044003624105402089540812084040c411049030750b954086068020340c0e801c4d915501100c07012420700590f00303103025032070441c802c81c02000c87c4065028000d4809548001f1622040b002d07400b44151507800b170146c0c0d031207420b01c1c1020b100c1c03003503c10211000f500500000030020030344003104174107071094100c20b242c458440e900c0c01c800900c1c1100d180260614045801c501d07556500110201c0c42c03c180c0341c2c0d11031050400c40010204070982003031500960110044036010340e0007003027101c0022110300720544504807001c002450802d020b100030b0421781c00080c020035120f0002c14160b10641c00f0380c003100c0d00554010b107614120b10a600500d89960001e00245d03d81030b03005401d0003103040c0010300d0340744940e85060301001240c0c0400740c00c4000d40c2d0341d0700d0200100020320317001041510300c03924289010412001c00d251180c1e900c020003420010b1000c0c00d038505031032680c0150050700700a080305000c1041c41c1d04999599030700c1442500c840d820b400400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693987392 1250 693986142 693986177
    0x9030f01050106050a2703050f0c0907020a0303051003020603180601120b1f26190203070b0a090305010c0e030115150c020102100f0209120303010b04030311100516 72
    0x604031821a6106485c207802c640c0f04454400c0c00d00d001500c6c13045131088010002c4c494401030302c0a5030280d0094007960449020440ca0f055411200d640210791490030070100c01e801103403c0300416050308010525a0f03072340c0c85101104110fa00020350080020060080d410b20f107011050390b4602d4102182c40341d903220511441240b02c195401001c1c0e0804600260010301850511005020541c214041e070035250748071040e080b50100b0f1040c80032400c0c0a074140400f0010008170781a182c05d54002203559409402194845e00390b4060764a11000000714050420304c60f0803444011500308000304603030b0304840e000500f640383c010f01e807901c00e41c280401c06843d240911840780803103119000d80c413001101e0650690342105000c00c16415809122032200d01d4000d18050340c40e600b9140d20b401030340c0f20400810054041c00e01c9005d08038a030300600062051080c940215000e0b00d4040c10f05460080b800710000380741c805c0c0307481d200c1a01420070090141041e05105000b041002513101e580c1121000f0844 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693988642 1250 693987392 693987401
    0x5130b0301050616050a061a010f090f0b090a08100930201509120403030219111003140108150103080901020312040f03090e190e0c0a060509030f01 65
    0x2d01d0703444901003040710484000b000d0300c1041c492044d4142e41500100ba2150412102002821703c82c1514000c40d0304040e603400f0260450203038040c101110001c2c18201d11030100314880c001c0040245d000a05401e03982d0345d80750320000806440084a2805609035403560280907006801c450111815144860714184403411101552482d1054801010300c8002152022802e902680d8000c1c40c0059001410324107000e1426074000d20724803404d4500b80041d107249006542d00500a05940500003480000d502040752861003085550301c001003e844c2c200b586000c800c91032425400b10081801e00c0d540c40d0142c02c02c0303001a6004625900d07603aa281042c2c1e4855040140305a52480d0003001400040e210790702a0100c01c41c10310403241002c000390b68210050806840036140e02d0710f1109101700b0180e02449071405049201e606512070308229440741111885802c0b0721b4031068980444190b0798600300001820284000d10020040741da41d50b000c2c1c40c07540600901d60103802200240d0003004014003d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693989892 1250 693988642 693988649
    0x2a1314030c1315080a0507061403150612070e040605031f05040809040203190f140f0402030109062f0301050609060c0307020402041d10030c090f0e010c05130b0301 72
    0x26040030141c0400700100d00c1c22000700e000308103603901a0152900c140141c554040c2002c00001c4c000d81d9000c4c20482e1400061758031000c09c01c4420060349500415990650b504424012200b90450b0300c03406c0010924002c00d2000e0203982c0401080051032603011140751018502614208000703903c802c141740e141e07680001d00c08040480c403040000301d400e03240c0c0242c1c0d0090085140b0790510810130001002c1e03038400d41c1c1e02040741603000220b0410056500c510145080c41e005c00b00301c20342c11614100d54160000b49801010300e010710000302903450030340200300f404d40c1c401070801401418103104c04030b0500703060a007501d00201c501030101c100000c0c01228182e50b80181058280030701c071802c2101d940d00070b4a8002c0180424420039005071517170700203000944904403c0d840c01040e6046d60705542d08008141c07046c40245c042c410804600355103c4030f0191052203001081c9170050814070800f0380385200c1c11140c55803810b030800e04004d44c4035001e42440c2c4502047c8610702a40d403400400680805e00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693991142 1250 693989892 693989899
    0x60d0b0424060f05160c2c1b09030609062e0e101a03181b010f0504080601080a0c0602060f06060702150d0b10170f2a1314 54
    0x1e400c1c0407041c06000005142d880c103240803441e20591020503040f1400151049a114818030002d2026005a1807403031242d01e03946240d00505800d51a004040600140403003083c03c01004a803030313070840303120300722240008040c0446550381007a540303042e91004102c60f1054019404440b0000e0940390256000a180302440503c084074105092121210000b514083c10140f8a440020b0a0311203410424108a0700380281c2d40c0b00e2400f00c2c6034228a03080185d0030171441d0007480280c0001a409071a80c1c180c510286400d01d07030440164420b58071403141e604034190b07600c030350800041d0002c0d00054100340c040c8200128810b0b01c1d0ba401c0f042e42c1c0c0d210306803040100503004000017101402c04101600407140000c0c024161240310355030042942c1c1c030000026410a480d0204941c45003001c0040868170207061501829084030141c20910000001d024540d02100300b001040d141940c1c404051240184d648807260048401421064294015001c2c4862071100e1030b0001942141000400c05c22403016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693992392 1250 693991142 693991211
    0x10e0604030b07020703050d03020d180f060903140f07121b150603120e01030c110a08090607060501170f060105060d051b0a09050a140a0320060d0b04 66
    0x141d4881c500b90000501c5181103205d200000030100d9030412020701d00810360744005940300c105210354000d0310188000c1281da131200e480b014001542c1441d030000003e802c130500284881c7c06213003c5071448030121401c08030170350204000d112030f0705034002460528480c80031080315400110064a03a11405400d01e00005022042c100220700d03607021003060a10f182800042c016120781c1c0d04860500055440d40c0001c2c00e8607010222543c01d071043e0090100c5604003032589240c0040d00e0340e13442d10011001440c1700300210721b207940394480310166400194040c0e41400550307168070042c00d03032a2800040204510803401ca400d901100841c486040e82c0b409400c1c586020364988180c00130348001350401000c1e1940d03d0b08a4200c610707080c06000c104181c0d40d1904034062800b01080100061a005618071140c0f4103100780803170340c540c03054508030f0b0b034406089100003603010521080d980c01843c00540003140061942035801241d8058009074004480c104004202000a64a02a02d94140f8920b40918 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693993642 1250 693992392 693992399
    0x1e090f0603030708032d190e060c07110402040308070318060504031e200307090e030406032703080402040f0902030d0e040e150708060915060906090909070311010e0604 74
    0x144801140d0100a83c400c030b01107540b8034025007542040708006e903c1d00000b040c05210144140048103002c03146480003d020100b030030041075882d200054840440601c00046503c01c200028507a01d1500702e000340115183c0da50307824100c085502c461000c4000034030020301050386401a0400750252641d07599524105402c5a541e8100349960400001c50020244c249600241e2030740c403000f012403aa6030039140684070000501d03181c00d4107600120b4078681060701450010000000361000c4848038507000c901c0ca1903407691030002c034a8000c441e165030580c501c940c1c1d040c19002501c46008600c2071380c0030414580f490f20428110b0300020002035040c0c01100809500a00c00c003a1002c240700001d00000311107400b00001c902c1c00740450781c0e100003c50340f04104a00d140e04100126070100301541c0c0b202051601c2c8004c000741f8625a00004d01c80e00012038179540680f80c80f0140c030326814002c0c10180080c00d002c4400c81d1f646a540c0700c12103c00c0d034040041d4600394404d9418015a40015108a0030030f4103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693994892 1250 693993642 693993653
    0x901090510080f0604080711062a0d210204170105040c0b03010b07030309051608151b0d02031e0a020c0601060216090b150f030717040807080307030b1e090f06030307 73
    0x112001e40300500d00c20a040705540c1c5a0000740012b900f40b500d00c1014048210180c1003118440220500c5a0014150a000150064800034252520b401c00e500300b2400c4a03583c41c024002c03904681c084000c03010740c0a000000c15440140035074000c4400740707807481c0e580724a01c130b00c1d2109009e08070503083c0600003c000640a9000740025502c100251540c1110403445504115510f40c0140d400d0b44c80407800c2d804480d407100d4101c0e0008080322442c44c5044603120307000300d6440340a00c1720001550000024210300d140840344180500807408500060501c155220080d4104150002c1a400b5540000030041c0c00083c14001e804141d01454a00780d141200280003030020303c82035174000c01c0c0349203d02d0010403400c00401a500e041f80328940c0300c0c00d1150005000d042c0c4003480d4a10285a54144008550020240c505841c0d0158000c2c2c0d80340c3e141582200900b40c5a45941e82090304030030380175103241d000e03080708602e90700c1a0f482c100e050303641c00a441c4401da0150745640c0c064100b00881d901080c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693996142 1250 693994892 693994897
    0x524040b060a061b0f1424061c030302071a1906080706030e01020702040903030905121e090118090606031a0a03060e250e0f040c0608150901090510080f060408 70
    0x45c090816a9841000d545452541a030049403602c01900f03c9495034410ba10610124920450294000c5d113191500001103481d1494400d141020f02105441b6601010300c40e030112041164454a00304000d11200301c0c8041c401e40680354500c1d0701c1d03a40c90006c2e20f00c22080c403403442144c05400c0240007880c41c2090a40081101180308149075400300f01401c0580c80314010110315038480c4d90006100100380c00c000782096644070050317092520401c0b031006004440100507020101841030144c2d20310100005841101a0b120003000000d02001c0000b0200f2440d840502118680d4406000c010000c3e6102ca0041c0c03001130030180e102129a905001107401c1e6030042c0c07090b0381c4074011210908403071210304c0b15880401940b0302c40080e500d80103100a0005000d580e802003240084003d15051035611411040e40c18000c0d90b040060200c0001e182c07201c0c815003000c6d84070f40070300a280c0e1945c581c0074042c00b61100310344c0400c00903180c0000045294000820124140811024188a403100e513108032055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693997392 1250 693996142 693996197
    0x601030e150c1e0928180e0d030f06120206071209050307080d0f080103021e0406090e0604050f0f030a030507031515140309190524040b060a06 63
    0x71205011a02a22500f440c51503009004841001d44078980c00c800c0200d003201e4104e42c03038030f41010042c000380041c0000c0d450005a807070b11007100c2034070780000d440c1400038071a202c28104070b44103210407186500d0301031340810f2054070081014407500d0b895143c4001c980d800c8120094200038108406404590180604826040c041c54074410041c0e0fa48000381c0350203020740000806400c011501c886032130f0454500e03196a401410304400d10340c51a0000303005002401d81d40664082e080d442c003401c60b078860f404400a01b501550030058100c00751040d682d281003c580c01c543d40d01c2100254020240c1c0064044007810081000390324009520300124050b1201420301018103031503640d00514038248000c2c2c0320181c10314402180c0300d4010114028410020070040e5102520304005001e803000d004128a0540100400d100740d20720150b290191801b01c00c0c2030b00700e0380038005610481d40c040840c903032203004d03e006200c201c120b610341d0710800002084c0c40c801d0002180050800c1500f007246d00c004019503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693998642 1250 693997392 693997411
    0x80a0209010906180e0711240c07050a020a0f050a050402250c0812120718060c020f04140f09030c060f091903030b0a06030e030403111906020606090601030e15 70
    0xd182d0b079000052440302c1e0540c1c1443c041036001c1c4000c400d0030410480910010069a004800898840050842d1780000b9244140301000000e0520900800700031001b80701da403b03040b0013030721a503d151000580001d800303011f2188010b4000010f2600c1d16000b52401c00e003210001c0b8629a61001c2a00c11203071000d08100e9448400131000100c0d00418000c22801e16100002e00da40c0c1e400160101032100001007180d4144403980000d180881c00c020340031f6003a2240342c14030ba82e98000c140005010040d0f13546640380d105090070145800085d4208071a802400e11805884040e15156400c0b80c80b4010045c1112050b800080081c1072100401d0300503412010400c1690320350fa00c0c2904884138000d00c6e03802500400e44a004d403544504200590070020407903840c0400c541880d8840c456141e10451101610549811400040030341d101100324000c4416a011143c040e5900e00001e51a8002101d03ca4810408040060117650090040030498051100908041e031700d210001451440d005d0f05e030410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693999892 1250 693998642 693998687
    0xf0f04051207081305010f080703020c010b03070b13270b180405060105090c070c03060218030f0d02060c031e0c09030a030801151403012102091501080a0209010906 72
    0x3410084034008000e818024891103955011300e002585060704180d01050401c070708000c0e00c000040d445160640c010101d4071307000d43d80b41d001411080c003601c09416116030501036950001007101d40c1200614010b21340c0304104510a69441d40c04108c1600700c00e207240100c071105040c26442140c2d40c01142c130718000070141101d1403005800701d400440e085408440302d40c0001d0040c03200380341214002da03100d10515003036464104580d80c1da04183c281444001e21071a00450440c00a4540e50125001c4031809400c4460907580d03029074075034528607a07580390003600402000c0307081a2814000c49100c2c85100309842c55180a0411008083d8001444041d20700c0c0d0620071900135603410f02c010f86215020303980c2e552007541450300b03403c895190300075220f0600061640c0c12405103450001e41e4115104008401d000d280c4c08102c101044055240c02948001c046040082c1c6040065211003001801c0c0d0360240746650b14448101240f16541c1c0c5180412141d2400f00002032060794118103d1342022403009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694001142 1250 693999892 693999913
    0x50711060d050f1008010b030a320a060b01030204050d1209240305010e0f0402010c031815180803030606070c050603040c0302030d05030f060d031710050114030f0f0405 74
    0x203007103030016141c91a00c2e50101c0c0922202c0c4c0e250b8448000030301502c1c00200000c01e10040000d568001c1e11a0007400885002607525095a5802000308460222040d048000c408801c005488026041e4100c0b031040c50845156480d51080c4241d60544101030700c440e0043d00503031952201008003010440030409c0d44403000c9500785028142c011680302510b05804065042003018068800c16084031903181c0d2120304000d41844004801c5406c10740a0914201403149410103d41c100d805003545407080610381d0340003850010b440301d1075202076903070350300e54444010181c102e908140d542d00c52396070590b00c140041036a41c0303044001844294400c26108544550f100c000c210240c0003100c00f920301c550740034800c00c290308051000c0c030702850651401c90300c3c514001001181514000c0c0049006d049401c00c60001c06006206050060440f1121041c0340e00d002034042c83c107461140109070001d40d0440180c50001d0498059a001d503000040d40f094a5603000e80c0d84254400040003510588910384801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694002392 1250 694001142 694001167
    0x90c090902070615091b0c020d081e0711010e06070c0e07030b0d0804090605150720030a06090c050a240c0213050103020f0f0939070b0a0c05071106 65
    0x210041c401c0c2da0003c500090031550001c01c1808840c0c1b003200b4401d2440c41d800061365a0109030310b10b1680b0030b00d240c1e21901c2003066201b91410304541405501030001e200000d1150000001c5801e100076640c3d0018a00e003401400140d00911200400c1d844a1150038806a1180c541099200260f03240004a03c4d03804000510340e10418a030565502c1300008091001a11a0140c40040c240503290050305c40c030905100f42c010710810030040d180300b007415040b140d9104610707803100030400300604070fa040300c1741410901e00030304503e20f00701d414200c9028001010f081c0708a4440882d900418407041c40b041081494100c03085d0b002e41c1500708000703880c115005903925000c001c480d8032588000601507055205228180b4411244280b00b030420a4413038800340d87d200d0000303900c082c05503107110110340c5044443c44400d00c000e500314100c0403501c01d81c03030001136000c001e0f120050181c842520203440e290360307141c11100c0c101d4031a400260100504c101082140d0044d0a1340200030700500d10b44092001203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694003642 1250 694002392 694002431
    0x14011e020f0d1808030906070318030b0f15100c061a060f04080c0f0f040903110303070201020d050c120601050304050708060a0606020d0215070c0602090d030201090c090c0909020706 80
    0x80c0d004100c070040e42c0c03901e120f5003d072038a02510607840294941680c01c000104980a080f10080c1040810390000b6149045200c05100441c3c0c8450160b28a0034000511407010400710b8032410040828280d1101c180b4140f40c04600c4005c180d11414009000b90301d40b080030b0441c0e90750000050b103210415007040e480d514024000c800081c0c02c1941c80364102140c090801860450a0f446400e54413090030855450384000c2080e01c200b19800600a03100385000c1e075100d1080c005880321070001104003c401038040d001882c442003e84c100300000d039590103100e195409000c441c0510b20502c5400510154043c0c0c00442e0403030b015074211084d00c0c0c4d850030107926001d0b00b01d40f203400300354a40c50704002d442d40400c5080301d800d03060f00180009486014041e088800000c2c41e440c10084030700c000405001035903049980c0d0410103401071701083d807a420b0180c081d08586d5400c903602c402c2010300090025040c810300040b03880eaa50b0304802c039131030b00030080041c0d04464420b4501580e540111032007101d41621 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694004892 1250 694003642 694003663
    0x6030406060806070f0504060809010f0c02030c0c1c0807150608071d39030c09190b160201200c130b010203041a191814011e020f 57
    0xd0119689040200342c2e8201400601031310107118921000e0041540c02034291401d603541c41c501144546c1c3c07902c030541d000d0a00c55a21041075883c200303984000543c040000d04420307032840f040381c481c0813150003448100d01c803100341030401120500209001a00e03c00040400501031030300000c00725416a090310840726240e0107402d0951100d1000c00c250032000c4c65860011b80380c03140e10070045c27819003003040000c0140d264802d820441c0e003d0034814003c03210407503e40d50000c00307080c4c1d0300c0780b4000601c0042c0e988242100f034403c425038201c08080c11500442e4600b035038401c2c01821704000483d0b03a928903041c10040c1c00c906120f1481801d0258500746d81c0421607020110000b4000b1503000c800f803040c0c0d10b4480888840040c102119900c4a90700001160122241000c042c3d80d505074410364130056001f000d0ba00300c540b494401c10303070034000e600144100004895000a804096603500b00742c0e484048501440d021135000d40b440c0c06900200c0c441c2486841060042d28140080c040c40300341000350052 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694006142 1250 694004892 694004903
    0xc03070807230a11100206072001111b030415141207050d0b0306100315020f0a020f190201210b040f0f050108060c090603043f020c06040506090609060304 68
    0x1e0b50f070018451500f800c201d8070320b0f00743c4003c000401510f0340203440720002000302c8280248400da1840b441c90181c0351000c8108084020404040c03180c06d40c05c0c03140e2080440e40c8441c03031401c0a130402c5074004400c95080700c290302c04d02d07042c48109600980320089410100b6044031801c1c032001c0c1400d0442c3c080c1500c10392996407040e0341c0d41000500756085400d2001114041ea01960402040d40d0000c940503050345c4c1c01410302c03050170600d1211000a40b04045101c0030841d070100c1c85003842ca0f000600400590f0441094035026030b603444050988000005006e030002d00130094660b06a050541c0c074081c0b1000300c50000c1307841c5002d00003040a481c4181d00c0e403e146540c4001c061200c0c00144103950140c110ba8000d8911030820b0a811101c5020717a00f8040e1060030000042400c02030a1010002098860220304602d198089640c2c041440711900c0300c194581002000c003643c610104002194640c01407100e401e103801c000c10303c031558002006051f08000308120a0485694901c040d5100720310a5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694007392 1250 694006142 694006153
    0xf130206042709080a110f0312010305101a0103050604021201030b0105120102030103050307110a170d2d030b0102070509041b050901030b04022e03090c06050c0307080723 75
    0x10700740c024542d0324106011902c03881d00c1e280e1400592600b0440d844440c0a00d840140c0344261030700f881c188680e10b901b00341e4502c000140740258a48000d409812030340207006403000064199042d4059030035101c4a80740b04248002c0180c96913000303600c00798200f4005032005003440d0000d44648580c0200783c10a5a94030a840f00401c0546441700b2115100c1751100001e5045524581d1116a40e004051009001c85e41c0c207601c00c0c06685079042039400401144000d01401c42542d450740c3d4403005940c400d0000a80e08400c0034030040c3d0b80c2100038180c035010559011035060001d81c03c400402654400764114041c6000000d0107588003018107000d03a0142c84902090f8008014051201c90036501442c0142181d40040001c50344030000c1980c8542c05540300320380301448101212003001c480308082d0808500c0c1103c120000d515a005010b090b1051560305581900d4010545d254000c0c805003050f164002c2042d04000340c03030355010b07000c9544101e28040701c070f04283cad200c0c10900c01c0050003040d5a5006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694008642 1250 694007392 694007429
    0xc060c1e0311010b0f0604091a0a030b0106031a0f0f24090f0f010813020301020d0603030521060604032003030c0d0201050a0b090402061c020f0a0908060f0f13020604 73
    0x4c0c0700d0069010002c03600f40c40740340f01c4c00c40031030458003c80c4615009581d030f50102c20070800840c0719618034a80001d042c0c071192074403460300445414080c01000300281c0707840000b1070104840201c07403111443c0100200c2c1d0301150f81c0c0820000f1856101999000220031000c05240c1700c0711443c80151814420f445611400050180030004032000081480741c5e0000f4036143c00f80c1d8001c0e281641140c40c1207107100001d402c900204e40a84030355084590840d103401000014903500001030b0015803041d5020050040d404c86940c0301500003901d003590301c80701c1004200001540c4452084201305060240c0291031401000641150420800310407203402014004049a41c2807141ca40e20103a00302e03040007a40a100c0200e084401f0040c40280a11000a00032180c0c40c03003803606000c81d11112a095558000701c80c1d80b00e409811031040503010960840011441c26400b1031003603c03a40e2020442060741da1040810224264082c2031002606040b940c400c0241c0c80314001040580740315226174011428 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694009892 1250 694008642 694008677
    0x2060301140f0a061e0c050a0b010603051807210524070212070212031c021902190b180a050a1a04030e060315040f0608010506010c0c060c1e03 63
    0x56458118802e40f1840c0091050641214150080c000c482100e12030065200071705545070342c00d07000301800c00d20a10800001300040105114182c604a503030a128948822500306c0c82900004604091904030150610940070030a80306d003252400d6035883c0784014115100d00e820a0700b201800c40f0084c1ca0107400121030101440c00a80005580c4001c00d451814401c0d03001c4c082c054240000c0c8185900101844404810010358114011051040540245080191000f54402040525480540302032035001030300102e00d44010300045072400d150f00300c096444120211000740f0620580d000c0a001c41c500c00000c100048460303210380d005207500316280c00c01b410092180120704c100c510f0030404000c0026441000701012035000d48446440342c85200c0d41148074541091001d80061514402da805114250040030840c1c400c44003c104940b41c5d0070046501c810040340c0508014248002000030030b110308207042e0f01c180070302580e0104081d0b82420440002080000f42c00150f070303c4400030282070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694011142 1250 694009892 694009909
    0x30c010203180f0d12020a0c1203020c090408040b0c0609011d0c010309050316050309040b030a0327090507050c0d0203041214010e120703030b180a0504030c0206030114 74
    0xd00045003003519542c40e00d00440d030a46030050050107400000c8140c0c1d1904050210a030b94414100d54610031201c0000356501c880c1a001d854a0f13120070800514a2000c4a4186c40140c044e4050002e90042c201071140040c005041210302c844100301c00610000380d040500640401c1c207007d419a801d05461540c00d640148558131451a03850b21400013a600c00103680590400a09011030000c0060031314609500510054485241e10418035004000020004100740c031400c0f1401c10414040707030141581c92170001d400030040341e01e0000741404420050015003000c180d00d0000c02d1442d461b00d100c507040d03900551b005000700700007180070315041303c1c1402001c1c55000e01d840210f0400d46048005241202038000240c00000e40342c1c03d1000c0c1c00001c0d04107103416999201250b02c900b103c81c91a081c02c0c1e02005060f40000d15003c43c0101e585031564905500038003200c45140180c503800120002000b01800440901415448110058503414040c600034114620302c8914240c00c00d05106458 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694012392 1250 694011142 694011163
    0x30717130e0c030720062d090705120109120c0618240e1509190f02060a0c0204111806070c030b07020f0102030a05061507111909050a02030603 63
    0x3007248003084032520040040d03036480221880e101840c48045605644514000c506070103032030141c18200954124500280310b0300340b1102c1c641208584a1442d131501c601750664107000c0350703000080c00f04030500e0807240d0f20082070001d9000007038140103070b65080b400301008034110f070100b556511102c1c18402181f080c441602e40c00c03080d00e0085080c960f038204003896800e01c545080c1c0300741640d808030810f032030b4842c0c00030880f018100da607a0040c40c3c2c50b50000800860f803c01a501c50380016401c1c80703d4a503013646149900c1527810701805110b900700700040d04100c0600d0304010b0150840c1e0301580d01c0707014807408996440c1c0c00c0d6a6130b6400c0750640840b4030b1840401405508100700f55400206e140c012135007180d420403218212904d030b000c0c08038104007079440030080b190300200502800d22101d03801640200402c0300c0c030364013280105124442500840785d0250005610b00001c0d0598104030803492510428404602030243e1102c0c040d03000c440c020740701509402d0703022041015500b070801c0502c196 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694013642 1250 694012392 694012409
    0x150f050c0303130221060402130b060f09100f14030703020f0304150c140f03040204291f021f0f020c01050420030706030e01091a0403021510060e0303071713 69
    0x85c104442031542d076403001034002409055600e480d2044400340341d00c104e1030518003c004a07600c445c4007070555156008800154070800000c60300300d498501801400c810f01c049611600711782e40c45010742141c0c50300010006400d040e020400c94030109140700c01184694812405400103180344440c0b04100d90022070450705121000560b589a0070078001034810721107081c112195240e8a510104015202040742c06036400e40403c0601340907000a04c0d00c144560b425610a54414031070b642d980121440b08060101613000040c613802c1450501c0e4254880c44115000412900c0340181d921040b64031400004490381d540e80140002c00400c400795007040380c40c645400143c0d0755800c00203911950544140c409242e41d900020402d05d80c00c2d044a40c4070381c0c020480303140d2003c0d50250b01040c400700721812401801a100034111841111000502074010854110300300b500f003078420b0350740b42c203201100c552521003844003100103054031850102c440c0320b4900303103620307003c0b1000410900c01198221a08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694014892 1250 694013642 694013689
    0xc0702041409070906140f03010902030307150e030a12020d0603050601081f200703030b04110a081e0a0e07080106150906050901020d1202070506091e07150f050c03031302 75
    0x42c00c881c00d1b4510b440441103070a100720040c0000001d004101056000f501404003180c80000e10400b0300700e5410403c100389041c04044410709a103600d0b4429101c90750003042c60212680d0102c405c80d80a03144d00041003030b00044d129141d445151421000b640810100e40c001440b0200c1e0040c4410440a1031500500910034440d100d0010b01440c070603450450481c15020a05000307052090b040b50b10a101c1c060020480c0d03089034441c038032a59100003030b104007142110000c903104804c110050200c4221401d50201d05450f1000701c540a0560454007220f60b1050030408150a1030030b1142030014195490741030519030203d8000b40040d0541e6100c101880340900c9141e0080e60049903500c01d81d0007500d0310800110f00101490024040e440e0f025190740b00c0c0f50200481d2038000102108204110403039051040711402040d980c0701c0301401101c50303088000d600c5140860084070700b0138450100781001ca052042865005185030402c0780c0d1040c44165040e640307400e6051a810303000860403400400d24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694016142 1250 694014892 694014899
    0x2161a06010314150103150902070c050907020a0b1620030405031204121b1203030507140403020310020a05071b0e010f08061f12061a040c1202030c0702041409070906 73
    0x81344007281c1c0740010f05054442e03e5040400b500020244080e10385c0141c2107403a843c02e800c1c00b01c50301301180a041c0c0034407007440116a40b0760000640410342540411300c0140355940040c02a1112420890003092042c2880010006220030301c40a0225207503800658a03285032004151410740c14030070011150f8410001030000450803245206000c1d0482e5035109494040f1a0b017540c51106588401c1000c901d0b0200b85c0c04066054010500401c181d5841c900101064002400e50f4803443c84000e505a101d41d10044142c0000e801070154103520b030a2440c246503aa480c0c0320440100c600308250307002001c000600c01c444801c100745001d0002c103c0c107c0d50315418003840350303601c02010302481103205a40c0c8d805e00340e1040d8443c2e4600074000c2c22595050004240c50a8030107007201c03802004074002048030310510f41c245403003a940740c0c0d1483d5a031000158408050070000307503c090f2020000d0001003101d140961650700500313030140c4100302c0e059684d140c03a804150400c409074010f0110744d400d081040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694017392 1250 694016142 694016161
    0x6150e0a08241e040b060a031e050d0201020f07032703051f2c250501110102090a0e04080408010c0807081003030207050105091807020c0a0b0a08010902161a06010314 73
    0x151301650000401055880d00000184071100d0fa91000b8a05a181d0302840081e02c10000001156031003a01155454440250280e00341d009002c2e140052582c14881e00000c81e100c0ea0b07540c01c0e00c03c115220508175984402003c111400e09401c140c925500907100300b022601c3c1c00183e1078180b000d40504008080c0680c4d80d29070001c0004110107100f14101c0110340903150b0070f00c030040c080d000d42114070030300700800b003455101108584211404601c1ea031189547c00541070003120b41e0700e44001d0055404034280f50700080002c0c17020700190b030760141c180008503540c002441004c0602100b526850a40d1910310001000030364000d21155401c40c420b03001700000b98002130004256075090074a5030303d61308802c3c04035410340c8600301042c1e28182c0400500c0b203003980105140051000968131850740588452030840d0318800c0d6240e540004000c6001000010001d0b4007a107d80c2c440440452402c2c0a551074100460300f100116401c0c103550007050110381e68061103030041e000c4d4003402c00000d40c07070440c014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694018642 1250 694017392 694017451
    0x70605070b010504020930010c0915051317010504110f090a0203150306040f110603090705010c080904050907050109090903020c060f0714070905010906150e0a0824 72
    0x803d030046402042c1c0e50055502c07440300003170b41c10b0081d4074490f07a0352a2640d82c030701c1c1550f9560007003000d510304404948054803e42e8001c05680c1e08c10b021403203020440008443d01e901041041010154590000c9510208204461401d005071350022070075003001e040c654110107034075007041d10070f00070040d407240c8a8894030005031b030101e0f042c0001602e99450b0900340c6d8030074004a1002e54580580d03002c00c41000103881c03081d21964020103603c05404151428894a40f00c250760000d15540314440401c00e81d84141d04034414548140807040c10000075901240694030161900d603c2904106000d011650381304500d0001895501b1080c02550b1803914065101d16400d54118082c02c00012415245000c00b030854007116440403030f46603030159240e50702c1d0712a101400389004032801c1030300000c0c151066002e6003050355150190780c916603d04250540300c0d485132407051030300011460000500180103014024001d800261700d245070603402d8204410b910703c0248188406120044442600c0700350080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694019892 1250 694018642 694018649
    0xf16060c1212240b25081303060b0306160c0305071a040b0118050106091403101a0a0503011b140423120105010303052a010609020c070605070b01 64
    0x4540c91038030220300803910094180b401d01c002504011000d420b51003000e0030305141440703040814111603160030403080d0610500311019100f59251203400140300406440300d18a0340f05150716031a05c0500d0340f541c682e0410f9a8002d031602ca40c0c1e80320680c99400c062184a5105c1d0041950174120007203220060f00c0c2c00c61802028040200100d07001c410012660100e20001040c200c004145103058030789605480f50034052180349100300030421084d480d03e400384506a843ca40c03510103005040c02e00b0758190041015215038144120780140c24000300a00c82c1d400062810808030284095010030f00401c2c1500d0380c842c6019a1501602400105503100134801083c040e140c49000c40c900403d414000d0700494211075414040007640c20084218500d4000c0e0b1a40244d503042443d13229680c0f40d508071217003440050041b0b08100f10741400440000000c02d032002d19032500d496503441036041c0c10300311401600511401d079400216035070801403c00c1007100500c1a494030743c2c9090280e5075641d140d400180f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694021142 1250 694019892 694019903
    0x30c161a090d050a120e070f081902060405090601020a02090403080601170903030105010c030c080d0c031d120901090f1205011b0c03051c090c0e010f1412070b0301080f16060c 77
    0x810045d003100c80c90300495540c109082c11aa0a291116422418190984079581007441440172075090705407098a00d886054000381280d05041c9048140320a10740000e140368114000d5141003801642c80d64a098040c4e4040d50b60800706161a030300150018031040b0b0b00180448612081220b0450000b007142e054410070f00e40b0b94140380007031809440704a503500c0018240d800200f544100c0c1d0300c00354080c01142c060755a0a00c4410241c1100503d981107070f43e001242500b140b0761807840c030820940101091007062600c1c3d42c42c0c0b952403071070038845042a08800d5402041e500003c0c1402401d028641c1c90b4a82d180402560110f0650003404100800d4001411300c180400c000721280074044100c01c3d0060080c42c1402900d450b4500403000e80d03214011070b10101406000494004a0703400700405a03414510000741c804061000c10038403401806c0401e9052050b084049000daa64101540c02000503900622201c4038200c100b5081c0b0051000144800400710000c0004a901c282040e50711604170 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694022392 1250 694021142 694021157
    0x30914011a19030215070b0109050f06040608060f0c04081f0e010605011d01170f0604060b0f0702090a0209060412031106061c06060905070507030305060a030b0408030c161a090d050a 80
    0x400703200044c020540301424511302c01f00000383c14039250300080e1140003444c07d000701c1c07036450008000440d4072a0103490020b0380203400140c084075179407076100c5d04182195000d13810316a50b1031542e49408038425547e90703c40d0481050307150400442c010040800e1100b002406600c0c2410002801103031038520502a90482540b00c540300e9000e854001180c00d181a544031062070300300410342c5480070580d0114081c034074104d0005803130070542069800802c2c10041542c5846145e4003005290540a482c1e10310007982040030440350780c2c42e4002000207040800c80260344c00175908002d0002000304800001d41c1e000070003041910303900c0e40329000b1200324024011030b11080ca03040a0340180450f800443c1082c0c608010310000a1b0090050103d042c46a031301480b40399103000610040c1501c6100050902c2008000310700003851401c065507020300b4542810b410501a4051804008121542a58031414102c4142101580822059030004038040203003588541d40b00001e0452081c2c907038140412081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694023642 1250 694022392 694022419
    0x2030d0804030302160b090d210b01020309090f0601090b03010e060d2a15140414060706090c03020405070201091104021e0d020c0105071815030914011a190302 70
    0xe43c103848102c0c0200682e0010108180b901a400540c1954442c1c0c003441603080c4120310703034407565000c0c9500003510b0242c00f49c50111201c04000e40724155061381540803c0c40306042a481c0c80380c280f031040045d64070741a031609007080050841e0f4115000b4200d03aa000304010b00040c1046113000b80c00c2001511050411002400d00c10006180f0242c0401c500d203030890056100c0c0302c1e140c80300c402c4d035111003200e99680b0010039081d610418085014070840000b0300040140d0480c110f4149040480034181c07900e89949907440780304444912000300c654a030940b0301802541880c2c811a507000b0340d1030008003d0903510340c40f5201ca80a1000c50184280e800240061312036601170b8210301041c200304005a00d0717a0500d5031041c0a500030840c480419860100092055031240080840b107000f8030a589e12881d0a1130b0b10042040c0e50103003040e00b8942c803000010f000a090a600d4030444c08003400001e441c003907903c003501b11040850813003885004142719490814150480039001c50b50304580e41e0300705488 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694024892 1250 694023642 694023647
    0x80c09070c0b040506061f08040f02030a3f0804200612160e0d03080a180f05010605040203060a14040e0a26030c07060513020a15080a0902030d080403 66
    0x29200030800c1c420780b020b110801000160f80b0b401524112442e80011072102620080009040c00e84000554210081400700c1e80101078048518000380c1612503043c850b4482c008140c0070641040300c04298108100c46903000109042d4403800180c00c01254210710b444000d04c000741c0a00007030030803114007504003101d50b8000706115502d040900f460362914040028008156011640c2c0a031100e108110440003900c50858840740c510010a0000c1d01d11203501c080b0744407000149480078907691140744010b4a0501c560b81e00e94188036220000741140349140081c03d40c0c0031a4031141c000c0307005105001c807680d6081d418800b0794212080c030303410328210140020041c00030411011018080c074800365092024a01ca1600c10020310300c507020300405c19400c401e8044c4401c40c0c0c4059507140601c040b80c001031080e00882e0304000c1291680c070800c2003d400150503d10a40d00000da20600c18000640f010f801c608a554008e0020b1000c203d0030a0507004030f071700d540524002c40104218070002804160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694026142 1250 694024892 694024907
    0x6060a0621140106020106030312060503030a0f02010906050429060f010c0f0c0b03090d0203030c0a050c0c220f0501030f2d0c09180515131712070504080c0907 70
    0x258018440b8156503941c0402034002d00315408142d002543c41c0ca80120b000350140a24812240c010b001545407601105007164070078004041c0c00f003155201d0803040f0110300f5030b0080ea4061801460440c0c11804181211205c2e03191101c1441b500081040030082682d5070120702150500c0b0030308020442e81d001d8541003c4050000000401c100d22445011545991001c050b6210381345c241c007102c0c000d0606250607603483c04116200c002c512000c202c1e40100c1c91240c00a88ac00424010440d0b103520540f5000680500c0855125002120521041e80808040f8050030320040c0c8441d00400c115411922a4406103604000c05415440c00120300340c103080804000c000303580b8403040d401c90040f99501c0c008c101422103100d4000c600341042d15035044000003501f04040c9942c800b0061503001905000381240d081c004107454150a0300e804940041050f03026890740018036808503039510100c0855840c41c684000d0103040401000740418000b00100184c8014030340d45c02c0354814202d41c0d035100d045450030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694027392 1250 694026142 694026161
    0xc070f0b0d0b06030912070c08100f0c0e132a0e040522170c010e0a051c080c090f0d05031c02090f06030402031203070206040506060a0621 61
    0x2a250000804140e00009000903940c0c042061048001070010403580380000d07980950150042d01c1e2018060300d102c0018414180310b504512401c81e901c1c146181401c07190403d0341041d079164803068001c0d85c800d12500c244005241001c0c50440c0100700840c1e42140e040c41d00d00d2400340d44940c110102078051185c4c00c0000c08506d050603003106003501c002c06011905c4045406941840c010400c03001c4914100401240c06030702c050b0101c50661945140e687c1c8100050b00700b00000c001c1209004407e01444400d03c10120051928030045d2034840d240040551040c81d1025090862241903603015420b2900610300c0348203941c0710040e0308001442841c6001d02e141e0700060083c40c0404005003c0050a400880c5640e0000c4c00301c2400c9504060b48200c0110a0b0700501445407501d040c40d003800507580150024080303a0342500d20800003407240e801035070f044001d40c0c0000b080208004041001da58800000d03101a9900d030700d030a802410b50840000c01032421a081409484184003c2d80800c408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694028642 1250 694027392 694027409
    0x1b0112090b04030c030f020705100c0c1a07200306180f030d0c020d0c0c05040f1103091e0c031902030c0409080c011d0a0f02011701060e100305060907050c07 69
    0x35420a8900540809204c0c44114003040d403c80030f9038245400801c0c080100c40c00500080016031000c8000c55540038580c1c1e085405a1019034082030200d400007030741103001c0c02d680d8065a122918113204082036002d84025060600f003050892543d1400326026410403e403d02500c100d00da00f58840d03040021000612226100115021840c801a41c010a004a00640079144441c2070032408a0740001c40c0640030300b5150000354204000e01341688418000540b40b5800900c90011103641c0802d64001e5a0703422160784140d40109145c204068200f082c0722080c3c000f040310800e56400f2030303151060421001c000c1c0c9070a2003090b0941d00c0900c418054080018410808561189403402c110342080c40043c000750f103008407030041181d403c1d20300300341812490020688901170f03640f50240c1503000d400490400441c1e10702424000603144a903406002552207025903017040c403091040b54010b07402050200741c1440709000580d102c0d03408081c0c00503645d2806a41d252025452140350112640c00450b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694029892 1250 694028642 694028663
    0x10e0a120327060c120b010206011701110d1a09040f021003020c0105070c060c0c03211b020c040c03020403080a0c0201031d0f0705090405070e07090f14121b011209 72
    0x20441640e10014000c0c910b5100d417502d03010030044920403110941800d5026a200d00b0040c40060490202c810704560301d6030002c035081000180c000801c0d000030306600350b01c035201c607000002806041e285c82c0008100f81c90700080341c905515001a203074032828000c1e0103440441605601c09119404503055004000024000d0742810703032004050070340c412019140c26240c00c41002106104d5100c0e4a20250550b40e20b5080720000c4246045407101c05100c01c040c650303100c56038804c4061aa0903a8144029a009440d15020900c140026940110590401c2603c10041030001070316903810b844008103180b801107090106840164010408804040041e003c1110300411400d0b00007180082d4000d0b40d81641c8003140d454042c400700440a4074001c25541000d8418072012401c501c030958065102d00e00300360103a5807200c01d07018159050b008908502440f000e02c183e01d0412001414820801e400102190982c030141400d50710781d03941c02c40f07041204600c0c854042c0b9410b82c02c021a003903041100c81c0c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694031142 1250 694029892 694029971
    0x40b070318060e120c101d090112060507090b19090e130203073f0204050c0a3b040b03030406020102091804030c0f1505010602070503010e0a1203 64
    0x30121007003aa0f03580d201d00340b1601000d020400c00714a40782c8940000e003c8011001d11000705407505940111201d0381c10b1104090420a41c5e40d49075064001c050303900c0c03200100040c60520600ba50002000da0b803e000c40c0c2c103000c10190030300b2411030704034803043d2040310311441e99108200c40803401e5501060b01d480045003400300740d040c040c1c4500d5400340b0890803100d100d552008081c0000b4a18079074040300644045002400f8013034042c94620700c400901350080240d0751503001030103c40781a90101d901c1000811440406034000c24036408220700411031044500d4404180545c109420341800c000c1c4015070001386151f00e070354100c22203404000301620f80301c40c2c030707624024000e40050070160700c500b1b20320841c40c45041031903400e81c1c0103a425603a5a00c0200d6582c580080c400c40f0018211800f001403090842c00c9403035482201e02915540d401340040d5440c0c4820103080d1004185030804c07a402c1031900d09c001908108411070b406000381000306944140381c0001c0da1041100e910221949175004541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694032392 1250 694031142 694031147
    0x112020325030c0905031b10020a0503070b0103030305010e0610030b032803080c180f01140a02010e0d020d120b030c13060f1202030307030e130606050705010f11040b07031806 77
    0xd2103a103e0030313660310803c03543d13540426130b132810464228588840049030f10003190620042d5030310001d1840c0102e42d4091003650300e81e03255501a1105840a043c07405c01842010380c107001e0540101030f1f000d0611410300b0200005a070702000a42a902450f507161400d0010752020300c00780c001d409114a5900074000520010803003500441c1040b8005010400024165074480c001d440d0742d030000400e0340c1e20091810303050000d1100c0481800d418840c42e1080c1d0b03d54045c102005050600b141d600100340041042c5155240071082c80c00e003000d42d040500c955181691101c1020030300719140c0c1d030205981141001003403c0c90b04165005c0e0f00000003080744984064507410040445040c50310005039030b50b4550150740312007a0002e000394160000c01c8510042071180b800c900410034014000340f003110034403516000b12a641d07400103001c00e00221304001442001e2090708450b03000710100b4001c140400070b4246251107680900e03800083d0100762032051610030a00c8006d5a80d0581c0c0b07284020b41c542801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694033642 1250 694032392 694032401
    0x717070e030f1f090c0303030e01090803010b0a030b0102011b032406050a1b0b071d06040603060503011406210a050102030f01170d0912060b151215011202032503 71
    0xc40ca007500c0d103110042d103502c3c01e441501e1030780303401468032040c481c00d540d401c038090840784840382444d64036142c3c11800f0031035280042d0700920184201699800b01c0d0f01c80a4144d4040102c2c03a8196450040382e4036200883e41c00700160a801d500d80064105218048842400c0d100c0a5207201503c6088005c5556a04000108000c85c080c3c0c40e070a00c06580156005101c00c10380d64001c286041d14000b1500305402420b8080f100244205080c49940d44140030800034ac01991001000036150348007000306040071310500c178103814070300c0c468113651501c0008030f0f000300085404000b0411a00f0364070140c00c01c043c040341c810f155001c00255664280410101a2460280903100c010a0803807500c01c070000000a442445095944400b01494584214244a0f911043e41a20800e80381c3c07100555655451901c07580b0603200b0355420f0344422103161180c218841c01000039407800040841218980c0c0c00c40410008500e0010000d07950380d8503081b01d400711561203200141031084030a0050a9142c00d80c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694034892 1250 694033642 694033663
    0x415050d141209010207170715051b01050a06060c050304060c020d0b071e05070c050402130503160f050901140409080d0c0c03180b07150e0a0605040b0705030717070e030f 75
    0xb2030b00c290f82c945c08071950003075100400c03500c0c59101840811080c1d18002d9142600d401d01cac244030b03090191401214003004200d0110003200d9644800b002114500c61203103002500440c5405581c5030950350750181c2e00e00c140c0c0202028010035030300407421036036403524110f00154041c1d10214a401c109102804100c24910350100c0200b5541070a0200c1e84104161100d00d608003290b5543c16103048144002540950200c803104200e4400124190300d08201034080c003244d6242c0d04038030390700d0801c12038503081803030300220321418621004010118219802d20210b40c0b040703d0000764040ea6290043e280d116400400b11540d00b42048101910381042403581d00b20300907200c0c44e11401542d0210320040701c07140544c1c440b869044c0301401c0820303000918403c5044c0e503004009010201c04060074501500100300711100303921072080004100c6c944100c0c079085074141c10201d06500b0903c078080d00484d036410f41119901e01000c001850540719605036246100054140c48407100340301111a1140103807003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694036142 1250 694034892 694034897
    0x3072301080606030402010c1b09090c180e03040905070513080c10031808070c0e1f0608040807141501080d080906061c030201020f030a06060e0415050d14120901 71
    0x3400a49039040074400c40e80705d40d60503522081c51020316600c0a5040004400c0203840a18060000c1000c195511840745590f01544010342c000385454952405ca41481d0394112000341043d56401c0452400000c8d501a00d080c03440104150f40e51840c12074040c0220000c0d802c43c100140000903100c0c10101e04044040320680d8109a020141001602503030000d03480b040054019510020100f0003030005080c0140c0700312143e81102d503503241e10140c10302d02aa02c00c404d0180e07440c041e0152454504042000748600e0502a100b89004e0b03d64980e18091100050b1280014080c0714030116000c0c40001d000e01121803213402c5c41c0d41c64545c0b6540da102c9568500d0b01054403100411f08010b00055a140b044000800000c3d01c05840704034111440b0000300203c1c00e540d024801041340d14fd0f800007652107041305900c002155450700f103000740b20310703548007080740038a14010101400c14087c040360410340e04251404203400c5820300d01445074145851041d00d650250a071004841c56400d1300405803d802607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694037392 1250 694036142 694036157
    0xa0e07021204120204140f0c0c030d060e1e0405060f1302040903180b0702060702010f02280210180303051b012a08090a0605060f030f0f01060b09010e060903072301 72
    0x20303001c6c06481000e840c5e10107600090000620a0500b65005250385014001a41e0500e5800ca03030040c00d40e08190032503828445001d003040060101c2c901c2460300c40c0030020b85214a400c1c07a45800c0d07103502010303007011009191304002440241c140300c4d00b0020f4644c060030030081d008590600070440e00c03584108208000055800107440043d0303600703485995400a00841c9003640725801556580d20080c003500640c0a050310884010a0111808444914550b0000007503452441000501d500d182503c005003c8040540702503281c0602510b016030b0f40c1410441d598000090006400c40c1212900340030540c201031040a401c00c1c0d0501164402c031100d0300d010b4001c034601506070f038941001c0300c484a07241e10618812000c031740c082d0051500050080c2c03003a140045001c020074207000151130708107000d41c0318030301d1601611424421130005020207040642031000400c0000c08011400c1e400510407580407500030b0180c0c1c0c1c18401e074030040001c140c503a584142c80e9000c0510308498a6191030116001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694038642 1250 694037392 694037411
    0xf060103050106170c2b0c0f050a0c122f07060201050c07060519050a020c0705040e0705010804050102090901150f050913091703090304090501080c0a0e07021204120204 74
    0x1020701c1084600300b12111301103a580c030300100d4203130340140c100a0b0350060b030001c611501c0c030056150300d28124000704003c1191951604040c000d604001030103400c12070304001442140707900400a402c0958070a820129040d000721040302c50480c546107012070703450b21000d0320707140000081c01c41030101d8001099803595551044164200c4008880c0360004d1035040088100051440d803040e540b1040c00505e12002c0d101d03a403c0d6004980e8200c85404c4c1d4140c0c0007508002a0303c2c01c000e40c10080508403030a000901040300304d16103444040c841c03a4180f01e15a0045000c004d0207405903034822030301030b100c05115a500c030301d80c0580103000032601d808600d41c59100d128880c031510072100f00c0b00d800f03081c5011025811100340c2c010f010189040c6c034a040300c2c1c154003a14a0300d010040d40925000c900941e102c50804091404840041e8000f844c00e501201d411219074803004242001c031120101074242d1599105000da050031001801c003070310100c0020340402d1443d08140c038403039228001e0341c2c04c02941d501e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694039892 1250 694038642 694038647
    0x30504140d2607050f0309120a030f0b03010506130c09080d05030103020a06050c030f070f0512031e0105102012180303030402030703020f040f0609050121030c0209070905090f060103050106 83
    0x400c0e0b034a00001a1304005500100b03040750020f5810408000440b400070804400900c1d41ba0000c03010f0000007511a00031181e511000c0c0a80c00c1004001c9000308520b040620010741031090f00e007010400c00d521040c07403000b05809010300c8030080040302d05441c5141b000606c0182194424041244203410104000c0344461041d0241c803c00b02c0c402d80114038000040c2035010041d0403104044403500210a18800021014400c10009000903035241e43c8070b0900084580e52440000c081c03002e4004280010003450352042d040d130064414a0414a12169a03200d00e2101c1e400290007804003071085941c944c3c01c482002000f0954103415810041030403120004154036031005543c06941907100080a01c00761810008069240f4801800080c142d100012640d0681c0c42c2544403090040d6204c0040254150300a806405220305120009065034582c0d8098a95514500041c1c05805d00e84001100c25014030b004130040c02c0b005040d03031400d20b4081130703521310200d080b190540000c2c14036000044c2c150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694041142 1250 694039892 694039967
    0x11203030e0a0b06010c14030a03060f05031b060c0c0a171b06030415061221020c01080f0921071a061516080a0c1b05060a030504140d 59
    0xb5800000030040d9210040110780b440c040c5441610703120380c40402c11000d18410001007410a41d00d450208030b0305d240c4045071304c13800f0050307000b2030003070708240000140d054220000c2d29000004034381035505c0d160750010940c80c02c090705030741581010850f400400d04d80e0780c640000048151120440d00c0007070720303a40c807102c00b84111440c0c2a08100140082400100c20382e43c81c0d80030500401d030016880740d841e4428025a40d1902c42510521200c0c500c0d1040708078800784044504070140020a401c0e565003000a0070354500800400a0340180000b2450850050052680040d50340000061a440307076241600594850382045403034030150f04074002094a0340b03028601c070b13a4004101180d0100d5155240702c0d503030320143c1e0300c0280c000c0c0622090700081004002d401c0034141503a0740002c0c0509071a1207076070032041213041b046500b001c41081042e039623200b0440701031180c9480d000c5031341c0c0c40d94904101e045492900580b040d00416030040c01142c0d1010404000d007001180c3c903040d0b4401d4400050307919 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694042392 1250 694041142 694041163
    0xc1e01090507081005151809010905160602100e030405010c0807080a050c060a1e0c1106010e160309050703021309020d06020a030f052a0d0c03140105120a020f04020f03011203030e 79
    0x841031f511105e0007030044500b8030303409240742001040949a5070344241c10000d0714102a00312036604113050003015410050340028140c002e078100700380e1040f40c5001e039503401207104050411201c0070f98442000f40d02c8080c0c5440662000c07038140c54a40702d642c0501603820500c10302c2800d100e100e00240c04d07401140a10422503000c1ca0303550220340c1c10303620004064507603040201c0a03c1303624800904100710800103540200f0710407400c680340e41800000115942095200d040405050100b4640411000308110044a60458404418410110b00100030740310420020b503020715907079400024041709800900c030301c0c0e030140c2e41085500880e20b400c13801c45100740d800500d24003004900341412201d004d20314142c00908035000b401c04000042c15400d60306078003615070000352282c0103484000c11401c03005e40941400c45110301e44c2c402c2034404070783c3c841d400c40d0045d00c2400da480c1156070607102c950403100c0c80d500c0100065503940c0c446645038501700740071400710006458007504480b0081d0100e0306000c43d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694043642 1250 694042392 694042399
    0xc1006052706040203060a0803030126120301120c050402210112030c08070614090304050103060e06010f030c140c070503070b0408060c03061306141003020c1e0109050708100515 78
    0x160b44902060000a400060116810558001c0701190381c007401c0016500078441c101c911502c11b015003400c1000111121030201003a44108800030040b40100c0640341520002c2c0055482d02c07036107040c841116800d5a118075046440014060000e030140c1c804501e01c14030712000511141d81e11078020b0469180500c0c0540007804d00c1003040002240d844c01051894051312011500c10856000c0303041040e0184e4094100e07510000b810032281d41c25028141c001c0116054600c00703413034800c001a11668241e1000010190f84150390369504d2300511a03080107107140d424003500c036800001d043e69640b5090285911a103e2400b00148062101080380e0981b208480076140700e0302d418190846641002d07007400d510a603107a40c504040c40c190710505006140710a80f100c4084503410602135501c400358040020140104807141c0000000541070005c40d44180b40c2c14004800301d00c0c000d0041200c880c0c020300e1030044000004411a001546401c0105691400c001d242c451800078003101c40b589054641 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694044892 1250 694043642 694043719
    0x606090f05041d240604050c0a08060d05030a030609050f010303021507120f06051807051621020c010206010611060402011215240207051f050c100605 66
    0x4500300303034200f4462041103650b020f01e10740015071001c3c00c20480704c040070b100500fa40798502e44200d0318810507070041c03020b80e010441820803100080b01c62055640082c240450480413803a103860314521050320a4010058a4a800310030700000c014210903c02c0040c80f42c2844040341544100044803412139a00d500249129058a500c2c441d503901c0041490f4103011240840c07883c030040300d00a0440442c0703004400030b90181080c003003080c8482c03030342c2c0d07000500d0801004214401e5003103802c0300e82102d140c1e8425446941c1d01c4c030b0100c030b0402240490300506000b01c03901e02c2001d5000a507a884001090f000d503403550b0388030f01d82100c24001001c3c00e906a07a1110010901550080c17030144100301036a840800c2e0000c110031301d80e20040007580084503203600c1e40d43c0b00c11101d40c1d4204000d41a0141d10141c0240c80c0303840002006801382c103000f440b802c2140304000b2540390040040f5280d41d04080f0586000c007070111849001009148103003030003202a01405030440502c0c5910b1503801100d11524803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694046142 1250 694044892 694044899
    0x70501050906310204110d060602010c030c021914010f02180f030f030a0813080a0f080a14041106091806030c01080708070309020103060518010f05090408191b11040606090f 76
    0x5c05000007990688645404004000042140d8000c2801800080c3c0000c2136445001e180241150008626401103400108071140304080480b403414460745c001d40d8144050380040c652034018108100d50006c4030b4800035103455400080e140400045408036429110b488006040c543c60320b0b1140307090912a0810401c1c44540d03405000c02542100c0001240b000e4003070b0958900e4a40d030b21407290040803489140614029540c002005507000008600920204988000f521008080034000826041c1181d001c00d03100d440c0c03202070310101ea00040c019212101030551000d0141025034030300f03000b0b010b4220615110b5000350080c90080c941da0f51103020903981c0302c0d4110010034000408034109a200e2100080b2961001da0302c0c0e20306042e040d40301e1041c1d49801960301c210203180d03000764010b00341c20040002042d01c0e00151030103000c03c1d0003500c100401d41402120315201c142e0300161004590b042c04001d002a0a907201c0c0761003800d84042103074549a680a41b000c0d101840b4000a1030301100051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694047392 1250 694046142 694046149
    0x90e090613030c051504080c120f1605100504080a030f0908030403210c030b0418031b060f050f04021320280513090915020f0705010509063102 63
    0xc1144a0052003683c501702e100d445e91720904882600d003a1040348002c1072420203d0000e003c0341d107100d010480903624100c21014032410600558441c1403203010500504424440144031010101894034005c0056282c2807400d0651508101e1444002901e003140c42c0f006a5541e00c02c052000c0c0c1c100718030504640d11a82c0c12251b1503101c0c001a40300700c0c0c21011460308030070305019108011100d500c0c08034040713000206000032200850000905442da041c05000401d801180385a416001908400c1d580c0ca60b9003000d0b8041c006810110072824502410801d600383c5081c3c0207805648200c8101c50115058101c1d002a140b100c0c400200c5242030311100c0c220041740301c2c024405c1030820400000d11a00031140040078481c0070700e0000c041400040d8001551030200390b140003400c55000c080244100544070310424540c08440000b94903030004130445c000c422034080d03c1c02154040028001850004030340c07a01e41e90300384d03040003042e401c0005202c0901ca06544080c4d4240c0c9200c41ea0902c484d0325000c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694048642 1250 694047392 694047407
    0xf0304030807060b030c030a06060614130e070c050709090c0e0609060f0d080706390806010c0501090c090e0703080f0708091509033912010c090e09061303 68
    0xa603641442191901b0715140c400f48000002d1a024100000b407580c0b400310b016081d07001e09540707030f100340c5420000c2000304040740309000c080d2000f04010842030355404205807110304420101805612540b4400140c4101030b40016441038414440304461650382e5060540802c01954030300c0d4003000c500005a03a0303040118204414030300082c140c030340301c410b40d8540544070303845142d003039603807580f42d0404003091409149450901c52100c80440d84100803041d50488500030385a910041001c4d4401060301e40c1c1c8034040008400750018000c01501409152640c1412814841c05c0f145604041d11581c540d000840c00e001183c3d0450300c01490070002100e18005544021800c4503a99800e011858103915003501241d01103501a10f8141d644a1010400d850400888040004095014015a2841100031070707050306000002c1d900280004240010b100c0706503814681e0410340c40d011170030fa00700c0c0d4444644030031101c01200e031135180c1e12451000381e200d41c82240d0078540101d104400b0070019101d2a80d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694049892 1250 694048642 694048661
    0xa060c0b1f030b010f06020d120e150108160603230c0408120d050f0411060a090306020c1006050604060f0507050f100e011b200705190303020f030403080706 69
    0x100100a070a1008080034181c4454200781c2d10024031200510001c514940418040c0405000a1100003a005001002e4001c0c20040310703066910b800e6031240071107007005070403503500f0403224103046583c4590004e07555401380080c80c02c03602c506c1072000803413a01034400c40325051160303c40754030140341a00c0000412103020b4405581001c0401001441b420144071589581c2d4228105a40e510000b050030f20940310040e2151b0105180d0000740800a06941203c004c5a0810344003540c640b180c140069601041583c0050312460000030005440308003c1000070b0f0326186004104580ca271641d040c0140787c0914091b90002c03400054003000c0703041c003c0010303000c16407150017141c0404400910440c184458114003121550700c84109804160080c007404e40100b401981c02e400d1b081010b40014580300d40a415000720b400d40c1341c207030b290000301844001c0c080c00c00540031481c40154407070580100d2025110540050007906002e0410200100c12102141d03042078609080c18a80e4854000a00800d0b8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694051142 1250 694049892 694049911
    0x12030a0e030f010606030504030801091802131b0801080d03021201090e0708030c030d0e03091f0e1c0203062215020c06101a2104060b09010b0403030e0a060c0b 70
    0x41290180b9402401010040c00250b41c0100f02ca042924020f403ca2006800050042c3d080440c0c0301c0c444a5041c0902d803041c1c0e0122001100c0a40194a00c0700500c0004002d50a4040950080e06141d030400e0305d55040380c424030116107070072650382012022070080c04000074022005200421042e41c80c0c5e040b4000d0300100c0428ad42225694284061a40d844107091800d02c0d0404078098100c243c06200305012940d001c1c029520f00051400000d0307500c0510b20700420490107000796407810911030354000d442840041c1900200c0c0e09440c81c8510b6268220100324464410302c000240c00c0c80c2d04001008044011050118182c8603568420890308500400031404541c240b018030003da20800c10300d401180210904410345007459480b400394294100e0080c4203103810480c05001403201c0e042c100c144140c401d640895500c1d00e141c608098600c0c1124164000d030701000205200c4580310017002264842d40f101050240100184840da07250342c4116070102d8105041500851440540b841c0c3c40f01000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694052392 1250 694051142 694051153
    0xc0b041b0506090d0f05030c06150a14010e09181f15030c031101030917070c05100c0615120b070e010c0c03020409111003020901030f020921030405040c0507050c12030a0e03 76
    0x50700b08c61520f4000c60b880040d0b100d1000c5003034041d003072202c41c460240180e110032029421000001800000780407007650302a1501030005801c00501800c81c2d403608441405441e0381d0384802402d0240c00e040d0784901c0c000d4900d44034809403030141c0301030124220fa5000701d1345d100251840c0c50b654584000514494141503e4031444000202032480020524075090303121911444d40d8103003509020901e1700142c0c041ca03004440840c031036800c000aa51019401600404c403000c120728980d4070101254072540d000f03004440130030b0030414001916446108140e0f6001e0115018800441d143c4011100280c52407491000c10b0016040981040b20302d0790045002800740c0e5205000f1802901d07000c0605000241d010542000c1923078180541c0407083c2051000b1750500e01c5a10019070750602c00515400c4040c2c41400800c4e2a44017030050f41d004001c014010060700d00008405001503100d00412501c40c000c3c0398859450703181c283e4010780c00d902c00c21300079820b103062050151007403604203441507898400c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694053642 1250 694052392 694052407
    0x40210050a030b1801061803170c010b060f090111010902060a0c030513080f010c021c0c0c0e0705182d012a060b09190203070c0b041b0506090d0f0503 66
    0x30028044d0140c0c0000160007603075803601c800104805400700d01030a00d075880150030408103c031011000c0e218842504110b55a84601050318014074038115a941c202078042060034000010b00301403e240502078031407000031440c10504a08230340e000e81d0025032150051105034592442051601407007032180c02c05c507251403196000c40d1800c06055000801e03aa00281e1030030080c01c030a0080d80403c042500040c52541141801140d0040d149038100c000c10100d0610740d0280904044540000c160351050103610b410714240091045d40500c44d280c0703d00041c140c2e0340c0c2c800c0c01c0c1440903200d01d42440b229804450301c80103e9a030309900c038155050410400070001c05211072803140340801841d495610349007200b2245800c0302a240c100c000b82d80f003240018200650104e02400711404898021070060381c039510240c0a59a200400c440980709020940c10482000300041100a10703200e00459005001d640e1020014248580500a504420700103031640c0000c54103151400203d00c18000d50781000b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694054892 1250 694053642 694053649
    0x306020313080d0605120a021521010f03022106190e01061202090703060e040b0a1103090309120c151309020a120509151512030f0918040210050a030b 66
    0x1003400f002d01426526102040f0529210401000e14048880a0122000b07690002020301072100358002d14030714000383c40601900002c01c6460350403034044440c01a07507101d03000400060b03860301040b03000d0220307145071030800500d1296200d20030070300358028401da44d00d07000010b01c1141c000d5207104040740c849503a054166802c1c003807180a440d14891140303171440300740100241356002820309020325182440c103011071140b0041880d8002d4204281c000103440e000b552900a21074100088040040801440752610002c0000e05400908481e9409000c61b03512409071100915682c4e030b603001012440b42000410020090121103450311901040342c0d0b5910550420b0343c2c0220b0042e40022112000c0400d00485442010303000818030000701f49120740e0b20041d0032151400b600c21010a001100520081e503202a0120344540d4071400b030702d888081242c0b4120b81c0d0f80002070711a200e11081100314075604900001e05208907002040300d02c1d903200e00b9a00380c41540c0078501640426813981041c2140340c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694056142 1250 694054892 694054897
    0xd0b010c1e0308010504050403050307270b030702010e07050303091302130b030105091302030d0804020d0f06050108010f050c04060c0201122c06090604110102070801060f0911070804030602031308 86
    0x8a08900d180072445291a00511442050700200d2180e490034007030002081e0300806581e800509824801300b00c2d04558004800d003140b242d04030030820482100810446402406035010f01c4064009200b540c0244031201c1d00e441c1c40d4050b454142c0c0c014000c03800c1e43e1404850360304560001000041c0340800e0040c860b0705280440c0c0082d206a280000100640d06146543c0e961010317900e81e00d11000a0243e000a40740d01c00f085c0c0b02e4040080800102d020365551404403025158405c1d2450300c80581ca14003403018140034030030090203500e00b1841402d940401e0240b28482c1c00703200030203803070507043c80c00954030000380d0181039040048908030280c1c0018144120700b12005182c4031012100884c41d00180120b00302c1d540c422198100d1024007200500000d655500a9403041042405c0f600c902c0040341340401c540d0003031300c3c0c0d9030900134005210f20b8040250019100d00e8842409104807100c6a125184100e1000600003503040004101054055010b1508000f8586468241400da5110381c83d4a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694057392 1250 694056142 694056173
    0x601082413020f030105101713060209121b031504080304140a05030409050604020403030c171c0f0b03070803071506090c120c0e060d0b030a080c1605060f0d0b010c 72
    0x880300013006003c0c62400f000004007504152405414801909654000140c0081c002248035071540c20f0750010804590140d070100c0c0006000105140d4155040a80c0d07403c2213500f030005907011340c0241d1441c0c00c000c01c8841111004896410560303c580e07a44220030350005105840d002703848100302c05010024040c030400d45000d900115140c0b810403040780304a0302d000c0d04981c865071041004000003604091a821000d03044074400e00120851903034807600f44540481c0f0a4040d20071005406c400d07900d5172000034454100c1104000c1600e0301011701d0394906650040d07d000b03610901255001a1000884010305101e002011854650b2216003406450104c1c0503407000c20004248444000c0c8144120459555145021116003010402042240c800c2ea900c803c80d00d91a000401520740b42001001402644104425a585000415281c9070712500c2110541404010741c002500c1c03819400b59100e00541c144d14516040301a400d00b00107005a01125060140c0481c1d01004034042800e4034044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694058642 1250 694057392 694057417
    0x1e080301030501050c270a0306053c04120c0c0314060a090c0504090611030411031c0527090a0237180e07050a08060108241302 56
    0x4a5046240032420b50340c00401c94031170101e05224139050206040d0f900d0380c1c0122514060000e003c003030380104050382091340000d040682080140006404d141c541c1030700749500c0d2007454241e118000074001d0005110b1441e00b603001e4040c0045000f06501252210803c0c08a003414550020f44ea580c1d080c000c0880d46c01510718002240084826607400d0140580c44000e2034400c01080e500d917520700c03c2081403801840e0140c4c0d0742e101140100041603102407561100c01d0080f40e100d2915160212803191042c07031150190041d034441c080000240042c1c0c881c036110940b500c030b0a18004c03100036000c204c20907100200000711407d0b025801e455040c1c0c003d0254900d0080035a407452100800004201024000c0c02043c2d5078030008180f4500110f80031800100b94900104084150b0303040c0314007441240c0284070314440c3d00040c408110703000303001401290103070384810390107036980e00040d100c1000c00c407554000e03590036a001905000c0790080c5207031251030040583c0128104502c5040803a04103264031a034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694059892 1250 694058642 694058647
    0x270a1719030518040c09030b10171b06030f04110402070b070306030501050106090302130509070803040b0a0e090411010c0203010e0d0e120a080a03050402010e04020c011e050108030403020d1e08 85
    0xa41d6000301103500e01203802e86041c03117902000000184480c01a00c0301402440b0f43c5c4000c91030300e03140040240010000c5540f9500d8580c1402c2d02d4940751b5034810705c43c08021240384044141c0c6c0c10b2500540340302d0048420001000e03565501d501e508070300e0300c0d001554801c1c0c1c00c0000743d0010b819a21107500543e45a03400064860451404508440060b040740d406e110010400f000103a50700b4030040c404014030200452588c0720004800d26002e00c41d04803141c1c9000c04240850758100f00c00142001a01a03500d500d08a01d800083c414141c03410f80d4040c109a50149010890354083c10a0180c07440c405400010040c034061443c03800c0000c240e02840005034210560300940c81c040c80c00025103004140545075a09141d51000000c4c442c41104805044e1507100140c1960300942007100c05400c050000d45d03490171007151705030080c10741c030404255456840300c030320500d205c45102d039905940c2c82c00029440c0908613001c100b2040b164102c1201c8012952014054040c1d050b000306061903c0360f00511f8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694061142 1250 694059892 694059907
    0x2060a05071103061330120b01050711010f020a0605100503060606030f060910050925090b0f0d090606092903070303081306050c270a17190305 63
    0x2001103950380c5803440f0354408001d0140b42425500d800c3d640b664040d59140c6084031649460a12007070360340c20400702e05003100300030250303640080001d90346d48031a0b64104440350b00c01005458501034030070050308151480d20300c07040ca5405003000f09560324450040356801c1c0402d0b40c6401c00d6070340c00c8600004144080b84108000c0c10200300346600400304841035400d515118094134a10320303000701414810103a06010940a01c401000da20113000040d186002c00c1ca450244002c801c00907913040c0f08800054000039055620510311141503410201009103400000a041055600881e4451007440d40e038140d5100028103520601005008143c4040b40c0c801d44501c0c0f59144440e446011405000180c003c9029990040b8500040e650305003480c00039602c6181e244181034100250040c0302c185050103000c121002440030b00352f051440302c07483c660211740881003860301d072496155039080491443e091001c0080760421003503200e0a48208d4007800c504d80070118010098901c141c011840004461 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694062392 1250 694061142 694061153
    0xb0f220503130602030424120f0506090f1006210204030f0b1b040303030c03021c050114010201090308010905070c020d080409050c0711130f060e01051e15090d02060a0507 75
    0x10b10003403402d070000d1800e040c9040c02d0600300b0314203a8080301702d0180c901d103801211405118400c0c159000040d0811062650710400b40082a0a1f241980319901c4840003a01e5801510740c090700c24030f40000342c0e80040f03240820a41d4520042510b403481c0d002007041080b1b00000d548040d100840c001c030000c201c5062142030889202c00050400e10b449404409195041070050b0122422241e1602e000102c031151608118001d00031500c2c40348454040c04003504500245400150680340b144100c040002c503144016400c907080c0c038030001c020a403030b034004000f85429988503540c0017250f03042c690085816030740043c40c4084942c408540c07403c40410b003444191460300c151584081c0d8010214a441004e84483d504e03100c0020078288995401040c50030002c2c00c9412054030310255440030303c0055100c441180144909004031405481c041c90f0380400000d1580b00502c98070005450003418200c4210100302590261003041e4018a81c000c0d503000589500c0020320390701c5441e60300c041e19803119241ca07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694063642 1250 694062392 694062427
    0x102190e030d0e0a09060306020702030f030901020a030c170c07080c100c02040911030105191103060f10090f15031802030c01030b1302070501050f10030b0f220503 72
    0x15804100030858111a95140014010100300c401c2c20310381101d0000c40c00040240207290001070f07909007008400020030045030003802c4018422400c0d6091046005c50541d03036400390321409401a131080302e030800802d01580350b00140c0d030301901c44500d142c0e84103280e010f074650111940100e181e0080004008001c824071031440598011250800c0710410214000c060028003280684159039541c04002001a490032300c1030380741805402808146000700c80e4a2219102c0b00d510304030141001c5948011140400807213100c0c01000b00300040c02ea07400c60910aa14544003502c4c01403103d00000450300403100c001c054010803240022030b5003503480003c020190340040d1002e00c030704500a1540c03001030b9070109a20344803000a1a001821200c12030005001d4032000045c17013100352000491105102064119038819290f8058004040e240d0070425501d0854910024040c500d0b00e40c081601c41059221540d08103000c5074aa821040444078026071020705080300311416840001d0030550f11444026 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694064748 1106 694063642 694063687
    0xb03060105190c122a020604090207080c0610030309080312010e1905150114160f020406030506190f0c0e130e1203010f050d0f0209091e0102 62
    0x1e0459084e5405045524080e000e400c007244003403908881245d035018120f00c1c9003a00d4050b05400a400007030b01182d00501c01c04c45140700007800c0018038003582000074181441c0386545805012040c03641d100b05060740090201b00e1190000041c41411120640c0c0b400340c00e07644c7d0114202d030000d404c0c031110350000e140c4414050303802100c0541c0d104800080e2920041c0180d220302402e00390151506951480c0d0003015000000750004214029070791000d03101048ca19100c1c0d50b03032030034258101c902d000c040007140c40007040e03241d9a0090307150041c20108c0030031620240d03420007000441b0703050340c96004c0c10714010012b00d2072441d54040c040906800065901d400c0c401a15040c141e8828411488070f2a01081e001c140c03440c2509070700d0400d80d8031203e910222240c03603007445001d0500070f15920443c01060451f03010040700303000001b1000621000160b942200040e00010304000300b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 693884892 694064748 := by
  have h0 := BRFrame.cov_init 693884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 693884892 ≤ n) (h2 : n < 694064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
