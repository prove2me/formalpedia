-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3643
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:08.357194+00:00
-- url     : https://prove2.me/submissions/32017090-47d8-4d7f-9a81-73e49e763037

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655035971 ≤ n < 655215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655037221 1250 655035971 655036003
    0x6091502031e061f02070803221409060415080f01060e13080403150e0d0306210209040f030212030907051009080318030c0a090f0b030102030c0301060806030a0b090d02 74
    0x800c10200c2d465207250300c10650b04c1640c912180b260403101c100d28101040d0001c55403030001080e000e041ca0070340311410209680005411002e291500b9190342c0803406000fa46900c010084041070840c20281d02455072152404061440d181c1c45c0c0e42040d06d800a600d59080035a9074580042200c00e0f004403800b900300d074400c0c103c0811121151694a071038010b074007000d80f406031144031045007a041640003050a0107000280d81c5080b4100c00050002d104600c1816488001c403124040040d4500b003c03408840c0d03008020b1041030712030b6240c54904070020341003202540300b142c0e680100502d41001441c4100c0340040180540e0781001300b848110681d0245000a000d0b80c1c6d1414442c01d41c01000340c0307070100c60381141e99003003d400d01d00083c81d100752100f5485d00000d6090000c90b448642d0380090000380f840d070b00240711000160007454200e2108a64a1500110034001440128410034000c1d802c41c07002021186410203980390304080d40c07000c0c0c40300395055201115640c6030307a406108019020903560 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655038471 1250 655037221 655037281
    0xf060a1e0c2c040b010806100e0f0901030305030a05180a0b13140a050f011109040c020c040507020f011b050702102f060a27170f0a1701060c08070609150203 69
    0x19010239202020034620b0b130144040e420001c0700b10b4851003600d042a280003030806041d03503540e007030207400e030b6000340c0c2d0740310b2260300380000a10754a5030700c52404180c0d07100300300515514145803140d1407402000b4080d80100c8652940e8000410745107241141610000d07405040414000d01e0301525080418a0300250750341000c6112104e032000c1c1042d207900700000e44001c600c025103042c0c101c0c10810185813496201d840c000034400504d9001603c100c0b1808082c00810450070201d20030351403041004040400a0001c0003011b0060604031503000740980141803040b003072403002d21400b80c50220740107158447c0444815850901004105050300a001d0708000c0140d4428070705080d001c90071103040c3c12180c4c0002072040b410490b54500c1216120b614140141e240c600720144058250311105031000043c100d0504024440390355002c2078101c0388142c0382c5201255a40c0d079822050b4009503419100e580da01d02984011808010121011440d640b5005030b480c940603244606002d580d8980c42d021407444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655039721 1250 655038471 655038481
    0xa060f1a040905010602010b03150c0426060f011a0702060f2d0a030c08090a230f16050909150402060f120f010f060503010b030a090c06020f060a1e0c2c040b0108 71
    0x10070b0840d8150dc078a03411801040381c042c5102c2c81043d0740c0c00100c1e4100e104810800410000003800b00d41a950480c51620a0082c00f591030351081c0100d84010394051400c03c0f20103c10a500300040401c460b8060580780394240a00c00039681c10040140306407800000541c0382c940642c0340c86060002c3e502030034500c2040c00c080034061383e0b40c0740c500c5004040440350591010818880084050741c82c641c2c400b1118640c1d4580c040c00c2c5c03201c00304241c2e00400e180d0380802140b80c4c541410078900ca201d0017002402c52110035024010841e00141c0f050340c01043c10451940590a404003c103401c1c00d11505011003428000f21203007042c41e05034804141903110207400d0001c29030000c2260704503413404802ca5101e80351044c42d40000c20f10018002c2c119614500e000802580100b00c201090703001c10f069400a42c0e4a42e03031700d01941c0301600c4800154004200c400b120040940c8444100c2c1c01d01e1902e03030200380c9044000400750711581c0640290050229212081c3d00e841d0107150280d03e02031030843c125081c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655040971 1250 655039721 655039741
    0xa03030c02060a0c2102040f030602180108040b0718030209010303020d0801090605060f0f0d020c0d0806030309010906110106031707060b04020a08180c0402160201080a060f1a040905010602010b0315 87
    0x10602d04405096645c9090070b80702e50103601502d026160111500c4415980c038680000298400d44004003c0803485000c5207003503004201c00c501c00c903046000e0041603940d41c1401c5178800c0458141d402d10700b541d080c0100140c1c8030300282038041c40c4039030001e0020801ca50000b40801905078000c2402c6820321005000d01d45810081e144800007401c0c04503103858140041402e640202d031303100440a84041202041198000b5604440780020744135800e040c3c03503460a2507102d1160240d11408039405103410094070340f095012400f28a070410000502036100d82da500040e03008022003066855002c68940d003400740c248160724074118103e40440c41c1c005410f01c081c02c803000081007031781c030702ca58424002d1400000f40301040582000510466568010020341c4445400d18032080c0d0004090000150910050b803051710117640d40c6094162105142400040c80001c1c80c1a00c113420140c00e020015a136005806001c0c040c0c1030680000c280c3d1400c0700281454003140b40200c0c008a00e06000303110220f88 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655042221 1250 655040971 655040987
    0x4110919150e13031e0c050a03090302130b100c06180302010b01020c0a081c180f03140a020d08030601020703022e1803080a0903050a060b13020901081303110a03030c02060a0c 77
    0xc203440701c0d860786145d54000d99041c0c99618014100c0d0182145581c101540014604180d074800c482d01e008032000062001c084500403921140c01c05080101250303554056007110f01c01600c10a008660003846000303144c401520224200c000d40c0d10b603004030200d9a0180005c142003002a20803940b4540380800440c3c0d40c90030443c0716003405060101201085201d20a04c01940009000361299255180e0100451125a220a40300c211110b002ca0071001c4000c40c00c003111940082c0302d200000d000d034640c143d0690010300540c0c190321600d00000700685071014040958440164440301940f03601c861102d296011425040412081c003400b003003410901c2001c042901e130403800760307615952001c0090b00c000da40c03034001806900c0f40060071070801c100e5401240c3c155030182e403a01c1c08103080f40d5100051780294480349001c200c0e600001094030307824500f02c5180302c0c040e10b0030082000b11810700c54100410300c1016030000b501c03a070a0000031030301000340b00c0d081228011300300407008040c100148000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655043471 1250 655042221 655042247
    0x1103010e04030e0d050c03070f0b0d15080706020705030d030e15070504180e120f16020414010320100e040f0f0c032304110919150e1303 60
    0x4403150303000c503080c90300c03c81c40341000050240c84456201007030f00f08207550703019815501d4400e03c101203000c241c1508054482c411101071740d81d064208281a0001800791190b02948540c1035170000700054600e204000c090010100c0da00589140d9080509050a2880403d110021305041c0440902c4d0a00000340700c0410220102401101e6161220219154400d40d4400480c00c03c01c8610040c10031000d511210040800a040703c0450718058010001802582d0541502c650203100c0d14050700c01c64060744002c0c078401080018080650764501d14004020380081c0c90120100342d00700c001c0103181805c0c00d20355000301c40003041c0d0048110b00401556140c07240c24000da49901140500f413500d50010808404218003e2118451203c8014010141040d060000301d00040e03100e85020030201079140210781001c0360b65807081400c0140030310000c01910200791a99512000618506d080c400d1518101e0340285440c5000d28104400d002144060003000280442103039203800650029034041c445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655044721 1250 655043471 655043489
    0x120209040f06111801021905101a0303040e011e350a0b10090219030c05120a0605090603010b01020604020f03010608060c040801140c07020d06090812040b0105010201110301 76
    0x68242803420b040500000004450b80e440007007000308055075424840d01301c00d6805c0c1e084544420a244043e0303440b110b41c0d00c000e403450300b0040d0010000d64040e04403200103210000e103c040380c07420742c010074a50740c0158011001d94201b0300052080c0220794401444402d0b4802c0c4410320581021082d01000322450070013007410200700810f4994650f81507030840348145071b005039005608641040c0000c5441190a0104400c0b1a0307000700d1003482a20980c1d0245100401c0740d01300201c41c0200340c00426245000c5c03402d000042c07200d034090310795484a0611a02c00780d100803c520f4507140601401071400ba04e25403081c0d0610070741b840d09903400950136500c0354041f50420b40b24000b900c0800c0c010540c4da008485640210020401500c1d0070500a0049840c032000030003814072150003a032144802603030302c1140706104201c00d0025190000b441c032003041c0500c40000d2080d48664071200e160f4001c0c00c403040725441c8002000709000700700a20074018942800240300c244e00c807000c00107162105014044403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655045971 1250 655044721 655044743
    0x108240c07031110090203121e0901050714030408100504020d15060b0c03090306100305060f0721090c1406070b090703050118111f05180a06031512020904 68
    0x303151103910b484600e00c1c3e0340340c1aa0700800c1c80681000141c0313444081a0700034480c51290016103e610340c211403003412802c00c000200c1c0c00c905450b0007107070300030450380c0c0c1040380921038000421f031100145e51780710029030300841c0e0307403860074804070304002000b21141d19045c41c01e0200401368846000220b003180d0f200e44094400410088500001c01c0542c0201507809000700700c0d4130300e0714800002444a14002c500b203070342d50355881300d5990460800b400000d105070080030200302c80110848a581e001041030030710554205078030380820780190b80d10f40b10000b5981c88155400030b2056005d2508042c5c6013185215446103084000f0441d24810001d000304641c8400001810071501405800d028550150081c45071104126000c1b07103020800900790381b0110466800700441c80e00d107100c1140b0800d1890700c0c0008607083c00c000e48032604045003c2c1100d40491004d011140d0318160101e0103001c0a0b20300040426005982038544501500304e10010b103c0c2c014100050b03a01c4143c040d0780541d2040c05218 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655047221 1250 655045971 655045973
    0x1a040b070e18071d0307030807030f020c0d0c030b100b1902030c0706090e010b0c1005130b0406050702010b0a0305030409200304060204140907120b01020a0206030408030108240c07 79
    0x40000c0c81c070000b50141e00204014442010740c854880c4020180c07450050659400c001c00f05500c98040d48001000003401300004070019000744400d12818216005441e0030090240c0820b004403269001101c10384142e00303017071007081801100150418080010345c04628204608020309115440303035450503907180d0307032240562442082140c050a4a104c00d41e03482e50b80c4c1d403030003030070b070191500030a0040501e12001050013042030301601c01089020009142240000ba0103400030100503000c40c2018290700070441c08225600100e5000307a214160002d100e207040701c4001d0858104580d1103108010000007040412400001d80741610690000003540120a001d0003070100070040d1410ba07010305c044100710034014964080c10454030328007070352580b96407200204034195408542170303404038164541c1c0600c41c980e554048001054103004452000d15180c001411a0700200d03401c9400c100c0000042c4091003040c00080b10300000d0302c001a140707140d0441d1040500200a090711203126020501d14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655048471 1250 655047221 655047229
    0xa080c12101a1623100605151e09040b030109030c03090504060302011211090a090608070906051c06020c01110702120a0f060f0b1f0f050f0406030905281a040b070e 72
    0x80c008182d20021160003255003d0544050601d82c4a441e104610502c5081e2a440c617600448418000e4040d102d02034600c200118051604001c002b40d40165540c030803d8520b480074403843c0d0b4901e0294440310144172462030014102c240c00d8104900850070030302c007040107076004000c0e03944401e07142c500071400c4900d59034460028041d500702e80d03070301c003000c03400020f03a40840383d21080a031703020402600e030030300c0d01ea461006c281ca1451148580003040102124080c030500e9040c480100d200d010003501d40383c02041150b0035161490b4018802e00c100040d00c6085140c1752891040c42880c10000d80032030303811900d9140c000c05402c100540320759150401c08503040701b03a40c050350b9040d034000c186000350940d40d1048603142c048034030702d0030104010507050798405000d5020394a00348050f4065510b0103041200c118058864030b00129860300c00c0603045800e46001e00344c48891032581c0c000340711518082e414403591288040c50010300b2001208280030104000b030751001d520a5040c100fa00da0703294084049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655049721 1250 655048471 655048523
    0xc020d05071203170f13050f011e06090905060c03100509010b04060e040905120715141b070206030105012106030506150111030a080c12101a16 63
    0x8195000d031650105401001c0700e20b00c0d102a000b5541c0c0036914080180400d8809010340c0d054001c00281000640110500412861954803440a664001d440101040d094494030b030940351004a005040043c03104003489440c008101558080c0090449602c0d2203440704405090000c54250000c0010b190040300040c40000b0316000d00078104135a5204c1c5040c80d590840d004060014510000038001403038603005211140ea00040079002da003581c5000043d00fa4044002203036003550448200c0300c89401441480317544e0350341d000b2888581c03038000040605170464a5803070704605424090040543c484070181ca054610a082070b800b610756a0010b05e540e440c8250803940c0071030403d14084100310380841c6c03032401345012246070001a424200196454030303600880410a07030007804041a4984038034180e907001945000320501d06981d070b14000406841c1182c00030b0030400008000c0244a0320140224814060700441d241020380c141d178110b40c60764481c0c402034000c0d045404120004074000e041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655050971 1250 655049721 655049723
    0x130506130e070b0d0c030b030f0705130608100b120316060b010e120a0201020d050a120f0e0319020c060306060d0b060f0a0c050c030601180c0207090c0804020a051f0c020d 75
    0x4180d21606904c0d50a07010f00404822000040c4c100541d102140c203002031314120414480c405050420300304020302101c00d00a604040009450751000a19001c003880510700c440101100402d840c45000203100104100d50740000f19580b0801500031158000c0c0344c01c2c20825803000c40031400c0341030034004a0b1180d0391418002d40c005424201c0c1050f44400282c0c41032068030030f0b000c1d0b80c503001200100b42c0e2503002e01442d00c2d0105555001e00d41c0301181030f500c4021541e13205400055a9074644140754950303004180d01091880c80703000c0c2030090b541c0400c20281e2003c0101d40071807231880c01c0408110540207074010032850548619041103c0d03503440c82500c209443d0592501c0d281c2c1041c4000604507000604141d42c54002d98480c0604c0707040115420b070580701080e10329103d8001100030800100040c20301e910440c00352440100b40640c80c0e0060001da403c0586c0c402d0610300f414010450018082d91010703215400c0c0080d400803c20b922011100e9a100c00c0c1807060f840542400401c40504040340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655052221 1250 655050971 655050989
    0x50a030c0918020306030c101704021206010803130b040b090105030a0b131a060c150c0d0908030a0b040c230c031306170912030406090b090705130506130e07 69
    0x4004442d40e0283d80c06036105e481c080b012a0007000340841888031030100d04001d01c000440d03c0380240f03403500303042840c140c0091000e4a10f40380418031a10b482d0820b5070130303044083c03030743c00c0094010300240f90520240040c024aa1249161510300f051102007403182508007410321201000040e01106190300c804480d80d03029107101080c004141e60030300240741501080c05d00e0a8082800d003202e04114082d1201198958014201109041400080d403c0014070340c601c0e03010700308001c0c45074080e240070700d50025102d03007005512424040c000901340d44c0b03d040b4480c0201d10302076502c0d500c02e601000e418a80d0803d10701d140c01d01c000c2c10042c800944600d04e8104d0b9103103c005101c011740d000c1d41c0300402c1110b40a507501c0800b5010950382d210f408105a4801c425640f200740502c0d5120300600046800611070540007590042c5562000d0700000e045070000f855801001080100d414400e00703402c000742c00d0a2040040707190040001c4d0381c0c8c3e01c0742d00d0000b14055586081a41307400e0f00300054005040d0000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655053471 1250 655052221 655052249
    0x4050411040f020a0f050412020603130f03090509090c0130061404060515040324050702060402011e0813020d020a0b0a030f1109090c0d090b0103020a15050a030c09 72
    0x400400c0295200c929820001000c174000c01c1c840340e11400c26a829102d45d803580c0085500103408214150b08003800c0f01d003011000349000800200d06021540d070161090715841402881c1c9002c100c0c0c4010001d1042da050340144049250726a8003018400907070070351400780c8460304c1181d0082d50415421100b8681140d00d40680030501e40180112498000400c031002c1c0b15480d110b0f8103211100c1c00c1c01d68200c022180600090000400c8404540e601000c82d0505141c1000c18014801c10f581d000d98030000560401c20071300c025540d0240d0050420204030301c1c0d101000d241009d008051403001070414003455000c0d00300e0011075a030841d140b00f40c60f4005044142c0503844001040b81c03039200078191070100b4a051020b01d00a4281e0007142d04900b03d1015040c02c03c21131005010b18194020285403502004000304e4003040024800c60211030b02561072000b0640c1140705101010100350010885034011074000d107050395201c0101c03516801180f41c08181140707450390949000140d030b000b03682c401c1052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655054721 1250 655053471 655053491
    0x21c03270c05060a020706030b0d0b0f071d01020c04093f090302060a1b060e0c03010e070503070b1e161a0601091a04030f110901080f07050405041104 66
    0x14208100308103010300d0080c29290758510400c22503104400c0c103180907030028902082128040d07400b402c00c440f8003510380300c00000b45540346000c0003000c480c5426561541000d000c90103500514100284109140d000c80d0040e264001039a41c44540c2809071156813600b800c0b604100b04030b18200000307500c4924400000400c1c10303002650741643c5542c0540144400c000081d90741c400c2d16400203d9402501c2c41d4034181000300c0c00c03600340100007a0b0951050701001242c00007401840744d11580980e482c041c007078001044041600f500c07030b11845002c0f0b075409001d060001d950042051821901c0d02c0014a650304c401e012144134000d2081c241461884001c101c894240d22a828440d00c80ca104650703840011740300b60341d20300b50705000303a403441d0000d10b0743d50040c0302201103a15120f406030080134145090590360350721032801c506c50010444e00c200c540e1101d44100e040500145001d0100403005e007500e00f80c010041960b4028504c01c43c2c0c800c907242c1003c181442080800366001c0ba6000d0400c2c8080c00074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655055971 1250 655054721 655054781
    0x3020a0f1d120f1002070201020f0607120b0409020a0b09130915180b0103050114010806390d140903180402090d060c111605010219110a030b0f07080403021c03 70
    0x7001b0164054082e038201c00c0d16803840801c0462281006032250f507612410140e801e0000d1485021080d001070b5180c40440c0035035078803800600107000b80101143e941d4501014400c01420101050401174149450000040d1074540740b030206081940d030001d04621005000d9002c042d55000251054030000c002100344001900680860389095950b040380d039990711050742c0c2c0c540d402c54040040c0c6100800d440d84000b0640450b0054442d80c4075504503d00308902c006581c3d40c00918041c410740d559080c0c1030342c42100c0f013040c04d038000c05940c0514200391a00d40c48020070400c03c038074244540d500243c0440c180d62107242c0f5003561900f1500800500c2800e000140920a8007006000e05120300041c1180c80110518401c2c187c600603030240510300e0701d143d4524001040c81c0ac040f240c1280c000d034500c2c1143c03941d04218000798080d505010807030501d03200340703d42c900c0054582d00401810b1010040031940020754005400030302095400c036106610000c0b0300074a5501028260316200460000030f26034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655057221 1250 655055971 655055977
    0x30309090a0c03050f0412030c020c0a06020303100b281e0509030114160c02040609110307030f090b04030509220f0506040606081f0e010603020a0f1d120f1002 70
    0x42c9030b103003084030303403a500300e141c000d0707881168000c026800e00a000300e0403c0c466001100040d4207070040f40c03186078040c0d0004001501980003607005910220070407940c8014003000c10024a002c11009203004003400103101c0100104400744816022000c0c01c081c000e1140c46c40c0c146101c620490b40c240d80e0032400d0014010b50084041901c42e609090415440a4218081e5400350203e525100e90b4480794003415a84213041100c00e0f42c0c01a82c034113001410340624060b00000c080d200c0c501c0b030f54900d071000004e0111450710301c003240c410340307030040c0300c00060322580d030054200e605070902584850740080007038149019070140bd00d00310040c0b80305040e02c0002d07401c01080c03111042c409202035070700c0100b4002100d03031034806c141c0040c241e02d0100e078204c0400d6102003401d007138601d40d900c202a1250750056140c0d07002e07030192001913400608040066480005031f10550b180e494012015143c0c8042020b46c03d4840c0910f911840b0b20304500b121107002004480a203036440c506650180604824000c0250 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655058471 1250 655057221 655057241
    0x1506040e0403081803180f270702060702100b0d051501060e04020f090906120109030e040f1518060807032009071b0c1d3c06030309090a 60
    0x580c1500421341001858036411003044028004506211840750b4041c42000511440c58200842c86041c0081e5207540305940c01e01d59513061400803d40603052181d000010050100c42103410130014046010fa000c44d41600e2030030240340c041001050341c07001501003d03c08a004007184580504025459900741d0f039a41250a19141c082c4d5000c2d1a5040c48143d1007400b08035410520200a08505450444061500500301501500e000c0b01c02c8941d850031a10b02e08020f4000c66851555519030345424080c00415460861013031020311103044460b402c1042a024511061000031b004100d0070b041503101c40000c2030310100321250315a803401c1051244110520801c0554900c008051060030035492481c020b030b5030390380c0c0d16440d5100300781d02040780c0081000868060401d6600000c083c1c0104d0803034451a83d02c000c0500380b034101411500d4058500b0203407000340303114480e001c4482e05a80501c20218901c1910080f01640e55000001d041d80700b180c00780c55200102e40180140c1809907030002c0f0100c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655059721 1250 655058471 655058477
    0x40507050a06090303080103020907200c1f080610020f15101a040b090402090909030c070f050f0909070f0b0c0106050a120f0303090203060c1e0415081506040e0403 72
    0x358485200f252030301c1c098000a004518603500420050800412a81c0d100100b403501404040d921850707c882c1411007201c0501691204681c501c40f860201c680c61710400741240e011a107003d80b160080d1200c800202018440c4580070b9005682900a000c41790340c508040066400d6100741d45440c0000440a0710496003030030080c140494256038017400000300c0324070b484201d41040e00d4014083c0d215840402d20b20b400580921801c2083d0b10380c900a24010781c0300201440c0c44540b042a9180f80039015030103d5120b200315481004145c403400c400000d0a8010350380c07400307143d58103603080c1d180c9011079000c0854200c84440002d00d00c030805020b03041d244440002030010759654000c000c11030600c0d00030708140418101c1c1000014103001204052284241000704a10340f0a4000a080038012101071100405c00501b1245d941c1100c0c0e8507851410740c0c4002d20782445e0410004104d11503a00800c20b00380305c10600812024100c001900840003030090060b80c0c0c55848002c55400341400390740403004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655060971 1250 655059721 655059739
    0x20a03020f060907051002070e0c090405060d030e210d09030201080f090c10032912011a010507020d0c030302011b02030a1e0c060e01020408151909110904050705 71
    0x42000c046030040c0100403007001480303010f017003008000013403551341442d40540c41051000190029000c1032136104401d4484602c2e00d0311002030922040d40c4008100c14496410b161035440040d41090f41c840007d0b17000d85070b07010b441e841003000302e4942c092100b001a49103d248000d10120750b2100c04041035074400c1e80d44549075198a03641a05104080d2035030340702600250000310b580d041904280031a011603260101d1119052400403105c40e0451402c044158403240312010359041c604407101801d0810b40081103047c2e400020114038400e40206a4108900011000c0566035030b0310f041c4032002d802c026604039140d41ca18001c4d000301802403a000c0000504411601d140d030011050742c28007a440c0d2100c08041e100c280e40c0034400e070b04029844003403010003a80071012440d14401da40303981400d0000180d5550601302482d191900329005c00980d41e144100b0010b1000800e1a4841281d001450205502c0c1c4a85031200d260018106440d8201007500200700034040c0014284c000c4400555035024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655062221 1250 655060971 655060993
    0x303110607020c0d080409050f0403030b0a0b1206040e0f03071209030206030a0903030e070f09140420011b121d150309100903090608060402040e0f070c0c06020a0302 73
    0x61110001c03110140903802c5641c6041c1c003410004010a0410b01c12003185283c1a1a03099600449400ba1508040d0880e82c90401040542605c51410080d8040341c84000341841c15000102c28810391103072001460381000803523415201c07500304541100031101503e5050469811a5030f40b50000042078039604101034102000c0b41c040c4021005580c0c015221a00e996a04c86290020300040f240807410907645808013010501c0c20711005015091003075900a29500d406d60039010386450402c0d0030182c03c50394040c00006080c0b00c03404411b00b401006200404490b00e001640d440380041100b800442c10100614100000d280050041c1da210351500400c070320b00e4812072522201d00c401c400b60820303442d41000e2042c00d040300245078000200310445210301d8080440d41c05881c44006c04402158803103200740249a000040179900c15800d072801c5042031714120141300303414400b800e0041600c41b140302240d8004c2c402c0c1c0807514481c3d007054410030120ba41d510001c0d51103003441400e400600403140506 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655063471 1250 655062221 655062223
    0x12060f0a060302100c0c0f06050408010f020c0c2e03020702090a0902030c040f1b180b0313150914031e1306180801050403080f060d0302121b0a0c030311 67
    0xc002e49030003038144e0f9120308251400b91034a100c5107038282c803821164100014503400c0c05d2191009001203a0302c0540b1285860045801c2d00c0c100d90010094034018010b211300140f00040c0300d0f255580c122445000001811040e40c00045180188882c00d01e100d1103c040d01d40d0149c00402c41d1074407e480303c001565601c0031407021101250340007949034004100352803141c03a054000c90110484420000780c41250181d88802c9078054840c1000890711102001d5044c40b000c0c826080202500101e040c51880c005101c2c02c03a401c010070380201102c00e100c41d0449a00c0c403944c840c02ca8550f0044040d0f06c4000000c46c0e040d80c030b4000c070310318050301c0391007120080340d000310f401c1030703403609020b43d000756112034181841628401c45c0c00f5800c2c0c0c103a02610a0006414100340a8140140e00a8940f9200f03030401001000003603a00800300e501401d100000a0006580025a03132043d01c4500c044d242c45051001e4000c1034080381d4100000184200b4607420240203401c10900300316403007616001507800c0141c00503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655064721 1250 655063471 655063481
    0x190201110f060408090a05090a270804060c08040b1305040b03240a2307021c0804030e01020327090a0b0a030f020f040f0914280206070212060f0a 64
    0x8860782c1c0081011600183c40c1c0c20262041e034100420540b080f03030b19900810b4094104850340113195403558101ca09002d10012103004071024220f203081903040c1c903111701003207110394490041048415500c0c8401e0081020945028003048103442e5610741c200122200710300140d01401e4071440ca414180f04251a00080f407000c4225412104000c4082c42000c1240c4400c0c001d00b0788900680311001030400720345030084030084c2d40c580191114942031144000b45852908490340000c00300034081c014545412203d8142d0180e414074000040c1c1d224580102d0035801240b107400408140f0300f90304a4043c0c40c400050180c488241c0310543d8503507035101c511041e0346080b0680d070b070484080c0300b0500c0410321038032404004900241001207245081c5001c607045402101301181150350b1084100c0070803030903403542c00943c94800c00401c281841e0f0503410000742004803600c48280c0101030907074211744480041d1214a50000d1410114459070103070140c40c2c0104555070070041c01400009034850450b0710075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655065971 1250 655064721 655064743
    0x60e1201061802072604091802060f0a090816090e0111070206030a0618060e06030f07060c0c18020c0d020307080d090809030d02012007020f06070c0819020111 70
    0xd904001850100242c02948451010303036903038100e62028400c500b040101800b80c0056202c42da81e031a45801000011941042c04089415103c50500409aa00c1a0070303200c00000c18590f0583d00e40c100d000660700c401c4240d000000c07501581624a5061250001c0082195031947c41800faa103101c800143c229a030b0f00003403a0002c94144400c00150038520b020710351017031903207000180700d0751154104800c803501000d05200e016180c41040c031143c00045440c60b0050340070b80c01440350360600406982c9a80c1c0e80e005610810100700341d41d805010041803c40e0092465540005641070f0180a09010b5070041003120700a2051003010010684000f00b01c0f030400e074102e0309090a200300c4041071809080e408401f0ba80c4880c06000407140d5a9007070001261850b1180c0000801400c1c6810854603c0c03641610806041c80c24003040c2c002d80ca0340701e096071410b0011a1120350f2426680340c030354420f0803503801c184c0882c0b1418001a0900b071968a0543d82907000340c0350045454218190700b5501e02c1200c00f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655067221 1250 655065971 655065989
    0x503060a08010e120a2c102c0f0d060902030c01020d02060f07030e100e100603050c10031806140a05160f05043803070c08030a0b0901060e120106 64
    0x402c912000d003412002e44601c070081d1038480010603c540f07851101424168032090704403102c0105091611f0003460050507000346003883c00c0304100c2a00f504056a030240c0f042c003945010300e1043c59003580c585190003089d42000303180d2074176402c031410711100070251102c0803806486055014031440d0300019464088103519401041e495a40300c0d485000c4900c064160024562a400c100e1101c9038140b00c207081c0340380c0d000400a0581075101174a0700d085810741c84150010324041d000d1020580114020503190310a17200c0701103030f40d07204400b01e0041c15840c1d5950030030001000c9100c1040b20b40c0d0002125608420004070f125140c00c07604501700d910986130000c62405188594041c0d034040c03a007041403150607050450034542d48103e40f054408126074146d48a180d42540c03100c20307041d40800105030380751801c5118158a41140090451501d19801600004010000650340051074118002e2100f0103040401c20f541e607050b014000042c030380703421845042000184032802c00144500c07402c8908030b003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655068471 1250 655067221 655067233
    0x51308070b0304080a021207050a0507060e1806061b10110a050a080603150711161406030a0f150815160f0512010f0f08160b030a0213060503060a08010e 67
    0x55295000d85d400f140d034110541c007502c1900c10022091401600055000383e000d001e0030030240c80c2c49d50411485800030002c0c07028540c1069950b0f02ea41e0362280740062280007010103500c0da80c0009030a8028524002804030341480b00000c00c04000c24005500000c106091141031100604860b46020f1310720006c00150302402488842d42c410070711913401c03082c050280e030203203c2c070420245d0307001d102200c0c041d021500940701206000010044d458025001e5081e205900341080d00c42c10000c2e81c2c41207000d100303c4001c408101c14a186610112020803080c41c2040103080c00d0704010f810030594481c99009010746c0250000b540e036a45407091090f98040e0591550640c1450b0586034141003407088000c21400344035a00403003400d680624040d141032007503003030a079281142a031102c10854104070340796005070800f6448102c0c405982801d80b0011001c036600ea03654900740340c00034051080a64148040c40000082254010000714000c04040c0c80c00c1d807600d0380701d960840c01c0c2c880c280b2a01980794414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655069721 1250 655068471 655068473
    0x9080d0e0a29071a240f0d06110f07030f0909051b03090a0803011e060512071b0b0a0501060e19030206180901080304081b22020408010c051308070b0304 67
    0x100000c2458502c1031501014041551140074200101190405400c0d0b4841d10803e0340f8140c10003000700204806c8030032080303150180d000b0039200408200001c110300c0d01e40000150520312441504c0c05054101e01c0661240c01a00b002170000044501480100300014400700f40c0125600401c0c1c031503c00b5540283c0429109812090140c4c002030003180c0740d0068280d0000000c1064000711300801243c040b126000c03240d200e58801c0310610794041414041d04002c0310840000300e00255900003080e042104280c07410240780283c04080e44001401d00300e150040140b034603038907440141070740c425035241284007a0b007809000164078815540b1000001d000c10030001403400d90010860079402ea0403520713441054030041440c6600c280c0040405400100b414810070301c08000e00d45c03400d8015841c0e041c1c0d01405d01c0c089070303015254141d000002505d070b800d00c514411a680440d002000c07040020003005001c0c4c800201180c10596541c16814940100010070800c009007000c15200710f2400781c0c1c95500c41d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655070971 1250 655069721 655069799
    0x3020f0d0201140409050402040506010c0b01030f030507021503150301020f181804030815370b1b0f0d14030a110a030b03370309080d0e0a 61
    0x500c000490401c000560740c3c04108a214000e04000d200e40c0201144a00b001e10401c01075807001445141005035925a540c041381c500e50090b81100e420800b41032301ca10701c4c0d05040328103100301e801c040d400902038020610310b4641140218460300b00c0c8442c0c0070f200c01244041609078445c004440990883c284000702d00d42c240c811254203041e0740145403124054503520384640d91001150103402050740c0c2c84c02c02041080310600c1050161045803290140c06800495000080d0042c070385403118504c12814503005400c86083c1e402030000701c0201c0742c0b02c06800100010000000c01d45040e2402000301d0840362240c0024028000a81921240d490706a621401c8541d41c1004104084854035029a0014012148020480420966030200d6003030172201c01d142c0b602c022500300d03a941c014100d810f1291304019240150701d55007440b40c607004441c000d04040b00c600741c0ca0f401441c0e680c090082c1269240b81c100603100300c0e02d40c080e0340d040d06041c2e40340d1a602030403000d12005a241701c0c05107070b07079190804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655072221 1250 655070971 655070989
    0xc091501050702100201051905010f030602030910060f1505190c02031507020c011d010c06050703091a0f0c0a050a140415080a05011710020d0b1002030a03060f03020f 73
    0x40c5001c50818441d90001104448140310b0440943d560700144040900ca0032100b560300079403940244551751401d0f0351911400440d01c405410140d0100211b078a0020900c810800c405c0001c0c01401810307100c0140c8510019140b050310b013140c60043d00301c04024096030a40b07910180c80b40e0841d0030085201001c4d600e800d241c4404130780c035000740000400110448111940680016402000a483c00314000740912134400c4041741d28216044014040da82c1c00f015000029030310840106990720741c0a816006400300c502c0090000c2449500c0140180c450500b10303118520004441c541d40e100c0c803400200f0b52103850b0004002034410080c400b09036000d4003e036402c0c0107250039245e00d00f950318540442d11490b000941c0001070040001d00070718050901070701c1d0141c406040c1034224091801900c0d41c2e601c1040da80450f06a070082960220350f100f42d070015880c0000500896410500a00c000391241e0041c41e80e000030074541040410792281c80703022542580d902418441300441010104000780b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655073471 1250 655072221 655072261
    0x101103040f02030a140102090102060a09241107060f050601080105010c08070f080301080a02030f01020a05041712040e18060f0c07170412020109081b0d1a0c1b0c09 72
    0x2100303144c2c8180016043e030780b100e009950000300050700c0c0c2c25404002400c0c00e6000c0c0c0035240d05804c0002040110704051000c515543c01c94070002070802d202c090310405442d51001d01b40c1e00130740c04949170041c05100e41108800100e03200080103565161401590304074000c0c0280c5000407510f01c10b20001542100050803824054009104419103941d1070314010350090300322548030b130003483c1c8030402c60904001000f800b141000081d0300300400d100004102e801903102d00135036098011002c0001900c03d00084056140810b484d55039030f611380076011480360040c0c0b45548140e00b01c1e0f852088030000032070400e000d80c92400c240b4440e602c0301d041026494100d890291000d0368948008144582104000c00050900f0540400100c00074000074000c4666a07200480a4000304141c0c1c1d1401d140d034085102c0c10070100c80c44a95026241421010302510701e1810020001c05c80a00000c060110080d000018001043c800c2d00ca00408246898801d40381049402883c03a6000c6004980d804540c00c01c0710f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655074721 1250 655073471 655073473
    0x80703020d0609080301031419080910030b040f14101212122a02150721050f10080d0e10021f090b071b0204020f0d021b101103040f0203 60
    0x43d0039540703072001075030302c2a842124004003000d01d0034000c52062040d03003402c200d101c0d001d011041aa442d1400c0c14815001e030203200380d4100c41005c01c1140a40c2c000c00d0b9018000e0420042d03890b24002410040c80d44220802c20030014100088083c0070540442043c2c070008100002c480780607945155658410086030303030138032016641d448003641d018410621110207103603160702c060b040c0402224182507003008401c00c6400c51105a480c2d40c03400103c55130000035910b04150001c04c1c1602484c1c14450b000148241382e81000c00f88070002e00303105c04590040b892501c0e12680e41b940c801c20030f541d50a0055003400840c181030950000c904e002080110071031058019101a100c4c03c0140038444601d91060f60906a1340b071059100b40004a6901c0d98010703010309103044031207141000025003c2d40c28074000e01c22a0002450081002404143c0703003400c1030200c0a42d00c42500c5d000b44081080d00040030700c07035403140c2042e8410b10100c2d4000c0a8032546050620b500e192100d03214254412403d810990301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655075971 1250 655074721 655074731
    0x1b0c1906230c030a0305071209051b0a03120e040c03050f1b0f04080a06050109050105091618030302010c0807020c0a1701060503030a120c02210307030f290a080703020d06 75
    0xc40010b00c02080b0744001e0b980c0001b29031501c12000b51160717001c6800080e41a241510800c0090400241a01043e0103e41d481c00032489410004600d8401500010020b0403841615809207030000241c05040d40c0031031f4180102120300f40101c08481c03007160f81105050810f0040b40d014010115a440740d600003c2038145099a4427440202941c0039501541c1694481d10840c820300c000f5100e940e0160070380d9001484517501d4440043c0c0f802c01e02070102c086908510408100e128022450410194016034001c01f5081e035905010340201328a0700020046160840094401071000c01c031501030800081c05540743e40c0c180503c440c00748560444052941d1f5851710085070940d0700300080d00003400e1540d02c800210800b05c1c1400161202d01042070300b99800320780e43c1e0700101e0795212201e0401c1e4059032415101d649030641103002e4620303903240340e420710710300146142c002825a081d5180c2402c0d022060400d5090301c014071011080501c01c2d1041500003042c00c1c00107107000451000340c2e41c010103010030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655077221 1250 655075971 655075987
    0x709050411070c210b1f0b0a020f0f030301120c2d120503030a05131203050702070803250521040f1401021c051b0c190623 54
    0x41100e01403003400007034000c0030820701d0030040711000c030034003070444443d11307540c2500c550400000410b984480100006039131310000310700400c2924a0000d1101c41c1a050904c40d41d20b07880e09150340d000c0c011030740041c0107c0c843c5c3e0808800005a8201448584000303600d180c0ca0a00140c64242c0c03041812940d004030050700203002698407444d0000212892604c0030072480c00144451050346070b50240d0303086142001c0e8080030502c04001c1e02c0c2e21003076100340070a4941d29200c0d0b020341d000c000300004250284041c440f403600e9130300d0740c0603500c540c10b140c00311261140c40700e0b031007a40c82c0144549a001418a00c3c2c940d00f0070f0403405609ca040500c110122107103615440c400103603070002141e1045403039074080390401818241800c0e00c0000c2000c1c0800a007040c0c0c060340000c0d100d4815400701c1c030240c03004c1e00d41d03400180e10800450300b912043e41507140c014440005502d880300d1440c21014404c0d24004c0702d080e13980c90580d4441c01114120b440e00e8620080e50101d540410640c0341c8641000c0c041842404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655078471 1250 655077221 655077229
    0x91510030e01140114030a030c080306210d020609070e16020c0a09020d0c090b0304060b0310110403021e060d1104090e06040b0c0f07020919150e0603160e070905 71
    0x14812403680c080003c940d0b040030311090003408080321051090344038840e88008030382c02c00106520300e40c0010420307949580f864041802c10108011802c0907107450700905540182c08120401100580e500303407016620b4890005589130414040d0200101840707000c600c0340b1000e41d005202e100e500d40196523044800000150015089910076039141c0e40000c0c0030581c000c5640b241d40c001c2200e5003003511005040c08021400c1d404003c1c00180b50590361081c2d140303035030307010440140c01f0150310301e0600426207410041c842c00e80007031100f203025035207881c4448a400c1c409600e04800300c902170410790600d1111445140602951036940c84089020400030400d4429801b600c00b6106d20400144080c1c00d05e86010628004021700d00c01c1031010901c000150404030804503582c2c15012070310509591200d62298566084841c10200007504e05a403032400c40e00200b5400e0101d406a402d1042c01c0d5640c0c40506488034108180e0300322285c5968800c0c869404204160b54020700c0601c0d040030031030b031110046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655079721 1250 655078471 655078481
    0x50118021b0a0c15030204150f020c0a0b070606050a0b0703081b070f1208160e04020d0e070503070603180b130b0a0506030c04020f0a230301060518091510030e01 71
    0xc1c0d584021000f41031100802e80801c050340c0c840d4502d0214603203890007141c6a10889200801020022036482c5050030b50302c04c022884c1c1e0b86c04020701300001e590390344110404603400030204a4030503041007c005182d20b04002c01e60210781c080445e291a025580c1c1d012250042c0007071000260044440201c1030014401005d82241d43c07180403823440801d020f040c5420403440b19a20781d010490f89204020510121011000e6000d41754100070756400761150000c0c029016048420545919099500d04100c900050303002c215075055003602e4007d62100c00c00c809031010a800756104400343d600d1034001603110000c0a600450258546145880711b5076920031a103425108402d40075110414849a45014031900c8501c00040780c0c118503041200300c000e10036025200365001800b180030054142c4040d02c115141c07402c84010300c040c0c1d40303686420002e496030300680240340510291204040c40d900781000c0b064010680d0a0110680d00c56203070420212814000c201c0f41095282d00b507400807001d0034060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655080971 1250 655079721 655079723
    0x1b0b0a020c010801050f0307360603061b050403021507060f0b041107030c08031f09020d11070506060d0303180f0218190c020106050d051f050118021b0a 67
    0x41e10500140c4000100121030603080144074043c00080004c0b00d580c00a840e00c01c0324500100181c0c48030010030500d44200c040605880c0300040e9100c92107840c49141d111074141c9110b030a0400c1700d054051983c640c107908410107080420b02c104070a20152510802036218903041c001220318115440d510b20050b0f40c03d01c810f1038550343e02c441020303101b840c0c10300905040d030002c01805400c04074944c034001c00d480e0050501800c0488000040307032905001002d0b00303d0308a80c1e001d00e101d445543c1e0071050001e5020700400d4800ea80b80420f1444400703940b200700c03803403140c0020082459858050400c544040008400c0f014169180b001d20824684004070f0410710340984411038141c0128014021200d202003025070205024001300151000c1440760541c00345688071000500c2400d250050780100801d4114591211701d00c1800010402c0020b965450000002c00b00f0141400079041030701034903400c0c01103079111081524042d03402d031586d50207880440d0400c0d40c5e1810900d064040e560615040c020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655082221 1250 655080971 655080973
    0x2c04061a210d0f14030612060403020319020c010c03110a02130204061e0f080415140106120903120c09030c03030e12061308090402071211010e0102070b01031b0b0a02 73
    0x1041109581400040d0090200341008407410500003001040803100600404c241c110210101e503090703ca1014400e8607000ca001120b03901d0034a42806540c90f040149000c4e0440720089054190780c2c0f020540204055060319141801c241c03640e02643d4503104000c01071080c2c460180382c0c0300540c1d11210b120181c0c3d881e100005a469041500c014030b90002c0c1d403803280c00c0403680207101030490b501c03411030030418a5a240220107a01e4928182d204412040c0342028042d00b08003803140c060818901c414100c83d4540c0703a40c00300f441150100410341307080f000041c010411b00390340c0d940968099040900d11400d50725020036107a80f80c1c5c1e0780b41c055514a400070f40000d8030709a1170722795504046101c0012441c080d402021946002400007250500c845030007000c9000100e0314a007580c40702e4055030b0030142c5c404800c04403204046001045850681c03510200f0350700740540d0312400c242c1842202d031100e41101181001c0d03802d54070b0710001c0185c110100450508025400038a03894001c0191002c040c1581c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655083471 1250 655082221 655082269
    0x3030f0c091e0a0f0b191709070905060d0b070e011224061b0f060908070302014a2802150307050d1104080708072c04061a 54
    0xe400d01c400c0c200301d600316241c1c000300352405005c181d59040a946e0031610051407404040e44040c0203d03441172240200342c9942081c0401e20012240118039181030302c151400070855661400e04010045041c07580c050585007420703000c9850340b03104211085044806040040e04800c9910070072048038200f051071100b0340c03806801e076034030191203050300002000c1a1504400c10100c41059101030300780c2040040c21a81000600340421140da044500380300c1d0460b070861b454141500300a0702820340d902034000c1c14a140d079141007405640740840803002415040e0880e1010b9000c84001702c11011841030718840c4110107000c3c4a6694200032008803030441c00c41c2e01c01d410414418001c0100c1c0c1203812440b401c00602c01c10560f59801000c1e9584031010903000302e0810340d841441c118502c603d8200440d14010300101041084001031108110f44940000e01600c95078039401036904140c240150070410724200114011403a160460070f40502c0e01c2e0b500501081d01400052604140c26080c0d5200038140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655084721 1250 655083471 655083529
    0x70b042a030c080d140d0f0906060b03040b0703050c22030501110c06060d030f050306130f020a1b11010f090e0708150a0b0418060918050708010b010203030f0c09 71
    0x140486405680507060111411036031000d45105030040c007186c103420700e070303560083e030300c125a19000002042d800150410801d5100e602e0038800798002c031020f5401000c10030214802510910a003031107041100d100c1d50808030388058903801c55000d000f0f030b40c0310410340c40004800f203042132180c80d0499484204440e52040503050690402d9401068035104c0c507010051000480d8020f031a024401002d807404030380d00c0e610440080d800c17101c40c007080401a46001c9101c403000000d58003d180500580e00c420340401c503c000c962000d100c0c5850003c10340c40032b410360300f405540107a45455201c089414440300f142c0d2110510003840c9402c0b01e00c040054503060510808100da02180c00c843c1030180c603c150060304000c21f120311072207544256500340b83d141e4507030b900d40300f081d501031070140034106130602c0000b0340390340450b0302107140080a841c0740c06a24000903123110140704811071404107030003950131a81c40c112105d04a80e402040a2a00c8608200441c51540e6204c0e0002031541d01049406010101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655085971 1250 655084721 655084723
    0x70f0b070f3e011d030f1e070b0309070909080c0a0c05010f020d08011404090606030b0105010810140603060402071e1b0b0d15080d080615070b042a030c08 68
    0x881e24150442c00007000340900590340110000f0700c80d02c21141500182c501d0a020034501241070040070f0702ca0150341c8a6100c14442d0140041c45a00c0c2202140c1003a5150b07000c2d42894032003a1106900c2da406208100b00b1800c2e660006003c8500825230b90341400c03000d14800d410000301d080210303410002c000052019680007a418191541e41d88001c0c41260084240541154010b004801c82880e9410410126035115007040480584c0300740c045c400540d4a06e40076040c1c0c08280592404900400d000900d0751058071600310880349113a011080a50b2108180800c65102400040e00603800b049003001141441c2400300145a203887c074072040c14054140381e5191007540b01481d010036000081005190301c030900383e4007610b0045400242d000141d0582d855182000c0d480350300c4070300540107428032042e0400c2c071311840348406031001042040900d03600b0101303218038130340202400d40c0e0300c002c9008a14410009251041500d20800c28580c0714101c448941d1810b600c1120421804801130204400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655087221 1250 655085971 655086053
    0xa12032001020c07123201020a11010507030e1c05120f0703110a0f05090303210108100501120303050a0b12010f0e010603020f0112021306051209070f0b070f 69
    0x40026466040c0341c0c3d95444040340d0301c414200628074015051b1300d1980e017005241d000090380049008641e903041e03840026100601c1b1030a0031149500c0c040000b540316000740200c00111182801402c00ca03d186982c5040342000208403030104082804803092608000b400e0b40c0c0a03841a003860405807038480001400d80d2000040ea50410303005200e909410354001c1d1041103014264242552030b500a480400d2850042840d1400801141003c1d4042d5011a05030281070703949060a513072980d0000010341713040d9807080c820703030000450560303038800424800e610071500001c01c01d4002c01d0051056000600e01e81140c82c104005035501c280c203810541300c0b07124580c3d05030304000c001c0c440140307540c00146a4000c00090641800210f4001c0c2e0506c0351164110741200724200c0400315550b4a401006200e504980c080b200c844003540040b50502c2c6000408004607140d484401019904250850700c49030804031017255400a40000c0074001010310070140d0680c1c10948000038101d148510746000e9032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655088471 1250 655087221 655087229
    0x606150712300c0e10030207050307060501150f03090812090a0b0435040909050708060709030c090212010b09040f1109100c210c140115060203090a12032001020c07 72
    0xf000901c4103921988800c9103d45d110400c42c00c2c016113440e0340c0d00b4002e0a611400800074a124038210010446101080c000c15806074603940c2c2044604603620305a080303d8800780c0c003814055080c40100110340070622410361160f140c0d000c0d00c070050400d545200581c54250740449165211000442128604802c80481c0003510103c068000a41000c410b80b0f074805c0380102506280c0b120304503000c0c80b00401c41c98000344140780440f05945041c0c08002c050f00c50354081203407810010340c5c0c0000c1d9404140240d4240303004810440120740d180814001d900d90203241300582007074503428030110401d1140300c0c101800c4001d2082590f102da460302007041000c0701e000c00380c0500c04920b0141d0003066003480c0400381d0503025070004480303803504803040d14649481e00e00104800c01c4140300103200c202c10340086043d1002d141d80f0901c1c07a45c80d440260f840e0301414031a1900140030003070401440960140e0425210b0003420000f9000c4310210030200c242ea0844901c0c0d038a40c0d00025220412441005407134001c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655089721 1250 655088471 655088477
    0x51c051008062a090108011a04030803010807050f04090b061210060e0117010204030309030f02130f02070b060a0602100504080d05010305160905130204020c0c040c0e01020606150712300c 82
    0x20400d00001b03040340c20180149040d81d2925510300307104440d42c00854010310340003898a9100c0da5520801517071440c00e80140340c0102501d8055041e11305150080341c01803640494960025903441d42400344501c4482e41c0b0380d0051040c6402400660440c2c807540300940300c1801d00350b10070341c14008a91f07211622640c3c101c03685e038410801000400e41c0141c941c010340398494901c841c0405d0b1800041c14806204040410b0540b40902480c0d07400e1030f42d03000700003151240030301c5c00859580d0b60420a0038101c502ca01405a003002c0030381003031404a40d100c154007501c43d22046003003c00c0042100122482604112a03a6001c9e10308200c2c8a900000d00301d006000000c401d11070344c98503012400c0410140c42c4002d0081c0e801144286020806000007007060801078420007030124132090080240c00b00e1901280035003c0e070b0000c2203242c101000d005000099110281c5d141065903a1507140c0303a00c104d0010f0040007024202001c81c240501c0c080c2258004464600190480e00220202240c3d00150300301c3c14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655090971 1250 655089721 655089727
    0x2070503070303080f0c0904050115030f060602061f080706020618060606181c061a0901050d030c1406090d1b030e120106030602070c06030606051c051008062a 70
    0x3984130001640c4182509580c5103180c4503a2103c1c21180103002480b5403213820200045400c0801d40181c0d142c0c20703c5ca075400d101c104008074400c0704440306070181d40c0041e0042400100c00c0c41e40403030007902c10302c200c0c1100074100b44c1d140c8682e030501c07240d81c000000581003c01031100c0036406070440000610703543c0c06003103141040030014010b40b0139042000105000002444940e6540c039010405516005248170505181440c1a0009040e03141c400a42401c91450086603414165a51816104003500f024607595054500360b4100a074080d0450303401280747d03046002c59505022941c007800740400101140c0040f401c028040303540c004200e0540d400c400100d00c000c00c0d0b02201c0f011903c4411f035a4807885a5100304442c0c0074140b00e81020385410700000d280010845145100e03070407a44540d0703080081d02d441d28000c407010311801a00c800181080020358071b10b5501940201d8002151100d03050391203503200d00c01c03400c0c614100c0b040c01d5a40b0340500c08105110a81d400e91410701500740f02c60f49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655092221 1250 655090971 655090973
    0xa020c0a060f08040c080f01050429060d110604150e0114031b0d0e070e0f0c0301170c100518100c0303051f08030c01140c12070e10020d020705030703 66
    0x40c0c090b140d04200c10041c0d6030002c5030600411044240140c0380d60b5050702d00c950340f00220036001e40f01c01d0705c00300c56940d40101000035140c1c0c02205a5a410103c2044a00c00d40701d6400300101c060051200341c62410707640b1108104c40d80d6110080009205980000006985240d409402c032000f107240c0313a040c0310301e8240701c003404008842100d503c42ca1a9001c4010384e416152040d5040c02500b0650981038030700312004180d90400101142101c190f401180b42c00d035991010306001e0441550040400b036401c1c001400545440007946465400c0c1c2812210000a01400030340a441142c070b41c8404906c0010716029150324071114041c071100240c49808000c0038444004180d1101800c1c05410182e5460114500d80c0314000301059902c02503814202054603080700b01d0b101c0d44a101d498003203600e81810724003440c0d030b0900070510645040142034208200c44504141180c0014822020040300d02d0942040c1e6444180c11440015a45d00400c3c0c0000e0a0354044e01c2c254a0740c0200d4480c0d4001c05c1c00300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655093471 1250 655092221 655092227
    0xc0114041a0f010312020f0f0c04050a02160f0807291501050d02070201110304060302041e050102070308090609090a0605030c090609060d14100b013b060c070306020a020c0a06 77
    0x1c3c1c1129800b003806101108480c4040f41031411219554046004482c42c0004485001924218040701100c040003540c844907841812442181d20f03100005040807050408107070350b00c1c4007040c1d0038061720141d841d00416580300c405184e01d04c00070729909444003c1c01e041a00c6403550312944031080400c6e00740c18248a0300040c10500423062440c9010782c00003105400c5920070b000e8403409540342400c81e92180e03129800980179410901900a002c51070b03148142c46462040d0400302150343c1030b005405030604589039604d0a030b0100f481c0c0c40d0440420004800c01d42c451007111803254240450024401d410042090300f01445141b900344940c8418082c0715642d42e84148868001e1400c50390300d0380c43c90741890800b19031038948020a5160003000c04400c2c121a154105039010f82d4260385004981c0140c04401c10980c0807205000c405c1f107043c004020101d41214007103051000010700f60b60030903200407082850003030240c00071240d181d000301d5031f0006650100800603400a0850342d42c0d61030f1342005402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655094721 1250 655093471 655093501
    0x30c030f0c02151305030409090212070b0403060507050f0703031a030c011b03030b09090d081003050a0303050c1608070210080105100507060b0913030818150901020c0114041a 77
    0x101e0b80c52000f4000300d010114918000340c000c903400b005581d100d564501e03541000b4010f40d1811380c007840c5003141201c0b80400114811003520400107189003480d065807540340007003400500710000d1204c108600304000514001501c41d1900ca03641c00301c0e2012044400700c0f6880009400302c0c0c02a4800f041e4070311940e800480c010000465200301d40c2c0c1c020f02c5418102c0103003c0c000304907a000101f070070512000c004086207606204e86603460301e0305039480751554080402d41502c00a44141c108800d03904c0042d03c41e401442d00720395103800a41c10040485800004041d0070f51044941c3d4000207203002c210708001440c106800700900348a00e15615010100b0310080c01c0c040c5000030040700140100401c4032940c002008140041c10904a0703181c146186000240e0b601000d6000c2001c1f0380002e040a8110900c100400c0508409402003140b141d003d074414a6000c1d280b5a4155001d10113000c0c600024820698815021101409181000c0c10b00c241407043c200714141e215039000d000c00c0380410a0900c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655095971 1250 655094721 655094743
    0x13020105130b160512041406131a0c011103100303120212010e01030b090a052104080a030315060e03060103020132250f0b06010c12030c030f0c02 64
    0x1079a140d00107400030140c2100c6400065000e00046009103515800c051800030040c40f41044a44e00045c07004400342e01d0242d84075400b900c1078180308000150908201510b85010100751003056103803680303003102c40d0312030486d03d200c03c0d940c000c15416900402405a50907403c0080d04451440c144032450000000c0140400307414006e900300030b02c9204400d036040ba00515001c07000d0080039616032550300b024500a02c800d540c013400c4c00c4041a514800820946a400d41c4140208191000200c03064005450415170142d034080c00c4c4000a4118020301c0503000d41d030312035900090741c1421207001d420701c24015017000742003084070781c0a00c2660300c00050950540c2d809003012509031809049900e40003806902000100e401d045100c45c15215481c094244c1140c0300d148100c02042e00214500d0030340b000c54000d040840803030320980200f55a030900580081042c5041c11030702d80161104285010703403041160010340d03158140c0188660501c50329650b074201a00030700008404d500f00030b40e5028a000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655097221 1250 655095971 655095977
    0x2031611071203140d02191803060b010c061104030501051f180204120506010306061403060a02030a1103040308040b010e090d0327050106050906030705010f050c0102070209090c0a0905130201 84
    0x100b02800d02d4040c1243c1e00c003000c21038040c10303a290301c00c0c42c50030041d400c40b040c40c246c28a4a0310117170301300754002c0c03802010141c40359100c90659480c6403110300c040c064481405050203c4410b5500100e8090b01800600102d000d0080c0c0d81c0d103181d45016400c40c0c80081c10340c003001201801d0b4000100186260404a03442e0611a800400d0380e15004402032046600a03108690f10030f00325000c004000c03402904172401a80104210755560501c44074401840200c00c5d41a0020b0001907110b40e00c0394040e6400101e502800a811480398580210a62050380c094000c02c3e0480200400c11003c0300407a0301403d001009901d050808169807a40c441072a4059018582c071806020010034880207510003c000c40880541d90f40300609040b070003442240a01401503000c08001046800c4c0007800c0c4c0121001a942c1d0b0030000c150190484203900300448150342950204200c1c80507076a03501c1c2c054002c1c0c10150203452400710360003c00c000e0018a41c4801205c60404040000880b070b4401d0300c0448640a007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655098471 1250 655097221 655097249
    0x509070e01271203030c0f0201050c0909090109080c1515060304060b011206260708030412031101110909060f1c0f140d0f05090a051c060f0203161107 66
    0x81c41c80c2c41c0000d85420403210585000380709410f06a0541014050349603c0d150141d1034251903030201e0a03500d048500018601c4104038940c0d5074108011140d903c811061f00020f011070b0340b982d40c206a94000d0400c40340c02e901a4060b0107064441d1090980c1011a42c280003424181078004035000303000c000c2c4098151640c030b030016142c5034040e00c0c2c0480c2e84920554104011512080c03092280b4421f11945000b44601180801c504800054040103990090700194241490700c880c2428003161040308600f000003880c01600c1c10701c024041c50040c0741c4010391701c94480900d0400d2100e500d400800036485808554202c0031940c98900c0b034804c0400b054407621704981100d041001c3c14210b0050000c1c11000c0b240c0c203901d0902e001240c800d0490440d07603184011000304400860300303402400f6100381e01041c010000c200074075000c15100e40b038180310524266002d00700d449001c100c852501d26408002e40000030041d0060742d00c0c61541400d002810b1491800004800035942c0718114041c68400c51050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655099721 1250 655098471 655098527
    0x504030201080937021009170c062508040e0106030b091003140c0a0f05010206100f060302030a060914040b24060309032203230a030c080d02070308010509070e01 71
    0x3c1000c05600502010341000028100818841652050302300c2d0b0103415030ba08004001c045040d80052600500450400c201e580311820840040f00e4071001c0c1e00d4240a4540004000402033701c01010700400544d815898418090241e80101c28050303c950181c004100e07180712070340142c00a4942041c505014140d0004c034951903e60381c80c0391194880011000001d003110840d90140540c1d20030781c02c1d10429146e000310500146018090003519010703d40042c0301641c441d5020710f034021440c0001080599030b8040000c100e44264101c0764038805250200800c2c4003001c2001c58000d81c2c030208010384410034240700c00c40e8140c01e070003d6220f501c001021400c07414081040c2c9403c100c6410200b003954034044150304031200207110844010801d9290881c502c0c1c0c00c00e00d14000002d0100103040300f2103d59a08407960f43c0c1c6548200c80c0b2440600900a12170384074400b400645200383c13180070f050350414081012a5034020000000c00004003001043c0c2d9030b02072040e60050351814000c200ea1030b06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 655100971 1250 655099721 655099813
    0x106050a0f180f09020c010f02030906010909080f0f0c071410080a020904020313121b080a020a05030414040e011a011d03101b0201150b07051c05040302010809 70
    0x4158054010700d08a100049a211415070080010041c206c001300100e040d60300500c0282e000c1151860055000100100100665904070846803031041d40d2140ca030003614014150150820904100c06000100350f02642c10010410040030b045103004540003007100d100000d00d5a030260140c0f804210b10640030865803103240d010b482c4203c600070425904e03441c0c036080828a0100b0cc400580b174811044144080341802181402e46d00d4618230040030941c1920384501c1190742c0080b20340000c40c030604401c0380c0811010b2007c1c1000c0c082c2950048500c200041c02c01c020380b281403400c40041d074900003c903803514080320f00b481401482801c00d2080741c0141202c5420203120343d0016601409190703000d00c2010440c0d400b054101040d0b0a0682d0203080640e4128202e80003003428442c283d031842020300c203040303920028140e0b40e48100d080300c04440d0800491003604619001e6840410b40c0480c0506c1150b0704195550791180c0728000030b00342007003a800980c01c0684828031203035401401c15994060004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 655102221 1250 655100971 655101017
    0x6010b0d1d0d020303040c0b0408030a2015090f010501081e07150c0309120c1a040801090807060e1209060a0509040c0e03010605010314040204050901150f0303080106050a0f 76
    0xb0b40d2a080d00d600740203520b0fa4803c440442c0d43c51060040498190b0069003a20151803540006505000480707006444070807102c001007015011100d14000c0040c1c08100000c030704000c0310749412150900c10201480d10002004a104030b904020044c094108001003a800920701c156070010914a08104981804c1154101002c50071030110030740001504420802c100c1842950b43c0656039a40d103108607504c00010b0b20051180d010341e41c08003d40011066a00d010111860010f4601591206082e007141c0b00071408642140001c0340900c107002c0c40d0f00c9108551039562014203290644c4014a1100b40301d8149054480c1c40b0208a070701c0c081d03100d1300655200b032070f003d4000c000c007810101015002c9407a1240c0e81c1c0c881e42c00c01c08046115482805149c5620b141aa81c0e05181d0729680d08010150600500c0c8051566a40082e0700030316480034114070050901e100e2482e282401c50030000d006003c160081e1060190030401c02400c590711110150601403039192040c5203845201d003c0b11000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 655103471 1250 655102221 655102271
    0x90f01140c0601052706041d0f0f010b1f050a140f09240906031e130b061801051e0a08150108010b010c12021c0e010e0306010b0d 57
    0x100c0041501d5500300e00c0020040c0c16a0000c170b030640b0034035130700c2c4030b100d0302c20a0000140108055407001042079420306da002080c00c07a038058080c0e101c250340c0301e500d14035000f00303400c24800c55032000d6a000601e0f942880b94200880040d03586003d08205161400c0328035034648804010440c0028415101c076100d800c02e41072045411264542c2d4402110700c1d003144c1d030010388100e48264600e100c401c0d40880f400150382441440ca00d0740390709004800b4100103490b0001492403001420003652507406194a101407881070383c2c0440d00f81854045820003032003400009207030500442440840c4a01085400a010704446c0c01300d0b48070340b204821414000c1c04404501c0004c0d009201d244020641d004003099081d0000c9a061001280f0381c1ea41c0700550034bc81c2420706ca18049005105c1102c085074080c80c66041c800a14011240c2c016034606160b00c0d00403d81e44600c00040c0c0e03031240c42c0950f41e03000c2c00400710020210028031042d418081400d00b01d106480c00007100381d80d141000c07080141c24080031000a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 655104721 1250 655103471 655103507
    0x3070f1103070b011716060c06020702030709060617130609080c06041401150b0a030b06040f0311090106021f0b04060f0f14090403050d020d09080d09050d0212090f01 73
    0x10304064940720030890320170301036025840640980585460b4001410401c2c03101075000904203140341c0301050720038203d50041030710a55000c00094000d43c800b0005100205040c02d0001000c51500310002c1652228046000e140040303d42070103aa40c0702000540200340d00081c00240c0340140d447d00d01194480d0a61000d45802440d0402091010b070010700026140610004c0c080c002060307103540036051550056141e5020705101045000340b107644078541d0003901a100a1400c0e4486040556004c01580b040f9401c241d05910303d015810420304950040c02240010403007000c05c99030042d88200b0b011030a400641d95400c42d6001907903241c110800074005048414040f0740c030b030018034001010318000c902100308074040d910380c0c42c1032a0318081d200d15010754886041c00ca4104000e8083d5000028819000d41c0300c00800000c10307110350082030302c1030340c281c000a0948410303e00982849841d8018034150341200f0a01070301c602d50002180c403003080884440d03030540807001c010303141148000200961 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 655105971 1250 655104721 655104727
    0x8030a0905011b020c010f0912050a170301050a0b071e0c09110c07142215060203090a090b0a0506030604110a0c171e0307091502070513060b03070f1103 67
    0xc12040d44064030b0304414079420784609020810055450b0407002e81610001200006c0810900030300a189c45081071003001644c18258140c1c803942410303280b8050395207100c540040104028601491072500500200c0031890400285859544103000c030107000b0b0500381e144c1c2c0044070030400401c11090250040c2030080020030f001415403800c680059a5407100c3e40305030b00c40441d074803001c00300c0c000c1070060040901c6a80c45056811185801541c070340e80c07031690384611400310302212a500e2100980f01527401075898801c0841001401c0300b0b6580300c9100d081c5444000401c43d04d421b002c081c141c4a080d00d030b02e9965101e13580403030300914070400846209800841c451094561201e04049500d000340180e04135034000c1c42a103401d0f0721941040c4441e080d0f40d00700045020150342c014550015850814040c000c0c1c0d103040446c203280000d44a000140c22605080c4294601641c2410b4802d0012804005181c140036001c03255210140c0b45805210b64100c03210110b5120359080880051150150ba071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 655107221 1250 655105971 655105991
    0xf0509012610090b06031017240a05150f0d0206070c03031121030610020f070602060109150f050909070f080105060f10020a0b060307170d110f0a08030a090501 70
    0x4501c42402100d4180e414a4070107545844c010f07080d21300444815081d044071b545440c000612884004244e400c560081c150309c04405076400c081100301d0300c600101c0c89501e00d481c0d4807140445600401e481e900000c2101020545c2c0c645d01607040000c11f003956550894002400001d10078007400c0c5000348107403580c1c1c40100805601200c1c0c3d0251020040844903105404200c00d10080014078032007034005400d10008043e031904a1815501072400e0060f1482c004046400d5814442141c000b8070142c2e01c00001000151118440c10020003419100442018206100e00015110510a0f0f0384a40603210104514890500c01c00e4028a480c402440405a4502516018010864015204203525188034101e07003045901152a400581e01a00d800b02d1550b0300c021025001400050301031007a0140452220315200681490380b0599000b007041540220000301181c2002c00c44001580004d031804400c2e1000140320701d1401e41c0011400e840f41e0700d0202140090003c204040c2842d802c0c0b50b8410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 655108471 1250 655107221 655107241
    0x70807270602010c21020f040803070f120c02091807260105010504330506070c0f0602190b0a0b040f0b0f0a0b0a0305060d1217070f05090126 62
    0x281210340a0700203201c0303144d030084283c400308142080145401d0085200c0c01c0c1e09015a03008084030003001541609007500c2c2d000952542e002960225102c0221754070742d0042c001c4c101000c50a0303d1080c60f054814464a5000c0361004030b01400d41c10701e480c9441c83d0a19001e90510104018021807048145680c00c40d24a025681080c241c06050f603520b484000710b5503080c00d0184e40d218031240c0030b0145c0c0c0e254044840c20b08401c180d4204140d500c1d200760021410f44e4407203004092003400340ca0424a4141001486c04690400780c0c0103000355402840c160241d000c1045560143c943c10440900782a40c1300c1085001800d00305000355480351811050708180d1806074000b61202d05e040e01c01c15240d050b010103000c0000081c0c010b640034003070240814820548030ba00300590181025124406610b241d699540301c8021112520300420111074101c9401c002850081c0d5102015107800d41c698101040f020701548030340703e0107034104038100e85c01e034195001d088102482218007248061036440c1c00f8641c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 655109721 1250 655108471 655108547
    0x1050a030506040b150d060b0405010e0f01032c0601050301051b030703060f06030f0b0a0501020c2202031509160503040b06180c09030709290a08010c0807140c06070807 74
    0x1014036281f5029020034081c0c000e009503810360744117847c1d03d03a0002c3c2c04030030004a041d0201e4541d04140c1c072500b24071107a020100b9030054000000903120215071041007001e0074590143c1090f8003030380c9420100b0010501c0201c810000100290a06603252140202100500415007080384e600302048000500c560381603004c0f0151892141007004400103050400607040100e10440340141d205004000c03207443c250b000400340340070f00c40100300910004120380c81a81c0046401458214100040006609203d01650317400010b039004550340420712180074019010140020381740414200000e4016190005403000c500d094a800d18014601000d202c0a0355012100450190003030040c001041c100c140115682c1e081c400400c00050900440e08692280e11000065840144002c000903400c40c01e200d03a14240d1002c0c0d6580034039107004030300a00b03c600ca81140b021091010424017400300d4001c1012504070700586451083c5450f40041103441c4040b05c104c404900c400f0021a030384000c1c6104a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 655110971 1250 655109721 655109737
    0x11030726030708040b180c04150504050c0c07060c0f0b0601121805120403020d17070218010303230a11121303170703080a02090625060e01050601050a030506040b15 72
    0x2e040c4103545c03182408010010502c9201b03500394440c811706015481c1903000000b042548409020101e665400061b080d104e081d103407100b0800000070000c501c40000c0c132024000d0b101505104407801d145585400c00d0070031643c406001f150a1801003a542da00c1000c101d04900101030003400503508014501c980042c844500321141d1085500c1403191508030780680d01240c1e0020541e08000000391a04003007410552001001000704204040041c0c0d504590300a01e99000c1c01c25107030940c10b500d4007818119130042070480c40d81d244d1001414042c44181100c070312542074036081c010070b41c0000312305181132502c42d1403558684003c01d003909003001e111070740c03002c5a00410740c0001000c22149042d40c01d00c28084042c00292040001a5420350180c0017003500f0707080584054a001d0b8840074000742001c02840b1201c901200058140074056280501c080c0d950b8417000800c224209400082c0403440380301e203d40141505d41c40002c4055a030303a40500f00c4c2d00d8000c0e180301020b481c1c60309072185503884600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 655112221 1250 655110971 655110983
    0xb030a060602011a190e09100506030c0f01050d1d0c150304020319050f010606030204060305090c0102210c0a050703171e070f0c0f0609061103072603070804 69
    0x40c029105010f4040503030b20514544c00c44e00c02e5001841031401e80c112084403115078400002548021900800e0f2294101c03902804101d40c003030151006842020740024801d500c00706480206a84000c0c0c21100b0f072000342081c0b13540700c2c440101c1d9401340c600c03520188030790031842c0c507940e0052401245060f0600411203420b00f254014016074480744c0400d072000f94140e03101c40300c2003440d40d034204400b683e01070280701194440143d00310210300792001d9400050019030040307420000243c05004498220300b540f400750003480c1001000035614120b8034680980c0c1c52405044411034401c05048801411421040c0e9100c401103040c0300da40e65401e8441185d110191550508405000d10281c9403010030400c402003181804409030541a0401c91040c1d9000782c1d0301104c140001c490345405d000070003003c001501c8051511001030000c19281e030040c01400601450b00144c81d002104a0340526840706221041d01526001d044c40c08030001c158886088002062010840c0c0080b110f5210301e102c0d0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 655113471 1250 655112221 655112231
    0x3011214010e0319091202220903030b040b01020a02010212031306140708280b120102070b01030b06060f190323061c03050702010806010e1c02090f0606030406020d0b0603010b030a 79
    0xc131040314000b0701c0c0c2c418819060b00b014442c80c01032030940b0700580072920b03400c0417206401d02c800c00c2e9400c40b5040482200400c1c0d850003100d000b4202070203000c4c0c40c004240058800c3c20070a80010351211041a0310701540000040001c1c1d01d084980c80408081d03401040400c600740446001050319042900c061010440180010341000404d10000e02840d441601500340480b80f080c0c450060001d9a41c8107500c0340041114a941c80c10910107400354030301404c0f01010a51460600705400c01000d08031a010346420010680500781d03940c11100360040545402c0244841800114001c040641ca0003442d801c500307054081505070f03154a14000c54080303440f07484d65505210101c903145200d52004007c10300a002910256010f004100d60091040c1091041110940300080c00a9400e801e5010b050320082d10941c150f040904c13070281d1200c200840c100e06810014002103150000820041c443c1e900010000c00140950b0480e082c482c0018240503100d5841c1c0c00b03003040710f800c00c1f25a4008030f8546 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 655114721 1250 655113471 655113517
    0x3051c060f0e0604060b030a050a0c0206100320030142030206090f041e0b0f030a0b0a090803190b03071401032a050a090e010b03011214010e03 63
    0x1622a280032a114520071146541c503026464142020060203d54415139503940090074284c44401544103c2008600207a140707810000301c0b04079021244090308540c807100402011420390000d400580f508132649800005280ca880c03502504101126600b5500703004180b0b011110703881c44a242d006945c948150200500c0110360300080303a20322504c040551403070082000d401c0880041081d81c0005e0011082d5400540100341a200300413440010000c0c00c1086211801031489044865101100c1c03a0341c982d01001c000941e00e8402c5000070701501d900300e0204500d246c0652000a500350711000c0140c07249050807a403a034030483c000031510038034140080c1c00c6c1d29150109144060312070840c07280c0500d0307206800440080c10040403a400070302d807840011820380700c0c0c142c41e8000541940d840f0790355501041d4006040c4025a403003104c00c81d010000600c00422540e0540b41903404210f20303450031001c6400c201c400072002c40304904c407951030801c0c07500342c5680100080c010004030300a402100f901c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 655115971 1250 655114721 655114777
    0x203100905060c03191a030d180b040b0909090a0c030f170a08190905030c0c042a0507030c211115130201091805010f090912080a06120305 61
    0x1c41d641700b0b01d9112503103189600081c5500805d144101ea44003041d060106502280c54002c0000c80c10012a031a81445d010b5600300500601c05411055100b50030203150118003401d034001c0c5922980300d0310b00c21001400c94034003002603c400d290060082c00a850362818613030509414035505a0700350515881110808441c40211101e41c4600d03901d2150315a20884c142070301400c4042c02c0d0304400e031102445e13004a001003020700018000c000141620710105810031003125031207151041d002d24800018032495040340c81c0c00407001c040f400c1540e51007902d490100c4581c0c0500000410701d104600c5070000a80050180312611040e640302c2c080c0b4460300c4d08800f5542d0035410001c0081084100c0004c02030b10f02080030600051060421005181d107500007140c092203909152280b450b83ca100411004024082c2c500c0140040c1c0380410a080240e25021800102415484144000c3c2c01c040791101c00240d2010004044800c0d841003c00514a0000c00ca60300009640e4a203040c211821400604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 655117221 1250 655115971 655115977
    0x180a150312030524010e120706050c0f0705090a0209150406050304020906030c0d03120e01141510080f060a05030f010e160501050a080703020f07060204051c021c0f0203100905060c 79
    0x400344e011510001c540300044030841d441030350040c3c025040a29010104804201c400040c1c0f290b0349032039446014000c909890560f06100e01d54640e80000030400460b2191000240c21408448015913619001000305200c1080c04070010a51034000400082c03480d4401d01850046101f1180e808203071300c4031400c05580f65200c003103140d801440020142c000038000c511084090074144130104644a880303042a08440284105000e050050700c100608220402008070a800c0c0485131900000d025031001043e00304014040c2d580070209a003c10301c1070f03482c2c640144c001d0900504480042681071107140c00303045c082c191042c003481221403180301d00e041400408103881040c0d65403800d01040d01ca045a401c44050240c0e01410f608003c000001404c100007131503083d00521015a6371460102441a00c0d00d00401d902007945007120740100580e20092410003203400e078500c0035100240e2f820710140c1e00308040f10003545840340d20840040f62030035401280c4100d005600750b504550b2580c5101c10184 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 655118471 1250 655117221 655117261
    0x2030c011e0302160b100509070f08010e090f07030302070f050d0206160f06110a0908010e0706050c0f030310080c010504150804060e2514180a1503120305 68
    0x1201a840d0329902c2603018100c0120980e1290038070001c41c0d112005000d9082c0c41000040100b25800d10080c00c00c149026041100f07071400000b00914040001c040c410103000b040c681c1108080440c001580411600d50301403038450540740c0c065500d10f80690340b2000e500c550441c00450175400501c5190800f810400c0640203002c8514058805490300100305402c00e0845e0100801240c01001c07604503c5003014003640880301b50358480b404400680002c140b94405051a030400080d01d121075804030b800011078045041140d12401020522814020458541d00e46440b0100800000070140c0b91082d040b41d01e2035007920715866808004603840c0c13240380035140c84405490300070b504213031041020b81c0d07105011300e800040c00708401c09401d04204411183e002d807031101c01c2e0f03608104440c038a005401003002d90001c02c00e0304420804200fa144680341038400030b90100002660305042a000120606400840030303012580380d00e80210007031403440c82e07080001e1a01c00064128500003070618944 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 655119721 1250 655118471 655118507
    0x20c0907110718060803040602150a0207110f040e100218062a070e011202100201061809050709060b07200108040f020d0b090127030504030308070c020310060302030c01 74
    0x4500b42612590390b1505010600ea00035511900021600d17020700203000075201950140c0b9000c07841002c1c100c802d280c00390105c40154410440b09000905601442540c254250b5001e484170108400050003803500203844c0c0300034040c00c1011500040542d000302801741d94204044ca12184004c20f0002d64080d15405c01054400046c3c0b40c034401e0081c07244000340c02118030441d0440c80c0c460015618450007a8018801c0184901c400821441c0c24148142e0b400a1032000700815440c051100008d02801540705e10b810707545800302014071009102a0014182d1841b003801100c0d80e441c180142c0354410201a1303102900102d600700201407034494030707081039016034404120351200c0d1141c5119042c820f078100e0b844900030400c2c600060300c19046511031007544000186c800751400e50641848113454a459442451080b0b60000a8015040c3c50070f4079054644000c0c1d5684100040c4d40030311010a01030740c14070030000f0758110512550410f0040e60b01c01c1e41178403901410b00d001519010240702c2c2502c05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 655120971 1250 655119721 655119733
    0x6031e0c05030c0346050708150a05191719030e130504110312070f0b0709030807050d4a090c070204050601080c040302011b02060307020c090711 64
    0x2140c11102c004d141c002002030304041d00740c2c105002000c00700c801d0b05260900c000180c020101143c400c40080c5c181012070600900403440c0448008000035402040c042000c8040220b261040c0c440481038070107010040d1045100f800c51004503525007441d841880d030201102c20b0524800c80c0c0205910010794401d03c0e22a4258034a81d8040d200032800c2d41859030011842500410904014003910b401039002c0c46110304059180011b05041c0540b000c20702008a6040141c03c00281041c6000c000140d00322100703403103d8440130011a11090507500240403284003164002c144040840c1e10032959419032240e111000c54100380ea4034510340880002011801407000c40400301c507040c1000307015502c0c2c41502c0c0b1200340c0c02d4006000e00e802907d0b880016100803c0e50000c600345441401c1d0810000d007400300480c90a40084102e03441180030090400034649910840d0a5094200c8441c0c40d60060555841e440c02c004001d64030800e21486511541034280803c1f030141c0201c20240f50550303000041c00b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 655122221 1250 655120971 655120981
    0x1407060e090402040207060f061e0e060409050c06030414070509071e030b0d050a02030c061303060b010504150509040b0a361b03050f060d020d030c0b0106031e0c0503 73
    0x60071403002807060ba0810b03001c01161000400794030a040005080100000306103040054010303e4078400d00701495040380c841e0051110501d51420594082421580410361604916009060602c00704800d904110084144801c001c0094504240d507080c1c003044606141d84d8404004869405035003400109a601c1490340b9548a900a10b03000300300681004500b01c1469000316803206560f01094440780c0084101c0c074214a424010081101c0c02103429a00700040c0c00c800040d80300303c0c0d1000401c41079449214200c02d901900075500100000c0300c2c8044819141480589240d000c81440e40c0306030700e8402c0301e551920b04890080c0c26210000000b420044d117040300c15040092a01e5030010351007034183c400c60800094001c3e003200d80010b12400302c800380c4008003e81518005001a24400c00640030080c06440c1d8003c03c291403a011240b040d801740c01400c09641391649004040d0440c8240d500100d452074140e000000350b01400b040152070707514688001f504a800c3c04203224000389040010071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 655123471 1250 655122221 655122229
    0x302090106030e0f24090102090a0b0a030b06030109050f09070e0a0b180702070303090f05031f02090901080304050a090504120c020a0905040b0a0f18080d02040e131407060e 76
    0x4a03802000c0303803c0b61101116280c80381d141141014800000036008085500803805e03a10080d900003900ba8025418039142100007203c4c80740c180141c12030064081098080c151003a00000481c06001e007805a44c0c2d40c6030f00013603001d004101d0b0020b00503055100800e00700c080001c0d144040b0340014611358010780b2074981d203001400448a141754051b2088c2c282d0032941210801c1180158a941c006110082c0340d45005041012164006800c000c001001041a0b44000c5008030801000ca005100c0040c6901c07140300007405000c00d00340d0030140c00800414149030000080003a98000c03200d8420340d41c1e850702d1800540310116001071105040f2140703600d040340a6444288581d20041c07020707030381c5a00e80707403074404844045900751095034811040c01040c601e0f61046c100c0c86410b1410900c1952000402d02e07100c0c403c0913400914075540001c1c00e800a52191307041d03e025204404414500b0b00308180340c5400d40c005400c09442c0701c4481a15031098000018141d4122103940c5c03212040d82d50300c0c40c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 655124721 1250 655123471 655123481
    0xd0318020f0f0315010e040528030f11160608091b06031503120a0e0a080615130920010c020d03140d090f150c09260109030522030209010603 62
    0x50305803084c0190800c04800700c00c07142d030180403403014030f26841c501424041d00d8071050946000000410300040c0001340c440320302da00720340c580600f807182524200700002c0304c500f6000070312560107000341c407854140f5103407003414001241c40f566142200e64643c002c8003516180245041051031071029810b540740d0a02001850b84103601d000521800701c1a20302003801c05543c3c0c0b003904151840080c49000603904001c041da8020b0f41680e0080203541899001a81d51801820101c0c000141c04001a059075071044410f840c42c040e440144505030b22403074980341e5032505200c1802c4408481101c0569940701e00e6041d03840030b400070001d402d8503074552010758482002c0d00b4030a40c0741d1402c01c03030407160b00303810301481c0c00680c811150702030b507040380d42040c3d02401441041c400c1002d09000c0042041c941c071202503010380304080d100a0021312404032030811040740700c8820b0f0aa500f0800090280f58020740540880468075203035540d020300f110304038040741810b03020003584111618010322042d03201c0c0c2e00c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 655125971 1250 655124721 655124749
    0xd060207020919060b03062209080c1605122503080403120206360c19050a1e092f0c010e161401200d0318020f 49
    0x1031611015030041910807004841526816080322040440300c00903215210040c0114a8002d08500f806e10018448101034000c00005140117100301400e00c14030307485817041c1c0d507028001c50b0765000e04d0401144c0f40d0b510718464003481901c0030000229030404540b29690070701d01074050180551031004c155003110342903c24009001b0b24600200000c1c080d00020400b03036014001c51240c072029400b00038074110009002031922030310507140e22015501c05040c03000840c0b40c0c41a40d04c4d15031001c8061490040c05121480e400a29602d000e029641c5141d07181c42901d40c20748034454000d4881c420804c42a6820b0460719000744864010096244c80750f000d00c440c02d000d862082070b10007140100300c028107041481d103034076050001101034009109100f101c40341e03005034000e4540000c20000d014003c81c404c0c450740300d0804500003600002da101d6505819030340005010700d05048191144d0b10340c6d0f051103101e41400700785041c880000503c1140e00503000c4541c02010111a0382d018010300543e490030102d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 655127221 1250 655125971 655125983
    0x90914010501141303110f0418080307050d050a02041e080604080d0b1011010f06030804030f0f05030d0e071211040e01151d0a09050303150102160e1e01140d 69
    0x305403580900c4510032500203500a004e103084885000003000080c13120b00c005c448c800e41c6007200808000250481d88041c1c51b07082802144c40382d03030304081581d80740718105440402e645044108010840c0340d034040d009890350350a681c00030103402001d0000500c003d000b01585035002100141c0042c00704401002030980810340462442400701c0440c81203526080d42c403004c2003800180c6034110713000340309010800da9910028400c241ca103440c2e2220900c51804080c240303e16000c00e603400d00800b0f841c0070946070340c0074049a540d48403c41c15017008101d0780c00c924000f805001e0340011200d030b003140380d04840c58004100300000b018010421006000c1070407440c4055407640c445e10442142584481c0082800c0e611040d00b5101c80403201e1b6444a0040c007101400c0d01e00044140412400010b0302d52020308901c1c1140d10310032860050346044006c00319011208001c550110f180c01058019900a805913400b8107640c04180320051f400b00c10900403c000c00c4840603402031586800082c1307003042c0b40108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 655128471 1250 655127221 655127227
    0x310060507020d0f110603070f02250909170c0f0c030a020907180f180b060403030c03050f0d09060605030606100f0e0a180902100203040602100e15011509091401050114 74
    0x180201b030305500101c1e503107000b0402e113401007881560148208805d4a0384006c04030715900c0070070350a06076000c4078015120025915001c1c181042900d001c81c0840c0c1e1100c1e10000e48406001401a580d903c807100710030039600810040c00c4032810001009004c2ca5401000c41d00c05039640c0c04103d80c10068020300c007030781c00b1201c1c0d80083d407c0e0340b00341e104c4050141c80d40c2049420990a42e040141c89800000794000c030000c03c402c00c0829030000024100710f40c1440d180c1e50303a11088440381c0c041d00502c161440038601c0c2143c980b04200720359100d00100c4100f5015605180d5610080018a00034036284034003140c0020348181c2d0f10381c4940d03160342510500410240c0d00580b103102c5001c201584a440740c01040d500c000801c2580351070b002c1503043d41d109200440c50113040c10402500c1e007000c2c00c0d04002d40ca448860742c3d0780c6241d0a01140c0000180110852030540e5901e41480882440034454404200751120101d503c007020b01800d4a520a0084079280d5a441c01e001141d60802541c5100304601041c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 655129721 1250 655128471 655128503
    0x203060f0d29010302060406030c05190f1b02030c092d01080c0604080d0c0602040305030d06050405010b040627050306040b0403080f0601210f0609020310060507020d0f 74
    0x2022401032001c2c041d041000750700c40300002c15040800c4855000702148088801000141c0e10700e0125400d4414510f00402d64511001058665004824000e4400710340d03000400d02e05d40d0b0100c6a43e0954087d6921824195031207100c101c000d0503001c2019405400041d00303400c05062440742c041d0481d042484080340b164104024011700c11201036643e0030513602c4801000070013410000c0c101e0100085900905c0c29182400c1d0356074621250110343c00703004510001d9001e0101e01e41c16a0000c1d604031040e00d039942c510b4443c00d0010004c50091a100741d1500001203100d501110988041c3c4002da1542d034100c020805a484510394411503010041041c40d00211b09070703d042c81440e004510900110b552401c00340390140ca0f094008012914510b00001042542d80e884a000740c00000e000450b460811241f0103000302405030050946c05241c102240010043c54030f90003107205000e1041100d41680e12000101c81e144500d042c0694445801407401d80842c3d0340300242e101081c4a1110101d051400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 655130971 1250 655129721 655129729
    0x309060914040506011427030f0d030506010507060c0816030e0c06220e1b030402101209050105090f1207020109051302130303030f0b12030415050c01020c07050a0602031c0203060f 79
    0x2c0813403800740384447c00000c0340c00014800c160f180003580403030241010311314580990340c0d01c8020b0030b03059040503124004606564080c3c400c5440f62a0000024042da000c00e0340e0207400054243d034074681810020003c221102d10034401d004200c09004081d014100c5848104200e5410002c0c0d40c0f030540da41080041f030320382d2094000c00010800d00f80200d003e4680611002425103a0500d0181c07894808c02c02c000041e5110350b00020704d01081c0c1040c401804c69091414000c01881c0e0004102e586440244002803c0c00621150041e003140200c400c55002e010103800c060080980080c0490b02042042c0450300c6c00714185c01c40d0310140c003401401e100310109280e4003441c0c5603009070b010a40d07554100519015034050010310440a070340c400740f031360302c0c07501003954a1003207114510351000d0982400311601d00c03520468150781803a500039034a40c0e0201c414140ca0b00c00030310910340f00723408400e0009070850000c002c4d10b04112644e1805d0030b0030440101c07000040c2d031009005a41c04281548000680c2c0e032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 655132221 1250 655130971 655130977
    0xb0c03040902160c0f0b1c0b0a060e03190c0b03190f0212130f03051605070311090108060c0403110f0d0303090b061e1c0c090903090609140405060114 66
    0x2c00f0f2000303480080d140d403c00c0c06012880340c0181040311070300c8000b407100c4080d0104845004007041001d450243c035103c440030090540080d259801030345003000042456214205503e500070403003d4861400d007540307800c42421161600101840703d1458104820603070400a550302c19140348802d07a21508204608003110760b000c16418006602040243d0508020286580d00000c9848a8200f20426443e0f04603404a120001410010300240c1c00d1501641e65000d100030660040460b4201600d034500514030f0031000b4201805012b405000082d1280009401801152000701a621f46811a201c9a181808009803150041c00c00442d1a1980d1210314011700514001c2d0380014400c0701c0380c6490780200002510540c461401c01d80c2803c0c4031b0b01031010300441e540044550030300c18070340020320446021954101030801e13041e412000449811036081030000300e10a40e42d03101c01c5525001c050f55400800d01a903c00704803089082e610a003000d0f0300068003c0c5050401c16103501e1501142d94050f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 655133471 1250 655132221 655132237
    0x7170f0a08040e010501030204050d12030e160504050604060e150415090f06150f03051312020f0106080601451e02120c18030a0b01210503040b0c03040902 68
    0x7180054100035582080d820940940400d103025440c0c02d1030000003507220a103181c4090254582413589500c098000c0d486020303142122410b4400c9018175400c1001c606005100d80c1c2c2c052410700e000144185480d100300001d5520120805419846586c400d1030322000741e007000ca030000d54601c1d01002c01d150950400c2c00900c0c800401180344c100e8201880107031203096000d103000d21007100514100c550003006540f41403000d1710b40001c40d036a07841198038082030380c0b0300702426501c85070384030001c0c0690114079401d610685400910485d955488910340d106400d100300f0b80048003010318032f100800d41c00070344118451100d2094074882100c04515a12120705040d5100281e96500711121000507422491060350900354114103040e4080c100c8940c00c01c0050080e24100300018032108003005569007841d0a02000c0e0441308410420714090220890a00401154403000002003c0804030480041087c0ba8090003071070500d841c0840c156100c1d000103204078090300050202080d24610b52000d01444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 655134721 1250 655133471 655133483
    0x40501031211032205030d2d0203040b0c0303040b090a0309030602030a0e0f061617150a0b040f09060b0a0c0809030a0503030a150608130b0403030902090907060f030209010207170f0a 80
    0x1207407400b0101482c050500b2101018441c0c1806032382051000c44008960b580400c15050720402c020704022821440b45801850380410003150160900d10000083c5100300d100d14840b401c0c1c0d03240c01c02515038582d0355100040004844200520000d0840c1e000340da040913403800040781d181014400340b030400035050a629042e038444c1d0100305140d0044d0401d40c00d0080b07541040c0e404100248440351680030300800c8505070709180b4140400ca510fa541d4443d00030105c60402c551644e03200e440002410f011803280030b50060500d5004103004025400f11a1306422903220004289410303694402541c004a0903150b15004003441000400d00900003540300d100201e038001418000f56044003181003041e0003030010040d20340304100071204404807048100340c005801804aa40d03520b011030160400100c001e4001104409001e0304080000e0b00006071a0580c0311070304000c003c1082141280034400391f807801680503c41c100100b0007041c130121072004466003a59084460300c1c107040d180c403241503000c51365 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 655135971 1250 655134721 655134787
    0x280c020907020c010807030c0806190b1204020a0506030606120606041503090501060e01151d0a030f060b040513020d0804051f09050603010e1f17071404050103121103 73
    0x14569014035260341c4004141420231900e0114140248071600c018080e80c051810700e81d40e902030704061314515004000700f010b001d6a814220451458a190940301240510007960b0301007010b02e41203065900c00d401c080c00f031340e04040c81640783d222380b044090a400d13081842040042405c40600400354040c1e101611f02050004403443c0550031280a58080601c0194860061082040120304000c0d400243e2501c02e2040e41944d02a02603c0502449642d2050418000004010190580c0500c06020340800c005d240030303883c184001d840089a0b02242142c90f081210014900800040c110f14000c10220381802c3c1c8503400b103004c000c45807001c1252450070050441840d58070400c40405044280ca080b801c6501d424089050a030020304005260341e000d0307211a030340484929411004041d079207030999402440b082481e4a96174103014100c0401c486403c880d1203400e0a001d030f0b0f41225804000280d528960310411601c1044442c4480f030310340030420040c1c5100070010708401446002102344a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 655137221 1250 655135971 655135993
    0xb0d05071e20010615140d0c080402030f060919050304030b040c0e0108120a050703021c0302030a060602120a0e0a0315021306021c080c090a030c08060705280c02090702 74
    0x200c001e1081a84046030303070404e02c0030f211407962031081d1a1101c0c000e08012003c401680000030031405070030b600d807000c10300e486038014049500c4075900340154020f4080c0c07038180200c0009a510f551080701c41c1c04503544816841076403000000291700c8a00d0141040c2c9080c541c03641e482d54080320054409903030350311840105104400000c0201401030007a14028108081c2e2400014106d01800303140005000c40890184185802807211000030b594840c81c0b8014581e2408019009400644004000c103161100c0482c14600000c0c0d41d60200c011070000c18200041c00800302d828900b40321400e900030307441050000000e5204808642c502d4650540940c5945000c0090016000160301100466001840303032020001d01c060020010760b203500e4545001e50351468588010f201d460051900b2000c1a0030000921003c01c00c14402c1c0c4860109550f03503601d1360700b01110640a1040c1039126540da240c0445014130004400c000f50745c0c01070512a8100d40b5035000203e0b00c60045a1800c00358103d424581 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 655138471 1250 655137221 655137257
    0x15041d04050f19020112020708190320030402090a02160c15090e0f060f1825090905090a12050909071107031410090f03020d0206010b0d05071e 63
    0x100984901500a08180f48454108001d41100ca80080e060140d28030701e070100030a69804542516800c44421940c8484510036146002d000541240000303203400d403d0b013524501c05003202c0ca003e04641541c4c4c295240c54003044428100545880d0001d6820000041c04040c1e400880081500a000c1480300d145040d80031110034951540000401800c51000c4c0b00070360145c88401d030083c242c07c2c40300c0c0c401d59034080071407400c03c1000714096100301541c00c01c40041180c0e0314078500c41c0001a00442042194005010941118800000c041443c1c40e809000d0307140c0580c8515800850b503022222203035000d40b1403150f0081d124003c8030018000141781c0c2241d080005405410440702d02d88003101c0360003a030140c0c0d100c1801e404008d00b41c0c411100a0341010802300300c40c001141500d042003090801a24003403068000481045015008444d40c840306140081180e40c121808a0011481c01149400450040500a0103c42031049808244a0040030100007a1450b1071a49805401402000c161 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 655139721 1250 655138471 655138483
    0xe1306081e0706050d0b04140a1a0d050a0f0609021503010608060108070203041e18020405030618071401170108101a100503190c09060f03020c0c15041d0405 69
    0x12400e5108040400020364448219179440001300790008074903c0b51070001d8098645500c110101c0f0001105000e02040c00303a100e4026111900c100e44d400001c1c5100380710080c0ca481d00060600d0300120140030115148480c04240d0610810001800184ca40d00280c0e08891510700500c46400200c01400b849d07401440060300701c0000d09204002c0c0c5002400217550384228001e000300d60b007041200004000c60551400040c4c00740c40c02003a4a06a60f8404600079003040c8102486486140e0100d8030038080c4200d04800c04003c0c0010b004a641427000204402150441003810006088400c0c8510f1648a2070b01c0d0181c811070002e483d030700220340011001c1d607e040000500e0040c401d00054180e0b03403100c541d1098402d484c01c05644030703504c0100503101041d00030ba8160165042214000603907034000c07003007015030b0596220080350714203012048040780610304910043d540b00050140c4135107440c1733003980526200428198589600d40c01345100b2414000c201c6aa400202c03428403081080a20003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 655140971 1250 655139721 655139773
    0x2070c050103051003061a1201020918041e030e06031e090d02211b01020a080c070f020409060e15090606030f0613030210050405030d0b0306160e130608 67
    0x203201d10300340710070384c011070300c00d58400100b4566031603401c9600222400d03020001058020b0141d01d0000d81d40711182d0103940482070300c5209801d089c0750504003422038050280203a810072010503210344049020103000c001c51009030240811050f021016650310401144160440e80503c0801d1100c20b5a07005403042c05882d0404581001e88400d5410f60300081c4914140341c1c1d0359400e1000c10000c0403940441c89040318046000307920b01c040c907589190540040c000c2040726588d4001a90710385e146c80c0d002c1c2c0900140240f00e006001c0e00c5001503d0140c010b80c9209018500001c2d03070b000104c1c0358070f00e0030108041c0700749401c3c004d20070803951220602c080c07a0300105c240c0191504d904483d01186d2910001800410030f81c1d011210082070610800c9108001c0b064840e0810030340c00c150800a660340c200322500203600d401c0170b40320340c0281004a05140501c8000500306090b2560100036a1b035204a4002e80d5000b491070024000c619419000d110b0003801039001405030111060b0800781358040c4212 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 655142221 1250 655140971 655140977
    0x1c0303230c07020d020f0307030c061d0d060b03070521120a08041b1509150e010801180e0607050403050d0503041e08070510020307020f070e07081f030602070c0501 72
    0x401c1001c0d68a00750101c030074240d8100d03000e400c001c015200041ca0041c11060703103501441003280100030041520303074000c1517902c02c1d01c8201c8400d0200303030704100301c0807029015a04001c07213600a80001d0f41d6070300907104411004080d110101e4680d40461006e400c0711600503c240d04000502501c0501480000091020748001c01c0c0f8040d401d100113803c00c94003500080405d145201c00445d03184410142034040d014211060146000b9107900412920300c0340154600b4010404004005501400c0c02010218040e102e28055a10308480d5030900c0450003032101132103443d4662640d20b594248078081c4189150340b502d40d286c41c15800c14501d021800d5580b402480810400d0001203400c100003071140070394070500307060800d841e858010b03610f000351074000b00343e44200303504500c40107401e8029511410080d17085801c80300404109a94500c5540f259910f140140e8010507015442409841c0e4070525000049611602c07a01540b03001c0c0b030b0b03070f40e1040d165141d0200d010401c04c01a80780c0e850061400b40307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 655143471 1250 655142221 655142291
    0xc06030b0d080304020d0201020f01050c070606080f100203090111070f06050c030c04030f0f0b070908162102012c011701030308130203100c120e010c05040b091c0303 73
    0x5914002d42d803002a002912803c002c401020031a882000302100c0c64808100a001e2810320080c403400503089010304031203280c20010003003030000300050441780034a11840207001ea0f81000c072002009500c013500381c044a540b01d9403014000850392006107060b13441501d810208032807a04009080b51400b5001c607284550800c2030056201803c410742d02540e030481c1111084088a1030400e18850680500800700d1802d941002411a001462030045039081800d58150403050141c02c4806038041c010680c4000c7c40c40d001d5200d8100102491800d0391041c1400b030400b60401c07032030424807141e406807416440681c0141c1c0200f540d1121700c1d5101090501442403442d41103a03005007000034010841d01542803040410310655504200090721035003110340402c0310451028004040d1003120342000c221500741902c0210011052080d240c0615837550f0f058107060400101c5201a404820703044e40c8000c8451110802103e407203824418584a0b0b00e00291030410b48203200c02035180080c202d04550b07408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 655144721 1250 655143471 655143473
    0x7051011100c1e020c041805060702010b1c0c120c150c1a070306030c14091302030606010f0309201c08041806030c170f010b06090103050408160c06030b0d 68
    0x321000048000b10303c510783c40a440c03c0302c2c00301d1508400d03065040c0d1042c20302e00c030b041030a811070550a5145000e181611500d07a1b5440040e0f00741c032541111a90070142050b140390b1074804a5501a1340d451080b40281c01095035295079114800685009403a16603055604101560010003100702410082c244441007031481d031a601d0f1048440d40740c0050400794840002e00561182d0f00080103154009103031040b0648030a40294001d180c00c900c24081d62a00020400c004160031951084503801001001d1607906c07803004444170302640500c0350a140e111502400006c10303480a403094403509040c007144c404200c500308401540d8400c0340d440d460054800e013a02107620b08045500799015407140c041300e2010b2041038001002035900152a40118240c00f05001d0042c02c0c1d071030004040c81c0101c6411031501402c0c103080781c6400b98801c2c7c0c0001e0400c03003c50b295000350025a0f101e80105180d42c1010014030041d0a0801e85c0042101c000c46180b4017440107581601c24040900301c144c2c3c0200502c819 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 655145971 1250 655144721 655144727
    0x1208040306020c0a2102070f0b0702040e1e012a020c0405130f0506040c170a110112141f050d0f17040e01140105070b04120207051011100c 61
    0x840c000a024150001101003d0742c500300090148242c2c030003010b0203103d51080c0311030fa0000c0854500b20050295240004400b401c800302c0505031560740300068070b0410150701300801000c0d102410301540c021039002010300e080386811040c1c1c41880e5800031596890424202e1040c1c801404407656070f08280f0104140a5170000e00d000f807040c000d03140000d40d0703160f40c641c485880d00354000013803207071411032020020080007041090046109900d41d031502600e40b20300300441c50b01160704145503841a06840d000c43c83c0c0181c140c0280c00306041880480d0900100c81083e80e4202c1581074007a810322003405462680c45450000b83c880101054920905240004107142c080400260000000703104800c2423100010384406c41010302d41d455036980781d07210300d00c168004003440741d1854400440e641c488654000c208030b603496075218240019681d619507540c82061005440201180310321500462191100b0344942058907464542050344090b000066181404441c4015081400e0020414010350 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 655147221 1250 655145971 655145977
    0x904030804033b03060a090f0602031509010b0a171315140711010c02030322050f0d030b0909120906180307060e030105090610140f03030c01151208 65
    0x16141c03030580c8224410070160081042c00300c3e20001e01caa89491200b071101e414549400140d8016829100c440d500d01c0352000072030309111000340a285000c003250300054001c1d401142d01030000607130b0004801c509004941e5800c0309800c0074440d40030010719070403695040b41d480a42c141c0040100207a500d41180e07600c5014446240040540c507507507045503403c21403904050b81200da51402e80d01c151034000d00051240704481d03d0714186501e444200c0360050b2010086074412468102010844d80f496014000d4544450100b44d50364010803401d080d024800b0b0041c005100301541d00420205e0341c000c1082110319024290301e4166000c8801000c0030311b0b4600580d0081081210019100c00d20820031010366550040c080d40d143c040d0520115a1a80040c110200885c00750f0003041540d541c3d507101603a5500954070011401120031041020b403841c044661082407014002c07140e1b5549000c0464615042300c0004a240d1b5100c2c0d04131032900d402010608003c2049899640e00745001d6141c00001d44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 655148471 1250 655147221 655147223
    0xa050603030a1d0402030f0f010801110306060901120905010b01141309090f0f05100c080f0a0c02010626120f09091e0a140c0a1b05010b090109050a05060904030804 72
    0x100c03e081c2451000c414040602d03001202c050000d41d0381e0f00d400c00c0410600c01c4112810903005104074004519048144515840002074401c0b052540c1c546c02e04000894000801c514100f2155816508103041c0346e014091580d4840e41c00403980c04007140002d080c01da404840c09460703540502195071540e008030f00c64000c07500b20550000e00c143e500d09002c8490011840040d1151413060251400c0000015a683c6100000e06042000b002c00220031a0400c000361201c070f413a81e0518000c02c922803219131025a6012040c000060758a54a4900c0f00c80d1000305000b1a80d001c0034109400309404080c40a503103091002a0628500040c052115205001f801031072809100000c0001d1511070b6000b4102c1c41c02940c0b10f810050302d182520000c4c018018494801c035404c41e8076808a5090b0881d4402d40c1c00c1040c0603264558070743d003902c241800c04005000300b61003941d210f045010301600e8180b00180a0896140082024030b4040500300651300d001e0101c501a11a25040101280d401060f03e80c0007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 655149721 1250 655148471 655148477
    0x9050102071509140114071a0f04030836030304061103070909110706060312030b0906010f1d0406060f021b01050f0c15100302010914062a030409050603060a050603030a 74
    0xb400700840121481c004512454100801c0001c03010103024502c3c01d0240100c00c00c14508d038182d6110520032110003001e0700c0040110300b079000403600b40301c0125808000c2c142010a0590360001680881414000d82804d41e0515080003040c8401e00030306002d003600488808581c00d142d41403007040105240c00c54031844071300c03030342d07030002c4960300c0045004840310203412140a106441d2a4208000884e03502240ca80100e41781c0b20144100b0b040180c13032544500780503102e500741c0b03180100c1d0603100740c8405504114101c51040c2803500d10f50715885644090b05071652003550040c90003002078500065032403141007007006043d4481d016a889070450340d0100c04050401c2d25041010b00180c1380c4109210884005100c0382c04008200018a00300c00407207000342d980308240d41e0b803200c0503c400d049102d581030b0401d00c20002141205020804421450420580e90f03181d403104603842400e40c1c104c2e40010305441d40310403c0c0000362504015068018140140c00c02040c14440002940c900ca405058418 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 655150971 1250 655149721 655149749
    0x2a07050c0d11031606120c0f0e010203070605090703020102060901061a160605010b18040608101821111b09070203040b0712020106271a030d09050102071509 69
    0x2084210001c2c0702100a01404450444000511120004403180100c0f8001170406010034110b80c0c0314005c1d1a915541034403410b0244130540b80c216a034460094031141517100c10401c1a0008005115661250441c00090510700f82144002801c3c41000b0f011030882d42e06141d0148040c0c80c280091b810b03031320581150b07140e581d40040d0300d861071400075074805040b00e450240000365492805000380b0340071100f0210400080340361800c00088545a00903041d0300c2c0d10a440000307c61360258446001d91f16000c04540e9440865502c480142500e00f000600c644050210310144ca44c11104c60001800984060024080c160a00002654035440c03000c4c4a140080c1c040f4031001d0082c000c55000d405200344541d503034403040c10003402d6016a1002d0100562801344006001c90240301c484009014204140315054141c15400d400340054800d55148402010850085c2d035404200b0581d000b00243c4401c085285040000ba09020301c40c0d1103c410075100c0329501c89070551001c119401d031a034f01448200303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655152221 1250 655150971 655150973
    0x30a051e0f0f07140313150204030302070506031e011d01091a10030b061611010c0308010902280f030e030a09091805010c020709150b1c090b2a07050c0d 67
    0x504d5814003010805603140001444103142e4049004d641c824091041600c25680d90410102284258440a80185c101d40c000740001c1c50180300842d04805400240c0d070741c04001c6582e00d080700e5802e074014840c41c001d131a0030300d42c03644c41c1d40c03810360051035602d5080042d81108078030b44081d5160703010f1551254101003d1079144034000ea01004032190068102d80c0c075009014464610f20480005c20781e0003440e103170451441584604011280c140c0d041d5100445a480c0907040c1c0c0c040e4126412040380e0388030b01c0c00300b260b61041d0401d106070b201c0c02e5a41c0780020b200842c41d0190440303064903100c070700580082010510082c0c0080c111412103404d070400003080b05001312040e0a07842c1d940001442c030b508044803403100c3d41d800210241596160b1108001c900d0828000c0c1521a0003031040310070740e074801d0103140a84507c0c090301a00b140010403022074131644641d558850100c00f00c4107101080c000040003102c0c0440b92260401315000200c1541c0f4000a075103c0d02e0b620b1851407002d41c85943c040380d480c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 655153471 1250 655152221 655152227
    0x306030f060717180a0f03020316032001051612060807030b01030b0108030307021911191406031003240f021e090d0201120908030a051e0f0f07 63
    0x5010111510309031020350408001c001d2042c1c1200303c410b000c14082c0e50101c1c1c4500c1d1924035940461201500074003c1d84c0c1c03e642e4440d071008542c3c000750150300090091110380741d03511003142a03c4e0310a43d60078501030341c5412585042030751404020820303803420f0100031700079840f106108410030312424200031140c104c08a5a0160406410251450168003c00030421082d18042c0703050760300c1342c01800c02503078903910095a24001190020b0050f400500b070600d585080d00c1038000c0c440d010362021951000b5190102d600800305149545125501d014104803181c0001e1034a40311036002c5070443e1a50500055840740c0e1002e13400090206080d1680e154014400042d2448980d144220144070701003c425014000390000700840310040c2e1903507040f000a61080b000c0313401800c03000b001c03c290442c164004450608100501c070008558401c08070f404214100c000d50b00c108446400400c461a2407c1c036820140d81003815009508a07150034003c80010480504d81d103c0c512034215401c6036a200c0c811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 655154721 1250 655153471 655153483
    0x80a051b040204052724130e010c09081b0109031103150a0903081302090f070302040503010e07030611030c1e09090a2c0714030106030b0c0706060f051005030603 71
    0x20f641d0281d614900c0c40c1c8603004c11910300100c12400081c100031669404002900b58215880c4455501b00758000d0222910f80040d8615202c00b0b03203007000940d0580a4031503821034218005003030200d1031000c010802c030101001704112000550f0490f0401d0442100080d0040c04640001401000c81d4060b20a554604001101142c060410904554200300c0040801066055415800036105100107003481c610056800ba049a025261102c603079030380b0429850004000d44200e04240c0c08110004141d60240a9018203030400c9026211a51442c60041c1c01c0702d011050482640710148100410381d820705050b80d440b2a031701002d41071412110004075003184100c0044981c080f40c03d00500101401a601045103a11100301c00190703440c0601304103801e01510300001c50140d00800d002d10058006000400945402400118040303407280e40d46c4a8580040fa0f2030480c5000100e02c1c8410320069005500092402c0b00e04007040302d003041c021911103000040c415051140c00004121146c03000c02407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 655155971 1250 655154721 655154729
    0x1006140f18130c1505030403030507020f07090e1501031e0503121e0901110306010e030c03010515010f050c0c150909010602060619050a050d0503130f0f080a051b040204 74
    0x240310002d1800501c0d0341003080d40745a05807062140d0744004a041c01c0700c00242c40144c505038071900e08651722a039046010703007070040420045008210590703aa0030000c02c24000504081880454a107200c00d82644c946240000e104045000000c01000401c101ca44100380c1d803800c028894080e100c50782412440c51080401c02190150010200a42c4100c0c8090094407070490390400800c1b03480b07090000782a54441040034171000810000b00c0c541758007407400200c469038044c081c0c80080c010100080c3c01c5590440300140c0168030266032400540c1c0c081110300c0302e4511030030114188600d02c460141e4600304104182d00920011080e899640f2340d201c10382324442002005c1642541c0c440800179114039003640d6a40c02800c030043c0300d2044100700d80003070f0169400a009070100d185041c0801c50302102da40b801307136400d010130008420007420780c14403107001d0102e0301541d00b801440d00b140c4102907881a8003100b40c1d07400c1038021800103900840d440500044203610480380040540008000344200e42c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 655157221 1250 655155971 655156009
    0x3040314040b0406270e090c090a0c020c0d15020a120c031401140904170f07030c11010c110108180106060905120631020414091006140f 60
    0x50002402400d442c002c000740e40d1160b03240011400f40745803c003640d035050580750555200c080e000f40700c58181a6999540407805408503600c001c400700110344503003c181ea8011180e92100c07c1c00d11074a4040009080c47c640070b90b91070303131000030b1502c0300c401e40001c0d031440c0c200c429000581c4107201441782d007142c400904800c004000c41c54130182c000d80200780d44100c940c0780c141c01c84000a1600151041e05000b0b080250050003035941b240c1c0e41c5450b03140344242016285000f0310001200e0038600001d4440c447c8203440b501501c2429003400c003800c40c07030700000504006580303424400062000301ca40030701c000f082c2000721150712007040c043d440e0000004804019032902c0170000c1e0780c1d03500904881c1182e000ba5a5100e82403101d4502070340345d04041351041215a402d0240c420b01880026071421031109031811003150f400264002010345020341241d00b41d4103800018030101c41d07030038401000003002c021401c0000c113103007420715004a10707510b03851881070725071424562030307030702d42d02c0d1070165403e4920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 655158471 1250 655157221 655157227
    0x121224090c0d0606050301120809031504150b0d0f1209030516260c0904060b090414010e070e0105010507030c060509011e0606050711120f1b040b0a090203040314 71
    0x40085607064001040e812001c9091035030009110340150b045070305840040030380220480c81900c4058041c0d00080341590144100010800180341c20740805019500c1404450b0301540e403004140f040d1a40802a1807089c10340154481c00681c81000034044d003948a6401c04402012080558151140b544003502e180100c4040001e5041010303100740941e410b4a5040104480a071307035981a41140300040f001ca83d00000c203075620791038803255041e4003030b22414003c00e4025280c001314002c2d010a407021aa9495082c3c0301d580d100e502170040c2c80420f0039000040c41c0c403500d0300020020300081031041a052004c0012200c0515125141000d0001d41064040c8280c2c20040065402818680080000ca200c03c1b80b4107a840700b094003544040340e1156070341034141540e42d25510700401201100fa540302e21000410a481c4105010360780010f401d120180c8441540e103060195914000103e05104503c5d2080504055803100411403d41c2c41c04074005032241d0380c1d40350503142d031f0600340801e00e1000404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 655159721 1250 655158471 655158481
    0x91401020c0d0c08030411120a030903020a0e1006030b13050f0609100e011a22301101020c0306090c040606140306040c03060902070c030512122409 65
    0x15001400092400300403101ea1541d01075044419280c1c100e4018200f020800210f804640b80d070141c0b0100ca071f001031100c4000c00c030302c1c00c80078a00b04605100f2400310f10081800c01c00c3d443c180c50064010003c800d5100150320305140c0050088515008501c18156180e4031a207903929007100070103a4002000040200b8140803000004c7c88100b02c030303034520031005000000c60005046003084111080c244500d4070990070b01c18484d079080072092900c449103005010040c40c05110300c2200910703407144280941514140501c10f4541440b004040c181c03c18041c0000305010700f80709801c0329241d0003800c08078115500e00c2c0100d0034651030420140d418801c0c3c00a020b680d80d40465021000401150100b0220f036550740c0684210a0740400000c081c10b05000095150a1542007014049800d240024076a40c403401c1200882e0021001501c40c505681020b008200701040a14203081c5840c40310340c100500c3d90f542c40110840144102e045107407140c2502c88108404944504588008041240e18980 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 655160971 1250 655159721 655159723
    0xc1e06090b010501030912140f030c0307020708010c0e06070219060906020613030c030e12030a0509151614010b0409080d1803050a03020c100c02030703080c03070e040b03010914 78
    0x46030400340c6403220101e0001480d50700910036102c2c0654010310400e0200c0c0c00c1d04c0c1c1078a6440c81000800031407881007180080b0300c07441034010762140c0da14a8856499080c0704000901d0a2a56040407110b41c5c508900d410385c0a42150701070146240c101c0e140c5649003818400306079000b20b50000c0d034040c0d2004090100d90160030040c1c00f002d0b20002d5084400030b40e41c01456621040c820712018003c070300003917400f50100c0e120380512221481d029000d030340c000da080c2000c10301e198800306038680003c4010681e080b0782c3c03900d51250072115100c0c0c1070082c10a02c6041c1201c48034094060014401d04031003206510200f0700b17411144140400400c20061100e5504000d500c6034000c41d0308400062401030f400c104000100460b2480603016a80e01e410041c0349001a40203601a00b03480f40c0e240305010342462200d42701d004424491409078041c544601f1145000f4101d80c2c400f800306a1304603810b01c10860303110b5205840c00352202040710081110241c000119004015401014090400000c000020b000e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 655162221 1250 655160971 655160981
    0x30a0207050c01210f0f18031814040203040f0209091c08160507030903080d1d03030708160c0512040305160e04020118080607081807031502090a050613081e0a030c1e06 74
    0x40251101107040b1411580c10109c41c07802c0c01001b1048900c02c1e0850002d041a03030103541d10600c41c0f44400f000581e140c000881c407040443e040f90b070036806841170300c404a454034180d07105030051b82007442190070082e103149621032403282c1c0d400c00c0020105070613090500c02e0740c3c010005d40c0c21444807940c45102e440120050820400544e0301c0c0f8503009000250030390000102d910402e260358601c0c0541d10381c2d0010300555031000462008000307040030842d000c10014010401c800440146241d511403035480d009042c4410003501080210f1040c0080201940144070a40d02a03070929000781044546440c1954040d01604050018401c0804029034150010f005031b003c1e030213079a099070b48840748441450b5501658080202014440805d50121040c00c1c7c02078580c810f00140103180321601c2d80e000c0380711b542240860815030345104d501003244000a11521404a500c40c0b14807801d0401c010b042c0341c1e00c030b00003400141041260004202441846040d2008100b0515118484903000d41401c82c0600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 655163471 1250 655162221 655162223
    0x1027080903160b0307031e0c09091109030a03050c03041a03150a050a0303080a060e1306050f010302010804021e0402210a090c1e0506030a0207050c01210f0f18 70
    0x102c51002c010781c030001d001007484112034424015602c0d50b43d855004a0250018900411f407920646200e40c100000701d0160030300c1420107070b0760803800900e020740b4042915681c580141c6030000030820b181c07468a02080d8592525050708049540303404101829241d480b65a201000c1e0621619010b40c48031001c01c02103000d02451140c020028071844108641e10820f4411a41d200040120800001703005036522988112140c0000850316039480000340c20110071100b4501445009448604110440c400d164201c01040101040c4e0360456002a00210001c4c202911504000f50749040000da8842d00240a42020b8000d42d1a5079608213488503070507178141042d41e40304030840020300d1071140b03200d40444250020303e0400400e14004501d040000740e0400c070054201c41c0000440c2c1a00c07040011b5005640b000c2006030341e901503007481810036000000700360400214903000700c02015010510f0300240c02a0b42c0c0003500b8441000810010048601c41154650800d10100000100c01001c101c1071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 655164721 1250 655163471 655163473
    0x702130605011707201c020a170c030a03020702120111030108010608061303030903140414040c0c21031814010b03070f03080306010c1505180f1027080903 68
    0x46442d10030303000f02d4410858621000901d40740c40d00480900303200f4052405100c2d0300075180010340d40004880c100c022181c544001d603000c4008a02041007501c20b041c0e8041469002d9401c4c0b84224900a0b200e00c500f0002030105900420703c1c0082d0740c0d60710200e40121000e100204030b500c03240d0240c20324039007003449031a809510705000043e29400c0400d40d18410400803406010301601642c0075030003005d10041c1a420440304d07107440406036910744010310103090804440701400303200b00d08010a440740a54030000f007044e0441c092000400c59002194484081d01d040813901c4800d032000c400402410070364444002640b10031506000f03200c0762070301c0c40940e060000c1c4240e80d045000d056803418140704403054055144400c00218403250003039600200c05242508902e061340e101c03804140017810155205a644005220b441070501c0780c00001500303210007501e11b0100740889142c45003030b58500568620b44403600c80c1d018500b0fa500300b01c110042010a000b4080c03003070a0070b0441d030f0040d00b280c50007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 655165971 1250 655164721 655164737
    0x304080a09080d080a1109031c18060206060415270b0402210a0908191b1110020619150801150801050f101502070503010221060d080717070213060501 66
    0x190300310350300710784c0b081fa0081d000301501040004004500c1946a080104001c000700c0010449002e40701c2d07600091200364018216804c9c01c008001c100e41c0000b44c0c803492a20918001c111415076040d1b40e581c140201c82c21a130310118070740d0012010704405031003207a1040c0b00140001501e0b000081000804601d10781c10309040c5d8440c031030101164001100035000d1a810f110f00c065000a1900d550740440d06403400903d5220b03111003940d4030400316402110b403451444e4050600d410507007038295400030079200804541c140119900940d09051035412049521a110480700c0c0808642c1c040c01841c5240007041900d00c81c2c16914000e41080c010035009500306004500e4240b0042070650150507852440e035465450000050b01013500d5110f60020b5000790980007581d80d8081c4090700d00c40f41e8440e481107020740c21032854907807041d008007034500c40c0c403001d02e1650100d00d12800f0f40301020341c008692150b11110130400d40d500e01a4141c000c1d484850341880320090151a0811000c841c802c0e211040c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 655167221 1250 655165971 655165991
    0x21e16050d05070b030c0909040b1905010e06010c02030a0c0f030510200307020a1b14040905030702010e0a180f06060503060d1e0b10060f11030304080a09080d080a 72
    0x20001e110703403014040c3e5009020601c40503020303070000c60300709103044641441c2c44906e4000ca4451a02220b040c7e40c50010a010846010f00c40e0b884d40c2144407140408110942c140b03a07046042c464040d0200f0304001c07003031480404546040201211b03590300000030204455841505010b2003410b40000c070348a000307000c801c01141032103004182d015800030350102840c00b01010341041c00c0d0802007000c4114816890003101041e406c004404e29030700d2a910300300c0d0103414024411b0010b054110000e02440c07400c601040802e1001c010740b0001a82441c0ca59010340481001480c1050035401c421135102c40e4110003a4840c00e1507000401c0307080a244203105003a40da090648850100300c0e0160380240703510505000280030b2144504e54807928498003c003c030840e071184810940708580004000589400c184202d50300702528002d50006441c001d041030444824a039281d01000e00004c0408201054090b0440e0080c02000b0180468100b00c0380c252050b40d5004151b29410b5482c4202030303182484542c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 655168471 1250 655167221 655167229
    0x16021e0c03150c04210f06150f060c080307020102121501031a060d09080408150a060b070804031506180209010e0604080705010804210f020c0306011401030b01021e1605 74
    0x91207001064400c0d0306144c83c1564611741d501414040030000c2d05034980c40400a500c0440608266020302d00000308220740a00464801c1c00b0303078210700d10015566000700000c9520040c41c50410f03034443c51341a12500c1d0010140e0190103145080d87c030b616640f50400c15131a206a440d00240502641d05014184050426110f05a1020100d54000100300700400c400c01064000c10207180c031401c0f0662410341d44090282c10440081a00c04807040c82c0810300c0111b503000d00850340a000350215252400f03405984811042c412880000c02813161a4213801071069194840c0d802041c1c003101c0b07000d140d00070f0340820700294003840142d0301140c202541c2c42c0036402c00d54203440986100a004000ca1401c0c400151560a00208101c40c0080d40801090303c6100290303003081c640c80d0f01e03110551039090f40c050103401d2019844501d0700940c0418010440c901e0789200b840e00006080c00d000403c46071003c0100e0a04801064400450a0b1808540480d0740c0015809680d0841c07030071020080ca48580c01c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 655169721 1250 655168471 655168513
    0x90d020111030f221709041a2b050706050c011401030321090602070503030601120b090403110c0a0e0106090501110d0f0c12030504060f021216021e0c03 67
    0x209810305a050009150060407204c00c10000074800d089101201c0319503140c0020b8031400c580c0100550002c40d24102c076080c00e0240710002200b0142542c0e6161025001c00d901000441c66240340c3d64481e4405500c0458401106000035005801d0307070082a12144040e106270702000c2c1c8080035610305507120f0204521001424182c0307034940d5980c3c40804140300c051001c0d12034022600794079540c82841e04009500f610040c0b2541c2c0c4a10b000e15180c0c40d0000000d03000c07000d0762201c03c0403035003816101083d0350b48010807144c0c05613040c14030048480ba0210018941952445110341014800d030300410f1030640c28152604a50540c2d5940070140d8591004640301e49040b1008019544002e201c5240030b401881075902d4082c503407501c00000007403074071180350002c104080d0360b0210340e80d001400140b002c17a011b6400c40422aa85c01e61400511607400e80790210300a03c000d079000000d04044104500c207003c1c0146442e2404502d501c0c204800840039200c00a030000c1c14030034883c140c0101c5c815000007140d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 655170971 1250 655169721 655169731
    0x711011d0907300b040c0f05190e0d050703020f180f06030c0a03111527120708011407021f0513020d030512010f0807140a050306090d02011103 63
    0x4240749403610101074031002041c41c0b486080c00d0b00c204200d550009100d920200003a2440000310f2884102400e02c4121188940304a0412500010340001c10ba002030846d284080c8080c000c44801441e0542150a20a41503c40ea485803003024103100b0300c50005824010307079000319502104481c500d010041c0c0490700707080404880c01d04800003004c00b496000c901e9030151700501600d034501c0b003040000c2d00c51b090b590001c0301c215541c0007400040c1d0402500c0c040f014050542e001d443e0811401c03865880c0c1c41d810030510a418080004540c0c00d0701c419816034030203c180411039440d95104c40400e4081c041d1240300050a0074840009410603200288560218018002c42c82490340484420000340c0002080a101d000316001d2020060b22001c00c8288624065645d0540f100340b4410030f140d08500607400b400d500b80e007500c0d0502c0109000700d0b01d4002c0b01d030142200f9252858030008100141c4441d480b207a40b5004520402c002000081660081c8104507402000124100c0d101840d507030009070340d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 655172221 1250 655170971 655170979
    0x2072108161b2102040b090f04060b0301090c0e06010309170a11060610080915011508130b011206060902031e07030603110108060112052d04020f01230711011d 70
    0x7480c0b8000300c03d80b8092040d0900180011070760844401c08144901803c0d25080c51011142c0100014800743d03204d0815000e100310028850640d064079030a00349000c1c4d0142144003000100810001d0303010358000c40c4038542c010300d0070b03103440c6100104141d00d4010642010206d0032030b008500100101080700b81c403400e40209044000400381c00125901c0074000c001d0b00c59482489004a00c100c1517440350b500070210038a4008100c94084002084c0c003001030b00404a03820b00e40140360014400c510107606450903c8080401c1c03040c541048400313002554171881029100106201010280d003166401c9203070208560901519104c50890480d40a40b10280040b03904215840156105c1c4850540007141490074150303148043e4510011600c0650301d105540421030700e8416040b1810303807000340d4091203103a5640c06142a0700400c50281c2140c0d481c41c100201080c0c5a0485c220150258400700084504c0ca41c40d521035240411f801c0500303011150200d0303c107551500c3c400c003000c14042c0310300002034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 655173471 1250 655172221 655172249
    0x903160b0d02072f180402030604080c2a0a05011d0402030a0f02131a07080f07080c0303040f03030f0b1c0206161a01090c02072108161b 60
    0x4030080080d0090f10003121484c3c0251400c001074854442c610701511840f420200c00345041ca0300f0000191288070448a0014001d410000943d8022801d2a4015080800c1030342d03600344400494101011071504c3c1c120300b2600011003008080300d0000452541c1c050741e11800c44c035118401076420f035000b69042040074004038003a103a1410f10741c01458104c0705601e03000c50140001034018081c0e0300250626440702400d0b02040010300c2104418010b041e040044991400c0d5180e16034007158880c060b105909620300040160402040808030340e600c41c03035503058039141c1c182480c00030032000c1d1102c8180c0000342001400701114840788910444d007c030050a00a2110286032418200f070131840080c0e904ca01c05114031106c50020f00c54400200744100340501942140b44c909a05450040e00a00c1c0c00926100300350901f9500010640306645203180c0040f03940020342104038019401034001801c00c8404201030594100645d4003c40186c4599950b0403d031401c5007208801004503c0b810501071122 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 655174721 1250 655173471 655173487
    0x30a06020d02070f050a1a0c04170f030c1b062809030b0702010608160f030803090a0c061d181812072103050603120a0201140c0903160b 60
    0x603030090401c54003207100941410031030f0711340040b031440032082980d1030b4000d070030134004003d02c21801140074109481e2049060910000102c82802640141eaa01031143c08200024410400c520500003d007442100c0d51482580f2040c3c0d05c03240d80b010440d90584040c038102c61145081d4041c0d4400e24480400d8190080360003145181c0085180c00039403d1002e441d00201c00314503000340c0103100381f106400104419103081c018074030304110141780311001351400e2000d00148141d42649411213800c0f102c0142c89840343d10205003801c0f03c21200a0844041240014020340c002440c3c20281c01ca0030350f401c008000e201b0910600c1401c803079503441021100b20000d450ba40a002c41211340780e140408540e0f842c00005074020290b1300000060702c4180800d8480c1e00c1950069260360810f4036640740c240000d090100210f990b41c00e0110fa072004481c00498403801661003540103002e80d20100f81e003140142007520324400313103034400c2d0301444c001c1c00b41030f22402d40c0347c03240d9144004698a0b06103c515041c02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 655175971 1250 655174721 655174733
    0x160819021c030c030e10020a0f0e0928050a150b070b010b18040509070e010f0602030d05150d0b06100f120905070806070305090d0e0d020108060a05060d02041e05030a 73
    0x103c000a41410303903607000398a40a2040003649000c84610f000140e4440c0c0c20900542070b80107580250040001541440c101c80e10741060080c0c000f07080144c3c041d0b402440000c251200c01d042c601c4080020318001c2000700c082c6d51038200807413000105c900e01d0841a2a004003100ea0300c03030030001909001c2140c0c01005074000007401000550160101d5500704039a40d00090705660059603030b45220f074010715050103542c4000009a0042046108080503507142100c06034a030300444208480d6143d5a000162282c00b151a6590810030b00814500000b00703e4a032001e8134402c1500d0680c0104080d100781e82005015198000c00300003e9150b42000d1071760040b0b5100540401c14040b280c1740210b11380002c004c1020000d46000d03c506441c04107061030504078040c9842055442102000600d01500566844010b2080030b520b40a2810f01001d03900e07200400e492180c1d80c0d012542003000000c031461480e105034080d100303403803c081a810b0103482280a2044070041401030351f605801c0f180101d800122 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 655177221 1250 655175971 655175981
    0x906031a09040312091b0b04030201120b15040e0901050c090a0b130312121506050d090620090a05030a170310050a1706130b060f0105160819021c03 65
    0x1100e03142c00058204950750060a0700c83d840c40c11219001c400402c15030500031006111b000d016144042e60510745980c0000707080c82d1007040e0402140c0d40d00c200d221025142e030f02109042c0c02c00340510030b64540d61040f40e0041e0b120100c1d030151007940f0301004901e581000b0400c40f80d40300c10040410700c4041c20580030040503030180d083c2c0c1c442010385a4000002911940048060701c1c040d4850140740e16030281c7c004280d40c603000301259500721098042c8462a04074007980d16042d141200000c0c01c01c114941400140f40d041d02209002c0d6054068604000c401002420b541c04145d41b1010200d81d07078030034103a8480c010803004100e4000c40b0904650341810324055a800650318403640720107540d4502240740100a50840d01700d0305038404105211050030041a031308003500701c0d150120b1502c2a10388484030400131300554030481c4030300d02d00525a0b00c10400e5844403045695800114115131800c01e5040c5e000c2901d841090418244c40121640081280405030005552450300905902c0701200200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 655178471 1250 655177221 655177223
    0x15190b0a03020c0d0c0b10150e030a020306010e240a030b130c15030c020f0d110a0618050f030408030d0504020a03150e1002070317090a0803090d0906031a0904 70
    0x10750902078003091100800242d0a6000141c031040041d40d0181001c915821000b0560b0391060b4402000300032903060010000c0c01090f0307518009da2240781a60000b8141940440b000e581485207800200c0d201100601c254024504860340300b401940e2280f0b0420340100c140781365a4030901c100001c101082400000720f44c80381c0160003e04040503680d66038904800c003a005880c0c0d10303e1140c51160702c1034151042d0075208800740001d00003608810030940d5100002c1442d40c04010f41e04145030350341d11080040440302944944c081c00342d21030300700d0341b0781030055207400661b4144103034006144403c8001c021941500c0c1004061883c0c05460b20740300e00a804041c10403030308040c50000c000081116000c003103092103150348020a4003551101c240380340954582c542c1240500c10400c00c00003a402c040d410020220280414106e507a40031019803d1011800c0050040200001040f600d48008901c40705a40601d845420125071642c5045048a042032070100004408000c40740403450300c0e090b184cac2d200d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 655179721 1250 655178471 655178477
    0x204020903070f060e06070f031128150902011b0f08070302060601080106030b0d03080912040f1d010e010e060a170a05060603060402060a0f12060e15190b0a 69
    0x2119032040400d103455103690204403120040301c0d060044992003411030b00e2489048503168109116a1070707840200041010050070b10050300c0745501058010702c000e1810580da01a803032134101c44031607010040300b129501181d4581c61207081081410462090314070042e0181e541502c40c0c1044801070034800050701c01500c0f41901012080700043c1000c005002d01882a40944083d04007000054a40081a041031041c94100228400c058031a04104502140c0504d003000302070b25000c91050400741100c404c0c0d03081c08000240410741001c0c080074041110502c1621000d003600b025141c8145001c00e00621400344034040042040071141c88401c2c3e00044001d00446865627100d0880c58a400288400185c0c2d4000c550480144030b07090080d59809542603015001da46040d034009030300e6215280d21002480651044600c0003485404404419101024100005a25401e62602c900030448024582e951502400307560b074182114080c02c0c1c1c103100314031b20101d50f0400f000c5001d1908030542100c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655180971 1250 655179721 655179727
    0xf1b141822050106050a0e0409021302180913021e060d020c0c03070e0603010c0512060d0f080a0201020304060c020d0c02100509090c04080f030c060f100e0f07020616050304020904020402 82
    0x608201031140b14001d20b181d40721035036241c10050005e040c0725100b28030540b24a14003045400944c030350850714030748205403110040e903891412a8100a80c0503024801c2d07004040b80c420002c0710183c42101451450080b203c104480c000f40b40400c030820b500c580306640004060084540000050f009482c0765200700040d100d4509080011900c0c100e119801066403418100910504e81400e2060390301444052a11500d800d40c4401c0300c801c0414060081da0042c00b80003007000620401f0452544c0c0030b907002581030f0303440a01d100001c5c0030350001d44041d20424501100104290300029940c1003003c50783e01e650200c0420350b020000210b09900454090100c20480044035903a40442c40384107803115650780362110708003000145008004908203003154010404008c1d50040041c100c1d60003180010704800c169600b0f22004006040e80d4442d007500c02c001c2e0184a290205240001d01c11012a800c840e0b165480c4000e1500d00b00004c0f501d800861400c20100c0d015045c45600703140d0150028002605e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655182221 1250 655180971 655181029
    0x5160503030a1a060408070e150901080a0317010503101125050f0106300f0503120609070507140f0d050301060210050c0318010f1b1418 60
    0x41107a00c1200e040b01800e540302101c0240c11030040b44481441425503c03981410306180d44a03594140d5405200201c21031000052018100f0315055080d00001034840001940e41c0d245456855001c07440841c0411b9481244000c5a207040640f2412154000c0080041ca9400403110008040300074022071880020013901440003203102c404c0e6610501c003880d00c400002c103800d0042c1485525107035003090ba41000000c2262084003004030340700c92020403030301552414007000203020754025030008003409511081c1030700340a008030242c480035100d0006054640d403028104508038100321243e902144046c01594040388218116074021110003045031000070560b491907240000c07410017600062400801804019814400d0280120158905010b01d04114401610a000007414034020b10840081074183c41425080a10800c1d0448010440d01c1c034000d038506403807101603210101180d0610b0449100c29590400c8809544600004802c4205000b080241e08505480302d0079003251800d45501d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655183471 1250 655182221 655182223
    0x1101050d060e10030b0c090d02130b0414010302040b0a0b0f0a030b060d15120507150c15150503060903090d05121804050603030a14090103022205040b09070e01051605 73
    0x3038003c28480b00002502071440c6051030149030000c01c8000705640500c506212601c42c200040c51281c1c0c11560000080c0e07500d455080204403024442e60f006080210114000b001a00400e068a00a6a0603c12a00002c0600c207000d841442a500c860608120141c00d440c00e2074047d0482c7e2015103800304a000c1d655000910b00d40000c260a50f1390f070303030341e8884020492030600700c14020940c100c0002001496a00d074a0389450f824450700101d100700300342201e4240d00c00d6403c8083d8660106030340751031a842191000040025242503402c003103010f1004200c0b0716002440c05d1040c44020021498210032005010b0711a0055070301300c075a44594201c1d042d0301c00900001d880448000d4038500020803005c02007005907200a811213000f40c00400240d2032a0350700c8418020a500721104031a540d0244200480080c4541c90010762003000901c0da00380c0e1300036280d0101d4102ca9048500340700b452a5441007188221040d00d55074040780c1c804034660241e5002c3e00c0a41130000e20b0107a02c408480d01600c8003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655184721 1250 655183471 655183499
    0xb01110a031b0605160305010f0807051306080a0c0303081b031302041829160305060604050301060305070e1005033304120906090605041e2412091101050d06 69
    0x19a10420740008500038291b81480f841740108040380d0600151842c04255589441c6540141d50040015411012520500703404c072000030b0100c1000c6442040c00380c280300e03521140038001100098464030214001c42442004036482100c0380088a00e1922000d1100128200041d0202c2e0003640700c0f0a0321003814010090303a82c0c400e020706d010380015402d0b0284034010705080500c0050029211040c840074100c80c0b501d41001b400b00c0c0c14001070350b407600d500160207401070b548056490740c01c0c60008010890049800804c480e41e40c0000000381e1580d58280e0300a4a40d80161030b0540d2026100142143d4410b003500710490540c07912b0528800c540c1c1c0b01d000f540c00c0445099401034203c0e042c0c3c4903d90f62145955005112624003052081c0c1407800090652050740718008110400d454150441400200c0d043c4c001c00b000c0900b48851000846c071848002044104040498075851600300405514007d1010440d445200c50b40c00c10b00c1c0b030005540760b070440500340c00c40702c3d41d907100800c0080c0041c80e6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655185971 1250 655184721 655184731
    0x1c171314031207031d030303160507050a0c0609032d08210c030f070f020d0e01170708060a1d0a0f0b0d03030203011701290102032b0b01110a031b0605 66
    0x18400c078012511040500e035144045c48034000d0b4010010403a03103c44d4003110440c4801e2a240103a500c1c1c04a0070458a418000c82025015051510b0001902c4c0d8001e04840c04881c031840070b040f0409586440141e10349111540548540002500040000d909400800b01200d001000c24450100404401e400303030300c01c442c5489105030000c107008400c02c5401001d50311840c946880c12526205500007901c07126143c40c00810721007110104101607000d00c000440541c8c20741d13902c10843c94282801415000107952140c007031244000042603c001600720b1780c18401c0441040b80300c0351140004200201280410040d041343c0c0c41901ea50903590310400201c00d103000b95400768803175061500122250240d0003a4881c160315080c0c640368800000c03640202200300c0b042400b0882441000140d05510404002c15014200f000e003483c81d040d000b00680801400b803810402400c03d1080040d00c1c0014104c02d20341095002000c140002031080c402303170344184940703000d42a00080e81d030f8540e0150760b000c0d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655187221 1250 655185971 655185977
    0xd050403020c0a15092108030405100501060503010b0a120e01021c0b010306050f04020a020115080d0e120c0d02040b030d020105010e06040506150f07021c17131403120703 75
    0x5942c1c1d800740b030100c0114000c0c1c2405803010326400710450300a404041e20740705040e060b6642d0180e890984a83c00080b00074241c02a41c01c03660307407500703140c080e440f0115041514047c03803900c0c00104d40a0b225006481c180c07852400310500d412001003081e22013800c0120381d01603841e240c420032a15204203001821768558240c0d41040034100740350002003034413000340e8024105481d246d0104802c0d611070042d10b091410075030300143d861304540403ca0241140e02021809403004c20381c0001d200d10006541c210020303107036503050329171080c1ca002c1045441d01008880150741c40b10103884030350b2400031000c510084c030040000136864000b04c086800c0c0080c0c903040c50050b0759128010803070158016111688920304031805c00051500c1ca0000d0a10082d0035612846000701040b10544811000200c41c001f64000341507004410400e407104400400c2c20303008580c4a082c0e00c0c0707442150003460341a20002c00b00b034803070020b18a062402000c112403035040901d9251140f0f0001500f45d50310341c401411542c1c0296 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655188471 1250 655187221 655187233
    0x806090d0315440a06020915070f1502090603010501110a0b01080f0708010603020102030a08040f052e0626070e07020706021204051c02040b040e030c010e060405060412050d05040302 80
    0x28981055210342c0b00c3e1092240440d00702c5841910b4000310700003001171380c0a4401a02e41d00c03030001003040c00c00800381c405030103900001c5480c240701d0050146a18148651041d03144040c00c92549405d90041000c5160042d200303100601a56006a40c500070341c02c0382c401242c02c4d5022680341c035041c40c2004c0e44802c8407500041303481e0086000c00d11000b006002da400081c070403079280d0342c0001e58900c611490201003222a9020408100c000300c04515441d070088101c03403803c40011000980d400a142034229032149180d80d0070b054103414040c0400303c842d85a8000d2101070280c482101000b048451a4428003c6510126030321001d00642405020300f42c0c000e0180c2400d084003e0b00c0c1c0007003a1802c0300450000d0000704400e50f031700e1000c0014114200c6407807844104520200700940800f030f00b41c2d68001c3c245411007180300c1c00000501301c2651203000a00c00d07c044114502e40300c410a4401401681001300068081422044160021616441d2461400000305141d2040b500250360441c01a001070b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655189721 1250 655188471 655188539
    0x212011b1d01020304050d0b07021e0606041a0a051014070b330d080f12070e0634120504090614241c0b09010806090d0315 54
    0x1400c0e081c21150280001c42c40c040c1080300241c40c0c40311500000348418410800100254030030301559400700042c6146c81880d061050708191030b100221401401149041507a0f400b0001c1003100c444098005442407188038145000d000441d02010885000c1c07010092003e4a00c4c03080000600e213040c01840003940604014a604404252102d07000b04044002010070072040c044032925450700e01c04a941549010480c5020005c030b00a070f441c201042100450300d0078800c401105114400c1216541e0088048060020000b5501409482002c09008018582c03c0c0c1c029100111003920121f801c2d9041c600d000d03546030541d140081030a04002200070808000500182c0244005003001b61640c0402c4994134000c2089c85803d6074030040ba0854040341003c800c2141421103452550940d00c1181c180d01940d03055000e0007440d40118001c4082130000617840340701089481c0201c1124003e03000010300c0341d008030050444c0d1700d69501110301038400065803c00507201408028043c07002c2022000007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655190971 1250 655189721 655189757
    0x80103111014070503070605061912020a03020405010905060102010606030e0c0409060906060f06080a090308040b10090e0102180603011203350711070303050d0c020c0303030406090b090c09040212011b 88
    0x14150300d000324ac90000034040d12103800e03800c50990302043c40381e100b00741c060f00014584244660001e5006440c103800800c0d112020f82115114039000c2e002401040d540d45000c130100c400c203e8108082d50060240b01600f4a410380000c50031034000c0001240040c05616014202d6500b5808008924041d1004018044e0885180c80e40400605010011000991005044414002e20013409448420009295001a010080064050131004101604d00c0b541124000d60044182c004056100708011003d860442c08a034107036807a403d040c4c14116180d40d800c5e00c070603104c120141e90f01e02c0302d44140c0c00380c4038411510321440c0781701c00000005410942d501900c9006100941a2903810941d02070000c01e070440c04075564411980f20019100d110000c2c1281800000310130507515000c00428401070010507009034081500400c180000b9072070301740c01d103650f40660900031130308414150b0002c0c02514000b5061000703605900008550210b051009400200c00504070102041902c0ca030103062803a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655192221 1250 655190971 655190981
    0x151e070503211008070308030c070f0c2d0902090604091107021c0c05010f1115060a061107050f0609030303071d040204062a1b0608070801031110140705030706 70
    0x1481075070040f25400c018400b51103241501010300003001c0013022a00120509080f00c03d55900452552902480c600c2c0202480d00c4900c20740c02c031140702154480205508000e5081d0410b1503d600c240404c1c50408004017a4003d2100d080c0c0c086014071000605c45424014000e0302541003040719a02c1c940c1d4410800500b6040340c2c2c60500814404002c40010a1008200700b074074000d0030a86c00d4805001412a2203503590106065580640e08895880c0e08040f24814010036080361034454403615440c00700c40042103001c15502c640e000f66010445402e246803804440d00000e02054603204d0f498000c41d1450340300b40c0d8290005039000d00d09040e030000340325012030820070446003540b40030724000c801049005d06410704c00e101011a5101005000119404503440e43d02030702018498406044204503411148906408261a003001910091146030039078142c1e940300c402204e440b5280020301a61801c6100008180707d2a1052103268681c014041c0013100c0c407900003540d507030b4082c0c507003002691 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655193471 1250 655192221 655192231
    0x215040501030c110d03110c010c110d020303060a14061306110c370e04030503040308072f0c06030109020a02011107020114070302011b0504090506151e07050321 71
    0x900c4515031300d400030124084200004520740840c420750000d41d02003007840341d07a03d40c0300c00390319003200390002d0342e00300901c900c6501c82442507801c040c50044003a031b1284800c886666000300c02c1c900074010240c00c0c0b00313404401c020242c80300d4280380402465070190074840c0c11400201d01c0c1c1c07206806241004000200e00f903142643c6001c44514400c07080ca080d0100312f004041040321070305a4043c010300341e186910003400c08040c0b028541c00e0074280030b4000d81c42520242c0010f01594001000b4600403101d1800f0203c7c88281c03503600130030b403001e130b503d0a0290760310303020040c042c6c1d0a0402c110f540e514051406070940010060b5142d01c5800040d0840750140c441154442081c000c100243c0e800000c1c00854588210846541c3d03881d620b0124010702d0f5590408001c0c4050900c8004090742c08001350042e0303a41100d08102c0d640742d540401c010b900024032003001c03c0790208105100c8200303541c2c1c0c007413881090034086410004190740e0039045400c03014030007400e410606c07410f0394100d8644044c99001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655194721 1250 655193471 655193477
    0x30f0f160f0e0d02090a02090a0e0103080313150c0e03010c0e0f01031d01090c0914090606010302090d0209093007060b0604051f110d0801170a0215040501030c 70
    0x54416001070000c030404030300d2405001200251200d40e4075400c070114a8603a00416040091030894540b50094002c0c2c40d4007070103003c03001e0020031558120240b590503070f27405c1000a82143e80b58030324545600d4000c80100c6490683c83c2e100d240f5041c46002d2008452904d855100b01c22140c1070034942182d5852860104102034101c040d00743d5181d217580812000b400b807034042502155038405000f441e45051142031158a0b100c604401d0088210889050385e20b40e01d8240054030703051090010381d950a076a484580c1e00843e01080003503000394000c0c05140005041040c240ca1030303070005172803850100e608540b5904901d0001c8024010240010004041d40c0d01100c211040caa103481010b00490000608e0703584d8450391218140e60781c0d02510000c0c80000d11801c44101c4000449510798165100d03d00801c9080c0340d03102000001040680007041c0503980c3c0001d981c07038540d81d9007100c1c01312504059a801041215070140e09c90a0310841507141201003c1d6450745044001802c036603c1d407540c0360070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655195971 1250 655194721 655194751
    0xf030102040302011b03050715020703140316030510120822030305070b0c040905010306020a030e240613020a020d0f08010b0415030b0a0609081908070b0c0906030f0f 73
    0x41c0c0c0c12000302e800f5201040008545040c5e1464190b40d50b05c01c01d140940b48110740c1c00c1d40c0f42c2e040340603001410502d1081c0d0b1006054085020b072420140400d544c203105000f0000300500d5100c0c484c0c2c0c0700d01e50242c40480000301d00381d81d45c0c8061f410040b003854180d88603e00082c40e010400f604007216034003803107900280010245181c400902501443e0402407068038444045580c0030120811345002d17000e90300d8104015656450b2441c02075000c8903902000c03a052a404010043c0d000c14500c8400e808603900b14041c4031071244040705090000c100c10f6000150101401e00310a59101404510b80c564009180c0e80608079005880c0b0080700004104100541005000005c00c4100303503011160440ba101007515003612044d80a01031048440b60420744402c00015055400076004084491050030354080b5060f11130040d2050140e440040c050350000c106190000b80359050340d0703500c025282c400d40d0030001d41c00f000409923802078600f403c10813501d500340705000c5003201e0042e03001503c214074148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655197221 1250 655195971 655195973
    0x4080a0618051905010b030d080109140f070e120102070305091201050702191e0b1b07020a03020d03051e070308090619051801050108070f0f081506121009020f0301020403 75
    0x5501c003441e203c1d5038a0b40c00d1840c40c0d0300400209401100c90100c000301580c401080c242070003801c41d602441a2940c56040952452070507402d00d2100340118210031040031030360748024081d180768440007400303034000381c5411691b0103842c020710180c07101c82e2180d0750300703030707803480340c04104503004068403110a16070345480c05200240d034001440707118115180c1500020f052640c180203401c41c1400640032042c01a4022000c1044601c10300e140c030030f41100d9903680c506120b015041042e80522180250800c0c51441d06101520301100e0541080344207240c201e183c220010603020807401012400110860041a11000c154100c5e180740c0c0e000030a90000c112900d45001c0050051044c214201400c903610408500c00c0c0560002c8a404070005e01300031f01a039652101c94555482c01c512803000c1e040c4480c017020542000519201d4125110400180700d1910b6251004800c0720024003e5a0702c510a480801060341090000c90381c4043c2c2003400083c0f50416005004107001c0c40160389109034070400040c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655198471 1250 655197221 655197223
    0x30c0b130b1602090c090603040b0f010f050307050909070b0406030e06240d140111031e040201121121060a0611030d180206031311090c0f070203010603060204080a061805 75
    0x2030b401901102c006480381c8900c3c40064803407050020b902d4000400108020500c901ca4a840e400780c014406210400e81e80c4008a20078496980602903050b0490790040102e45000c000047e041501c420603144015940e019240c050f0340207501c83c01c042900c5103801e448100045c42001d40c001c040a0300101c107002c280b020700d144112540303141c921510020810405201c160f40030400e80112140c003c104400d1002d12078a100c2e0422908122180b444003407412280340d409141a01172541030f1546482c1090340030300103000e0f22060006418086081c002d140401da1a068044030043d04000703101d049003860018401c010a807600b141062054640403820490b0000084070115020060b00181d05100701c0c1068540c02501b010180d404600071091282070190648a07060307051103050000c591421980902c403034540c04540d603110200c01841095124000500142106407000b00009000341e229960740b0104d800540001c42aa0310051007442000002c1c4500045a414598608002800c80c0c1c0d480e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655199721 1250 655198471 655198507
    0x507020613032313031b1a0c0a05031902010c110d0c0203031b1e0c13111201030507060f05130303200106061d0d020906100207030c0b130b 61
    0x804024072800f4218101840564004000c401c0341103890b0b40d03908005884089046a0100b514685241c3c00000701c014200f0440030101d940744d108060700032611019410342c540044010300c2032230103283d0311000010000c0c8000e08081d44241140491000d500c68001d0860386c15100000900034072900104001000181d03480305945145042a040180c610110b425402441e03000c1c00e440300c000c0b006a90303086010850052078203500762016000b08040841540d01c00118100c1c5030402440c0c04482c1c12310013144c012402300071888281320320301071864100c1c9455600c240d0055400f40c000340018020603034400c100050010441c83c103582800c802c0e11240c07000e500350744002001c1c020328681041c50000343e0649010000c04c41c070000c101c150f036150809006480594440c03410070700c000400440c1880c1000c80600c5080d00a80041016905c0c0000d015501642d01c071014154032030702c2c2d0000000713508100458003801d5941031403504c800200061a440e900603810502e40c1e0101402094071101e002c10403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655200971 1250 655199721 655199723
    0xf04050601090e01020c0303010902071a04031d0d050d03060501180b0417011e0605040f0212150103021b0c100c080f13050a0311010810080d03020706022b0507020613 73
    0x14a10b03104442c0f0600905c518098904540030210001a001482c0c2e4064002c080c040d019030004800c0c030100c4401c503500c0480d40203010810721004000d005000310104003107031700050302d9070354200ca15850301c81c50403070103100302d20010351642000c3c0030559000100486001322284420092411302051401038000e601480b14440b00a502d1580c1c181025009082d48a01c440401c00140c0c0203240304c034014122a000c0c1d54025820140008c13001140c83c421544c4480c0d030040e001501d82c82c1d4101e440400940041c0e624101502404040403141495440c09211400b0030001e00c0d4031305804d810301030b1204a002a000502000d41d80c0c1001142007581110075034170500400565403030604c81014040007054204c2c64101c14187c401100300800c0740c44052601c0000d8880000c03c0e40c428000000072440c0c0d0240070126004032406402d254041d40240030840d2080d4005800c00c0003403481603401ca240a4040d8252608040720620302d11941d204040d0000240d101034245071501d910384021034250600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655202221 1250 655200971 655200989
    0x1703090c0a14010e0301061203120507050a0504060804050106030b0901020a1412011502210a180602030d1d032803142e1e06091d1003050f060f0f04050601 68
    0x4e1101c64503503003035000001800e100000c000a40d10b050800920b00e000f800e1200390507915050208000d00e0062041d80da07403000595825103054181181101c030114068003c642c0340d9296500403000480c00350303045104103903d200040c0c8900c00740700c000300340040a034100c81d5000c03410030054264070315043c200741c10740e0142a00b801c00e00c5e861034030803454418030a40c403403414030403101072117803404101008081c8200d4640d2071144d042e80140d4a03100300541489010301580c8100400d002a10703064002000003140303091030341d00c0c8003c01c1c040b4604642c80540c00c9499100d444244000c41980d00078a000c106800c1d203001c100d040d5440d03090704003103200a030820b014900f818040018444024074403105860b04800e505140b16681c02c43e00311241d520b0520070740000c0361804049202807282d5a00300c00c540c0ca0b80b01c01030560b4951002c80200303c402074840058188c0b540008004110f0811500c1038100a50300209580d203400360561010660107000c040071102800184004140c00254450550b40508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655203471 1250 655202221 655202237
    0xa1404090c08010f0f0b180f15060c160b0f0409090807080a11060105040207110415080f0c0f040b03031c06170303040c06111213031703090c0a1401 65
    0x708103906116150307401240d0a41c28506060f036034840355005400c01240402e414000b80011408000f244a0b40d00b810300103207401d4a000500346800041e60365044008044451403681121001c21b005601108155006e0707408440c5041c5507a00210240c4010040b4032401030070201000306292803071042d4840e020455880c0c402000a00001c501245c5040e1390155480d84d0380d5259110181c403040c210542403085002d07000000ad080e05060080f10035850703008a058904017000020080145042e91301c0c0240400c10900c0440c0d1000c0400c081794441c08540000c01d620345102041115402e0704c940300034052170410b007401c42d50381c80000a40d206401c41e403645141e03042842e036040d4014205540a904000c01880c0e49000b8140c01000a5004038002d1750070f4031106403202070950700c0c0707141120b8a02031079000302c003940050301701c10307000e005480c10040100d11a20343d0f0382c50300034017840c45004c3d40d08402d00000a00840140811030b103040460242da840c1601c500d00300b6980300c580b0854114a051240503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655204721 1250 655203471 655203473
    0x7082502010f081b0705010920060d091401140f0c0f07060b04110a05070203010e010605090105101116090c03110d090809030609060402011101110304020607081309020a0e0a140409 79
    0x144400055040c04c14900a445100c103003046806400203070000e503120760070b42295100100300d04d00c1c2c0c0244480054016481c2007107491184008106904040d00c000c0c3c01c40e007003c80444001c0c000c17080d41b621036401e0b500080c01c0c800b080c00400c14014084400c0c0031420003203143c40e014040d0540d00d10310740180000510002d00004140a8902c1860358120300c500040e04402540d00400503085150094008001500d4480740c440c1c02c07900e07d0b0182d10f90110380e00004005c3d40c0340c101d0a102102600d4501070642e5034041e0b045500e42000312000e407150009c1c0f18800c1c41202120301c101210300f80c03070749024001e040388072564483c20712440b0380381480c180e1100b0440041c88a560112004054003800b00c580c10f14014110584031710050314100c2c000b681d00d01e50600b10080501948092000d407030312451454459a0030090642d0001038122880340b0140070003d200100011014001e045004004d43e4030381e0b800c04000e1010950012103440343c000000300344500d01002c0d9204100d9002940d00090340d01c0340d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655205971 1250 655204721 655204741
    0x10603050910090503030108160302300307063c0510080f0721080301050d031b11010206100f05060d02130308090f0402210709080307082502010f08 65
    0xc2e2203a00407041c20601803004000300000214101e41c1840b0540e5410140b80342480c1e907040c071521001e544000c1c00d0302c0c1c2e807400d202d0740185400159080f030034041802e040b042c501811500422010b85540381e40c1c441d03040c0c900008600c0c4140c4198105c5441740107000d4a2401005c0203d9450fa54008559071070000d49031200c9800804044c05821040350508220049069035405603801101c1c94105486400d150a0030079078401e8121542c06041d96080d03030300301400e002c0b540003000313800d4040182400c80210048a070981102c5114081c00803094281c5100e0006440c01c0c40c00380c50742003180e11600040044030413071400202903c00c100d8040350b480c4051102000a03000d80d0004925010540d50000200600940141420802520404030b400d002c801044105c2c00f5a0f45085003501c2c1410040200342c500c45031403688011182440e4401c66100d4640c01e24542010004a0b5000400166140c2c145c0380d40380d000f0410515000140d62010503903000801c8500d540d41c014080c080624081140c03201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655207221 1250 655205971 655205983
    0x6050702181b040b0301050a05011e0507060209060d0b03162106020d060f081009030804080d0906020a050919240e09070e090906040309051e040f0902091e0106030509 73
    0xc2d0716000151a15141d0040e428164020302c83c040c800c55039a01c0000c0c05500466403900400c1001c1c0c503070b601d0300c3c8180d00191501ea0055504890403035007013054404544d1280050319030410303629400034030030500718285803404c00703902c09004582d10042007c0000442c40489100c3d01812815800180320252800d0300103805a5088460039606021002c2003084400391584110362001c030445000001d020010021103540d00c0c005000602c030780c00010046001c80c0000c02e04032200b40400103c040c200d4440e001240c01c80f195200c0042e80020384442e0614101c56008502c9480002603200c55181074031428041c610410940f411100a00d03000064501401404080e02c1018002201321300c0c05d20401040340c2c0da0403040501c56094607000c60100140040d050b403280d54581c55164041d81803508003c102142c5514035040040402c01c2c1c020680c07514080c010014130b0750503001c1404142c6204101d02421b00034921040700c6126a41c4020030600d2030503560444125042c001000d1311a00b02080c1844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655208471 1250 655207221 655207261
    0x105041d010504030f090e07050a140d110d1a0d1403120c031008161a2110080a0f260c160603150b03090712060e070605070218 56
    0x151a000803c814183c001c49030103002d01c0c580d65800c605507211285841c03455401d071584000594207002881c8060700071911804e14030440400182860901c04100065039424071010f000040085142c408455041c0160842c1c440501c54001541c041e4001007192240d40a1340500100c02e000b0171040c98840c03e0040f201a08180b180c140030b0392421242401140c3c1c004c2e00d9010380780d0f43ca01000140003d01041c8000c80c09800c03441904690300d4080c03040c0d12107107100f80107070408404001301e10060060f0800301ba000c603103815102d0034628040c91000c2c83c06405a104034003c0e008150a1800241d240703c4d00700c111a13102d251458461342110444642240b4500300a20645001500801822000800550720708900000c14082920742c6400c0f415103000340704141801c0c4c500441880b91a240e6005554008a080112040150b81c3c1e04084200d040c290707019507000350f407403030300c020044814040c40e13029090b5824460318010941d40824415040004c1c42465420a074001c2400c2d1410001d20040790 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655209721 1250 655208471 655208473
    0x7120c021b06030c0403020d0525080d0e04110a0206090c100207060c0f060c050306210c120309060406050d05011202091302010c0209070f030b0a03020d0b0c0702190303180305060105041d 82
    0x207125840c2270781e5200c0e00542c614200354103181b0f44000804900405200717690199014080e4403440040c2030721414150b04405030300c40c1c2c0782d4951800d041e03200c8020f801030383c03955130080c1645c2c10070924280c00c4c41d8001006174040e9110b4004095119000903995080f984030303290607000070700f0300d0509000203809120001e100d98181a180000c0300da2240207540100310844010111401e0030007011901c40d4a0840c0c0e603800d4000d41080d00c1c981c07400809200c4541d03861741c156032138036443c00c0002d07900758490f40060300400c0022603c102468400e20666016040c459070408440649400184401b840140800039000710308814004691240e41075450741503001d840750b0700904090380060403006040404030f0010b45019072142e07492a0106882c02100d40252000d01900701a8850112100000740500149075040201c40010385230302c2886034040804140054001d425454020300c1c02d560041d003464403088250050011500120f580c078112441203400180f401031040c078621201d0310110b541652 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655210971 1250 655209721 655209739
    0x20903070620011a040c020106050301110325050d0b1305010f090e0303150d1703040f15020901210609020403140f030703050403060c0c060507120c021b06030c040302 73
    0x125402503111004007145502100060848a6001d8220f031302600000380e0809a24400440c142810740c45929241980d02c0082103003916071003c2425039090f900e4000700a1400030401500d0340d540c48007002944134061182c03040d1070f80c2900017000c5020310f07040034078210340d00c540c1d040c103695a034240c40c04016544002488250b030360b03040d01450751303201d4071403070320014101484144c0c00140482203034821134407203903042e0400f00140c040c0110080003a4045860f181284040066412070314061032041b40300750484401e00085242c2818104420240056024014400c021484e07800c4803080103040120a40310048440003002c000c003500c840c2c1d000a1205100150100c1440381c00e200391103181c6c80c02400c80d0910b41c803444403182e03240302c0d440e030140000c0c0c0140410700006000790800c5c60b00e81410310b44040c1054054a4440840724240e40200200c0c45607040d03088000010f0190081d040110700107020349401e01840c0500c0c0700788403020148520000400910001e6030703041928003a54019101c01d403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655212221 1250 655210971 655210979
    0x105031509280c0306090b06160c030c081006050f0f010f02010f090f12020607140702030a060f1401050a0b041a0f070f030e15070b09010e0609010b1f0f0f0302090307 73
    0x20040064040e40800a4200240843c030041c1c07501034443e40e00340188c00c1d81e280010f018400d150714001041c08a6281c5c00002c00080400e01800c1140040c09a0001600122261000d5102201e801c0d900c581e01078010303032038032100c01d94440e0491100c0490030f00740000ca01c401020200d0051014911f62400640350211000c14416044074010803503128843c000a000301007042681e1700c3c41c0458003100003e1801c180400154041005411068030180480e4460000f5903542d400342c41c11144010b580a654240c0c581c14982c15a00003401000b054070542e10701401c0401d0310005210fa0302600720404508040e0042504071242240c40003240c403291241c80b195140b40060079100487c00130ba002550403800400686070103071105500c0022060641c1c6400b401e9603d10f640c40c0c0e0024030740000c9560b00c01e40041c40d00d4050240d244600c00c0c7d0400050901d0707111040024180f03e1328000001c06860005a0b0b6503030303402c0000c0262100c62810070707141d8207100d10f4080b0080d20070700d40f41d80e42500540e84005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655213471 1250 655212221 655212301
    0x909030e030d0905090a050c04060c06060b040605090316060203030a02090d0f03081915031203020d0f02090406061103030a0902060c030a0f1101091205130512060405010b0105031509 80
    0x1541c104440905d2142c81c0d0f404c0c608150384055494411882c2c0410003000210b00500404000e1885002e02040455952904201c590825480200810800103002000b8a001e00400340045000ca0b80c0d0800581083e6000b59280001480c3c40c00403503000503da00d013039036071401d02e10302c49501911800c1c1346522450002d114000995124481a40910350204001c5a50041d07148854603600c100d140d091464982c20440700c4a00c04200501d94200081ca4081c00c0c03d0052100388440c40002503550100001400101c40890344000704012a00c641100c1040c0040100c139002a2400e2022442080c0c5000154840c0700c0c0742d502640600c000202c0c80f05094001400040030801d070f0700c83e4100710024010b020309030341654100801385d404034244669200d0144002c0c08554540d1404100c41a44a1700070991400d51140101040c3d4000b804010412100f4003032021819400e20b03110381581081200a15507030143d401640c0309581210018018405d46041c4864120000d4441b00c40091244851 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655214721 1250 655213471 655213487
    0x30605090114060a1212092111030102070b040b0a02220e1b0703081506040905090c0a030b0106032d09050f1c030203060307050604080303011e06090909030e030d 71
    0x180c000c2c00a440001446441c11150100c2281d1078200e148039001e44590303464120841c821500300030320002460105401402001c1d01c14000052290101003101505045944c8014010568403981c0100a000000b038a29940180c210794000c0c01d0003c19180c040b00800070b405002c0d90b42c100030749154603149032204001c81c0380301200c142c110640503a07103510000200401104d044c20b245040c0c10070800000134030501c45140c0c4044620254003a84d100d0300c0c005100f550180d88494030311a121018411050710910802022031781c106c0b01100c40c2e500d15074a1250200b0f05105003018540c1c0e82201c0101e6060660410746160318004c082500c80200c90101c000401e1214000c2d150713480791b008201020100000d040c48006400d0750060f8460300c0c54001200698002840302d6051701030520001100d8440c503010300043c06090029503140c5d07051403006d854806165083c1140080100003c01c80039420843c14001d4480d0103134081040c0200d405d0070795039040c100c001d0a40500c00e10000303040050b400202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655215827 1106 655214721 655214741
    0x5010905010e0d061e02070c050420070602070803010308041d070806041a04060b0a1116050f0103020909190e070302090601110f0d02030304020f01052b02040306050901 74
    0x210b17200c540c14018020340c07a55004a20801000186103805c40a040196420000b28a5007403000100300c0e007204d403282d901d005c0000c1c41c105002250701241c2d049078125089a5807540e6a141111465005200e90404014078110390b8608511600c1100c1c00346240c0c0d510100c0390b40350b00b020400148031030443e942107001050003e06a80d02e0714061400240760183c24551922440e0070041c25044c85101001140e4104c14440922048a02946829110305407a070100501040005800a1041c020310543c00740e1428200700e5017101c140d101030b6000160711b00030701c12050316444803591803110780170003540720160b2000178445501c60b10451b824143c0f21422194031102c00b6104030704000c00452280c00513040001008150f0a0000311120440d0081c0780a9150141c80711100f60a54008444c01c444001005a8404088030780c1d0151809035400c050100054102800e6040c02400c1d1801 = true := by decide +kernel

theorem cover : BRFrame.Cov 655035971 655215827 := by
  have h0 := BRFrame.cov_init 655035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655035971 ≤ n) (h2 : n < 655215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
