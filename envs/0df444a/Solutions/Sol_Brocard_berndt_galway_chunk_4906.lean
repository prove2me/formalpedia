-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4906
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:07.30862+00:00
-- url     : https://prove2.me/submissions/7cab8a74-bd2e-42b6-a5c9-a5dcb8aa09b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882194244 ≤ n < 882374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882195494 1250 882194244 882194267
    0xb0a0914190b0904110a080f21040b0a030906020705032701030b0105030604111603050904050c04031509050304150201140f010510031e0c0c030e0603060a030201110f03070b0403 78
    0x1401403001d01e03014004610900409400288425400d6845c5500d5540d9080c0d00030207442d44e4401c440c880254001550703506d22088241b0200a03c101524481c140010800c032410f03520b45c86001880c1c0061220120020704c85000c0a817230065080c40b040c000240207000078051001d0041c0460030080e01c454a00b02140b03c0411054141880c1c040243c0d09660040c06881d0300000072a030002e00031609040403003151180c80c03ea404c410b42010900c004050700100a440c00010541e0200840e98800442da0341c248620701014021911141411040003170540002100e14401c00a5900707103582c92a03480180d101c103030b50010250751146144145140d100b218141d120495626078441545044049404108442003503400c15880d48841007074060803400c1d040050301d900d07008000c90b1002d10001011000d102c0d10460000e10546041000d501d054410359000724001004429898515030040da86030403035035030b401207502560380314443c2000c05002600401d40200b109003c1403400b85001002d512499 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882196744 1250 882195494 882195541
    0x1030e0601082d0a080319050c040315090501110d0e06010b19020a08040b0d0e0f2a04060308070b07030e060a090212011508012d0b0a0914 61
    0x4004104002c40050400c24000480101c0050007002d0002d80000d00300c2502006074901c0342d55000010080548002d41c4140c448841e04a1030b41901001003042da08156100302d100b4000b8002030002c11400810b803003150140040000d108210b66542c82d09407500c201404140c201d0114a40045805a000c0d1a00ca115020040d05041d8140341458007140500303203000800ca200c0c4003818810600800c140b020198001c580282c40700d54802100351581d01055044203441d0500e480081405000a11000c00c3c400100142c001c00f9104c20801040c0340010712042d03540c1c00c800c620b0120030388071446035402030760045a90f55900d880c58102080c106001801d03410400d450078100b820030000108407907420214400010440e414140001140a5158a468010f9510b820b40d0224032030702912424013140c0061009110031a0040801c05a8090162070050305142e20401c0740700b000c1d0070313034007203011600018100c03d900364a4210010484101e521b034104100d030310f6010700400302e00f503480c1d403200368140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882197994 1250 882196744 882196753
    0x1050111070e0c0c2b0f1e1d0901080102040515040308070b1914101406071202011d071d04022110090c15110303010e0903040f06030b01030e 62
    0x204002d442059400801c41080d0034004111410f0f0404140150448610840f40401150794551a080d0081541c1c0f0b84030720214101c107454901c1e450107040d1a011002d11001880904124950181c1d00201e000c004682091089100811075070b641e5030b54a03010701a6200010b0b240c6040100340710f412a05010034143c8040300b44020000140030004480d012076116180324207a45520343c40010b24280402c1d041c03000e5080001c4a040300d078035002091710a110101c1007070b6540c0d42c0c07a07051200034202907994a8002008001c40d1020410f15849900002102c1c0300000e01c91092164100846049010002090308400800c0000320799900340140c1d904488507070700300a810185e002401c514001e00038480040d00d9102000003203482803002c0c1d0340c0490f240c4400d004418951600c0044000b05010700d0800d110503c41c038900140c440c1030002c90f2260390000542c03079a428040d80750f120326030040210310940300c10003003c40c05400340c0151400074821030b100800e11b900c2a40002d81a116140c0380300225a01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882199244 1250 882197994 882197999
    0x30b010e0c03070c0302010b0d110a0f0b0d051e010b0711061c0906060e01080109050613050a0f050307020a060f020c030d0509012f07060f020a020d0210021c02060105011107 76
    0x10003044070381082c081d0501400035091445c041c1e0143c0003008078035600c00141803c90301840f2540e502c0c1015250200d03038a015054680116010f014124002c00320003020501403da40035416601250300f014070441c03807004001d810405207440d200242c2126030b02c0400400c096003004007001c0786c4030442a0407076803a800d152400c0d080c440402452840c8100042c2ca07020300606110076a408140500a545110500303583c50700200c9001e411030200031a418403490b00010117454200d840d0041d140c0c0c0c0700e005400071540c0740d00e45168100e5a103006070b40744d000420801006980f11600c1000402d000c1d111a412007a08101c06800d1541c01c60155000c1c1e04095208945141d02c102101ca1704e15017400d00c4950504484d100d540c203245040816080e42d441403c1c40034002a0020708003040b200c259039041c1420290120885e2203000300900203402141c8a0440300041c40c1000f0480c3c4a280c5030301c12182680301014000d02c0d131881030b001e0a0b000da04490018803580d60f0064905810511440c0100002031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882200494 1250 882199244 882199261
    0x909030203190306060e060307110a0503130e010e1621050604180b0a050c0f1602030c060708043b0709080a1106091c0503131205191515030b010e 64
    0x2c18501b5041c03140400000140440b4051120307801c951000500f2540164468603140750303a41c1c0300c602910014401311500040c80900384030668140c440d40d00c007441c8a5110640c1c001c444181c0900382205110084802a481800007541c6103c400001c1501081c9130a10005200454076038030a103240c04100e111040000c03c0c00c81c003a560b00a048a0320001e420340e9030340d20b0007506004914405003038180001d072080350440c0c01c2c50404d80e00ba00840036540c0c4c0d40484000c0050030310911800800360034040c0400c01031210781c0300000d100e141004180f11000441c035403040b6034206015032012440e00c003040a00020fa43d02010b00c1000d411890b008107569001a101c0c0501d90288804c014400c00d0005007005d0305464615801ca5958841c114001c4142450b06d051500c9820481c100c0316001c105c004001885411070095855582d04400a421110883c1c0d80c66007a203c261501907900b03030b840c01c2c01000e00245a1044030301000201384460200b0b401e5251600c00500107a000281244c1c4070400e001c08030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882201744 1250 882200494 882200507
    0x204050f090a11011b050106030506010b1614010603080c0a0c152705040507081603060e010e0a1d071e03030e0907180b091f050306040b0406090903020319030606 71
    0xc036000455890818003c000494001c03510a0003040c50540303140e2480108141504081d0070f4a01c1903054030107a81e00c9024000e05401030425103501c1641c0c40c80a203010405002a01103100601000071490648139215904d19511013412502140c2c813031240300301072122240d54500030f0400c0103540c408076082010000c040d000c00c0b40c0744810000d01900c0ca10314000c1c04502c043c004002c040c00c01d124600e4045405860100d04071024201014440b40c3d1039000c921030312960342550300c0c0190898090742840110044804014000440a5600d8104000c81c49003542c1c00950702c504c000082500e1402c1042201e203039088914000c441000c104010700009411207207a101d800d10903203030800350740e6070024101e5034200000811800800c0f002801b04a070340b043c100428031048143c0f501d0301d100c41d40c641404150303102d02003800c002030414000b14005181c913070002e5116030002071003c5441511807040804032056000100c0240e4000a440e1003039030316150800131560020305003000751600c1c114000d00103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882202994 1250 882201744 882201763
    0x506011404051c1505180c10080601120e011e151a0706060312200d0f051b010603060506031902040f020c1b030601090b0a150201110f070204050f09 65
    0xc0c00c03030040b41c64201c0c400303d1041d1100d5400c5501800c81d10708075030403440103080075211078141080941d0303c1d40c01150300007124031139850080c1403560b9200060b10112940307103015010070304102c85103268210f805541e01030303020b044176203000000d0011030790050718410500310340f038000c200c90402c1031103801d20b0300c080205402c51316a600340100e40d84210712011f50b580f2802c10010000380c0380000110902c620310350615000c14603a1125480b80e2003540742141c00c2d6a1048102405c0c0e840007441ca0784080c1309054401000c0010b007017007400d0202030324007404c001d505a088081569504c103020410b04c07034140174081e0044015000351641c010a0381d0102c4400d2380c4844003074051030300c0d100c80068aa503554103c3c1c070651803a100750f481c00840580541025802c0c0c910303044c400e114080000c0b41161603442883c5407460002e1407101c0c4149415010103140040070568404c0d03543c2c50b00020200748182000740a82d80555103800e95500c081e01c1080125040901000031840344182001728242c1c000941c003a8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882204244 1250 882202994 882202999
    0x110c010e060f090621010902030402031905070506072406050303070b10030b0a090303050a0b010c15020c1e0d0f1403150303041401030f14040206072f04050601140405 73
    0x41d281e009107244800b0f44900002c0c00e80107900002d000ca030000101c60703e4190f0000c9650266002c1c0d03030b40c051000c103070300003950040d5241d00040321004440b24590904009a031107030b4107071401150f5403070006e04a60004502665a008101c1c0d610142e01c0c080c0306032101c40e6040f1802041001d007004040b036941e026a00000b0000d503501004607041c42e2003007441400840c1d1145c2404a14989400084081c040a000480c0401e003040049505812140500b0284c05410794174804803d103152a2500a002e042d425205840e50810003285818001d0040d04003040303400d000c074540800c40740601481c00107103010280c20010741703200740c1040d84c1d4005041c00303030300704000d441039281d885828407483c503445105d01841d40b603c13001400080c2001c1e50b54bc107104000d0240c0301003050300c030680065010388495102e50b51800603188001030052810301d01401c0c0b0340f0b002d5841080c08880040f0001ca00c400024000404908e9821071a1003d142c070303001c3c00350700150a1900d184440b2019071800094016800b401e407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882205494 1250 882204244 882204247
    0x190207151503050c060a02032a030a0e04050709080d05160219060215101406090a2603070f0f0812070903140c030a110d0b0a0501080d0f0507060c0903120f110c010e06 73
    0x6627410302200365680300301c0c07524064940e22040603c1c0030307012601c0c034907105014508001c00a00c0aa0040781c00c0003c4801e501e01810020070b225201b1a6681c2c01200c04d100c0c41040340024a01580324000d1120114040c0307145c0c00e0b289030030403401a280003007044100e003060707203070034204003800c00c2040e10306046881ca10100c40740400d0410016015005002c0402c0e0400306031035000be00d801280c1c0b91800c2e403920744044072148050521005440344140f00001d002d9820702c4151380c0c0010b000e131139000d13110b5010310032035802c000742840f0002603004c0c1646c02200141100500b03100b80185044203501e421000d1f0020204106207401080c1c40c1d1507110009449840851041d040640354844424520707030703002211547d0340c41c2541203080140028000c41281384100c1094400c0d0303a0141e06010b095418644880e400c081407981d845018203647d01890080100c1c80c4400400a03e400e240d2000c29002c0b511540300e02280b4410040a03d103103011842210b5104622003842642c120b8a4580804010754845 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882206744 1250 882205494 882205537
    0x306240f0c02090a0605090907030c050d020a031734110102011d0304031514010b07050304030804091a030c060f07050115120506060108190207151503050c060a0203 72
    0x151892640414041d410003ca241000083c460a50001040c2e80040310742e5012078950381c0e0b4081e600c01035408024a4260202030a0016180c1055001d61061008200c0004141c980d40d031040510088109242201c901062001e80062841007071b100d011000d1405018858480d4900c0c064000b0004005c0c0113640341b500c109000764400e40020075101c400303c141070b2020003903007c2c0d07980d61780c028030080e82e034520304203511006910240504002c0d6401030140502c980d0901c41010015071045504481318403040100000003001c400c040d200500050000040644082c49284000c1b03000c01d01c50341c802d401020128600e43d4455058030305103010141d4580d01e9807200d00d055401400302c000360b08412007800030001545485041444d030349500c03520a490f01a1220001507560340380a40d090712008295020224001a03280d001e80107a46c0117182c076a20305c06846840078201c402c075114080f01149204002d1060040810003c040c915042e01c29070310700586401d00940340d024060b00e43c024002d00785481c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882207994 1250 882206744 882206747
    0xe011809050711011803110607140c0705030a0b0f131707080c0105100501020d082401212c030d0510080f0616050c10020c070909080a0306240f 63
    0x1c00f099000900002c0041c203e9038902400c0166240100324009130707011400c1c05003010082044c1d8094a11501c4264508101c0e00003c4200e41280080c07000070311a500000855950801c48040130310300440c8d00500030705100503404800e45c4004c18035450703005490720b5840014181035541c28418070210714a5201e034a980b038200028450700d2603c403581d6083c88188600300300104901400c9078000d8003101c410354001402a01d000c0000c0301c1c02046d180103005122054040541000c2140310149801c1c1c884158142d5402c3c0c01e000d0040f1802c240c26a01e8840160b0008903460600c8201c207002440c448040700300581598a126450624807250b4442021685004601103d5406030241005480c5250642a00150744080441b1074101742c92141720b00700712940c00b40e003c80e41c4180507440601505c03017050103c44080c2d070061960ba1101c2c07103644000980d01c0300512504000346d00c504e02042e500c00e54400000c5c04d58059030480d030070f14400e4400e140042c0888100700c1041400c079042280050310580c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882209244 1250 882207994 882208007
    0x1206101802071106030c0702060720010807141e0c010501080c1c1e0503040b07020415240e1203041e0b0706090503041508040605181002030603031b06070e0118090507 73
    0xb4000d400c24008034202b030400c400c1e13201c008490b84500444030b01070600000115102081a0f070904045224080740c1c60003464070070020000e000030302c01e01c0c10b41c8081e43e0b094050190b001c11400b0413141d64400041c04928810b00c201250401d04445071b214003c03001844181000d600d4a000300b601c10503171050701002d11403212600c401e6401c0801d590710b440d48c52206440b80e601854049200c2ea00e00646410805032040c00c80e420780744110b480350926907044090009120300e400b80c8005104801c000c0310308541c1c0d0705c2d503001d010f41b031010701641e103652070204c1d440b0001c0d0406210016030040481c040c444400844160380c505a04070070b000c2042c400d5030a040d130071403040303401001d001d900e9000707040400c681100006000754812442008103655018045165040900c001c407a0f030342024110810324400758001c3c5420210007010f82e880e01c1c00c00c282c0c1c1100007a002050340d4898028608120307019411540083c2c0340070084c201701c2401c072114400e94803000103e00170501941c1e610800314040a11504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882210494 1250 882209244 882209257
    0x402400c0225030605070c11060304080306090603010e07120212060606030c070309031209080c01020c09180f19030206010602010509030d050a0b090901020d0f020f0403030804021206101802071106030c 88
    0x13030003004203040580c070040c000040a9020b032031044808001e00190304080c0101c9200d5604030200c0341c02d548401082002607400580001c0d415900c0719000c0440c10002c0c001000103043d038603544d4011a04074414480c00c1c681d2880f41c1c0342e45800c01c104000441d10380008595011032a040d9280d56202645016074165a0300d400191a119103ea154042d040c0c100380544c00703036580782e0100e40310140c4200049039503280c05100c0980081302c01e40400d50700c0c0f0310300304980c0e000d1035030702d0039200354030103440f03031a46050003080707042c00281a20302c20078041c980c05010070350241c10b142c4005c1c0820701d04108102d43e80c0c4150203000740025542c20020384500c0442e8000403041d80002e00c188444c4c10308817081d0f4040e4101d5207000042510b0000d0700c01410300c40b44201e0301c003000301041c0603040c1859502c0548001000034400da80250701c7c22403020680b00140105132040ccc24004e0900706c0c450610300101407100b9a109220706691040018030003140200910402c07400c03040301c0066880c1e4804211001d2800b805 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882211744 1250 882210494 882210503
    0x916031214120a021c020c1f0e0f0d0e0904030c0308041103010c02070f120b010302120a05060f01090c0903051c031b05030f1b0301030b0402400c022503 67
    0x5060025a903004e800403c0c01182e03024410140c15a240000d40032440b414854128a61021000c0891108904c507500d411100e60340000400c240c00c4224a401d144c42c5241c2c10020703411150206175200d401292201003440c0650316802240341982d00a0103c0341c90361009400c1c00f0082000400700700758124044003400c0040c0013400201e800c0300e000307942c07001e60740100c1c023202c5406900421101888c02610580640107030030070b04903074655028040030f00da985030103490078001c0061080108030208580303405007088179561a00756140070301480440b5201400e01c010403040b114100b022890024080e0303820104036102844100b0f20250580c014039207071850740710410b0034542c24031a0035000405984212403120030300d042d551720044101c00e009c0d480c010114210605000501c0841e961840d0550300610190824003044210301090451110000c94000d88803913100e00821886085e404441c440085902c0c02d21400700c44a202944030000800c40004041962000c0c0e584401c020503100000c40d0031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882212994 1250 882211744 882211777
    0x405090c1513030c180e16050f13050f0907060f1706010905120f01050f0105211203040b01050f1005090d11041b090b1206040b010c050111030916031214 67
    0x6468070001100b0522007030244040c40d0191401b40c808000c64942d5041c4a100e10300100b6901340001c00c00c1c203480d41900260004001c41c800b1a01030110321646018842280f03141e4402e180c17186000e450a03146402c00b100f0400510389460580340c1000c1c0e44da0034206489001503031070f950303000122100b0304c40341c0c065a444003007031148454507480810580021820344000740500c0c2e588107000c8000b00030a101e0307580c20017401e00f480c11029019008850709400000309a440e82c0e400d8900c90b4400c0e030001d40b02502d010100304010011464030340880903034501c1c00e0f100e101160700700c0000070b040381c0034129105e0701801d000350f080010058103034100d51843da0010020050141081c9510003404030700f80c400710105010910116000c02c040c0c1c00c1e140301f1407607d4102045992580180005055128210b6050001448000000840c00c0c01016209440089101e44a1400701c00c65440c04003009265288485055030074804034400c018010903c0e65141803034002202001c01c0d11a070342c840d08a0398215401d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882214244 1250 882212994 882212999
    0x80a030b1906410901110708061b16230a022101020702060d020306040c02070305060c0f0f0a0807030506041401030f0807080c1c03020414010807030612030903020405090c1513030c 79
    0xb6484040c04c2014000e0b42c496060200c40081c00740c0d501c07260f024034a00740d40180b0000d00300c0483c1c00d081e44000320005007041e082201c40c803002d000302a02c1003000c50f60040100702660300004e04520b0100403900000c01070041100e00d8002c284a9000e188ac03488202c41d020089540c102025011600e286a01804503542d035140f641910300250020f42d017070f5200f1420031640340045440000c260042d6504680600f4250701d54102030100c640c002c0344003034101e0f02c00780110400d81e2120b1020304083d40464440d00507624165100034201d84c00180014444e500c0c0c0b8282410080503000000d042d01e502401c3d0381c0034102c00e0301704044d060044410090203001c0001c3d45001211021464810702c800e40c4122181c03540d044402a02640a01d00030070604031007043d450300d003e40c8243c401c00c0e042941420000f55803a1900303c3d4030803c03d01300e02c0980c00701da1036490410860501c2e2007400c4e40154000040d041c1801c6842c0001c00d060400e40d040d8040e03040100380c107032001c107550707440d40c0007558014a00c03010940e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882215494 1250 882214244 882214367
    0x120213020f07060c05300f04051020160b09010c0e150d11130510270e07021b042021070e10020a0528080a030b1906 51
    0xd9100c074450201041b1404200c0802034201c80038005e0b580203024050f02401401003800a0448103113040701146003a01550310840c14000428110301030000e982103906190030001c101c030340040e0140308640c1c901000c844195501c07540c000302c01402145c101c40d02d0908050030706414080e408000c08400e20306015a02c0389001e2000500c01180c4101d00c8140c41d035903034420081c44912114140d00450a0082c202107100042c54020000712014030550502540310300c50348241140c01c845200240e800f00c030800c2140041560712444411049400780074000c1d6044913061910000032a511400d440443c10a1002501134641241f002c03003408030500e07e2504a000408602d254008103003d40c4982c150580340920206018442c031350410020220200703100c84001e110210340d80c0e860108005000300f0000030318590000c1204c12515075010440e010104100010208016191124840c03203c10422010340c0ac401140300d283c2c060b041c1155041540082019100d1460342c0d2440c1d01c071340940301a07034042d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882216744 1250 882215494 882215557
    0x10f0e010b1305271e070503150c040b0a1b03090e06040213032d05071d1501050a030f050a200703140f13120213020f07060c05 56
    0xd4021281c015084500442d032000700c40040c0c5144400c0c072410078504420060203903034000c850140900b00c900300001d80a40f001e81c0702c00c400d071103241c607081140b007040b4a1904010345004230861f40c0e8100c0b240c1c20301810140c0248164031540e920200c02049166000c0d000c0d41018001c01003011900d101840c0f58035000f000550039000ea0442041144042030301ca00b843d1082c2ca602d140c0c240c081c014a603086450b4612010b462440740310203104c8044c1c0300b4261b210f840b4480540c1074802d100410120342000b00000146084200d0b0f180540d460204100020f0044141e10b0040482800d00c0d6a8030b64150104602600540b1603100702d04c0d0030182444810f502c280e01c4200007546084003480f08051106550710f10748240c5030041e0010b40c00d41e2401260100c150010102c0c4031031180c5440c64142412610400e541503980241c4900b2940d400c03160543c01c00d0300f2490312140e00d42600b10b00e4400781040c662000d0250703050240440da910800c13400700c14003c01c11100005044003903616180600019800368 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882217994 1250 882216744 882216761
    0x6070c0c06090b09090606040f0e04050d0206040503120403170c031006050a0c03050f090a0305100b09061e04150906060e0f0102060f0c040e07030c0e09101502010f0e01 74
    0x345100000009030480c4988201e5007030701c0c0102000ea1030311342120304004680382c0181590758006400c01001941d41540d0b0340031001402c020b0541c5400e031800707040c042d0800540400000035504050b0402c0000364001c0101c603507000d905040d0400c0ea459509044545515990040ca90300703034010b042c0294101000061071084008041040b105034845038100c402e0f025580d541004100e121020f440040d004901810202c410f509916080110103400284681140c7d40103484682100310500d00b0b282480c01040800c2e0001d4401d0000c07804d000c000300310b80b402d4500f072120210010001c10080d80e5169086140000f03c4071502030f8125807140203100c0180014802c00c1c000c1891402902e0701410030000280850314141c001d00000d550b50380710782e41c9104000342094010b040800c404a4448490300e00030740904059500050040080301000d003102c481041034910801c0d01c0801c005a5000840803401680c0c104c0a40580285c0e02d41e1043e0f0151903c041c402d415581010f03015030301d440301580310465 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882219244 1250 882217994 882218003
    0xf091906120311010e0a230c13050714090901090e0a0609200a0b040b0322050309011d0d150b0405040809150c07050d0f05010c081006091d0405070806070c 68
    0x1011098084541d10074103103c00500c4c0c000310704e070b0301c0042c7d90003440c0381801c14824000b5510074041c00e500007100000c60144c054442d40e5950300303101ea0035501c544800d48904008542918003d280c1000030b02d0004140300c1d01c9210382d00e401d1150f440007001e000744942c0716032006083c40390301e40c41d10704a440c660503134181c80001102e0504081c503074a04100b14030b0840e5500507005240c58201900345009500c020f09000c541c040d64080409241b0409166540042c06035000e1a01c54000e440010103d012400104000d4a802131031003140d540c84962201105900046c07441815540801280103031502e64101c2c5d6100d03142c08208024003c11701e0007400555021620303941c5258a070a4280300354080c060300a500e90703014200030310042c24119440000c1c20702802c111400c13489a0754581e42500c4000340c0400001d0310000a00032010b101d1003442016054500b00500c140d4101801e0300c062503481c11074108110441e00c0414240802440a00e01922030b000544800b8949404050103c0309030a00845 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882220494 1250 882219244 882219251
    0xc0108070c0807140a12050406020c010927380603070906050f0409061e0e0105100c02060f0301080a032a151e090606050f09190612031101 61
    0xc0d00540704601581d80a54411946418048507071202c3e082c0480711a9403903040e02c208100b000106041e02c40c1c0a42c5208a5501c195646051810007824004051401418011400b00500c5140103041140c08500c40181e01c0040140c40c1d40000c1001e04100000a2100341d0216818480c00e0b0515884040c1c0d140e03e0009800303041c01c0328050180d030b48000c40b8000001407400905003d9240f09400402112401a15250500351140d00100440f134280d401410f800314070403203503198041d40040d100010481100d0100403980f500b80825a46818a20201d040003403001e2031108540c0c0e044255450b07940103c0e8640d13180d60312231190660381d00404505401062000e004410300142c1c001844030f034503520042e01d510350a0320f980c510032100c82140a141c6c00c1511001c0781b50607180d20001c0c03100b2659801801080d41a4036017044001c8a103903800c001d010fa20801c400c0a415102c1340c01207500f00080f03080f422410901c2000410042500350446070b501523134100c011060661007400b400d0400c0c2600001c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882221744 1250 882220494 882220501
    0x20c0f010614030303070c0312050123100219030c0c03030305100801020901050d180f030f0311090904030e030a170d050f07020c100207081c09051017060d020607050c0108 75
    0x40b8510410707000b219419807080000400007889404c0007001d0300d01c40d0402c5680341b04410390020a03101c098100001030903484c1041c9d51405803606894012110a480c110f5003260b4181c402511600d85500110700c44081c0340c041c1d0300f050b10a079000c41c030441d0403400004000d5120b14004001d40b005a50101500d217000c01c0100e1840c10610840d1078400701615103625001c0d4070100640038008ca0780658103a9580940c1c414085004407400c03003010b62190303a50070070390b000d0ba04018040342d10310b00c0000088602400120426265030020940203a018104100721404040c0007038504041d00340010048158031100316543c205000c06001812120402480796650b030110025428104681c8400180d100e51701d1840310782001c02c200b01e0002000e1059858154490f01c5040c500408208450061501d41c11200c1c200381c0c1c080c00000c0a040100d0b044611940700c500010000c0d503030601a000e22803540700c04103c00b6511640c2041c070003a4040c08581e2541c0103402c059440f04400d11595021032030f9000003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882222994 1250 882221744 882221759
    0x70c090b01210218060a0813060b03011a100c030801171e0604120e0603040b0a060f14030106090b060418021303050a030906020111120a0204031b080d0e0607060b040906020c0f0106 79
    0x280c5901107401da440b0307c0c0998070b1080034200c903d00e030b50b81917407026554000607005440a00600c84004490411594810303032410601c0107580700c0d01a46420005000244800698442002411180038021420720803000c080a0760825a241500040362100388040d4108000c0118a9522450040f41916640381c6c0520050b07448521011055030f2103001040000e000441c10000c0542000744013900080c102d4030741c441500c800000e07400501140c0ca0100298095103400d003c2c0034054a2248414012190300501284d494069802841d4a400b108950003907103080560503540c81d00550380b1721004442d9a81000d40d2241144441900090009400441c00c1c2c1e005000350758040000c1c0a86a180c0340e1010540901044040c2c90030b00032079001c000010201e10307400c400001c0840300d0130a03c0c0e110340c5490f072040e14184e9403042c1d0100744040c0c8462100c983c0d440c0707019128188d40022000c02e42c1c100100002d40205070041e0020841880030401f11007002001500b0308820300600001c1090315261901d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882224244 1250 882222994 882222997
    0x1c0e150106031a040e0109120306140a03050604022b080d140f070f02030408150118050f04020103020a02150c210903040506220902030402010311070c090b0121021806 73
    0x100d103c030350021280d600b00076041562244151041c00c00001601d59816640c01f0340c2010f42108800c002600c900b000e1006582ca17009041012808450700d180580c951360b100ca8480c40b001704040d20900c00c1a440a1220601440303080b1580d02519410b1100c450034030300080d1a4020f910b00132030652510301140f1541e010050018080c4056200000b400d0b41d81c408115000344080b50341d00b0842c00b0074440026007207003c000c0ca105032001c149030820385604001c040310300100004051a11103007004184286142200c01c3d00d0b801035020701c0d0140c6d544117144422383c0341541c190010501010741404201c007002d4040090203c804c9800d400c0c103413459169028400b020400d80e44001c0c00d42041100f0403061030140000d04c2200390301e92400c0e22078000407003004082401d5601058443e0b4000041208560303252182168016140020604050154540c640240154080d19500341d554618110080c0e018600682c622002007042d0120140c0302c60980000c1d4115030745500d401d0715005d00f164054a4401e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882225494 1250 882224244 882224261
    0x15080a050c1303080c0304091406040c0804081822090318030203032221050d05042114161d0c0a08060f060705160501031a01051c0e15010603 62
    0x2d004120460850711062100c2c2e00a45814000b40700801000824000c1401400242c8003055040e00c0c8514100c010302c020b55080781500301c00c2004203001c21000400c844152201e07004d148004415140c209001f1130050852003804003240700082e101c240ea000310310b4008807181072087d51003043c9100200c014458540312800700940c59081070003601c00303800c02d0300950b00011a03030441c00ca200a966008240303000d502c0089600c40120344460b07080c18800704000c4100e80008600e441440c01d843c11076220240210307a4101c418050992401c0001d02948040608100410a069480d0088044618010000b0740c0c4a40d020010008150001d400031400c4036901c103d0001503410f00c0c2030554801202c85801c000c01c0ca5500c2210341150400c50303103400025203645c511590040100b002c0c0e69406203182442540010304141c10509004079442d171150603400504000c3c207040351940b9601c5071410744100701c04c607070080041c9004401001e50000044514001c8140300a00e491a601c3d8030085054070080d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882226744 1250 882225494 882225517
    0x4050c13053306070f02100203040611071a0d09020604180e010908030f07021606090e090d02100e01022101060912050604170714031312050d0804030915080a050c 71
    0xb01020722090403d480102800d600c64090207806010740d80c00500740c0c1e5445601480103900c045000d100054000000c14010b1000342c0c000c00c130140c5011030419142e40701c0f003a081010000441c00c03001c441d0854000c0c80c10280d008101544841e1178010404030324454031041c568040c00d000009403081d4040c4102c1d4049078200340c400d8516641c10362654141c41c40035000400310b204459080c0700002c00e101c4600041c20706680d0703200c03166280000f1000b007101c0c0607005520740d8002001c141c60b425000035004250010b100f002044010201d651103009000e6042c482c00c0d00d04406c0d410003c55425501180e05803912500c6a081c1c040c2c540300540c10741041c054000340b882d40b01c00046000312700d2444c0102600d801d014516481d02c0165500d413080449801183c10455201040d04d15205101c1c440c080082c0c840b40d8600a60070243c1d032102556611044203840600842c5c0000c20305251003009a01c0290045154800c4040314084000b03107029801c49103a9032043c94031000c2641300c061002111403440e8070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882227994 1250 882226744 882226831
    0xc0607080d1a190503060411120601151d0a062a120206100e04060b1f0e0103061509090f02070c0e01030314190311130f0e090102190804050c1305 64
    0x740c0d03031582d806110140310b249c3d1010b8220358502d501d16003013000b14041d0050528405003102c0d0303c6e0f0080c08080300c000030082d118480769903800168807a2020001115220300e0441196508078a05500301545901c2d2000c40500318001c4406101e51031a94080383d401036404c88070306d50f030307401c0100041043d940101c05080c0c52440200b00803440307a4100c00d0408038010300341010103d0441d041001904180e40c24404522404602c90b21581c040c40307160001c0c50078030f046d001415042d40340140a80c900d4054102260f55500103541010401d45c1640c562552246007074500940701c45015204032800d120440001302049039174400080781c10b090340c1e0b9035a545550714140d804990415405409100000d1000d4601801800162000c0da04514001c0404260001d41e550070403046e2035030300300004c1036080c00b0380c01003040350039480e40c0c00308004062805151900840d10b4900c0c0980c1485102107038103601c16000400044024415446103002d2080301c0d0741001802c1d40c3c01280c0626000c040b540d0000d1265 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882229244 1250 882227994 882228001
    0x62b03052212060b0a05060301061706040204060f050c0f070810050c0702150306010c06021c0e010b09041e080d29010905060d0204090216150209030c0607080d1a19050306 75
    0xc0d9a00680310b1084000c108558a940ba06c0206902c0c3c0c20980c41040010004105c989402d080f80d186107402000984065207001d00706a8040c0c805504040808c0400c0360010b004030102e8414890007410080c02c138103803900c460307654100507aa440d2502d02c06a0b558034000200d00342c04a0442101c070301c168098291000d00300c0a519902c40b070742006203d907052009030583e410001d1250310041c52801103071055403080500718500c55007100c5c00030741d000d80381ba0b00d8840f9801c4a65289074010313900c5030340461245101050440603800c5001c1405006085540203c7c642d8041d48294200c0d4a02c20303c101c07003403d80000e148200c80540d503901904ca5000c01d40c29030060000d418440010000b1442c00c000140c601943c6a0b0004220b0384000000c03112446214140c1041100c01321702c1c0d0040d10041d100540c00e00000600183d2038170760341c42126206850000f401c004002082041d04d8841070410802c0000104003070702c0e001074582140700244501102000f2112801c04400c030344080e1a00903004125940c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882230494 1250 882229244 882229253
    0x110705010f1d300316060c02150a0c030b09060d080c0c0607050604020906060301031208150405071e020f03030a0b03120d06030312020c0303062b03052212 68
    0x408420310718001152802c080252902c8010681001c01000011003050700c203081c0308003003c003081d2000003900d500300708104001a030a80301c40000030342d0010400107208890f00d078140d151140c08400d01100003410820001003a04c00d40c420040c0b0703011610240085540e903002c0180310441140d0180d84940c0c154400b10220300202c02400c04181594100e544204409000803007a40080008403000d6108501b00310440c10310070b00280d0401c9080e80c0143c01d550460b0b9170a0200282c010480003048140c5d000030f0100515903584a070b610301d000d403007000b1a04041d4001071105e4822120182107092400c070303084001e403001030071456901c0d00741c000d1415a1034814100002c0d004001660b545807045200c4e800d42c003d8080c008001000c030170007001030418170b54031300a40310003c6403500b111818410300402c103810300c002c011030703070300040883c0d1030559040180000040d00200070303403a07026159007242034000c040d00b11f4000d1031003070041301102d80349a00556030003103584914001d484149080114010004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882231744 1250 882230494 882230507
    0x30c020307150c030e0a051201090c0801110d020901020709060e0403090b09030d0c0c081204150905090a050619120302100615050c0f1b01031b14091302030f0403110705010f 76
    0x8002042c0d911b036180c0d2000060045220845614010303591420f040e01000628000c00f001080104003e11441300c0360070b50442c09001e8101c1182c1d10301e40000b02101c40d40e2080c840007001c0c000c2c030081007186e40e880b15242100318008031790460104d411540c02091184048081c2c65205030024020b2a29201e0b01d48119065001d40300210b9514440c0040810609014050582036140240e0010b445070f1038807424103407040100900d0030030b000840c0da062200e0703100c0000140c1e2191040d036002c00c0540322800400c051034119209440d1802c0c0111010400084000c0b8a850842c00781d03003240c5058002403401c004561991040ba007085807030030244884070b8001c10182c80303196a01810740710703540303401c011140c201160105950890880140d50b512551303014411500c0003016108141e103501c0c50b800c0c01a162010110b00c5220603100450030320b45035559415072440c0900c850700203645904003075860b51000e07901540c0480100d035060000584201d40000c0d0402140e50513501d07074244c440c80b20015280e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882232994 1250 882231744 882231767
    0x813170a0302120a020703081f151b030302040f09061203031d06070206062806050d090c140405090607020c0d0c170708011a0328020904030c020307150c03 68
    0x145502801203002003c4000001446845600b4001d651b0f048180740007040d1180c0140b1481c80ba205400940d003a0700000a2102c0035038038480b041260700300d0701d18030a50f48203541c0084402c0750ac075200604410160306030040e10807a140300c80e0f8400d00c681c58011110681d82540038840c18200043e0403240030903c203401100341c100d00401003032140501c5509050614404880000c056800717501030002500f00744601d80780c1c08400c4c508400d1102400e00d895000b25070103204072420030002042d000c1c102d4009502540f40c0550080c2030880d4181e032540440804030301d001001e84164900b20010304d480e500031039070754881d000650244c61911854002c0142075090444180c640030781d40040454403240e003191031400451200014941180b40c0b04c440d03805d5811700303012001c07050300704001082030b510700140702105017203210020200300014208001303944022040107580042c0e54000c1c0424540c022070021032203802503017541d07007454880c1601d000340c11000c451140005d01c60070054000c40d02c22800d1082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882234244 1250 882232994 882232997
    0xd03230c0708031302011e120515030d021e1f021c02210907140f060d060e101a0403080c07080d03330e250e010813170a 53
    0x410030503884000c1a50000c03104c0d07104607244258080159a0021003003484240b07400c2610280f04180000240385141146c000880c0a13280c5022501148a0419125106002404845150b01104002503481c000210320214150103a07541da681600c000c500c0500b18030342d0700c8031880d0a075540f842c0c1000a500001d400242c0c20340171300580035400601e00082c20800078606402d102d20488684118020101038400301d41c4c2c0c1d0142c0404c01810401d1440340e000c0c548125851183c2144100c0410b583d8032802200c96403280c41d1036404140c0c0075060b2440d0340641c241b45e40c4031640faa10b4403451449943c00c1c0e0f120182e0710302c0c240030402c00100424000c011f484481020340b2505981e941d051071400110441040c08280c035420044200034000c00d1546416080d0514803445010014400035070354224003407004110300b800c00013856500c503a00703403007100003d4084150042906d444014200002c1d10000c0d0b0024010310081500f100d0300c0420000300720341090115000840b03001c1002c4441c0c0c050b155007030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882235494 1250 882234244 882234247
    0xb0a020c030a0f11010e0f0d02010c060e01060f0902131502150109050a150e01090e0a0f050309120c09010501032310031101050f250f030c050d03230c 66
    0x85094074240010140b0300d21030010141c40342d40a20f001c044905000c10000e04012111071261a05c1c2d9a1642080720b03040706407241340e0b80d13180c2400100e500b1480018080c140600381010135480c01d2056000134100c5110005080f6800c2d1a01c9804060b4403500140d210141a140350074490505d44d40e05496440c1d240340129a103519005403e2082e880c070990255115550310380810500300510b0091041c445100216454502e080030802402c190040c0200c440b0700da5903015103951248100400030415802c03010541c180c84442c07030455541c0e403103000128040c442e0030b0049820080002280700020b00000c0480059a00b05401140101a074000c10201c0c1c141da2802841d1038541ca0340110300a91812002004040c21400d1200031089600440c42c10407404100f6002d4030280301c2c0640f010754000000d03540c0d40d0350114481d018a85071168010303190b80d604405181c10190001e5581014078070070020303203000581700c007415400c0362040561000f00c1a41441c000080c9070301c540105a0000c020039a56 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882236744 1250 882235494 882235513
    0x3030a0506061c0b130b0108040602130b07060204051008070f0c05071d01051509090103080702040917120a0c0e090a0f0606110f070308040b1605010c0903060b06040509010b0a02 78
    0x140500d0701030001c2166903200030750800c0c24003400d05c0c1d80c440b12144007070003002c00e24000200454802440500403540c04200b04000651203108a0024800d10b240152208124242036000350301504c940b80c49910003082c0700d44210700401d0514850f0a603610342d00302100e1900c4099484243d6500c0889043c081c0080104a000507101e1055410f0340b0341d50b85401d070358144010300c90000c50040785181144018043c108244c0d40b0801101d0551f607100c40080e8031004144041005000c00d00c0004060300300502055200207210406411703016800122800c2ca91220752030501107480003205900000c040c0c2065440b18206400c040350089a203200008101024014100407110030380c10010005a031000800f01300002080a040c0d624412030142c000d0340d00d5503440c52140d10132445001c220070030100790b030242d0100c40001486c1e00d540080c001c0c0316000d4001d81c028500340640c0402c81c0c580d86800c0004595060500070b545c15950090006c04091b42096044205500105c84040441c41881200c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882237994 1250 882236744 882236767
    0xe071b1e050f150604020309120a0207030c091e05010303271205061b030f0612030913150e010311010e0a0819030e010206130803060a05091e07050c03030a050606 71
    0xb060303075508120080c2c0900c40c140f08414441c01030180c1514805e070700620520070112004585080140090201940c0d0b80c4002401a410318410350300c0034101403901c02e000101440b50342c100035100410a5042e111003403256400104854080c04080c0015103070307583c01081f1042d06102404d60280030000918055540c5150b40c0342041c2c42002180c05401030740c18040070380440000e0580c0c1e0120317541002e08515003505280391180000b0880ea128904181440ba41d01c8410320896840520140100604981529402d000381101203d002d240582c1064005030140314640e401d0f041c2c940c0018180c462060140045450f58072003064035502038406080020922000c02040103070b00c011418112400c019414090501c8100480303203419504010204100c00d043c51000c4490990f100301c11549985404010800503102a08005d402041d44000d11440303a40d00d9035084c10641c4000d100c100c50703680f050001c503414000d81880700c0d020340c424070206840c2611904150341c0010081c01c40b6007070002e400341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882239244 1250 882237994 882238003
    0x5030408030a030c1d0120031614012c030903060906040b01120201080a090501020405040c0306170a02090109110906160c1a071e05070f0e071b1e05 65
    0x49034080d0720010b141c0000d103403d07010340d11a1a10500300340302c1241c001701741300e084070104100c003904200e031030946075031919944e0345910040040002201c0d15074a903114061554039441d101520b0072255070407445007a04050007074400d4940c1d0210204412101150a240740c01c0b41410106d010340002e00c212422900c0403c0302501c100c481900805041c101410304030703082541a007041d0384003100792801c0740160340c228010540101c0c043c180012003114a003413160080c0604d4101d507600c141401c019041469054003c907090701d016401303820f042600900103c2d0b54001a04000350000c14081c010059400c2550200340d1800f807110503a440c100400d00002c006a0024400c182c81c1d6144c070382060240010020f10501130400a0001c00007007803005401040d6014440001b4116509110141032688108800b44a625440002c8815442d00d03002c4045040170f03135001c0e640c01c2e1a250f500042c0700e0f6102d0286c1c098000481e4a0401e19070815884200b41e00709850314043c1c0380c0c01b001d000b20000840800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882240494 1250 882239244 882239249
    0x1112070b091f0f03051506120a15120606140102060615040b0a11060601020c09130c03330207020a120f0b100f3c0807090209131404120309050304 64
    0x6440601d005103c00c4040e003110809030400d4403110030031000041d0758558004860b11352003101d981e41907039941c500c0d2034006001030702c1c054001c101d0840750000748050003500780d288481c402c61050000c01c3d1500071001048c25079288450040e0300800101d846818095903013000744000402d00381c5015160031b0000c50aa12041e07408001175031f003025840f2001d00500290f50009401d10203813144440d04800103070660350103406501c0b441281000c0703c0411040007054001141d101d180c44801d000c080c403080300c01d44013000c42c0100070f0304c1c0750403984050400d6108513140b1990050003000c2450400801c8aa000842c0c207085401e140480c904101054058042611580345604e1081c203c0e401c10402c3c010024040d4820442120300c02c600c41c0c550b04d6055000742403128041402d416211803c80d41882e210000d9204800300e0268074404680d20380540c00a11500c801610720150364584486200d044420f1080401130140d50000440d002640441e000a103644d807a20300490503448980302d0b5410360303000b135 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882241744 1250 882240494 882240497
    0x40f0305070201051234021002090d0f0f110108070918021c1d0102040b071104110315041404031d0301020928050913030f02120a0c1112070b091f 64
    0x8603100c0e803210f41460b880c144c03580c1b0103a0b68100c403405070030006503039280b440b41d801c14001d4003c5901e8006440741c2c03000c0d500380c50700008071403491091410101178042c2500001d940040010107081e0145d40218000e5001c0e600c41c1d500c6280e42850305104404142241d844d052141d50200903481500400008440d0303074404a8000040300e2030b211a4494141c0784a029101081e401840300308008031602c0d086d107820b40d41014080402e5002940090001d01583c0c080c402048408000e00c0040740c1c1c03075003122000c11001d440401906485404d40204820101c500070b0000d42c1503c03911000c0c03140d00b5544524090040d0016040822500000e6100c3c060070620403003107080300a004d00444a1850b04d14001d04043e606282503040110f8016020420b0305e8029061082541004c480244204401400790300080180e546595808800400007190741d43c0a55500c044e54020300c1c280c0c5000b078a01648240e07070300c0003801502d2420300f045150307800c4900b4903035104005150580854011203600702101495 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882242994 1250 882241744 882241771
    0x507140c04050405060708280f180308100806010302132a1107050406030218090c0402031003020405090d05090d150c0503160504030c0e0c070515090d08040f03050702010512 76
    0x1864010420100188042c204c1460448018901101c8236504040e04030f50f2800421041581002c54000d4a14481214402111505880700341603003c0400341c010600911110003043d610180b46031f0301d035003c1c007000c1e5014004c0615201c054840e98084c120320034004100a980c204852541c04844d0415410300020503425182d003498020b0520119016001c211410064a411074000c035144011580d001c5603c00601d1001c102242400c0084207540c60005205540d01c0c03030540b603140b85038501844224047d41c14900440c1d8402804285041d64040300c0d076905040490358420040e2030320110100380c5100008800d0155041501c2c00362690101c2d041e01d0b404d035242811821128404480d019110411030140006c2c00011400d0351088200c0c1c50055501009031a180c241c0c0203248100103000380f140c13203600c1104203403410b1444031601c110704000035504034150f0380c001036840120455004201c00003c00d800383c002400741015103241c40c018540a400c0121064001304009015074806260614 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882244244 1250 882242994 882243001
    0x6060e070306051c12050c01060b0d0f0513020609061c020304051903090303230a02010501051c05060a020d0e03030103050c090c0a080703050403050c07141806010507140c0405040506 80
    0x805000d058000e010a031418150507039151103800303803010000e01c000c150a00c20741c5c0f2400c0c000d11800685440c0104403000f00005980c454008146501001690303005030300340b6003443c080141c0751160360302c01c1350010a00041f048403a402c10010390700142c0d14a50050b400e0043c1084560220b80c200414040414016034a0a250508038540010207101e440b000b00e0841031100007a82c0030060208072641801d0101d280a001c54002e0801c40e4805821550410007044074040d0f40d0341500f29904131001540c07600080c510b0005804aa0072b0910006040340c0d100101250503010a5801030a0707400054000050312402400d9807411603000b03900554403907110b4500c0f02c4251502c480680e42049000c50160702c0d180b07a585026000010050020040c56920350010781458000c50450b40403040c502c0503a901180c070f40078280d50840c0ca02c0171035401000c5601084810a0031045500e006507030503194641421090707030304d0701c424150f0640c0c0310003540035003071082d4225119800383c90302440c4268040e0a0b02d19 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882245494 1250 882244244 882244247
    0x2010519031e1107030507060b0d03031a0f150c0a020604030c090b0405040c0e1803032707050a05090a060e040308010303020d020610050d0201030e0d020a050714010e060c010906060e07 81
    0x140014240011610f0000580020800a030482d185280c0c182001c1d504d5800b581481e00003403c0c1c110480e9008188034400c1820140d050388513100486d0b00805600c2c203c1c1d220741c184880925000d43c491f411951001700d2940101090009c0c10140c0801011075040e1145d640c0800c2c1c243c0c0040d4012107107070505003000d00c080801070045100308072056408002519050b110403603691403521801c210079951741c010600181241000c65814030820b011a41c1d2401c08007032010110b005007080103900c071944404254036030000b090150484100418054850381050b080080c0d082d40034001807400b6075a0607000a0b40101350450b28800c17802600c034185250301d54200682800358460902d011500b01301e0400041c402065200c20581d041032310803151420304bd00c0168014400003880c07807003500c140c10300001020ba00191a0b40000e214100f66600680e82f030220042c400000001c4501040d0903001c0345415003032020145c44c030b070b03840c2c1400403401070300c0354030740b2070403503520380c20041440c1052010029220b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882246744 1250 882245494 882245531
    0x15121b0b07080f18090f060a0e01030b01030803180d030605130e100c02010b0927120306042d090b06030a0203070308090d050d0f03050109140406090201051903 70
    0x6100c14246189820310030b40d0b62541074032948030010601c82d4081aa020300c24452144858541d6001e800707144a81004a007a510004c002c507195480744080b03210100f22060510705190407664000d8404c3e03466405c5075980c807801c0d080100b03048e10340d00f00d001c0c51280074401000306616059698500141c01e07411721007070106111001c4010070504e0b043c01e002d0a50f0764400581d030001301040705000100507410090032409030100e41c9910354000c0110052000c51503078201d11580032800a1101340210340700c440490b4541000140300c126103c014000103c0e40d080503048055a1108071090800341e01105104142600c1c004840d54685a03803000c0c5101002005281a0f0704084100d0080c60450066800070341e0702d40c102d0000915003000407451a042c1c0e00d944114010715540701050319039412503400010315150640c814100001e003480000a200c844611400621441c98200942c4c0c55840361901809003810100881c1000b20420144405041114441910398110307500465056004660840f80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882247994 1250 882246744 882246749
    0x905090c090103150c03022b0f141f03060c050309010b04020c07030323030f150d0f110d0506070f120c0e01140403170c1006051315121b 60
    0x103601c5107070051003c12980040a050f184c00b4607008500007900b107208030040e000c2c1c0500507a98a20103400c2c003d1801d445c8098000101843c41d0402c2841019080817040d1180c0c0c0081501110010010510b031410300c2c40c1403078041c40f14481281c0401c0e03803a9550001c40c0c0d018500d0800090000c028040c40181c2030041c01c0c038181d0f00315001d5003000c40c500700b09500c0e405180700007000e00512074010107040103441041e88400c556842c1c165224640410340030503070001201c0d41c0e440c24404010100c00d5141c002c002c55039041d0020f100000341242039841e58180c000006031a84c0c00ba43d0a424180050010800580310712300e1540d504418000d080c1001d000c040075941100011402e08903a0100c0c3c80d444030040803135040034030b421030504c4003801e0038908602c80c981010381800c01c480d0780507901c010f5050040c0103003a00042101c8083d10039104d090300700e910740e005580e4064100d406a4450340140d402018001d000b0b10345000040d680e44080c07800d180c01c81300b42150030240d040340c0c59a81000c000ba45200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882249244 1250 882247994 882247999
    0x81203010e1605270414011802070c030201030b03010b0409120905060c0607050708040f0303030515040b0d020609030c030a0c0501270308070804560307180905090c 72
    0x2a00c0311070b01d00c00f40c03150141980321025070481030700c100c118484c4030340b0303282000074044c000300400083e0f0540c0300d0504409004070500c10550804166403240710f07200311120549c000b000b154281e0301310360046002c2d103072901c0100c0e03042d0b4840048061980d1184250f19500d44070342d860441028801ca0060202c0049a1002c3d22410003440384a1880701c010031a40d5020003580741443c0c0d141c015180076501d5006941001c40e10203110200401055011340c8907602920207840e00b103c0000b100410002940c0d04c1040c2140c00c0034100d01607134010305006000e0803501100606031090320481002083c0f0b02110502e090f030344961100ca0400c000d50304080c00c1c035500354074015010140041500b03d4070644441740700080000200143e410300b1711180c0f20a95002d81900e0545c2e5001d2052070480c51151500300c0036407508683c003005107202c0c41e8401c50213880020f0982c400461200c5907100d15141680000342034109004001a6000080203510005405080654030018140c01d0040d032003480c141040c01421f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882250494 1250 882249244 882249271
    0x2181302070305030a182109150215190c0806040f0c020a1217070203071101021609020f210702010b15070b070210020c03040e0f15120106081203010e 66
    0x4002c01d500404980c1d02880c002e4001c1203140da00d010340c1158101c5000042d040892504541c00d040b0b0303004480007400c040a0780c40c00d000c151284c03230030703050849035064032805a80038503200020f1082d800c40e11030b401024060a50340003980031241ca0281d40e1045c1c04100010b0000c01080341d9450107226a102030107800c5010012510010340c080d41d00e00c0480c00251041c81603a0038000801c3c4070300075900083e54842040d00725400c144070041d5517504144030880300c040081c0040300c195440003405030305e8541e4101480700c8540c6810b21074002540590310364586601c042041c0f001c040d003207022000c802c90048078044006d06d481030009085400e02008a8030032400d806401041c504807406a0724043d81120100c032103a20748000503071034540e052500c0d804031800814030000035200407000d00100c4514884404c0103a81d91941d0019091048400d854911403102c003a65582c1048202014010780d5a8000600152a0204c41d8a0002c2c5c5134904501c2800000062000700452120103030007001500100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882251744 1250 882250494 882250507
    0x6050706110c280c061709060c0f0a0905300d020c010302030601051902060117071514042102040c021c2601090e07062a020607020402181302 62
    0x46031141c1d0744602120343d05640c0d820350042e5409451809460650000c10550581e603510409401001c030340003407041c4510100001100903001043c894400d00f00c405032103103031420b01c40e006012174001c5944501000920740e00484c8607101c5500303d110074540e064041c1c040080e503101c0b030b00000e00380010040e240e410240e12008096000038650351680e07402d017809a2a9583c46004a54500901020f0040c846c10708910800d41500850598140c80320040ca1807a90319030f002209550b0909031041070050925141c5100310588200c0c890901085d044008628282d03403880c3c0c000d6940d98011415208401d40002d0300c0c114640b0744640034205240f800585a410820401001e00d01c0d0100a103509000d04602d8005000700c2c603a00022845030740000c00341455845070710200c0105a041d4489030681315121010850314054010104091080000086040100980c0d214410103142080341c10520034090400140d8540c006000c09d10400700301d00700c008000404000c40110011030a007002441005003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882252994 1250 882251744 882251767
    0xe0a02120a0b09101b050a120b0310240807030f0609120f030f0b0d0b040c2c06150f0705070b071104060902090d0803090307051203070f021f0c0e04060605070611 71
    0x131f0310a8041d42c0d0030241a13200ba84258100a01400345800758140a91301c0211b1041c0d80a5210050309000d1000340c43d803055640b440841500414000c5c25215401030504000141d1400d100c0d04100b4421440400c0f201a10790310600707001d000b2441c900125a080706880e680d0307a411b1140d1940100010402d00c6030107028000b081c0380304000a0050b0106801900090520980340c2100000708221030260380d51803000b00702d01c1c0100f800c1a00c1d881c1085080301c003048007803a0070b00103031800d240000651894003202c014058441d130312854044915000d80c42d400280302000d81d02404249014001c0e03031401541781d40c00c110444080b6008079080701d2051105107920745413801540074590344145120354a032500e511440c81e501034504011301714803448032450f665605041c0031710f01a00b000d8462280600c60a0790a9845109504032105c0310710340c40d9990402c16065800030b422400241c24101c00e02e86540c0003013000d95209400600214400180010802c400745c8158440c031240011201d0400300200d02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882254244 1250 882252994 882252997
    0x30601081302030d050706060b03090309010c051504080c0d0801210302010905100209090f1330090f0b0f1b1002040f0f0503010e0a02120a0b09101b05 66
    0x100a0400c00010002090800a01c00107498960010115200203134803c100409907031048008907051800c00700f00051541080081e640903000c110051070038461440300440ba400c3c1c0080e0103603610b10600071090442c07001000028007440c000c004a5079103a00b5000001d14241a48001c0c0b420080450300412450070f04141070003800340325418007404107a040c101240541403c1700080d07c9030003401c17098407002049a000301220b1600352a070980a030380780c20000c404600c0403500081c0c0304052004174800918160301c1e2542c840011408d020b8014144480a1409000c0888000104070300c51414400c810800488200400000d0310131481c0c9404a043c0034a035020300d07140403800850340380303030100d0041d4203002c3c00c0c0c200400c09800710349665940c854a08400114407840c80048510180468903003018051307019801c1d18080100110101d9a003400f0300304901c80055013190140b0321070500000d800002140c010041a40200450320150121400321064030b00d40c0807440c8601e410b8804c42a40000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882255494 1250 882254244 882254251
    0x50f0606031017100227010c030c030e0d0614060307140109030807060605060c0307020a062c01020309210607050310060513050a031b050109261903090311011403 71
    0x40c3d8a8600c003840c408400d107407040325040c500e0701318000314003075283c88450f5040082c6400c1840303149080c80e1210005441041c13a030040600044d444042503400310303018803d052440750300540100d00905c01c90301c402044602d40901000311500c1001401110300e000c2000c1c8000c0d202c41c0d4030b441c41100c00030001a081110a1000425101c804118002801040d034481d0780101409000f950b87e50084045c0b0503269880400101e108400000f80442c000744600600c5e1002e640c0380c00d1441e2100c88054109006c01c4491001504502c410030500d8015103a00e4900c1145041140102404070000500e0724104903004102108000341407040100c9007214520007411969242071055580d00c43d00495006014550081c54102c010090b00004000c0c1c6840a4044041c1c401000032401d61540d004440e0803069220f03002805840440c000707804002c034407503480001c1d61501158071844203c0c4400c0ca44c506400000d8002c1030b0b41250800c2402605c0322450644c10003481e106003642c1c12600822428000039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882256744 1250 882255494 882255509
    0x18041406010b2502190303030c140306010c02040912050d1a030c1207080610060e0405010521010f090507060f0201050907090513020307090c02010b03013606020a03050f06060310 78
    0xb500c0501c2d0b1014400030f440711464000d07255240c0d031240003403003084006252004400117031030444540c2100d0700c12245000c0c0c0300c0d0307950001450354840c0001129414410304041c0d900aa45e21419030015401560000304d481e481d07224141c40702100c84080f411940000851b0042c809030b011100d486680100f50200010400c80e820041200c40d01c10381c0b450702c42107800c203280f18450307102846500c50034030f090b2100b1290350359901414030a4280502c13090b110213100c2e540c0c120a512440182c28103a10b00007211000b20b1400020344400c514540d802503030660041642c158210b680c003031081c554031800060341c144081c0000c1c4080e00307101d850315540d04814800c0d07121155846000c503084d10701c54580d84000035001812152000d88441300c000041c2802e42ca030b80f01644c40c00f13400c04894103042c0110300c46040355100100344820204101da140002d40c8180031100036900440c0c8000585500c0900b8818019940018051038070f0924650800f00240180f0700c80c10091003007040c0051f0455104042e14580d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882257994 1250 882256744 882256777
    0xa051015030c09020304020f030a170c0312010b09042f0a031b03050a1503032c120102120109050910110c030d051504020304080a05030c040518041406010b 68
    0x91110003226156030340c10042154214500000b5800502d40146000310b00884030038075828012010160b0714400100700400407074014518014a200c0746000c2e01144000c202a02d01e800014186450711100981000004034004140880c1900341440303030500604a5032813500390039101c52810780c00c0b42c00c49411018105e80014613409840d01c03a800c020b01120f212340403106500c0c1d04035070260140c10115032078000c01d0701d49100e40f030308155982590000c4a80507114041c018982c800780d440c4048000410725440d4803011400701c0c542d11115003c10801d00d843c000146c80c0c0600c101384c0c02140c441079100151b8107003004184000000d020a00c803c403c6c10014000441c00e807a03000c441a5070284c0080e1300740c98040441e0724030041015402c0365114100c0900040c082c0d0240e0b50800040780401d40d0058500d80c0c0520040c1c81c003d028200860304190010444c0d8102030380c8200140790411034180001d88d25520b501440108100e9110b000415801500a00300c50f60519641001038000c602404518007003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882259244 1250 882257994 882258011
    0x30414040212070503310201080a0e0601080f0d09060f080405150112050f0334020301060b09030c010c0302100902060c2b0905030601060e0415180e0a0510 68
    0x45076411654507441000020060b880d000d038000d062134208840b4400040304c1400c898480c041010350011000c1d00c04100c194907183c050300111494540104410302d07603540c0b4400700f40640d00c1002107500800b0703444020194a0602c00d120f905041c1d0094084060000368030040c0300307450300b26018180c1c0401601d01580d0941d11030070708900d8030b05004071501e164400c2600200b4045052445000d070a070081c01240c4200c6080540340d5581d00c124205c0441d003501200031000441a00d03100d106448812110a0b03480808540009084a04c2a4082c035282d40d0006039800241c182803285a0300044c003420010003a000545001c1d441d0b150546905400c2956850080c0455542c0020784403449407100441d1900d40c0c4040007001c1e10741080302036500e22101d0380492404103200760015002d440c0041c0280138541d19021098443c10000840c042e44280c481c0000300701c03c0000a07400e001000c5190a01d0861309101c2e0074241204c1000c290900603030810b21204011030340024415007038040c0c0d050300044104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882260494 1250 882259244 882259249
    0x60804060b090709091103130206030705070b13020906010206090604081b1006091419050402060d14100602150c18030604060605130b010c0609111008010e0a050603030414 75
    0x18801810580c04100031040c4100160702114040c02d0300c00c0128200039100086c10745035214001160040c20700400c250f088001820500041c0d5001091402c0080c2005c103596590b484241040354400d0b442d1101c0301a45081d840c0200e83c01e501b110080c000790099040110501d0b4443d0340c014400381500e0350000c0c031840b200c0c000110744a2000156003d649041d800c0b00708840140255110b81030301c4504080380303516800c11108600b402010f07100c030400b0081d006114020003510004000342c7c2c0c0080705020309001d0284034000d01038801d072009a808003500d00640450415030301500030070110350102c401031700c00d64616000340c1d03040140304044079201d00260801140326031000c60b040d030b054000c0307000344030800c40030f0382014056800880c0c0c80d54401e40b01c1040c0380210f415201000340001c0c0406101d4000c0b6000360703c03191510f070141d0941d02c1c540307203100c01281c001e100c80d09101d80042d64280040080b203c180c503140f07410051602e4140001d0910200203542ca00450199082d10031040360f106101e503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882261744 1250 882260494 882260501
    0x61306050f19240909050c01141b0a06050f191b1b080f0d1b050418060503030c1e010207030c020907091d0a0e0a020102060a270503130e010501020706080406 69
    0x11514482c1c10f4034280d01c03014001c0240008503411105807050300c0600703201f03600401c0140d000c1c105014039581483c019800d07038901c00703d210011032054060300c17007404081202c1b03015042c0b048000e5814900700f82042041d24860800e0031010024162500d4198904001c84403810545000e061a0080d500d811010034012010340300c2c200240a40c40c0001c0509c081170303100000e090042c4510108002d0442140380400c915078900481c1e0000035010803060140130404442d411007031212400000d43c60b07403030760042442c59000300d14122065209914008030301888000b1600702e00d1050b0000e6007040410303640070305910000c100c02445028802c0000710702c0703449001050700609000041c159050300310290f06a1330f5405807000507255040840d00c604002000948001503581a40140000c0e0b032410081c800801c08415401d466542c9078101402074485980218002400350717010755510004008946040c00290f40702110b40580c80b001000030b80e80200340c2c40b04032034590400400c195200d241041c000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882262994 1250 882261744 882261791
    0x5011d04060b070f0b011703120a090501060b09150f0904090218040b180d0212030603010b0303071a0105100e010309140d020703350a0908061306050f19 67
    0x4206010071030f03009020307013407182110160103500e80e1009641c80d0078030759909544265a15026a10030072007403100420030003540f40e1068034110f000030307850501c1d40c40c2070944107035034002e003000d002c0810030785210b25001098901c100c00e034160880c60420311140c619040c1c081c804d6064401c42c0e495a003e015500c40502401108101585580980c9003e260004c9020001d545040b070600000354030303c03015000000c20800c4001182c0003040702c1c0d000c42c441000c8aa00044c00641c05540300c40c5107428030780302000074024036032140c2844440140311210300344007094160301c00e911985002400c0f08055030041c040c18040d1030207280200e4030380f00d58207080d41e0030301500c507411120b441120101000280c0c0412a481540d1180c8500e190403441594100b00c4403251600740018003000c900100e070b0300a1014010450304000b420b11000d42c41d5a864824200300c8121144c03e41c00c00c641e032204080010500c84c1561020481d4243c0c0d24031b0500381990541a4000b00720505016500c0030100683d140d004c006081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882264244 1250 882262994 882263009
    0x110105040821160b0702011404020108060420042702090d08030604110f0a08060105031605070f050304080f010e030711010c0218090a0203010b040506180714300105011d0406 76
    0x141e85061034a01310141080b10100015447e09000d08419065007504502454050f55209019241c00702040014681d54101100d40c0765981101c0c18050302c02c4000e40010940c03059206401c2d20203071001d4443c0515081008442441041181015a1400d41c0045113581001d10765481350b4980d00410024020a02c1036000f03100302081d0190881c19102c014040c00400d40d0300c07806151106001502c250102b0349105c03d219407901e02125100c0d10403405811200d003d81092120403031941c41d0141594480e8118183d150012030006013415024015120300003205401146000200d0301c4190072075440000701e50402903810b60243c2503684860080005000c070500c022414105240c80a40d10441a01c04900950824110b6141c0e072801c1d10036135100304000352002007490507100b01e005a02e40010071407014880b90a03240c0c0040e4a000018200c0e09017900705607080c00c0e07500080c2c88003401e203030f0b02684101d00c2020010701030341e6401200350100000c0c202c568090300c0c00c004005006001b01d60003020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882265494 1250 882264244 882264277
    0x509070c140a0f0b0106020d181802090d0b0907080d0f03021b06150f0d0803070e01051b07031a16050a02072d0b03011406090406030803040f110105040821 68
    0x2000d00800c0d0256604880030b47c0c0072102450403604047e00c40da1b650300002d0441003000700c820414040a15034804100c03081c02c00040c82c01400e500007540701140c02d041540c15070000b404000788030600700003850143c045030b001131808407520b1000401c0c0030313020200350040540200e51038ae0325409400840c00280300f16070648181d86003802000e050140220006440f4502c408903060141c280f410034520300d190041c1041d031850741ca8a2082c3c642e0080340016174100078040140b411103810300c884494220762000040d000c40c0d4a50304007070401d1042041076248101d240400d00c011030500c40103000b80d0a8070750a00e5610f6450484080c0d007009050b61281c0041c4106404108040e10144021050b03106040380b000640d030740340d02c5411143e010034050170020841c88140c03e0701c2c0e80782c00d001400118400030000315205850b950340d5203098100307070b4084445050000c6c0b00ba04002a62949807568103007803a21504061070800007541d030f52400c1c400c0a105903203240800480701000411900080300803420030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882266744 1250 882265494 882265523
    0xc0d020a082a0a120e01231809040b0609160c0213240906080102160b0439060819020304050316030c1a060604180906150905010509070c140a 62
    0xd006060071201002590081ca15404c660287d083c0502550740111000204e604280c5058080e9000d2004032281c00340e160007a920b103682e1410380c075214a1091486815900f03008080c0881030b9009800401399041c4815803080390303035120b01494072043d0110360311010f1502d0a0405030080c1000030030140720306044c50b0072221403460182c894045503501401080a96a9042c1c00c9080b406070f0081e00443c28240145680400c01d0f40840381d41190107070101e041c0c072a6043c0310104c503420414098a40d2070940880d09085109525a45d078000c202d64280b12802c0d1038080c0c5030703003100c101325240208516408408181030003410000d40e1014923480551030038004440c140544564100203040700c0d10121040810400620300c030700f040c0a80c20141500b401d1504220b000246056144550484269501c4584000c0f4040c0d018070303192100300c0201c240e121400c0204c407005980050f0400303400350a030f800034004010b512140008501e50840c00300c3c01c800c403103c086e0500344401524040d002880340c5c03051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882267994 1250 882266744 882266753
    0x206160203010e0d11010c1b17070606180b032505090709053a05010e011416030209060708131a21040210080910090501020c0d020a082a0a 61
    0x3d41030304038940d12641004220b0754a514261558021250f00003142240500078010201d00180e18051080c1e03049c68042a48441c00d10b11600715800607128140c840c40c04000384420134444008078070444006000750001e20011035564142504a001d040c1d01c0c030b00c45051850079010b50f60b0b014140090444920303090070000103207800e40b035005042c802d51945903211552004601060320340032502c070b03d8510340300400c00d80300007845142c03e00381e90302e540f02c80f91020520020310994409070190728510341141007200d000501c880f143e01c044828184104400b0a040c1da0781d0007940c11b0240e1012115544100500346030305049020f5010340c58202400c12503924006400010301840d81021102e124240c50000c1d51410750380b81078501075040354041d9823090303006102c2d100c01d96101035107804a03441001001e00401c120340700054262001d035404110071040c05014003403280e027a030241c0300610b0448c43e5074545031020b1080c1030421103491100a49018400c1c02040396150031503101b41510f00c2250107080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882269244 1250 882267994 882268003
    0xa050906070f1b1203050313150617120306240a02010c08070c0201080412020712200906011704051e0307020a0e091b04060b0c0304080709090f0206160203010e 70
    0x1100d4001c560461000d121a41801c100100d03804c0840d942d1000c030464506540d031340e00c0a046031805821f4100c102011a885054040404401420020300646007825425524201d405403240503000384520307800d504c40c2c4606076900901d00f201c00c48201c900c0c0409041e20007010601c2019544404500c0c040d0f000c3c0c0640c0a17003151101911440c202d42e41b60402100e034a03298100003800301c0c60140100e4081041c03180d03040000d210321300407070309a40d8950100350441512a4011039540c0091071030003826003e44015141d45d140300b9114640d0b030342000741c00a014580782c2c10b5a03c0108422a00040c14044104810510500c400301c0c10000b89844440507070f266409860107a0041000c000001803130820440507900c0b890b8148003078003000c0340c8030148401c06000c4228841c0d00c0707611014046910705882d8010b01c19405840c0080d5525440c1110356030421406511900c4840c2c40c0105c1c100206003080b10710301c05c140d0b040300e038555502e44441c00c1c4220300310000d90294266190000e00d4092190006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882270494 1250 882269244 882269273
    0x21204060905041d0d020a030e04090c090b030f06151206090703120512070305060f0f060906160503041e1406040902070204020d050a06051c020d12020a140c092a0a05090607 76
    0x40d00d149c1003040140900c4251519244024244a0305030001c000d60180741d84803c10000d001000e030b688a0000034070740e901d0080159820110200d42c90f010309550725003015150580d0448034090142d91070000e03c070702d4617442213200141920141060301081940701da401c0303820041052000d07030901c1c04d18481c000c005100440b40140641604004043d451a05518400c40000d00628582ca030400c40713421f001ca1a0401c2400203600c1d4030304c09122002400078805003004e4000d800d80c007045100e10740c50504210840381e03c402c008001070760408045d500d580080b40d068034480d840240c2c0d90412440070800912441e039201400610703000a0019007800d42c0c000c10220380d0100c030031812004c00500701c00c0340c0001800c0b0081d4000e220800c6a0001460343d1100c041c02146401034824010046e00e84d0301008a10308507c2449030010fa0300e00c0307107074586a8a102e4103e101ea03560784001c1d40e005180204500440c00751541c04510200703020b800d0074071034022a601d50703401404d115114007440c0b410424810301d21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882271744 1250 882270494 882270497
    0x61413150306080a0209010314160314010b0d0506011a090d05010605041a06031b07050d0c1b1d3d1202060f0a03021216021204060905041d0d020a03 65
    0x58000106164005280030346545c00601019559107942e4404075401105000c0090340c0c05041c00072206c044500380703004019401681150710310081d8441d01c034210b5080105a900c100030828458001c034500159035070545201e07010654401d965034000018a0140514641d801500b074000d0004110b0190401d203702c450544041c4461a40000d003401224424000b054004006100007210000400110f150480c981c0f16860300d000800d4460f20304100d20001031b5000305a0758040101000005240c00d4030b504225a4118001400d003444030340d40e24042803010b01402610000728204110300a949036020050200118006044281d02d4504000c0d41d800100c40400d01400000e10700000d0244080550f40100814074145080c40114400c1c0c205010071404c040d403d000700d148260164000d5070203141e441c0c07120341c070480a06100038136102c08680c1c6226444010300c800c11440c0d07000a500000d854046038082120b20042411400100f204d44155040d0301c0b547c0c0100b04010380125444046a029 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882272994 1250 882271744 882271751
    0x60a0303140a0c060e0a0b09010c2a05070b1201050306010b07020d0219091a040203090c0105161e0203010f1505120a060207080901090f0501020303040602071b03060509010c0c05070614131503 84
    0x10031007043e08031442200c8007000704165070310000314004030480446a0045100bd05d420403581c0741c85191500181d50054203440301c0000d4110200900d000b035203801850300314010420396051681c203612500400500900480421b460341085541e1030b1220040c3c40c1d4020000741074180d07200c5408014220308118083c5008944079108801e00b01402143d110354281e1340184441d0300000c5c01180c480d480180c0640c60510301c0c001d6040060f07803095031a03041d031250015101701c0b00d10500405003101c12041c15002c81615114406201d5201745016404540007203800014200940c500c1c242800d1038414010850740c40020030804112440e00a82243c04e005e0380d943d0180c07900d030b864a850300c2c1303545e004031809a4020710004000401a400a00707204d072207090f80019004201c11601c8510001c0e0700120740d542d80381c00c100888042d00348903681302c089042c0f9240c24400360949a01da1031344a207020349020401102181c400c001511011038641120010040c000140d4407010821800c06111004000130304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882274244 1250 882272994 882273001
    0x7020301050702031b011406240a03060501082202040507090b0c0f060f0f01150306030212060403121a090c37090b180f0d0804030209060a0303140a0c060e0a0b 70
    0x10503c5041f005418049070100152260000c202c54562038a54074540340148810350182516008080c00c4420000d450128201e800d00c1c002400681d0000d201c001890306141e81ca400c1c242001042c0002107405440024254030799034401c40303940c0100e4000d141007610005007440c5021000038003402d2000610140c51550f1105825600b81c1e050a0304c0d51915581c3c0e401c014892041143c09a0b05800144d041c005081940c99000c100703c0841118003450b5600a581000141a0002d0880c4009170f0000d00401c88680050b1a81e11514800340c000c0f0f009007090400500c103994103078200c500b184074102400b4440100d1016004104980b800ea140c90340b03c0707115424500ca801a03034441c080d01d1600e0080c50802014040e61801c1c518110803543d405958040342c80c1791900c034461345140d024052258140e440f800c5006000310b0b0b0302d000d41400e00400c1d803d00304102007540f2600801031011480e0341c00b03a540120f58012200441d400602a18241c1362180042c0030b00800038428000500c20040c02c2036596 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882275494 1250 882274244 882274297
    0xd1b050a0e04121707050316020303070212090d02060f0705150411040b01090b13091107030504120f0c180b1e0f01120608070303170112020103110702030105070203 72
    0x8416200300c54148014001140002d1044180f40500c02402d10f040600071010406006141e002039800c5d41c0854000014417a00c1d00c4050721850219480f03000951641c03e055000039a00c00840c21203d40010000c19446856a541d45420480540045c041074541c0e0b00c4d10241c140541c40030300115030714800c50061070074540042d09800d12998009000c0121884030b001480054511018480d040214000f40814217400b200c004e8941d126144560900306801d1001c804212500b020820101348014091140081d4bc804122401d44140000c0c6140301c540914104005c81c400280003404e0b0b80110001042407807090b81c42c100345c6402c0c44805e00140359034405100c0c2d10511856140c4010300c440b0040ea080e420002005a242041031500e0080202200c004108817070700e680010074a03401c150030400505504c00204903d80c800615000b055501d00500600d080d03140c0c600080c1032540360010100140660030645458540140085c00103160075040203403240d001c50381d032100d08465001a0f04501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882276744 1250 882275494 882275509
    0x905010923010e13210509120c150c0a0f03020303160813030522030c03051203090c0409060906150f09020a0206040b2203090815070f0e01020304050d1b05 68
    0xb101490f000c0da21070344640d034000c120707a28058015a03140019014050400c5200000d94803c000d040d90f40c0c94448200d2000c00c00070800007107401c01554018518860243d07a00340701c010030015182c6400e0b81c1c81480040141c280603407440b02403c112000b5003039400f4035402000851140b8011000b03060190403896080d5a81c05040c0c4110b955600d100d5143d500003405140200704c582c50070102c42c0001c140143d803503003141c100c0d0f07001181c90340c40c0d07030384108100041040315034510a08802d510707045241140701c030396485401010007807040d44c840321140240450f9070f122607a4036400810a1201c0340480a80e425007800030722444428021001c000610240d0038425207000250680c09404c65885507203c00c030303603e40060404000200600c43e44101c01c40c14100c00d0b46030034400e486aa05c45440c0080031410212600e8114260305422003c110305254050007604840080382001c4d14116042030040b80f96004a4103c107411681e125000d20500000c60841000f4840d08400d80b80c010f9210320130311002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882277994 1250 882276744 882276749
    0x303020c13060f08070906120209161e0f0807020106080a06150b0a09060e061201121a13060b0f01020309091b0406030e0c090603030f13090501092301 66
    0x40e0040146480340d03140c0850086849140380c1008520301c0d44502d415941841070f42d01400455003d103804015441090054000805c081c6d03040700620061900403e4005030010500c95049842c030040f40d81d801c1c007c91283c2c0900c1d14460300300385c03151105400984880710b401c01c9030b008140e1032070015141d03030f01c14051082510107030710181c02e002c1200d6071050050040b0500950007581e6546000c61000c00300c07000b4000003202691707011802450400003800150b40488101e003d00381c10050400ca2040005109044070b5113040f09580211580c00d10400700c0007085941d42c5110402c40510468143c4c080c0804042800b441c0100300010b560810000e00000c0088502c1c0560020310001c2c40134605a8001c560105000d06003005a0b031502c4401011a4815040440481d54401c4001501902042042e2100318203a405041c10b082403c0020b649001d0038002d502d010740c0005200880d0342600c1c014200401c0010414400c650b1105800d50150022541c01801c01d6080701d154001c919048020904 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882279244 1250 882277994 882277997
    0x905040b042105180402091305010302090f0402030705012001060e010620060f1317250f150902120303040326072003160c0815060f2205100f0303 64
    0x602421303044846009010081c800b40d01c00e50a10541e4003580b03a184840c2a10000c1141c0000c1c591f0540c810020340320400b4200302c1c07100342d000d400c000050710b00003038500c10340e0403d081040c825143e058106050040802c4004055401c03c100003600043e00c08500303050340c0803070b1105003581e00b04602e00e000702180d214500801c0d601c02404600690b81d03958255400050891720b08100a005444076003842800000c1c251001d80e0005203060041c0c0a070701c0d40040400b190907803619400181d1038102e8820142030340640655404051301d0450502a4000c6048a901624075000e1080340d0308001c1e00d9410031201503000c14032101d1072103d240550b111001c2c4416100c50310752007079211102c080300c1070300c20080d44030a42d031a40d1000ca280080304101504c4944a030700304440610742c042c64410123040b4280c1c04201e156201680c0041c00303c486100c1c46501207400e6030380903445080400000c481030340a00060f0203884241202d80c07072072851900042e20803042490f41e049550b55030041e207003c0048510000d070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882280494 1250 882279244 882279247
    0xf1821060b151206360c0a081506130b031f03030c11010306030606080d030c020303070e01080603150c211605031009020c0d02070b07020f100203040905040b042105 72
    0x20110600c41005500804084c003182101d04864207420403160711010700f00681006a0f805c21000d440040b0100d60000c840c55040d420902d40c404050038042000c1c0c1401040c88404420741d00c262602e000f502c1d41180e0300100c0c0f40e40196100341d69a002e0f801955806c1100412586100d440e40b40b0040340c07401c595140d45c0c0c4005681d030319105d50341000801329001d4100350b02e400f03001011a1050042101600c0018043d00010154020180c2242e41c2c2d4944101950800c2c410040e03441e81214820407000c0080c02d025030241c0c1c82c900040d00742802c0c050703010343d41c050140070720034001c140f00c01800f811070000600941c01c00e049441014812001c031484900705058030a0042d80c02d00c070740b000c3c50304a0740c820001020b150302c9507a03520070781e00320f180041020740c004450704001030350406c0300e030005020343c900c1c06160042c150040b440c0410281c40440c050f40b0702442964030980708000b120020b220880e02040a410a0b207881003400c5c105880940e8a003140c00070b4a0075030160207a1803c4034002c02d4550a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 882281744 1250 882280494 882280507
    0xc20030c130b0301020d0507110f0d2708160e040f03110a021e0a09051015050706022109010507020d120b210114070f1821060b15 57
    0x4006002500c0521400790b888200b01c04041c0c40c02d0010300750141c10064003183c40d01d8480780007001106410350600301da03400094103413281240070401c03510000852401914810000030100400481c0c20308a134a0743c54040b01c00905d42e03034041195019001c028504440c5990394003403100f41e21400303641c042d14400700020107000080c000d014000301140d2000c15640000001e4000503410030031007950020040d280922041e03244ac00b40c4a20b0f020301081d45040080d070030005040a8620954085c450040c4000701800d80c040b0f0180d0709881c41d840c1d012805540d80d040e4107140040f04c5020309441540d440340303080403e9813200103010300c81c031802c4a5030042c0b5031001605030443e048804181030510742550b07044118030946500b1441d0140381050a1420f108034101e569550850300c24020010f295600c440034030613a15406030134003c09003081c0c50070900f02c0e500488201500c0f426a840210410b1641e403c03103e81d420302e0b200d1104818014101044003c121400b80950703034098480c0080b0030740003049034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 882282994 1250 882281744 882281749
    0xd05090703330207050109030f03060608011a0417161505070f0c05030a03080f090705060a11150403110111160f1a07080411011817010b0604060c20030c 67
    0x200c0140082c0c640c94405803090385440340c003243c0c0300410582d0140d4445c1110018150480d001c600d04000c41e20781001014900724005090903410700940d808445181400f1400d45c5100c07050703d01603c1107040e08130010b822030403055501d09103018205080d001e00314001460300c3d010351b00070390800d0968580700c0c0360488950384c8049034035080508403092440100081a980c0b0108401c1c1c6810b442901c0308610750030304400b910304086004041d5036841e4440d070014404c9407101030544803805224203000680300c142d0445641052030043c040b881c401a06402c200c2455840041814103141500080080c14036a00780c0f06000d04c0340c41580481d80d03800c9800ca1000170b0404801c0204203009018030350420031586400105842c0c10341e000400510075805202c00e0000281802100c040242811070090030505143d00c1d2074000e5202d42e00d0031004012000c08100401e4018660141005103034594890320707000d002d40300001ca07203001e4484411490040c403000519521003031815100500405102074074808 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 882284244 1250 882282994 882283043
    0x91e05040203071509060e0d020604120804081c17091b04022a070e011a1b0a06050a060509093429030402010f0e22020d05090703 57
    0xc80e01441242d8001526141070420140c82c4e0310b07542c2c0d41c00c1c0726078030304100241081071403c1d180b8480c030032102c02440140d07034190840d0101c81c20b00b030710031140c1e141c682419041801580d11051281c000c032508075142d1442c030040d401c0c0703540150301e6100c401e032a0f4041126030350400b00d4468181d5400045640000003007101d5aa86000e00148098070700404880c4444210b04ca41d11880b5261401c2344051204110500c948400b4008075078110740d0640c5007a4114050140c3c5501c80c84110200044030803050b07054803202d8028901e01412202d4100362450003a00400c01146d003000a145000404165440d082d600c00d401030100744018a280458011040080d0761403182c0b41c00000034181d801c100406c41d00302000010050007035007008100c8015031044940c140c203110000501820000c110043c1c0e084010310100b030340d4030700c2e02c00e680b100b402010410381c0c4039243e0543e001703418400301d01002080513002004c40701d007501d10501150b10742074107050f90741c20715000042c00003039440d46400b0410190b58 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 882285494 1250 882284244 882284251
    0x7170c031e031e0409140705090607060f1a09070201060305030f0a030b19080c18131403070807050c010503040b0708060409141b060412150e25091e05 66
    0x10300b40d034076150403c0503030843c041c806500d600c0300b0700020508225000d0315100d40a418581080c45440e9454211001481e038030481a016100c1c2d01c02090321024400d04d64000f081c421180503080098140c1e1041980a000010f542a8444c1b500c001c00a074000348180a400101d0b07038410015410700c01c10351094642030700b0100001c010107565048141e0642d566102c90303100000040c41d1444128103241c2824203040c4102c2c19140200c2452012001201c00f142045070302c1780c1c01101d200004c070301d02c0c13a01c14200c5c0c908041281030b610000c03414005210794600149580e61080342215429041b1200560752808200d9002d041000c4603000038500178080c1140640c0060005d1001403030b0f400c541d4a104020745107a44103503c5901465999806003491084580e4a0500301d510070300301490078031030070905000408020700105003215000d4001c1c405801c0180398614217803d0319000d0b4125558805403883d41d030401036050006506c005045080d40c441c444040070700ea124803802600c800ca81c10042d03e40074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 882286744 1250 882285494 882285553
    0xc09090c180231140d0606120b1f060f020a060f020408150903072603010902070519021320180a091413050c090405010506010e04021201260105010807170c03 69
    0x117540800000c2c01e14420000900242e059080846056061980111030b009000003800c000000d4070840b40c94014910408803840781c940340011130140c8104038100740641d84010b2800b428481c0d01243e40a264025005031907030340e41151040841c01070b0b05069a001a50100b513107800c01c1101e2004122456000c14140c0c440c0240c05010310302d07400c49100d040d40264042d411140e03003c5114400c00a051000003800544144d00c410417003034580008410211032000b00c4451580c4e184085080e420300000707091069080141292508801000701ca0b0810281808038420312071040041601030941c07240c11503d4100c42c0d032144065840d207003a6a40006920030984003441030a0040c0d05940d07070300304d8440c801c1e4464400401c1d5414004000750103804800c26061050380180300900000c03441420490440c0c0f210f2522905000c203400c40078601980b11782d0141041c0d401c100c0081006440091039000b10781c06000701500303605814015984421072110350b25855000310003c112403910030900b02090b01030a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 882287994 1250 882286744 882286759
    0xb1c0f080408070305010b12010e0c0103020319050a02070b070804170708040e070e01030e030a1211090d030309020108010b1206010806011404030308010807080303040c09090c18023114 81
    0x340c0c8211843c1240c142d004a40f180c0d1260540c8a071400c20398600c00103100000000d202d40b0011a020f5602d81208054080c101940400041c1414015035100040c511184208121604110403150045d40c440103041d900d050001c4003040802d40b00d071415a2182d0303001049280e04450350b680d42d14066014078400c1d40e0100f020301020a00994403140140600d0407501c403080703c179600c20000750a6880c00458950103400500036120015041400601140030481c000180840a221004098010b0111141e0060011003018003050b0b055401040658000d80303d515450780e8400c4124118400c41c0b40901c0362911440c00b0913603030b50181030b1541c0c1105050410343c01125a883c0849080d4015510a0f00000d000340b00400000d0070a20ae481c01601400b000b6524504d0646c40e10741401702144140b010b01d507038600f21130051011440d9400c001d000310344100200703110761407071100c0a50440440f048054207001e02802141920490f040350300c48110191121f003d2800381030113006040c002089420040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 882289244 1250 882287994 882287999
    0xc07030e040f0506040b03030f0d0510170d02150c160201030f111e07050c01140f030106030518010c0912170a050415090f050f060712050408010b1c0f0804 68
    0x241c6001d960310500c090704002540f4a0803508010a59580b803003103d00035041048688043c0b9030810885040e405c5003040422291501c0c101c05110004170703448234180042584061803090070104004d1401d03400c80d4215034604400719400d03603e841c0c00780c0e070f11300700200d0401c5141c0114081e05034440c1d41c0d0780141000501842120300b404143d070b42e0080c849580d10b00000f2100035030505241c000c0e02c80e081c0140e080c1d090031895607656030341e000d0408150307041c004810060702c000304d80c410442d03450480050405407a565151809009000c05031780d50703420b81c8410030b040d1031981014840c4241c808040d40e202c1040e98a03013000320b00c00100c0c40c4400d403106e40406206110180c5003000030329502c080c40d40d400d0f0380c40c0c4ca0041507004211107200700c40c007000f1141c0420441e54051031416019110120703400b82c046100000040d0440c82010300081c100e91000494420058200e00a80201e03400b000003803007203801e0501085114490b488460144643e180106808140e03015507500e200b40c81200018501074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 882290494 1250 882289244 882289249
    0x9140111090405190c05041e05060909100312050721020d0f050d0e0307030e0d05030d1109030618060606120f07031419060e0412082d040501060f0b030c07030e 70
    0x1c6030002610007244000804000e003150400c072340c031458003844004440320313814100000c4161040d0b5024070311451401010901030550068468005c551046240303d06400031000580560051403003a43c81740b510802c081c24120010080180310344982d4050588503040311001d9a000c0e00c401c40c44420803030244080040c045092140d0320035900741200031a2100b8035840c008242c2c50b00c011400b800b802c5001841000120004107441c150003142e071011682c4403043c0703002c03c42c074003640e03034105e0340b40c891101401402401034070f440c45600c0d500810b681c8035aa55009001440c441d50a00c0110262510001107040307011400d42038112400d854046100702a0003038000380400b0540340340d0306000d01050bc1c9081103a01c0d06c10b00700285640c0c1e29400c0b55140544a0031ba40c160340308002c2e014440c08000052211281410091950304081030011140154800907032000c2c40413982141e084d1b28040002c1703403075110400403404a03107042400c04d180d5603400c1032005254015400480a0110445020490385d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 882291744 1250 882290494 882290501
    0x1c09060e07090f051503030d091a0112060506040507050702010309080903030712021b0a050f0406090c0207030506090c09160c05060a02090f0a060f1103090406090914011109040519 79
    0xd1036040b20208501410100a104880c8081c0000089000b0715005060644020050f41d11452a80900040800250808503040c0724851511400120781000100781518003041045030300313009807010000f0342c1d2580180300880e48103448201c08500b0600c4a100150711903044070300101d22504030981081103007400b180c515000048101c0303245000c540844c8515904210500700356141412180c0c0320810b035408514003200c18000c043c001e0441000048070b07519660003144c0204402c0d40c0c10858803500c0340e0000e49070030103130200305c41e035002e04008140c5074600041c05250401008080b5401501c59042540702e022201020b0f0f42401082d24200340800c0c4240403151044268400140e82c03240c3d903034104200d10200200d503e1041c0d10201003030204c40d80c82009900d08c0085820103c01c1c1218111003903141d03002d001c2c8040c2e4490308012011805040c150403c80c4000c0c401c01070f80d500c14000d208481c0c00d0b1610308400094000043c0a12080c500d080c0e0040c9400451686040710b226201c00c00c103400341c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 882292994 1250 882291744 882291749
    0x1092f0907170709180c0c0c030b0108160503060105060a1b21020d0e12071a0d1103090c0d0303020408010e1c03110d0b030111070c18021c09060e07 65
    0x202d44984801c0742c01e071040840c2903900c2402403410b5010242451400c4d42d02c82e001700e503001c81182d41c4904403070b9a1750050110842403038102241c9040290740c4d1926502411f402d008407000b0703002d00d1ba0042c0800c0310106240013510002006414280e0070326044c010036400200c2c45204009040120300c440d92205504035580c540121301102d130682002c0c0807222100a06100d00d03085620140014501541c850310501c1c403400d0031030306a040c0c84681c401c0e05250800a0b000b011014120441540c0440508001444050000030301800f00d0880c1c1440d00155000c12500184c040c0c0210300c2c00a102e181000702d80d10018401d043c014281505e80c1c0866007140c1400a0194055004c011061b600c04000440d40d030b40d10250380707000e00503050400310085090044c003480710080c60307c0d4825007c00c3d903003c1d00301d00b18410800030482d0300c3d150181425810792456124800c01c032185960845011b030414000c480142180034046603152442c4000d040060400050560f490391351420301d00d0701d503002485403c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 882294244 1250 882292994 882292997
    0x1b07030c080d11040f052e141e120a02070c030b0a0603150c02102f041a071505040b0402060706110c030c0115030b0619081f05070201092f0907 63
    0x10041c00c6c1414012040e0404840307800b10b500319809080740705840a040901800103280944489a0005509030b0702c2c050030303210000695001c22803240003000340000e8034100480c1440080d00d40c5520291408a11407404003a08404050741c06001042c10a22080d400c1107624034001030165407a04e800707001c0312942c0f8095443c640c60f204100b5029604000e80b507080c5071030410801040000290f40518460300ca516540c00750a001904600c1d06190002e031070080071501032000c4040e500071021241540300890896600c4e0b00ca0f030105815100720310039588500d52021a14216803103d4082000c0e03504014000c484081e128551441440d039035a000c0d09110084070300458841481d00000c0f4252050310100700104003988800300702240304c1c400701e2034200c81f00344c0709040d50788404c50b001710313000030260040950b500c41d0055410b45038441e1990009041c20010040040f5100e80408a00b81e600801c4080c10071041002c95841c00c00d0b041100c0341c075065414080300000d11104000c02d84c07010040794840d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 882295494 1250 882294244 882294269
    0x70519020703120e0f1915020c0d030c02150c15041b0906050a0e0c0306010c03020a240501080c010f210f09050708030703170417070b1b07030c080d1104 67
    0x615003088039040d110f03034000300d9508a001802418500c40411b0f10b224009100407842c20701080705000348058003407100e001d01540c0c518445424003803c0c07100d00300310480c051075040049080102d11141552003010302e40002c1e207455500310702c0713483c001c650141c02a2006400203201014040c0c42c0400321000700006080130511501d06000c10040301001e07880b02d40750300310400170000820f5522048a5000345c00b400e00340c0d144806070034200c0c9440a4094014080d03d15106221024090b007101c200d0360303225040c2c00380510303a02c03000c0035525403a02c440c545000c903031b0039003224101d180078603402d4102d82c040d616040c0882c103608030001c06544000380c0b03031041103540e8a07041e07050000500461001e030160700000c505e410307580d940c01040441c2503041104c4190512002c64104000c508003400040400420b140d00d500483c01c0040780c402041d54164a017983d04403a00b00f1039030034681511321054041d2100601c142d0151501e06c550b6010341d102001c650341d00d10801c84401d814601400280402a000a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 882296744 1250 882295494 882295517
    0x3020f012f0607090503120d0905060414011a010e0f22050402040b0f031f090804031a01081207170408070b040f0906050a0504020702010c2109050907051902070312 72
    0x35824024094041403c210950300f05005c5600c00141c10703424250520401d5036136400741100c0324014018000002c1150084900f0b2005016088040750a0003c61400030030004c205603d10300350200d20349220501141c01e041031a075032032606100c4c800c0d080030050680c0441d40495061243c03080c1c403020f05e0343c420980d120180400c0d42002e104134000604180e418402c59200c41000035039030b0f1542100070120103c0003504202d142d1041d00100382541e846100640c03600e89078500002d104410090742d15034591810300026a20782d0000b41501c02d56401320310030f4036001c1c40c0d03110010312083c2002545a441d000304030004902204000c1000100300c4a400d1b207072a10308003a050b40c8004060381c00401198201071040c00140e440c1004e54040366422079005a0b0f58190380f0041e190709242034006030003407800400300203150800709404501c41c1055a26420500e494400300040700c10b05450040000d5000c1c084040701e1142012044040c0c0410b004580b56030390340e80e03160010b0f840d45015220000e581000304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 882297994 1250 882296744 882296837
    0xf0308150613060e04090b06100c05030f0301030201080a1a1512010e0105011d090c0c0c15040816080d050a110607020703120e032e15080c0108090703020f01 69
    0xa13500840c000c0302c0c140b088a9860302c404005002c003030f00740d40c442c4a003620000742c01405200010a655880025a5164a6000019101d03030b0424841640464444000240b40c408184100110741900415560880c03915405120b60700d02021202d45114404000c0c02c00015010f400c0c01d8024078200100122541c14a000140105ca2805c000c08421403030221915682d40e82d241104c0d8400320a030072480e15042c0c0404044c1c608600a40050742111804012400e5494088020029114104111107000540c5e03e1200c0e44103500d88644642038200d8048590480c1c030680c003c0c41562400e1508502c4071124640c410300b4810203640d0b0f000940e00101c0d0400800106c400c01c0016000700e030800b0b5141e1890b000c0402d4131540c001c03e44c3e5040104541448904441140d00c21043c9188800200b005803c0502d49a2480d011809403d442e0710980543d00e00962041c2d0380c040c81003031404041c111117459582480b0b5030100c44c292590500680c40c99503440a9040d0700f502d5000d00382a6581d0b5043c410f000302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 882299244 1250 882297994 882298007
    0x9150513090c030e0d090317041d0403031a090103020d060e1b04060614031819061505101d060415050304120e03032b020705160b04030f030815061306 66
    0xb904c0302c1500620b90307030395402e0f82003641d0a0449400c491103e0b4010b450035117100887c0f080d03401124181c0130a00d500caa6400b9a00708061185100b45c404000001c40d040d144403c0c516199005a403155070440103000500f000000c0e050390278840d10300070405903094840d441c2088100350789207400010f1601100d119140c240039840007043c07141010780703d02280100304805480000c080340c054040740ca0540031400020480d00d2440400300c00883c08060507450080d019007540260381900d03800409020406280c0180c5410810f41281c8031a01c00c544030300000e1601802560782c550b403001c0d050000282980700c80051080317100450f550603990340b401740b51001407400d840d10700c0401c01080300d1228485880001c00c803402500480341e1000ca0b607000c50f101c441d00d04a90840139240e5400811481c08002001401c404038000b21030748840003a0305d4a15008a9000d28400946450144101000464000c6001942100d0910720551030340c03c40c0b80214804da84290981050b404120701e040240f40d0f8001c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 882300494 1250 882299244 882299261
    0x5090312030c0715060f05211b01031a0102071e0e04080c191502070212030406020102040f060f120c05091e010e01020a121b060f060e061009150513090c03 68
    0x810001b4104100040d810480f0701600c1e02803254440c0e2000a174032307240f18a8195158140c03c0320807601c4404400d03540c44000f20039190100c1c0c100391090150100c03481061140356810f900600d070040c038081d4858221406461003030b018140110020500e07986000d6141e100e80d0258161a42d502c282040780d1340350440c00d15620b036102c400019204001200c1522001110018010150300da11150000a44281e03c180c413179a440d1000080010f121601900a04100c60040044041076980d4601c02d07508604903a491000140c05600c0900940005500c60035080318585462402c12120300302003030303c038214a43c406101d6200c1d0a0b02482d90b6901040311000c3c04170138405010900003130707a904000b915207078900700700303001000010302845120715031140c0509802c00300a20690300080c10090080529019200e0310340e8860b0000380300360074001d44010400e0000c1e0740310307003000b45400002d0800e098140b80c880d0411a040005540c0084090342240151000620026001501203070113002c03a040e15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 882301744 1250 882300494 882300533
    0xf1419021512010605030604020d06090c11070e070807141803060a02070f020d14060705030105030c01141b0102040b07140c1c03050d09060207050d02061b040605090312030c07 77
    0x70032000c80c60b00300500381c65044030401d082154903520713070b000050301a01aa03c24104003510380800001e0baa111a005400000e1954441d0444850080c440755100c482078010340b03c94141c00320120707074064407030028980c1c4082140381000c58142425200320307440d40f0090725030010502d081030b41c1c4550302d806d00007150040301c02035003140742c000240d80d105003440b08450040e10800203615807906000c0315109808188680c0c0c02507802c680741041014216400c01e0291034024400c070009a592035004030000c2c84522111604103042010110204144050214443c0c003155020b01c00060480340803405090964401d26401c074441c2482c0ca401494068000c100c103202e0043d0010103010300d0321001d95074603001d42500e40240e0310358404201c9405895011802011140300044a100748640403030ba9170041c1b2080d500b03444803904e0701001841ca4003011800c1e2888501d0400c810403440d03019034000d010141004d0140c0d40500c64010917030040c2d400441da0f01c031812034000707508400c02c00802008050841c64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 882302994 1250 882301744 882301747
    0x2030615042910032d0b061303120203071509030c02090901020c01050f0c0405330a020c010305240d02030d02070513110a0e12010501090c0e0a05030a0f14190215 71
    0x501c0f541c4171003c0b0350040c802101c050018403401454881d8000f00d1921a014203400da40d142c4c0b140c0303034002c885400e00c02a1450050320340081ca45074804011661500d810141c400e4082c1d19403480200286221a01141401108280d400c010384410401f41d106222440c001070f260f40c074030ba040c0c07425504020031440b65400440308005020002200740c40580b90180d4143c2c1400c0038812051410401000200b080c141000400030f56101d014001009800c103540e0a403600c0300781d03610054083d078034181e81c2c0c1e01850043c0b01c241400000084407000403944014990a5484900e0f00480c2c03e1219000d8801b005810411050005040012007a07103100c08002c03080210058814991615000f5540c042041103034641001d0240c0c1d40e1580034080c100c1c0307880000c10195a542400800800d184c94240c4082405034600180c146002c07220401164030140c0508204030706590381580010580d20121500040f100c0c40f140a0780c8108111a03080703012401032120f00310310740100114411400c55407070803000d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 882304244 1250 882302994 882303011
    0xb15010813030f090905010b090a120b06060a021e010203100b0403050d2102161211030f0a180608011d04081605010f09080301050a0506070203061504291003 69
    0x40c041d400840468051621546800985804803041c10503039000009250a140000ca0341080420082c40f00c0c450458a01c41c001c1c4d643c41c00d9020350314200c00c000d0011401800041c8040c145003008003100d1146206460300d050100390317040c10402c42c011f0720796566980801008014054200104080c0041d0078249003440d2071a0303644c554075901c10b0060010001c40d95604800c0710340350081ca5806c04841d0030305544641c005480a0f94000d0942d00c1034030851054024800058014204440f80e07440520196140c845c080c400e000e01940101e2466007080f2412079500e000d0803803800c0d028042d010030742c1c9409003945025a26a4400e921a170050300454445091200151081c011103907480c02102400c0d034082000c0c14840c0c0100b00d8003034440c0400742485c000e801000403400095040c4c031000c88410040684075010300c10340c1c1c062600025015448000800c49800c5a000e03800d016000c02070010460021242402d14141d2003039070006240041d50004481519111028503039641840c6410421040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 882305494 1250 882304244 882304261
    0x50106030b151e0304050d03060b03071d180f040c21020f1306061101150303020a0314160308090c0102060f0711010f021306020f010e120d0e0a0b150108 67
    0xc070b2076014954820800955400040301d01c110b14041500d450011070345a107090b007061a1658481a242d0f80001e15084011500580c000140d900520303071603a0300c1026880084688881034441c403011039101c10310350070425207600d51481003885035180c1c0040d003c0c00d003020718100c03061354400d80251490603624480031140032355104901510380e4040f2544003008845101040c4086800382009610600304080030a0352034021500d40c40e0090584020041006203500142c01090329010003001a004095198042441421544084170f2680304141c0340003020030701d200044410600031804240c04100b0801c2c081c2c41400101000d8000f80040d1004e032404047c0940b00401c0200707518240141003c90800a050941c4a11100c0c103803218110b58801312140c440504100f08d00c501e8006100b00740b0b00251f03444043c040e88582030900b5000b0100f21050f44020900e43d000000c41800e610740d204680c00c1485000c00c9107105180c0698134052040c140120420560108c44190074140300d0038005024414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 882306744 1250 882305494 882305509
    0x42105090f1005160b150603010e1602120a17010605090d02040513080c07140303041424031513150e040317010602060109060e090a020f03071a0d050106030b 69
    0x20003107a141c221080b80c220251494010384801158240100c0b200004000355425881d025401c09801c00a5607224601000f90a100034001d0130619050a408105150440c2c0b0004002c17144600569015002c0c21000c2e0860303400c03c50400000446040040380718104c1091010b0140035a898514608054500820711075090340800074041c65403103000038915800c1d050070410f030b154400c24055941c424000c006642c0d00480c001d00103e20071828242240f481e0020031207044030300440c40c0642d950300250030081170f8140d5058014040c0722020f21200b030000304000941c420f61b100034500c50030082e03020600001406860180d624107203046090046440701c903440c0000c8500d0182900304999480c0340840d42020512498060341c05010000b1481c0c0b500483c1c1d03141611215041000015a1180c110004441c103681c4840f4580007031200f1400740c201810401c11004c4090120b17680740380d9035981a01400d541c440e411b15800000700d8170b0a020f008601031503005116a140c240442151080024440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 882307994 1250 882306744 882306769
    0x12050303160306050f0f0102100e0303091c120c0507080d1e0c02030f091c381f1a07060b040203041703040c0302090a0b0429010311040e04210509 64
    0x480e03c0d503990386e25582c800c00940403842c0001006101200481c100c0390703926002903c54081e1800340c500032611903036800c812104600300d19581c030070900319080421801803288064144c10801c0030801c141c0462a00c800a01205d1442000081c6201c0100707002c2c40d500e481000801c3c0d645051941d40342000d0340c0002070343c083c8400200500e998003130040014481c4038800c540c9030b1503485074826940900c42100b00304948a01400c0c00220003001000c82210556040e40c200b90b101c941c000c1c0803402801601003480d1150390740e04000307006592104400aa110060008280030030070010b4028100201e50140f810600b800751419070031741c06d107a51030303000c101c1c2080307060060928040001002d200105800c20002c680140c074242040c20a0085a0040c0402e440f11038080ca040000e440c03e0b02880d00072203a903005064240c0e50071201c48000440181003074404525111005100100e92500050849401148203450241ca8941c620071400c4405810072102b00a204007031145201d1b1351100604a8030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 882309244 1250 882307994 882307999
    0x403050307050c010b1009050306070804120305070e03070f15081b0c0a08071209080a02090c09030c190303140a09140112180506060604120b1012050303160306050f 72
    0xc03694443c10103580104160004c4d41d6110a24400840c1c0c142d421041400c1a80d1068058039142d5803800130540d800c04040e18020841070402000b47d81d464407a0340a81d410240900d0402082002980040e1030500690041c88031004561410040e556154080c0c0d51076140324108a10f26103024140c2c03d82c180526150030039801c0c0009003429250000340410140e056101ca0225140e15540c00c10300d400400c480c5500d8003003100071502040910002031095203050340101a03150300d950310050328003c1e412a05d001c3d40c2620440c0705804071961001c01c1510000064541c02c442d507131035800c0040200741603070404115024200418a8250b0f4040d0300d0000b40e4582800c0748a2080c48400103c500704410014a010326181481105050a6042c05d511205009500706c0d48551592010130402d84030380c0c421200c48414020080703000440c2c100806600111443d04c1401c1955a10703140040548414011102608000100a0311030030748040c20710707031000c24601041a83d0505003c9140c1c00c900244051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 882310494 1250 882309244 882309247
    0xb0114090d030207050d080301140a080c040b060c010204031a0a05010509011521021b0309030a02010c0c1505120a060e060904050c04020d020c07052403040609120e18040305030705 79
    0x40905000304451401028041d00900101200b802e100125230400e004142030104034980982c41c0d4178008041c07a00f921802000340c0406074500042100504021005a0300540d0602502c0d56105081c406072004500880049120324002d007112541400c005040307030000c0e4903040050080e52a80042141174034403045032400300a071b81d2041541e802d80b03003a40038140b040307500c2c0380c214441249030041c040c40d540c0d800e00070651808402d860381e101d0150b4100e450301540404503907009580f10b8031051079140d01070340d071100d802d0392507004603c100c03081c42045002083c0c001600c411044500c3c81c3d0140e010746680350400c0702d036082065402d03a542000e4415482030382c211011509110050080910000001308110740d90b05e4001d4264002c0d410001050087e4096a140003900303003442500250301d68104070100d01100054003071002c1d26000904103490b42d0b41c1d58044800050740d07081e50843d40c201e2588681c80140310910800c001c800004158030220105c080c14000001e4020341501d4100f096410041d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 882311744 1250 882310494 882310519
    0x60309150a0b10090e0702070303050a030c091205030318010c020601050d050321060a060e030c010f0c0f0b060a0b0703020a08030901090803010e0703290f04090f11040b011409 77
    0x4014100c00015950300411642003c550941c01030031103400c9402c0381003031000698400c00700b0f07a00e070b810510001c0d001c0b601c10400c1110940c0b190344607120180e0b5905040811644462114036600c410000448185d8800018003030f01030300c24008444003034110b030028001c03c2d1a03031100948624042c4134443c0a4640c11040c0d804025041c01696020902c0300c00a065021007040e400f240c88206581d01401030004840c082a00703131040c0320303c00010354083c1c010842c06078144011a1034500c040c001004000c1c2009000000550941341441d8480c060140e4102c14181841044004a5a503206504410081200e940026000704440d54220380000d1065125650b6140d0280544280e03000100040b2002001088401c500c1d84924094581694200503400c1c1b1800300038070880030003000d00c00d85d078200c0300004082c0c540b403483d0340c8220780701400114111480e03903919255030204042c225600f50140300c06c0001e80c01c0a104001040070246040181100c0c034000c0140705208040a00e4005c1e070b0f490694 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 882312994 1250 882311744 882311761
    0x305090111150118020c2805150106090b251407030b18060907231e040b0f0a03081308030a0207030b07020d05030f070903020a08010c0e06030915 64
    0x516500014041074070781e074902040650b1010542401a64144d2080c0e20742e081800b4141d10079546000c0183c0c00400b008000803810310b01010711018080e0b01103080110400010f1030500c034030f80710765102120b262819414000080c2400703c00c1d0b000490074540078020f2094081c0601105846440c0f0410500040fa0060515801d070583c42d82c0608003d20a00d04c00008010110084031b20a043c40700c2030120402c00301e0074003034650400b42d40e0702c1d0719a4042c941c284100307140900e044008030780300c104240000e900d04c40804c1e80c0041003100d00031903d02c00b00d00491182014041c00b1104541211036100011f14400003480c0d0703c2c040e00000d8405080820b000758404a24044031002e480c0d00c3c000c03241c6450400c44003c2d03036442180421540741400030b01107243c1d14000a41c51103617041d5a110356043d0783d0b50855007160380c00010411809c02003605000030240c0c464052880240c00241d0012a145120003c040d00c0c11080074010b40c0290740c1042000041d0300086046911000300901e00f040c0d980b1400726 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 882314244 1250 882312994 882313007
    0x108120324030f0d1707210b0907080a0c08012d030b01030f0c0b04030b04120e12030414030601120201030e030708130504060909050c120f0102030c09030105100b040303050901 77
    0x22042d058400c03080c00d2101980c1c0060f40702e198400b29926001c40503543d096125500c2416551a80030403056075581c05d01c01c00040c4902c44104441c0400203808030401c0000b80c0c06482910880c2c080303002c0c2002d101c5941c111303005203078903200303075003020702071949084000b04680bc072000c1040f842c80100d81d40c440c84800d861504070015508451013011658690030725001011541c0001c54400520a00014604181034150390880c0d8001e41c01c94110750b41c83e1162010051002d5502c1d08020b0306515051140e40d91407850480510031400560f02c403401c000541c81103a40c030310b1f9058402c7c3d01c006c0040103081d4841500c00c0150343c2c2031a0110340b0921005a040c0303580601c3c40001c05002c80070800035440c43c5544040003c458046030140500c80c0c0d21400c00045408601c00901039800002c4d04240d075041145c064400c00419000b15880c2c1d4501c7d21485003203800075076801d00030300e8002030308030003501d000d0290341d0304a21202d2071100440e1528000665910951100070203004010550542c01da00604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 882315494 1250 882314244 882314311
    0x307080f13050f0d11060103050a11060d09050a02030f01090f2307120312050c0d051801090809040515100f033e03131e1a040b01081203 60
    0x1085804486482090035204c0061494050008003081c056850b0384000145035812240c004001c1c0c43c013a10b20f61038644038019808101a08081c04105424007240390b440b580f41c0c0f071802440038203881200c600c101804d05030b01000c03a0080342c0c100140070010501c4951844003059100c00c80310b4230032140061009409480c03d078913100da03000c4d00704009002070a036401c050b0624401c0d5a42000d03105420840030440703000740c50361f0341c0301441408024412400380c0d0045070404040101c1244001c2d005208a00390307808142c08a0700341c2000300d90580c590400c0e0141e80c0e00800810904142300c810b8001240c1411020200c22040002c080c0318442d81c20b0081d0300c10702800101800f2821030441152440d04006003201601c03800d40d00021403400003041c0e110550380075402c0743c00780310302d800115194104c0030072103c91182201c07446018003000080401d402d10138004c030000e2400002e0300d0181044180544142c4c00b02c41c09030491180c074443c8a070030004603640595043d10324400e440c5082c110024495014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 882316744 1250 882315494 882315503
    0x906050c03100506091c030c03020f0304180921030b0a080c01020a0209100302090a020712180b0703030f1404120825180806180a0b0a0b0d0c0e06040c050307080f13 72
    0x81b030703280051551040312140801e01940807505c0312800014000e989100310311414070307043c03c035016800d0010360a07081000d4140c01034806000030448014104c20307500c0104000e2010079640c0d01060f80c6401e01e82c0b050801440c20340040d080341c04985d00040c2d110400c1100080c0310340518400201d0181e004a40704010319005043d500c5c152602c05d181500a50204c07200340c942c038070b003c54981003840c03041002d40200102400c00c400c605207090300c18041e03600a5001101403644450031440b464503640f0540a4000b014001010b5900706410850000072040746180204400401001000688407080c56203860740240707940e14150308800c0403600301003c04950380c00c691040c40005245000000c81c0360050410010b10403c4180f18401960350b200078901c000c02c90601800020380c040c07410340c00001c0442e001f80c450611600f09a950001e81d0141d030b0090383d0307000882c074180481400c040c031529403d0b650a05105145041103040a4141d11008117200e02000043c00051010455400650321f1103610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 882317994 1250 882316744 882316789
    0x405091807080a02011e142104050c0a0812040b07060f1404030905010e01080408091507050d030b04022d09030708060f0a060609060e010504051002010906050c0310050609 75
    0x482c4802d545801c0c00200070380c00100000e030424590080c1e0700c0c40c0744c04028541c45030038090a0180c4030101c1d5030402d0745d01a54400e9031101800c900544003200d288964401d42c090051050b4123020000304010301c0d0000b500c507a1160003c1c000c520740000403107040d183d50b0f65049455180e10324006001c0d011641c0c404400608003410510914522044240158840c1e10340c1c44004d600c0d80300466002c0c0c600031004e40002c4030740000c503011983c201c1c020400207071301500104169501101c0d255559020140441c3c440d03000c04040340c03005501d8810100002c2e41141c0552514255650650384101c40b00070354840b003045030102e101c40120410072540316860203000d46441d15550024a6110842145c0131000c045100d0006000207000c0c1c4114002d49080c2d84803600054103101c011a017080800e1a000d060041c03c2101048a030b03505002000300b20307402e40c004540c0c00658504103040e20405811b26154450510512041c1319049601009966068624030b8449440600180802c25805510a0380507803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 882319244 1250 882317994 882317999
    0xa02070c0b040303200d020d1b0b010b0a0206070f051b0c04110a030b060a05030f0907080616020f013c050709030b0f01031a1e090706020f01050c0405091807 69
    0x421002503801c103580e5140c44a21000000701c0c2e11b40780d060240000c40141c01c100c1894080300e01407250300f054280b60030607105956a096903a00354101081c0c012201c3c030007011601011140d810800c0c00c1e1b010300d003460b00c040152810100034090780140f0380c03040803115500390502903c042c00c00002c070041c00003c20502c10200041504103103039001c20444000281041d170301e001c517401c0607011205036100b2640d030b80d403442e41d40d0324100e80b007044094940030b42405403a0300010700200400005020f41c104080152098507000000303803520701c0e66400c0c9441d0340d040070040d000a40d09071f04206507440c0402c2a00d00d08900e1000682d0f2044003039044014058030b08420303c02c032940e10140c4c24090b40d205148048040d02c603051080c00e01442480020440284040685003130a4800080c5420800341000d00401440d604841c0d101c0c0142199081c1c40e43d84821f43c00c200b040da04200582461f00340d9402080309060500c0062480d104e240120346c0207400341c0300454403160b0380700b110030b5003004400280c404054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 882320494 1250 882319244 882319247
    0xd121b050a11011103010306020c120d0f060e060109031211150106143402041a010807033806040902030609060a120308180d08010905010b09090a02070c0b040303 71
    0x20044114100056040c102e40c0c40b042005200d1000302010102c0c82c00d003168130f940e035480043e5200c3c01c665016130040c1c10300400da080c0804050845210032200c0804c03480005418107080354a117a03c4089891000030620030b169130000c1c01e0074140d80d040800007810956510040d41c0c08481310080700c7d0035101d9801c11100c02c01003c510380d4107844141d650f0104140079026003030000e00410154560343c951100c0c602201d400b00b16003015625170395203522900380301180c000030100c4c5c125442c07944404a117440200c40b15a803160209902c1802410104559014859900d80d0b40040c01c1340030488414102015100007041180700046200c001c2c0003e50b12915407120102030b4006076001402400d896001c030310540b03040c08500c4142da24100c41c50f00100490f4500725020640503060070050460200c24000b6001c080c06404540c070541d03210b00106500d04402041181c1c2c2c16070114860035014082d0180580e6118045904607812200140e10b584e0b4a0404117a04800c3d070340b140300021400100002010b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 882321744 1250 882320494 882320497
    0x5030a090c0b1b010f0204030512090301140a0e010c0807020a0b040f08040b131a0901081e01080f15040f29010f05040c180b07080714151005030d121b05 67
    0xd006010080c005c0759140c0c80c00c28140d004031301000b020703600020391814030050300d40054002c0d1100200081035883e02000c400d41c44da034042d100c1421068640700301d0b26100b0424014521a81c0e414a0f18905e5454280e0b0000c2d15104080001005480380d480030a0600c4201ca0035040b000d03400141140d540c82d40d80152140743c1e840040d003d060031441c0000083e031141500c42e01082682c42e818001d00e8205a0401181c200c2401060f80720303a403882c07600d100c01e004a6864218080c100050040501d002800c031940c3c6801c448182901001c90104204000201c1d108180106164024841300d9800207880071000c000c40420702c0d480000320100300025507118611089811503d007601d01b0031200440e02001c4800d824405c13204115134100002c1045000700c214020001607000d00b00c0a820030565540341462220084101043c651100b0881da020045182080d40c02000400c464202c461500380866100c400505402007803002a040c07001540351240c0098003c403039102003e0070076039644500a04203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 882322994 1250 882321744 882321787
    0x4110304031e091401050c010e0c01020c0d050309010507032d08091b090606040b0c0c092805060406030b16020601062c01020f0304030f06140705030a090c0b 69
    0xaa444148101405504416020380c402c0555862031603604002d105015407080d1050241048010001b010000400780b0852102d000e1a102401041913080c000a00d0010750301d000314499015415603000249001080b54402c210070309040c2d440b400301e402c1c140d03a10101540b507954842e0416040100001c8400e00c000c0d0700c100360791140e4225443e00980a540c500311515888401c508206a2301c60501c0c02d00c1c4141c1c0c0c0004000e007400e10b02500c4900e03000540d044900028100d0303020321a280e001c0d19012500340e9002e14801000005141d210804901c007001c0c00204110141d900c0010030758584a031f8200308051600040c0c0400c8038100702d5040c2c0c07034501c00b032181d90005000d408004039280e449002d465009071101c4588040c0744074600c04000c019012028440d040d40704078252108100e10030b1000c0c000540c000d605200d425440c50425406680302e02c2c120100d030120395030412409603000307016a0380248030a4000551403045150451420803540c208103940c42c00030039551802c0302c1581c500c001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 882324244 1250 882322994 882322997
    0x102070b0c1513021315081f050c090904060b040b0d082109070611030705070f030c06020109020907030b13020f1c050403020d11100204030305070506060d0c14010e0411030403 77
    0xe0303039051403d008039152060001d50008102d50b02044102c0c240d080440082c1000300f0044560741d96004e000e15011494000646003030000c4046407070301009102e440d41c08100800c4007464401d07a080055101007004100401141e41c45c0f60324072040d01e4641c0300b80b2403007002a0150765003848900300341c038454200b943e810100842c24441555210086d00f0124020801c003001811854280441070713820104070308001c14a4032085c07007010301041c1d0400c0140028403003043c51554190542c02d1600e403041e03240e0080000e5a060600b901c0c01629007500e1360342d2091240c9400500e04030a41c000a01a0901d04074800351a400400c01c82040380c0c01c107009120180c82d141d20200c8691082d0100400e41c1d60403100900542c20869108180e240581c01100594a4510039507089080110383c200c00c03600540c209500244001c1000d104002c410403000d40c00c02011900305030b030007146566051025000b4040c48409103100c8000c094540d000d9290b100c2d0502c1d00400c1440b960031400030040b105d8004440a80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 882325494 1250 882324244 882324283
    0x120307120f1a0f150a050c01020d0c031b09030305040e07021005043203040b0f040e01060c17120c0a050c010501030f0b0105061e0310050d050105011e0f03110102070b0c 74
    0x202c00b0329100801140fa40d0000204d40e040c05400c1e10250341540107042d0003502c42d5001c011420181d01d0714800c010402603240c9000910084142d09610f00e100f56440b01c00502110794818400b10360400c040d9411138400411103a10303660b81c00380032420002002146010203080c9424841080b0303030000040701e200007100308a0401d403072595601d010184085501c40094008000a202800c0040010300700903506c0014140b9080e070302e903d0702e01558000d92003140001c10301c02c1000c1c200550107600d8201800510030460400c05103c030303148a00240906400406200000e0b5002d9160051064803e00d0394400000c220a40c2d40f400c1c40501c0c0107000c0301c1119038036100d03c000300b524909903003500c40c0d001c402c80095407020450304a2051592000e00316203083c003401007001a060740c1d40200107000e1031191001107425403604072003907556140445024040ea500c0601440601c08081c41c50341125004a4121011095000141d0506480c1c0e0001004203d0016400c4201403000070804500144000800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 882326744 1250 882325494 882325519
    0x50607031a0a0509071107090504061404030f08060111010f0621080a050702030307020d03050d0c020609030d051e0103031707021b09250f080108120307120f1a 70
    0x80d06440e070466903258020030155052000d410301004140e84810b590500403115241d0035107251a0079032039445041c0352911030307080008218a40c0130b0710400d01503e0100c600b190401d076401030300f4030014024400400c074241001a4041c1c2c800c0b5800c5807501640c00c001c200c0e80500303803209006400240612101440b160b80600174800030194604c40b000c2d04101e0a41c1094079090045070303d9400800d044c2c0c0c0c0b5200038001c250240e992403c1d04120541700c0d440f05941c070b6030700301104025100d003203c0c040f09542240d810041d000c6004411513410000c032840005072a902c2e000d0100f044d0b020030711241d041129200020040641119400c42110050fa810f41926a03c80c2c40c100c5ea908032042c011081c1048500000750345040c945400c035082000071032145001c0015096260f0303441881c4407030700d001030104007107080010380012404e07014054800241060304c50700f03000d030745aa101c00342c594000c000404030aa0b00e40740031948895a8078120390024812601442c0c5120a4020040c0b0703400d00c5221642c440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 882327994 1250 882326744 882326771
    0x93c0626070f120c08030f0301140a0503250e0c0405031b030d1b0204050a0209040e061b30011d040201021b040f0203040812070503070e15040e0405060703 68
    0x850407510381c408041c00302d5050022000c1c9900540340300311012800c149010540c0380d401c0c4041d0442041c0f5070751858aa41c074007040030359a200b240182501958507448103200da0785010803064580c5400b10851085d0003603001c3e000380d80f2000341c0e01230705160208405000c020700d0000000d1044500440880c0d05800c49400304054000da00d03002c01c0c0c2c0c59070100d10402c1036240910f441c7c228803200702c1001603440909030049000c0c1d910131218841d0480e0700041052035480c1500c075110148114600410652510703c0584102c138001c08810540c8101c0800c0a00300420368005075180000110b481c00c21041e46001e020a00500030300442d0b44403070001191080303600c0c0f000492071046405a00403c01c0741c40100360196150360501d08644c2064603000d4000902c40340e400210301461082c28400e5a851542c148070041d100003a15100400c881001845103042d031100300c8005c207080c00c82c3c0d851542020580194001d115560101a5002d061030800080c0800400c0300c900c14076031920140440300310f00e181c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 882329244 1250 882327994 882328003
    0x5060105010807090e012114160609031a0c1902010b1806030a0f050c0303040b070c06090315111216090f060f110106121407093c0626 59
    0x90083d0905d40c20700100300741c040e0101100010588000310005007546501d91030104031110311a01c9141d809103403000341130400305030114010b140624242110754116510f05644c1d001c503544c0405e1848040d004030792004106000c9840500d02111a00d072a03039844800680a081110301e454803d681e40541d18054480b403440c600d2003100004c0180942d12140e0340d0b00e190001724003030183d515118901d9443c1d50381d102000188050800300f000c0a0301c03800c2070324010f804044240c20900400c000c5010410004090000710b2240b03400722240800c6058882074040d4035800b803030101d001d9550b4200148880c40e0600390b00c0c60710200b85035a90081b41929071b0346015a078601c0d84243c01c00550840180030540d07205241c0420111101800480c24035500c07030825200360b41008007550150030200c0d40002c03001013046010014501e0703070028400495640d07186901e004c0d01c5030005108e05c400380c030780c00402c090320081908802e65074001045226120001ca25015074840c002c919603d00c1c2044016000d10f0006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 882330494 1250 882329244 882329249
    0x1101090f0303050a0b0306071124060d0602090901030f0b1506180f03030406080708070207081018020904061a01020a080912030d060605090a05011704021018030506010501080709 78
    0x1080d00d98400c00c2907908a00800000781000c440e180d8665400a20781c1c0c0a200d00d41c094000c0c0d584224080940d43d40540c208000c5070100f80c181100d01940c4184050306c00341150340100122031500300100e603410400068824080070603401100200040f00308450b90440300f041c14011015009039070ba032034401020404030104200e0780300806000c011101c3c50503a01c002190718014101212034000700010034515002908400b0101c0d1048040142c503e50090545600500741e1004103c2180b07021200750700c07041d8900354800b04645815001075200481d411840719107034040d00030001d030715050500800510062180044400544060380c14030740c80010a82443c50308031805901e80f10f010020420350603107418505407240414081c0c004c80708118031403d0001c04840c4c440503583c242803001c214139035045400286c14071655401c0d03c0440070a0700c4199900a5060381c0d0641c00c491804800c6e1214014402d04440302546510040104100412094101c6030280c03906141515500c205446408850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 882331744 1250 882330494 882330503
    0xf030b0405090c1221120f01030b0129030a0f1a010518010905060d06091812080c04080102040b1c02040b0f0706090c080c0f030d090501182103110109 66
    0x244110310928141c90301c51090161030301100d0512901803010042001e0707113071783e95240582c04149007a000002d01c00050707004820400c1c082c125070455031902d40d0380320103010b001c54950861002000340030200f0a200c50420341c0711b0105031a0320b810b601100180051404401c05103080c440071480e0b440e244014600c60000513183e207410705c602d041c948845a00407189a42c10000d0f1990001000e46401c0c0080106150040700410054100a8000e054a49090588400788180164000410104500c0a203035941c00d00e010701081d1150707007140c2440e001d140c01175442765100190008080040c2e400814110403071841088075200340f514031070f00b06c0c01140300e2038002c20000c01003050754445140045c24030705d00c507402c000b4554841c0d8940140c2007841d41c021120352b42c0004404d6500303103080045030b40d07411411802410000e0780d407880201121803602c2058140a04212840d081120042601026041c0a11703034140d09540c00c030403400b038411855010703804258038a00c480018001809044082307a000f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 882332994 1250 882331744 882331753
    0xa0c061404030201360e061c02090a06030c06020f0601050607030f0f12060e010503012901200d08070f0306030b0402210f100c230a02030f0a0f030b040509 68
    0x55400541c0c0300a00c0001783c20503400004508104400c0558510000c0f95400102050260401c010100c0d1090003502c6280714507581564520070780200c601059209a0603074035544180c840ca00b400300900140e41000700740310703131b000408919942e00003002d2143c02040012900d4590760392041c00668800d10030081d00081c842031603414803034015110b81010304998508012010000c10301107007181c015030490038000c8030100040245140034041d0389620764181503080d08000b21400d11401a1a400c0c10090500080d0000b8181c181e480380031211040d800707101a6055004107180041052a013150000e003c0b401c811484a0144e100703115040643e03a108010784501d840d1502040f4030031481b243d0000c00070040040031048e10005100607580b0390162402009081c12410407141a1100301c1e09803010061500320600c114801c40083d8015005900a007036a22040010100d003140f02c1c600c01c1502401001520240e1158002900945c449140c4d070208503e00c507442c01c00007074030826502400c4e13a500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 882334244 1250 882332994 882332999
    0x80f070e060603012d1509080c010903020906040e0f0a1406010f091a030f0a06060b0913020703031104140a060c0b18070515041a07030212090303070204050103050a0c061404 76
    0xb051406241d1140090f03400da080e144024442c00e4812075250406c01035200000854524503800541103c043d0101d400030380038402c085400200302d0091884043d21503070152010881a40703403503200d0103040c0c6503102524920a40c0d405515591494403200301c4a410541d0b13554900710703801240241c182c070904014950702d5403501c0d100300090b00400030f040310010341e0f184480010355410043c060407000c1c01c07405031150300f2403410950101c03111a80130607c5884200095140ca80e0743c0c070400f100c02c0007084001030b210000d0742000c500030001003d8100b40c040000402281c0c444601400710081141160b00c0c51540340c45150440318001701e15001450303198400c02240c140d004203040103036100341c1c180c211903085035a400000c505d8030503201081c050b864009001e02041c05c401c00403034900ca004580c51032500007240d0700250790303021341d018282e9081000300b000304e001c0e5820710481704203980081c414016561070381000b6450360540d0b8001c0380c80402d519030020b41f4600071036070004052804055541881d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 882335494 1250 882334244 882334259
    0x4090c110c0303071e050c0a1211090105010507080f120c0318010903050a030b1201060906091a010503061003020c1f0b0315131b0b0a020d050f07170c0601080f070e06060301 76
    0x3145d40000c030352500030502001c1c4a41c8401c9201c00041200701c82d40344540809082030070022450f0240c1c00c5c0a041c45000603c0207980040840301d04d0740d0300211050352003511700322904490054540301030510540000b8080500c01c0344000d18041e40c0300d000b0080916220404003401c03541409801000302d00241720700c06185009c0c0e030208903a0300703028045002030aa03a6003103d0840341b058102182072075440c0c105000c2e464141c807a0303802001204800b00c0d00641e10f5400604207020090099102da120312a010a10382d210386c068074850211002101c0c04008101d202440c100d5041103041d10051808880c052a450002036500203802007042500080d101c032000c0385015010786c40e0070384000740005400214241542d480c00024940091140c6e1584040100207003800f0360011000c080103805e004005c142007a40048815041d8040d1007203c0300c01c40714090105500614444003030700d0290000008850b000401e62807002e51005d0305481546454011b0b502d8801820f0303e00c20b0701b0113803d000510040c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 882336744 1250 882335494 882335543
    0x5130605130f03080a0e03040803041e0b0d05043305130f0501090b0705040f05061c3324020c311a040902010504090c110c030307 57
    0x142281e6005664561030340300d0310500c0070400d804030300080041c8100096142d20780b003038002050040e006145024034029205a990140340500400000341e02810824040d105405100908424804035110940300900d400285411038054403080e482030741c0f00c440694008010b50660000c070b6005e107a405140c402ca9402031400808044001d905404400003183c0381c00c215200e40c510410000c203820542d803900028640d00030b400f50050140c24007003072100c0d0440860083c280e490a0742e64544640d4421000506001707506058441c10740f42800b00239603548045180031158040d0030fa902400514484840344640151103044c9034181c01001c4110000d0009101480082c01403040341c0c2200076000008007024211101c02c103a4151201031120b40606101c8a80701c002e414503410040b0300c030b040f050441840f000003074041c411603440301c0c00360071a80a1410b41f00500340e8000c00b081070540c214409443c401c004040c031546441900c10020035441c2c000b0855011540c003041c0720302900756901010202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 882337994 1250 882336744 882336751
    0x115080106091a1f031e051504020c070e0c0f0a0e1518010305040219080d1d0907081b03090c010e060307230d090f260405060f0c0a0f03080a05130605 66
    0x101501c900f000701110900010180480500220000d01f5007003640a04002000d0f08400902441c01441003000c14140418000c0480701c06140c4189503544903c140078140c0b007240098802540086000560b182c0d02901282e0b4036402034411945440c10065180064014808100306141c42014100d00d20752094105c1ea4100340b018041c1b001c2e0080d03204501061202c950084003103640450440840164800c06c10300e00e0051035900c0c43c00401e4020003194142344020844000d00240c2c0380401d101580040910f080c0d01c0d1540780c1e03113880341032100d84c00c0d0311600d100c500d043c0010703043c0c0c50b03003101032500c881240e0143c851621840465181c80b0b0400c01d909229009409240009000010b0508158095108011b100d0141803c48000c503140034005040315031201044842140313000401d0000c05412601a960301f102c15036104c16400114a55611541c0d03001c0046d4020003880d201000a0301c442034050310311a80700d0340e090b43e0b211280c0d00e088400481d545180e03c4c448202000204880e40c2c8031940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 882339244 1250 882337994 882337997
    0x2010e1504181d010207020a06050909010b160f2111150c0c0a1a0a0207051e21030702210702040c05070807030810090b03120c0115080106091a1f 64
    0x2e090707480c103402d030140743c501d03e620f100607940028202d421440c1081046015185508009003401d0342e99000c1000c20005000700c0219420029404001000702a0740c014107507409900030710b1600031444c090f07400c1411181910b150740007003903102020314018014840104088001401c03003148480107505102c101030559142801c081141d924406414400220200d008844505a4091000c4d061984010003000c0054291060013481c0000b42c0114241d0104102107c070035a5100c000d81020341411010315560514042401c412b013140500311001d103120310429026200400726150b8480022620400d21a140c0c002c00c125203001880e103540900e9510700c01d4a0650304080240d90340201a6221060560220f005081000b20181d0000410720142c4842d043c18051620703c00040380da14080250020614440841c0d0001d1907802540003004da5003002039030402072603584003124020300080c01929102810041520401c450303040301ca0340d80540140411000c41001c038944904916075010703400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 882340494 1250 882339244 882339251
    0x9090402190905090d0302040803030a09060b0d05010614010323190216050c150d05251e08041a07030e010f0609050108281502030a0902010e150418 65
    0x10308040e20101ca400a8050920000f03580e041208003240781c91614900101054010481801030840100c15a03410801904011505c101c3c2817030000040c03c0660031280c3c00203445407800c0c0038070105410000840d504002940c030248010001107059445240700302107410b46104d0b0004460051b40c0b129540400c04501c0c510b03080300740c0c1c040d400586c0c0c86404202c0d800c0c4000aa00750a102c0b0500400740012403c40312038a014400700708100c0d241c0036003001c1c110000d86c1c03000001e140b581c4000042104620994980c1900c110050000d402e804813102000d560907002040080f400b401030003400e0240b90000314600c4d08002100c0a02d0f400a130081525003003503150000b52442a07000d0060104001d10403101142150034150030b0011a0b00c164400c040c1540101008034507603070707207800714800642940d6040e43c502405040a203c94062031301800c904920000401c004030b070041d4070902056201766036514a000041003004200307404240d0b000c0c0500410030081000c14104812038080109486011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 882341744 1250 882340494 882340519
    0x60307150e03030d0c080901050f07050c0c0315100e0c0909130c1503110301141915050310150e060c0c180106080c0301030f03140403020d0c06140a0509090402 70
    0x1c0d0030358000314000c4480c940c171001c3c0714181980005555511a030743c0002084185000d000d007080c40180a405d24041c0b2000180b50280700f81c00b84118015540060700f00e4040c240c0d40440c0070791000e23049820301000c0c00100e40211340040000f82d0540500d40c50501c2c58100106601002407002010300140d50502910643d10001100034000303d0041030740d60a02004222000e6028044e0707481e0480000c080141080148030b940b47c0e0100d85200c100381951000402d2040f40c0302201c810075640c00c44044120381040e90300141e0f610000a40c4508400c0108034250340e650007515041b00110a02c10000c2000c0000014a5042a9004c0e1000e00500000c03544104001000b190316450709030808000c070341281d0014000103402801c442d81100420110624540c5582c17900355a002e20028010b081043c0407a042003560002c030280c40285800a0586a000e040c0d49440032901d0136a20916010030440c03154044500716000a4800c054001d49400303107001524002c0142a0900900482c0e000c040c0c0c1804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 882342994 1250 882341744 882341749
    0x8040227090d030e03130e0709030507410409081603080a050f0402010519030b0a080312010503010b011b050114070507060b060406170601140a0e0a0509060307150e 72
    0x32409807014401500c400080000010142c0e200d07040a2400741e4801c01842020031844900b40044400c100c014029a031103140c011280d10445a2014041d4401d1110100d0011148203a607154401c0d6605489030101109078103610300c46411111511814450707504807050b007065000140a117100d0a07066152600130440c50700648241501030700010b64540030815500598805c107038002d50b04903414555031030b1581c0000c126200703255052041080030800101d1403402600301031034400004003015074003600d403040f9643e07a030484800c0ea03ca5404002c00043c2a0606125030102070030180d544440c0f040090308501031044a4100844003590303100850a88240302c6115280245000e542d2035a0718011420000c05589085035014800c08003003204102e0079400189282c0311038548403001070103559180060312410900103c050303551304001420340b12158404d091548011003156040301082d1031340305120291340c048454a4240d88410420300081d010f20f0240700c007441d0149440184400c00901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 882344244 1250 882342994 882343069
    0xb0919090c1205060603040c03030c030c0c0e2703160507050a06080115020f1005280e0d02010605100e0307031514010b030f0619080a111002030a080402 67
    0x41c0340e000208400c4a148101c40d0902079203402034411282d103030650800361200c1e5005021840003c003800f0240d0300400030980144110800140c0107880e03221115a00c2c2800030401c0411680c0c010004000070548040c85d0341c8070807a4600c103403000d008508104903140720240e45000c0c100203a441d8030407440c000800380e403500440d4000d0101c9e543c40c54201e501d4440c25031038100d0803440402c2035400c084d0390314480e00d2000918607035a0b081450040744540702e80361200c1101c1c182228203214030320341c00039422028442e60000945108800201c07242a080528200d08864880c050746501ca80450f2013038888a1283e40000c030941802003d42c0d8000d0b42d282d44002d10100c1480030398840c40d48400c20034940c0e0004152090040c083e080486e032461500c4e2101c4503500310300619092081d0391100400d00f8200c1180c0301c0300040d0001804803154101d140c01c10b80103100d0038000e280e02c00c0e036410f6000d00c080c52010045c1c8010444da515a44100e0f111a400c0050140b440703018811301005038560f01c4400c1c0e12410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 882345494 1250 882344244 882344261
    0xf010504170f070e09120706181b05040c2102090d24110712030b130605040e0304051809011506261003020f04091208010f09060b091909 60
    0x1e0050004014021082d8182502503020030303040c1d140c1c0420401403a00c0481c4680b5581d0444c0c0103a9500d6203245480d80041c02d00310f1080201d080241214810800b2107254104203050704012029099521000c220a48103100c41c0c0d2000286a142d105481644201e49070039895000c1502504006c0d10001042c048450303070400703a8000602c0421614a01c14a00203c1c5d4040000300050111600e42e000003881031043c400010035401841143c58000b9110b03030700080c205280248402d502e411071844080142005000321403141c3d1600d094441d00c880000304a8040310009845000008054035a400015000515489565403504054002101d00d0720200010b0002078440c01542c514122151051820301c0c0e44107007600c0a40000d00c500c40180a110000f1207904131010315695410300c001c80c025105039400140b030440018050713050183c008410505841200e10f96151003541c680b512410340302e15100760603c840041090914908244040c0b2420007801c0da14801d155071703500004021074141a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 882346744 1250 882345494 882345539
    0x1050405030a090f0605160507081b0a090203010e040206030a23041b03050c19050604032603150904020316150f0c0512070f0c121518020f010504 64
    0x2034502d184a800600741405008001428a28541050350150542c802c400409441c080e06117628420800d04200346400703004110141c85c20b05005070032034a661a05940010301c00c203610880410380750124402c3c0d0b41244c0d05040903400c26110341d0240200b60b03101030704148266403034150500c80d240c45800e40303940c4008040c81783d10503403409040107a170b08985070b2b0001e000d604180000300049100018485c0701c0300c030110b0355017003600f114040c0c480710a810b6600042c2c000704042000001d0210001030b8220303071400b10790016034803610684440d0444c0f0040310f81d001c80b075080b481c0008040c204905101d41c4a40b0250032520143c02214903400030100c26441500d08040022070342000c0c650201e407000c10b100c0d103420240440c030015990a91245200ca646203003420340071940c1402e109021910001d02e42c0c111200c00050742d294100b560801c000500142c400c5880744c1c0101c0b030b0034440d07403060320404c0c440350000c010102c0140d801c00c11140a001d4031141004820300004c01e489110420403032151041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 882347994 1250 882346744 882346747
    0x30a05070311090a1a120718060603150e0f041415240102060406050615070302010623091501050d020c060105120a05060c1c020a0305190605010518040e0105040503 72
    0x214040110101004141c1d2844038109517041a5030f422a030414080c810b000c590f108459807000003003d24080c0180c2c0034446201404c03124082c580c2656100000ba0b810030b03502884016040e84001c4410509842507501240f04c03500003580714450078070103e400c9407207a1034650700b51102141407880c00d040e900800d0070f45e04403c2c082c441403e900510110101400d4040e004000ca0101c0002c0e468200044c00546207984400025200d0307070320741c010103460001c46071807140c50b42618140280201550300580c0b40c455511000441c03a1000202c0400603084001c000e440f0350b031f42e42d00362220207804502d6461b0611906024203001c0c0d520b13a00191203840907120003032200750300d0302d0200301c0801807803103c80386036400a841e644003240c0041403080d44884002ea40d550744a01d94101074501481d03c42d14000361070703c0880c51846066042d08424001c2d8085268681400256160501141e14034441c5030301150080003c1811554524070100c41041c00600019850480161990a480c0b0403202280d05410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 882349244 1250 882347994 882348023
    0x2030106050d0b04060b090d0f05060408041a030115031503140109060b0f010915020703150515010f020616030212010e011e120b090f010c0e01090b070c060509030a050703 75
    0xb6102d10714590600700e03014022503103448036554251160100c5a400381c0511109501400980c0c003a104600340c2c05000c56030780d0f2410b41060042c540150017040b54102c5c40c2508010500303406000c0da07050303400e60200c81e01030074150300d0700b0760041c800400605030031900c10800002080300002d4000354144560b00128079805103151604c21201688002441000e039000386200999010300c080d825580348061034481801d0303c1da01a03191800c3c44c1c1c401080007001d4010701181c16441e070001380c0540100303e10b0304490007525005541e04000034100c00c0042e03111000090291617030391401c8080041a040043c5801003044422141502c00d0300305000040341d86004111081501109081c44900741d51402c103084d0400702c0a5094460183c00980410122400b04942c824144074200900c6841c2d40208030f1092110800b030045078400e211140415810300000030005035a00860301d15540c08007564101504000d01900d01d40c100a009030303054818a0041d0300010010401407010354000c3e50b603174603d0384 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 882350494 1250 882349244 882349267
    0x304050f01290402070c030b06031c02072421060512010c0206010605030c07120509100e190305070905040602040506030114130b0603060d03051e0706060603050609070e01050405040203010605 84
    0x141c039500d565000f944100400380108801c0741e16801031307a5018181c803980c0c0d20307510b001070b15080b00034428004400800541c0c1c072585400003022001c0b1401210340c500e040c131200303071580790a10700194608042404000000f02d11101d04000d03c00594000c40300082c41512040401c21280c00d1a070250f01c40d0b91b440f95800c61464041000500410071403400710b04c0c2d45002c43c0507480a003d0100010860070300c009440c542c46000b042944c1d034050b03010303018030000f001d07244004101a8101d40964080c407085400320015038682e048400c00c0c0c0360000c00800300c591400b58521300800c80281300b600d10907400d10000c569540c600b00118000c144880a000000030300804100b5000e00f49000e44107118501525400e050b00c4901c15030f80e005800300c0c1c0c03007940c1d180c803802c054a052044a034820340201c01c000740602d2a00c0c44101404060f030003080c01300a46600c8403c19001c480042d10345a6200f99504009840640704800c540d41c1c7c880d0616146080960702c4022400383d0300207070040b00214401041c44411023 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 882351744 1250 882350494 882350561
    0xc020f12030c06180d0903060c02030715090605090c060a2a0c0e060604061d130606050705010f02250c09020f0720060d0209150301170f0f060604020304050f01 70
    0x6607248000740054a10945c00a0000c5142d80f0004159645516182000500a009a9281c3d540104482c03850515121040c5c0041115030780c04c0f60094540b001081e5207050009104500c002d000e00001e141255540041c2c074022103c0c503000c8124122541c41c00e80c0300900101c203e516500c01c20a91040c00d0030898210514200100402d0140c1c00620003040311a6000c0d200d81c060b0480642180c1e00c9071061400700d284440704158402d8250f003403050010300140d0150050132032074010720080000002c8a00b03e5000d0744200210119590700004409207030754504041c69110901c1407110b4165540e50300311000c10780e00035000c0300f0500003012034004203000030a10100b6403a040c0d41d4101158411030000034a05014410b03074800b683e035011a2100711a260300082d110b5131011135464944030342e03640c1c0e0031560600185a1880d03c81c001d140c0301c800517120004d8445285c08454024105540e034100910000f500000c0c002c0e9003911480380711104800c0d0030322440a02281c400080490100c811690b444003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 882352994 1250 882351744 882351781
    0x20909010b0c0a030e03010207060e1b0108010321051b0a03091706070e040b030102030406020414030d0c0303020a0c1a0901051b030604020903160b0706051302010c020f12030c06 78
    0x18081c108024070410901081070941990301d400c26500d90180d80010030b0081c0100c00c0018903c61a0514054a07180b0000b0341282c0d0005804280b416180818011192000f0a00c0700a000200d2034441c1c0202c0102c0c03056086140180b17107001070414905420040508004007207100e0316402480c1d03818245035101c00b1070310141c290105a4400803c06013a02c607a249070042480040100c0d150310603c0940d0f4a402200846100900940d100d04250400c00004d50040c8a929100408624141b405040200c0d907a5002507041d1030f855442c80341520143d000e50301c180b0070712041112140398400001d640000c51254940400042d00c101d2500c00100d901311007004d40300810f0308a400b071200282442450032294413440548015840e8100c0601207031600c20102040402d04105180104140b0205409814498045c40301807000380c4408a88030303001c4041040280c0000d01c1c0001d5240541414010b150309118058500e00000d4459000c0d1415500500e440484503000103040c4405840b101032001503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 882354244 1250 882352994 882353009
    0x615060c03020d03050415020a031b11031e07080703030c120b3d020307050705040b06030a0207110a0612060807080309130612110102060f040308060d150e0102090901 73
    0x1001003854070040d688034400015002016168030000c4c04002c0740203412041040c1946080d9140d100d81c04001c0d0145c2140181c039090030b2030100c519000a4414410310101c21081d8000c0d515117040d607880040c00c480c00208000302c500e030802144000440316001800058000d607800242104001401840790842c0e8031082001130900c03501421030f07960810304041c121041c03002108881d00068254800c48a0f20b000100e003001454240710b4030a0b000b00080002c18801e500b9140d01640f260708000032034070078070651608200240f00003985060300e5070042c03c1c0d250284e02020840c00c100c400044013006142c000d04000303984028030004002c0680594006031061101800010b8140741c0103c0d602d025100307120f4450791100f05144004010381e032181c1c01501a4407100c0f29414101c1c02d0840c1c3d03a1034141e00d00340c0144141d40010384070707102040007103000d586d01d0b076a80300c0961619402c002150444040a541c0d2500c0b80400c0d041c4402c545c401d10686c03445800015840e0480c61003040040c0005074001003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 882355494 1250 882354244 882354257
    0x30f040e0709211a1503190c12330b0f0904030c030527090a021e0c150a0501050f10050d091a09011b0903020105070204200403061506 59
    0xb40003451500c40b0312060000f8654440d000c01818161815481c2c031a84019010255003030000c5150000341d42a0480c0c010340455034610200d958048000c1c0304070341c0140c54400402ea0078408001344103400d40406000d5000c6030900c440d0b0742d50700180740b03480c100e0010304285800e1030321080e4045402404000e004c11900d0a018074a0500402d83c4004018401410801d05c81000c0701010301500580b0804d40050b0540c0941d0303899028404255644080410300c6140381000090021f10309008813036403000d4061201780c2440d400500c4040030740044020203124004d5400c507003501400c401d801c51040ea1211004956549030806016080c0500c4000c64003c482042c4c1a040e11600f00e01103610f036420f0f42c5400a070103081420315036a003280003482c00801c0f071140018032141c800d05400003076a090034610110b8600c28041c03400d0740d143c11580b10090101d04280080c901510709680065445015100d000c1813401241844c95143c0e4042c2d0400c845581e960349489120241155031100601418105403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 882356744 1250 882355494 882355499
    0x2a0910091808030c13030f0803150d0f030e030102040b1c0b0a0e07080406140a0b36091603051005070201020307090e07020a05100e010e03070f0b0a020c030f040e0709 73
    0x2403440e110003007066040c04000244400c81c045441700c070780c0003503400241100011141c0d00e4a540581d201365040041f00c004e4903034100c414a03080c4200409683d004510f400444016901a00c81f408410f10048c0d26550074080000c1c0c000c50f035002030003401c079812002548480b070303024024115072034840d007180030710200d1001b07100b0003001c0100b02c1d4101c0303c0c0341003a00c41036969140450181c85540050b5a003541c0c48014880c0ba020250451540c90782d040728000d98410148118104040070541c0780d1141d98034400d40303082903080c43d85085406c5082d40040d9140e04094041498445100d43d008031195400032850b996048601c1c814150410101e10080d899810640742c0201880c4281c010101080440350110790103070700804c1001da869900c0010388080400340c14809004106034031020b1a84d500300a41140307100d001108036082c190303000c1c10800910200d500c40c1203280070020000900b8603820020010f900300204040c0c0000802400a2541c550620803600e00701440a00000b0500002d004103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 882357994 1250 882356744 882356753
    0x6110703050304180905010c0518100206061c0b0702031306080105030601090c120c0e100e09070507020d1e060b030f07030b070918020c19052a09100918 67
    0x8a804890307840301d03241418004d10039000018110b4070b030010069807070994036804150b0060058400c116210382d1302c441c540c00f480188044c0c1c0c80c10407082c0006030010780c002071032032070708552020342c8101c0300c00c282900c0c400c0c603594903600480503914400581e20100d0990100c680f0312044c1000b41a55281100465140401280d40d40c001805901e482940310396520342c00a100e140b0030f85103a5400305c418030865012480141000e001382c00554007810700c07840481e01081c000c08450420b034102514041c1c01f5039660900703d03440d8120007030807644840c00ca040c43d03002c42c015480700000903ca0644240c5120790030302d040780840301007505d000d01a03007108105110601c40480ca003003c0b2a0885403200050340d1b644003c80b81d142c0b864110035940035404031061000096a80607000d10f62900045501031168003091240c000d1102d40d00034042e600c0305031034595100d00300042d00b1703590001003803190355031020200042100c9004ca8a0721030401c140c050800c00f8114501403203550118818451202c016507884 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 882359244 1250 882357994 882357997
    0xf0d03020a0809040f050f04020f0d0305161407080d0215060d030c060b0d050f1b0901090f0f0e0c09060901060f031503020301060e010e06090c030a09020315090106061107030503 78
    0x30003400021011a0f2144aa180d5810405c680e20400c1d100300440c0c60203000d0602c6401043d00c1c182e004900120484a542c108a81301002d025019121141443d014600e840b51a40214600b100c60704900c1c6005015244100702c1c20000d09a0035001c0d00c12040c104070000d18000002034089240e003034420500099844035503404402e15050b1a0000810000d801c1100c00303030113614405500801d13007207040740070310034003083c0740d5030b11400c0380c068406407040ea1107000007400010480b0f0703a000b80c102004102030811644130440700081c0c0080801c00304912081001100c401540c03810a0b60130108014480b840c10740c10305644010216007104a07941440001881da0b45206091418950340d101e18400c40d1007402080001590b00900071300159403252301c1100458030138030644000d0344000010407101d24042e59441e1249010f034070100d08503078440d0503000140c03102220698041c012514424600040844044c1c41034103103100210310300d0300e02000103107404601c01004031240c000c400e090001900120 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882360494 1250 882359244 882359263
    0x708070807061527060e0c07062901050d090b1003120804030f0f0306080d0c0b0906190b28081002090f0904210306060906031b260112020f0d0302 64
    0x101041d4980c0c41404d814002000140c111005101803c41003260b1500b07104010100c052080f5005d100d26041880c13404101d0100c4c09044410403144903802803154815400390071280070345500450040140d440e0511410410b8400c2404840784500520502c440404141c0c041441403400c440b1914294400406021000d41c002c4200003c0000740102144290003000140000e030b4165004c0015a860160008901c0760084502091100004429003404141c141c803a0301c01c0c000703004661440705418001802070150540d80103240d0740041020000000e401c40e01440301c04050000d00d070400d0301d41440c0450854251034058010440c0d002c03d80c0780c8010300710450310191050015034886107080c140c40d036442041c14610320810310035211415450341003102103800507101c15200d41d0b1290011010340b4840101d0540c620703500702c50307075001c90300c6108841d400100d40c00d881c02c0403131038001c1920412402a881902c02800215403542507117400915403007040d034219206501300220381e60280d1119080f1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882361744 1250 882360494 882360539
    0x100e0f1005100b0d02030402030c12060105010302031b0a0e01080912120403021207200a230102070f0308031608090d0815060c06070e01020106081902040207080708070615 75
    0x1e40100d00c00c41d092041c01e402400c0b41c3c1d0b200766103505204960300020340086405a10a200d00341c9501100d082450700c962501004da400760159070300b403d0046d40a9031025000b0b405442d1407101e0002041303031040c05020f10300036954511311380c01d03030180004040340720160142a1a402420544020078030403c01c07115010114096200d2541e124281a400d00581d8401c100d60714600086103010801000315a44459403000020f404001c0e00c142031100c580418000e1a100e9824210481e400c41071544070601074500501c110b03604992500d5001e410340446500803500340d40c0c040140440605580880200c2c0241c0d840e00030700301e180c44134803e035546054940807012b01400c0d00210708800c82c4641881c411440140030140c3d81c0301d034090210765444084401e080040d070720764501e07c003c0d807040c040c0300c045446010040840c40008401a903224011000c1282d21039420040c1000250744103000e000c0035402840c05035214150b90520506903400c0d40d203480042c4102450034010255a0000a0540d8084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882362994 1250 882361744 882361751
    0xb01020706030b0a05030303040b011502010203070e040207051f0603110f011b030302040f030b0915040b0105010e0d0b0a0c09092d090c030c1401050705070e27100e0f10 74
    0xf0400483d6645016800440d01350000001304400d01c90302030a414121a80e040100303501c07040d4900228201c0c0029900e520010301e103010341c4000784c60b0031b401030032003d4005c2c0d080d1303012460b0a041c2121480f00c0307001800c09450b00e0b140c0030003d2102d42c0d8842481880b0580b06181c1c01c03800140000d1425103c40c20400001c59010f46020606119a0644002e08003032a081c002d50f9849080c01f0900030790855044d4842e20034240900541d2402e0b04c5a00d0107168417403a520026400c0000550700c17008180c1b480e42e000410b40b010400403c10310304d010350149515803000501480b0600c00103080901e56041107a1f000c1c01d108206a0300e0f42d81c821a80d082d03003504010802901031480d083d03005084d50740c00203400c2c1e07644c8180101c140903801364450704030b403034084142007a01c030394600644590140ca0806015500200000c2140c034541c0008640d000c6d001c0b2082c0c40e00d108034141801d918040c0c046600300c040e0f0040d1030192b24148680f24190488c2d040400500c8488030425031a0343c2c40b43c200741c070100c84ca1b48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882364244 1250 882362994 882363011
    0x30c110f070b28030b1c0c05040e010906091b050109030302102d0501050108060d0c03080a020a0819080c030405100c0e130b0a09020405033f1b010b0102070603 70
    0x4442c10103202441003d00c0c003070482e00160310b000300a455902d031102e204880240c810f070743c1c0d17200c0703001d59500a5138400c0358820060f1600b0200401060f0112545040c1e5403138844034070016900f071041058191040d0f40300001104445d14002e81c45e81070b500128140403c100c41440030940005071252140480e00380424089403164188006085a91110700040c1c42c940403c00341200317982000381601c200380da862503140e660390100403000c90b1004010b0b0440040d100b083c80170484c1d18008000145a50046502210381e07540d8058048d0700c0b18200c20426850300e14041e4106511003043d0f078000300365106050550900c1d4a80f2070320ba076014400111000d9449210780010b5000b031341c2400380110000c10346101405a4403070310000c3e0003e0f9402501c00e803015400815038103100d100303880a455002d80241181410140e10394201030901c2405091f2103900c1003190010804a0302000d03480380c03001500d40e21102945180503000008100d28130090341410308000c15030741d0020301c2800721041c0d440c000c0384145 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882365494 1250 882364244 882364267
    0x9100e0703022106091903031109060f1206042a0c06020c0c03070504230c070506190c0309021c0611120709060809030a08091c030c110f070b 62
    0x10306900c000d400c5220030b144040c0e1164495000e604604401081e5003159413425100c41c0c441d80c02e400156138100f140b040600200f03202c1c0c0c6c0412000c0101c0e64205160003d4480080c0d0f403038005801c5e10040200c0050021641c039282e180681c0c0254040c3d40511400003600c140100b0712440d820070a104079200c8400e00206480750815800c400d4111901310740c0e801c0300804c0e03d901c841070760344098002e224030400010a41800e1140103981e0b01d141c008800d071100c0e844c1400c10551400782811071800400e010b00d0010034018003039a802141100401149544000744c8541680c218050400074180f4007008480561a0b4014410800410804548064289144c0400100258200458520404a030146038800b034802d40c035000c1c6c80c07030f6115070064a0f6030b02d03812281c07240e080300c0c1da201a41081c03110080c40d80c001e1a00507000394103801a6211060808520015000e0015210307001a40b210200461540c1049066407090b01d18006005450710150b03011b1750f02c0306244103086c1d40400000d1101600d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882366744 1250 882365494 882365503
    0x1050d061d03090a0815010611070815070f0503040c0b0f30010b03090309040b060408030a0c06050c070c05090603030c0d050405010323040f03020c030a151409100e 72
    0x34124034480c1c20701c54109076007607403504440e1046002c0c0c01c00340000b0441820010760b401c0c640200b07085001e00f6a00f0a142102c1220f05449205d000e441450408190460140640700b8010488003072042c680c82d1045d0001c2c0300d100003110840070b0040410901c03007c9240202c64406646403c02142c1d81c940d60b001c8040b21074898a404501c044030441a0b01d4000000c906501c1d40e205070740803003217000b40d0301e6203254030117803006441c0002c240c2c0c4204a24200c0c3e0400e504280c00c40107000307000303e0800d40e5498085082d54400d008140001d03011031084c00802080c3d114040d0800d08500100b810108030390b480c44007a00c2e480c00380c144260301060000700295030800071240e002ca1006c003503c0804400ca000505181c00c54011280440d04060ba1070400d01c480c03000c072010070510310850140d15140ea132103800b070b071b500340d19001c2d4114041c4c400c2c0501d064078100401c0004500c10014980d040540a07485000c0b16038a00608006103900c000f030107030002002685001c041d02500f40025403402c0420564940b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882367994 1250 882366744 882366761
    0x3021002180901090b0108011a0f04030602090102010608031305010305100308040b071103061b070311030408030702041a0d170d06090203040303050a0525031e090302100b0901050d06 80
    0x950000a040c1e5112112081031401d4080030703100005282d03224031480d030546004444280c005190b8000402030760402005500d40080e87c2c0311810700c3d000d25029655401d50040d00213488154002036103211650782441040014003100028604082c2c5c900301f41e402c1040e00d031280604050b00d95000c624401c400c1c442c003900a550010b201941c95542d0100c140cad240d040f0f030f4415155680e0740c40300c00045040201c0c0b094810700d40384641159200c9062084429504100000d40400407285144402150100000c1024200c0b060041d61030b46254810481507590b0004807541092001403d880140c0f24240701810340351340044034030204801021020302c07600406000c070602c0e506103000010246490790003503000718001d40d814011507407581510802e544043e00e0025100e82e02c90b2203240c0402d0030108000348404545004101c123900a00541004000b07107820781d00a60341c460041c010160100180e40300049000d400f48a1144c114000a642e0401440f0340390081c1d48042265081002680c003c00c01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882369244 1250 882367994 882368023
    0x6010f0f0e040f0b0102160e1321030501260c010e03120d061703070f080307020a0b010e010617150d0c120b0103150e1903110a0812010b091c0302 64
    0xc0d0344443d0020700030b000d21038103c6000d405100500e1703e02c03a000207402c1041e40c00c52010100301d0b2715940980c1058480030601960141c0300904541300c40d008101c0c404a190b0015030303021503154141203da9500115403264503046139500303105001d02c820007088084100c0b10900341064000010000f103410032094956000112000050f4456241501c1e80442c3c2a00d086502c004200c90181c0c010503a24410100050248105d4000d002d00045810303008503800380191055481c802d442c0e0756152503021083e00b1000c0c000c442080103200075903101291044918111003a40380c40d0a02020722500100030305c101c07034000d1580c06c001b4000c0c000141200c60052001200d0a0048030784d03400c0c020607088081c0821690001e421800c0c204041e45802250f003400100000741164400c010107003303002c0b12a100407024004000c0b048540c02106100c40303032040c0d0007450407035501c00c620105030b020400b058000e12010700e000c4c0308c02c40c40da8544c034096480018440d03030500410000f5080591801d018030f4942c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882370494 1250 882369244 882369251
    0x10206060f0a1a1e090d0f0c1e081c0c03050309070b04180f150501080a0902060a08070906091404020c0c0916020f15041e0516030203060f06010f0f0e04 67
    0x1030f9800000400420502000310040308000c155400f00364410a010140d00ca048440ca0a020820001c20b08482d41d10440c0300026a66494901007034a0381c0c0304509400941e1139402c01c001840e030511032400e02c101050780307281a26004020103003a14200a002808000c400700c00110400e4003008440081d0100042c81e83d2200d03540e0480d117070b042c1c00c0c4080001e525800c04950551310101800b85d083c5400b940d02c001d001c15405c000c011202080e004110480154444141c100540c941c0c900415184a16a5aa81e1f052030122409015072420b82d0083c01088200c0904008640b07400c08091080f100031a8096601c1c500142c00340d180102c4409405c0d44a2140c0c4180051350781d1b10721200e4646040d80d003c1d114601c0c0d640100c1615a0600d654440d982644080064005100210518003500080b105049080019100c403407802002500020f414241c01c1740074415480c080080e20b80c40043c0140f41490340c5401d20000344000c001010440c1030189201d841e200090040441540c0414044c2041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882371744 1250 882370494 882370529
    0x5031603030209180916030b010b160c09052502121b060f091b0a090c1101110403020a0e04020d1203090803160912030f0513051f08090a02010206060f0a 67
    0x100154402561000c0961189420785408451080b04c1d2404071fa400419101035a803031300c0b58100e100c2c0e0200001c1039041d0030001c500c01c000b0302100310140107080340c0d0100040c9071400c0f610030654840b5281076000180900c0450025056002501040e1b00021490039600d40300891341d169000707140c80401000501962040114603035007415480c1c4074803034040c200c542450758180c0460328003450f00e0382180c003d0305400b0180148240ca030400e00ca11402843c1c080000c1c280d0402141c2110040d882061490a0000c1d00b00700750310701a00c003000600f071140f140510380d09169000880b04503088800420345491403000f89000c90182d40301c40c143d107800c404135030f82c2c902d040c0d4a001b4400b4000040d0801041d00000c0110f10089482081031890307500d906e40500c0010342400542d1107400c041030b190545641002c011606884146410382028103104286034002c0c0032403006400618010301407802a03200109030405070307a000800a400110a4410491101002001c1040c94010742c002c001400520b1707840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882372994 1250 882371744 882371779
    0x411030a090b061c021203041502010902100302031e090f0d020a0b16020d052d090102071a0418090b1e060f0d1103010e0f070302150705031603030209 66
    0x212400e02c00c07a501c080c156070303100030809034252104003c0c9103c500e0f2212400107040500144014408490880c1d0400f0f0341d070344890190540a003e4140180d4680c1807503030450a1400344440c051000c2e0074103501f10700d07000158500d03002d0413202c0045540d20500204209000c2440001484e50068040d600c00c80c01c07403500650788406c00c030344c1103a29030140300014070489807094182c442890240d0140c00c0c0700110f0441110150004207010701d540c0c482011900d01858441c7c0307030401d0a400f034803006440d401c0d01c0c000a81454115400003100404410854092801c01d0044805030b40d5440da12804d00d03c4000a0403000b00b0003402c004000000120034000c100d000120031048141c00f450804c1038a42d40c00051081c105507100416402100722640740c2d001860101c0c0f080740418024000003001c2c040c07201d40300d290840c0c00445151a4010940c1402036082c0001d5102195401c201c001d490154190343e03196480c031402403c0412179030595071000c20117101e501100d40500d0014083d40c1d525222800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882374100 1106 882372994 882373001
    0x7050d02091819030305090f0c12011401090618060806072a030906020c011b0f02060403170405010e0906030d08071404080c090709030f020d020411030a 67
    0x6000104240411020f43c050000f0f0380d5005003455182005000c490026107443c000ba0444031a0410410000402c00340710081903441045840c1962002401055540c407403480f80d024440c0002a50b841c9908920227465908809515011000312440c040f0351207440f0b501c50640119000507040781c0901002c15060f48600303814540081100c0161141200031541100410300240051007100d504002d000000082800c001e0001c00344540c0400d458640700100911408400c4580411512440700b6140110fa10511410300b410640d000d151003a0054090f06000403840800d140213880e040708a10b004050240150440c0c00c0035620440b02110001c10401c00d1169119000c640801041c00500080136007102519141c040c001c1006000c1c00c002d40144104050340e442400030490201d02c0b4580c05034100c50440b901e04051011901034014101c1302e0030b00c0a0040200b000700d036620780 = true := by decide +kernel

theorem cover : BRFrame.Cov 882194244 882374100 := by
  have h0 := BRFrame.cov_init 882194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882194244 ≤ n) (h2 : n < 882374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
