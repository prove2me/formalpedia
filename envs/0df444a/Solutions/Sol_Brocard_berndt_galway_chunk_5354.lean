-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:34.454124+00:00
-- url     : https://prove2.me/submissions/6823c1cc-c4a8-472c-a1fa-4a292ae19355

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962769784 ≤ n < 962949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962771034 1250 962769784 962769793
    0x170c0a0b18030318011d0714061305120f0d0306030b280c03061e050913080702040506011e0e0a05010201060608010b0a0201090b0f01142706060d0c0c05 67
    0x103200040d19024031a802880c000d50040000c03c0031308404240c20300060400c8800411100003605028441400c11141c1d2000e692080070148401c103602015080b08034001d5800c5801c00300a501000401c4125210f518001e010750001949944424800001105c071660112280041d420500800038003c91005444290301170010a00601003903155400e484005201d089142c0924a030340350060030030680c9202890b81c0c030b01000038418290303100f000c2200c41000d50b0000851500b024042100d10040a00018070381c2c10f01c003c400250000f0aa595103501584c0001c0c560740d540006982d6a480721700d00d0b001591900c1548410303c0d0740103815094034101650b0102200c0e641e00c1c016801d882c0c40d4020400400c545d80014080000c04c0b0340540a03588951001040c0c030304070b986030140b01820903501180720745a60401801003910303a002d050400b08095070f00054907582081000140500120fa820751b000195010540a0b901c40040d15043c00711840c080050b10f6003980060640c00526400301c41c2c6024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962772284 1250 962771034 962771041
    0xc04090203160e0a0f0612060f18030206010305100501050d060507260405010f0e03070201080903040306050c030108060934030b0106170c2d0d0c031a03060402010f0c170c0a0b 77
    0x60601404c02110500780c103511187c0b001d590380030050003504040180c034680d02d08500c40070180602c0104007041c040d401408265055040141c2032000c2e51103201456070034440104941c0d100c0c00c040c2d4000d290001c000241c20745403c0011038409400c1c800c9020b003c8602e00680d88100c0b250f00385640034500c280c000304044601c2c2d0447c0c80a46048010224a5400c140031420140d4042c820b040c1d0700c180928140ea107000d4880c2e403907808030f40c401c2e038810780f4007900400140180c50040000b55005030100004005080040003840b4071281d1b4201c0140d481d00041440c0c1c0100e079190243d1030050b5a0050f2106083e68484800620501d07a00314415012a8400c0111b060102c0724000c41e40c400620001035890500000e64000790003c007104208008001044180034110041c1300395008015144c2d808250000c110040c3c11900b4030018116100e500076006010050303810001028480d0380c0c0c0d05261019262600380203c1b0150360450300966080001921081c0c0000407950045140c802c15076100f541c0c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962773534 1250 962772284 962772311
    0x602150c090d020126040201021612120e211b100c080c07090914061611030c0a0b06090c0a090b030c0c16091d0c04090203160e0a 57
    0x500654148681035030801200c0120308001c0c0d02c42c1c1009006041c1800c0c0d0410011150407410100010ba080f089035210600c001c5607030520032000c1024100300001410380c2854201d604500e6803a030010503100c2803000300d54000d03004600044140b00020050000001900082c4840d80c1c00030341840d0300707070040c941d505424000c0070231540c140301c0c0c025110418108110900740c4a082c89200207840c601814843d10740e444408103d114013805894201145101192400120451182c80004c100c0c0d00801304004410300000c03420b40c1c069005241c82a81000c05004260962050300d800107038502030502d0020a01914202082c041c040684014000c2d54034190590b24a0003054031310030000e10031000801c561031034040a1904481c00b02c40152410048121092503d2196903002c0102d5005131020000310392944035241540c001d00460400003400b94110035190303103034581d17414070482d82c036001101035403000c2010403940841e0380402ca03022601d442658190348400c42c1c0b803464041c00e2216201008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962774784 1250 962773534 962773573
    0xd090f050105040b040b0c0c0d0804030507050d02060706150f031a07030603170d0240050f090a0e01021210050612070c051f0911040e1e0114100602 65
    0x311343d203c4503282001c0c00c100c409001a031112006009512071118032132541d50322481104c44c218405c5c03003030f959514070b1841d24a05003400d551060340704140325003403c5c2c09600c5038001c50360f90f03a900000c002120181c000001c2c1e585002908080c041030440040441006400c9603008084450301c0224500340e91102c0c1d08400381c4159010045c02d03902c2942440d030080142a01408400402a8025040171800200102c0524405605c110b00c000f42004078401e035044140594800c24582c050524242d040c500440c0042d0310321a40d0034000c50301c907000174201c20f11a610540d04140300c00c0080d503444040c1c00d508903840205946030424000d1b40303a400166850920101da11061058008410699401905072414120040161407a0007040307180c158001c040e06c0140c9014000410020307001c80c003810304400001141003090301a41c580a42c03215202c50000300310740c0411840e041c042e041c14110f040075014004d0194100050f10380c40040c0140101100103610580d1041d90881d0041c22210020b410403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962776034 1250 962774784 962774789
    0x30b010e0603160809010b043b060601050c011d0c010801060314131e03031e020319020f0c0f0d030c02010c08010521031204060e0703050309040218030d090f05010504 73
    0x90b42030005042d009130046107020761090700b5500014840455402107030035140300300d03820444400c298204a1405030001a5445c0124007428151100d09481034120755500000d4101c03818884041548036040c5000d411590000000300c400c40c984040d0541c10b2580d5000c28000031340491841000800d010707200e80b09051004400480d00c1c80aa100c85100c000c5005c0c0c58030042e01c660344042c500d4a00c6507514041c0240380c5109035070001d800c00483c032020302078515541004207054010070a000c2280d090010b410500a1240c5005903203195055110515124102d01c449050048150404a8030300100d0b14185480a50b00c00b84803140c0d403200105c0c202e4200c425000040740b400c400520850405840000319507114032a500e0141c144161002d2035500300c0085400c18a040104020030001980075451a03a50340500610302c0354115500c4075100e0240494050045502054010035040101c18500e000c090107400d0314441006c0c0302c0002c2c030084187c007a6200003c40e511b03000900d9489a8101c804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962777284 1250 962776034 962776051
    0x602131a04030b060f0d05100507050f0d0507050c07090f050c03061e01140417070503060405060a0504021302030705070b01050a0f090911040213090507020313090903090e07030b010e0603 82
    0x203041d080d0f64480c58002d501a00e115001074110300c4001c01520345410140c01a070007040203113440d203c480700000c20398000400e00030800078203001c003084110306682640d6442130303164008070f0260390714070040311503000d0800c0411440c46074080000b01d1485a50085d21550b401040c24081c980c3c4500828100784015070b42e05400502d030300520f042240d180c05001c034101c070051400c000b05400784018a0903940054000c1034000e40d40c41c02818141c0000c01400c001003e00750040c0c07001d80340c03a0b02c1d030940340d81004241c00092501c480000e021507681d00c0080d40e05a420090441d01e0741040140200240c1102004440110180002280c00e1401551102c2112004c450301c4a0b150b08200558000d0002c10000b11081e00d80c0c6150341e80a42d07200d00207000314685924031450402e00e821000300a9400c0609680c00b0364004100d006040b00c05e42c40a00c0c1524800c0e80302203600000c038a012a100c50041e0b0020307a210b00a2401e00140a5041d0445641c00e44241d841d0034881140004004a40c1302c20b0b0348080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962778534 1250 962777284 962777287
    0x30405010c03152d060f110a030e0907030603020d030e0915030c040c03180b0f01090c02070303050f0c011103010f0509060f04090c0b0d021b030313110604050d0602131a 74
    0x72408030100030700d400c1c40c0544a2200d07103481132030f071508454040e411540108081c01c405030000e5034000f100c2010122940000d02d820813060320702512405030361103580d005040110008090a029401580003550301406a82c50a103040c103000344100650040f4a22982080000c95403550228a2004044000a02800000549804000003031020340540c90a1607140c1068142c140e461107141d540e01d03805510410550b10f4180155000e81070143c00c01202c880c076000f14812007550006400c426a076140c2031540e074400c030507081e080d1240a0007212848075800c12110801400ca0070f00514120703000854015241c507100c9041184256044400700c0d00043c45801403044c03854241c00c0103030303140d00503000080c0854669011480692060007801189900090100c111000250b1256901d01070300010f14151704051052884020200d4005002d128a02c00079122590313542c0102d80041200602909000d01c2e035181000294001d0041010040d19400c00000d0708580d807902849685a0852041e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962779784 1250 962778534 962778539
    0x604020310030c1214150606130905070c11120a081315030b0102060703050103020d03080405030c030c01150510050d020d0623152b110f030405010c0315 67
    0x2508001c000000001c0603220010200e12581d180901801d100c500705222000241014503200c040c50742c1c03600041c1e01040401c0c00030b00031030415940202084a03280d5489130480200a0600b889801c810041440d14080c04002600004084042403040c0e4412100000540c200401952020501091ba0f04641003680015201c1401011a1714002000410031034551010750003000c1c11102582c040b9591300100c40302582c040260540c000400d1078107000541c155800700f07000d90101070f001400c1c080381001003000c010040c42a2040030700c4880860744c4411004041c640a400b580130b00d8130060f2041640401c10307007000c00a5800c01500758035020321f045000c041a400950080c01a4510203039079030404620440076005002103080c04252450301c40d1082800c01c002103200c0d100e11896154100800c118083d41c0103a041f002c44c410701f80001e0784400d10710151024000c00d04640c18a980c00145e1440207a00400c0614012030013500204103030518040709070221440c100c0b840c0c000c00ca40c0d80c002c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962781034 1250 962779784 962779789
    0x100b13060c061b1206091503030c1109070e0a17060c0d0f0c0e040b0405190b1206041209060e0d02060f070b1005030c030c09130503070c180608011406 66
    0x1080040d48180e00001d4100c0048000ba507204040b941c10600040c00780d44d0103004803030389000304005441040f80822541b0915040032051540340c1c80002d0500c4404c048450a1100043c80180c04660181264940b4540510010080c25080d5200d52040701060004514586017248441c0213008076001008280c41d44506544c480e0000d004000741c0546a011079070324030000c1e01908507852415141d480265651004000c20b90344805201ea0045d460b0604009040c00b8001d80e603a00c41080c46000103003d103441c0042a84c040491303003290700034860b080611080141c0344202c8640c003861f039070f42c0c1042261142c4c42150303035144410060b40d0005030b2000840c050300d05503000340100d60564610a14210090741da6a0340c0d080c040310010207502071940100402d050921002880500c100c0c041c100c5240040c001400030315014011011148400100c5400c00a0400c100d403816904044000d520658030a9202c00508241b95000300990420b400081d10a10501440200303191551031030302e10f56184000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962782284 1250 962781034 962781047
    0x206090c0f1306090b01140922020c010504200108010b03010e191b110a0201080c0915070c03210f0e010917150705090604061421100b1306 61
    0x111158020986042c245200d11a07105180c010102c1240200d208841440003401c51070701c000c07011a15071000c00020307501d07603100c45102882c0d104842d021200c051103d500500207000b503001d5004150f10f041e0070b00050210030b000c8200c120409042160503030f5014401111012001c0c0700340c1552180c01d100611404100b480c41c641c0c40083d01c000502c00b42050310004080d20080765040d495010f40000304001c1c10f40c0000d96010b4441c3c1c840041c66a030300d0a5000a1500c4001020403110f100086411708690340c0314890b03150781d05c040018440d1034150038149a400140759203c201c80407200b0110741a4580400e00c1543d1241c001910361445503030200e9400d956900388121070034104924000c001c1520300340c002c207032154841c200c401401c0035462100f00a030812000380c508400d20206001c0c08501760350ba10211000e07075600780b901b0907005810400042041c001c0380851120b44444042807019203c016403051f200d00f0b405814900c0c02607568206e1041d602c6043d241c0355164041850600145000701d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962783534 1250 962782284 962782309
    0x308120c090a12020909010c05070303020903190b01240503060f0315090f010b03030403050706050d110f070326061c02030f0115170c01030f02071a01150206090c 71
    0x56149085950000140c00c0c60554010184095021943d00154182415041e030b014074068002c1040c85e81006000c0e0a500481d40d0003010941c00082000391900e082c005407000c000f15a0880c0c4c2410340625000d110001c0c01d01810b252848441004600c951141412004214a5032a52440e64861505210b13500c8405003406030544111545d501c0c01402d031034489449100075501800c0080310254285003910a00c41c902446948103001c140089800803401c07404441d078a0901955691070060800c0140032403045520906401003401c2e08003411480003021528465690350b040d124041030f00300a803500030f602c020700c0c400011001851a05011035031500d0b4640c4025441c800388d006070b001034904001d036125182c05135101c50300102c103900180d50800c06054042c0100001407900c98078950b99045085001d0704141c0c91305000c80d4403450940c11130300501d4206040750480401090303107061454080c42400d594404c0036100d689040c0c40401c68901514103400501860081403007040501203102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962784784 1250 962783534 962783551
    0x5040b040b0d080306030d1805121002030106020a0b0606120a0c020f03070c060306051c06020d0e190c230603061f020c030606100e090c0d0c0305040615030812 70
    0x10440d50759541d4826010000561041541e10360741e151540906042180243c0760002340700c1a542e100784c021900300c1211013952400d0b43c200e0035004c0d0498200d45419040100c0030822440000003140240d0301007034520030107000c1c3c02441d10780d80b10901409014400d0011001e04041e005000c6034481e20182c100000d203802c644126800a2402c503507841c01e552021004542c0c00006000412000d03070940243c0008003800c5403900041111075114066903009064014415540002c02c4180c44c0115403028040c0c3c2c00003802c6401060420290341840d100d580029a145122038070000742c140c0e04885145400d01c0c14030000c2e0703c0c90f400304d018000740350805400e15502c002c041782804550780b0000103504110480f90300030852010b100d020315040400c00307070810f4000c009809900d03c0e03443d0040100b00815209607003034012a5111400340c5424003828220200d03103410003100c01c000a40c1508154011400b618041090350311404054150040398030006004000a03c61101ca006000e0b0400b0740c0507044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962786034 1250 962784784 962784791
    0xa0f140f0f0a0e01090c0305010b071101090312081f050f0f0a120c140907090608040c09050106180f06021c0e0a0b04060e0109140d08071a0405160f05040b04 69
    0x11040061492102600030220821041d4010045d65559000304840240242810420b80d41401c1c07000003075218900000d4405041c4030040c60803a4414a03810000310b800c00c6100c00d21090501c0000d000200035926100141501a27003000526103194211044034402001074450148880034840d034620507558072030780001040d400240c0032005102000c0e48900c5980b070400070303600304800c0f030174907045e440c131814013a4201f0020458800d402684400650700142400011640c50b454121506602d81e0001c032405401d0038000201c407500840e444860b0903035443d000356004d40750760496080318001c0c8101d000580c0b09090207194035141202180c860061454101a100710f13101c0402c4030b00321a0351005015106c005010080d5503406044074054a1f42440d00d0b800b281d10b803040c000f4401034002d41c9076109110b41503a1808105204040360015940b01e58201c0070546100c225022491003104d0690301b600503c2c000b81500b10001900d10241d400d40c6e01d0444081d81440103020050080d10f1449410594 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962787284 1250 962786034 962786059
    0x52e021b0411220515090f0f030307140d02150c0a051c0e1b1237060501050102070b0a0203030f18011a010e030f0c0409030c0c140a0f140f 61
    0x208101c40c243d10503000841c1d181c565181c8411300000042d0200d2035480664203015060700d554803144540c02149089a41100c0400c00000181c154419041c00424204036015a1071084d000031400d502c0c03a190710340070754500e60081122128441401c5410429102e0108100610306e40548041c280711030b43d0000f54040004105003003030031103000d2010b00c04198490502e0b0301565180000c900c3d82c41c00b083d00d64504280e00c00c4c80407682c07011007444d242000340a140c40001c04103151040328000c200180a4541d1354651030800b040289070078060b09005005410000c44d620120404865155000d58021461030b903030800c2000122002500151030780036000c0904030340f1070090180d5580441d9039070117034844426450015103460141d00d641d034000c2e00403d00703008602c5408641c0030100c0c00d0a450114114005207822220039103c0c0760000c01302c0c0c10800011a148071107204402e1aa9002c1e6070b1044081c0c0c803645a81001c801a20643c4c10b81106a40c3c0200e0318200119050482070018294598460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962788534 1250 962787284 962787307
    0x60a021b0709060f0f0605070b0601270f050303070206031303021608102a05032509060e0301090b0c160819270e040507052e021b0411 59
    0x80d10b030388054400d545501090140c41c007106410002400b160380004041841e050024120740515840a808504d0190002d5100e03401440c15044c00551180d004800500e24038440320000c00501030340400d444000e0000c6144e00b8000110303151a500200064155038900342c10100d11004100200d007140240c1c1d0040c40041c000400310805810400c2c00f600348803188501000c1158445070000c0b03420042c08941020300601c02ca20010320070954608186da9560f0030140b4010030490102d4120070191120103030220b19800841c1306e0130b0300c440d42d8910301d4a409450405090b101c4281020f01440e0200c3d01042000c010f0000500c0305009446001e0071940c219110301c1c0071030300100301080c4241c0710a00483c4d00154400f603854145008100d207003482041903840c0048840e85401003c441c4c40f40c81c000301d01800700c2041000000c1400604400e21030f900c009040080041246503100d42002d240b104103901390010500c81184880400c8000c2c615a41c9030810019140882517a0703e509c004006002100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962789784 1250 962788534 962788543
    0x9030203010f06030b16051b01110a02010e0d2a1b0e070f05030c040909021503090a02120f34080312100b0f1b0303100312050c060a021b 60
    0x20702a068001406500c0c50805a507502001081d56040c03404640c906c11515401c20107440070f004000d21103c9440700d400700300c580182940080150803000109102d41001d80c1500131000400c0c10900381c0b20141841c04041c8c0d01c00c0454201002810300100e01c2c00481030703c40651201c07450207000d112544d9050714140c0400400c00d5042400388141c4c4a041003846900540324889068443c500030f403462500c1e800807980d85c02a8000d100348a62100d00010656590048510300561900b609a80d00c0c10002c0009644460400301240503001e801c10721402010003040c4012a01142000b51507411004a410700c004501144400081d51422a0301d080c90760f4000a008060044e000080d9a55901e6490010300040b008040d101054a40ca10501081c1e06003030543e41046a00914540c480108851141c3d624480c0020b641c55031201204000c04441600f0a0900701c078003400081d80e91b6070b03044008441030300c240c0c11491015480b01012481560a07613006040441080c0e0450303d4442c5a20201c0d07041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962791034 1250 962789784 962789801
    0x61c0906050403020d0215011203170a06081228030f020c0703050c04060305070b03040507270b120a0b060d080c030d1503030e1306080102040b04080606030c01140304030903020301 79
    0x3819512820041003540402c00c070500340340b81b40010000100d64500b0b01200500500481c0c0040d009420054100360083c0720000c000626080036800b1840c0050243d002841c083c0300b42c89031441158911003088401c0001c0b035100401c03e0096100d451403d9110400c01001d09000008250b921808498138400b148040c18502001402800c402d519509140703240000c50030f44a80326074540b10082001402c005641c508a8800901068407a41c131810030508000c050b5003c0c0e41c80714a8a0f01075011010505804c1859907920301d4104050903242c2c051100c0039801c060342c483d00340c1c0b02c8013030800410b1000154a40c0801c0040180d4080303100790341c3c3c0040309d80042c06155a2948040354041c0500c116004108070051400300c00c010480c44c549004045202c801022401280b0350185103291540039040040039040c040000d43da11030740c40e102c10040e13074498401c040c110300a8101203122854040f98910344400c05035101400a214800881001d0348007801c22000d004403400c000005032000e0048101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962792284 1250 962791034 962791043
    0x51902011d03250e01052e0c020303122a09040b040608010e01152306090613240302190e060408060112020f041808030702070b37020c061c09 62
    0x154103103850090081c4e10b106820151240d117150781e0704480d5010014850070602104d2500800b12000201c3c166441c2801400180d01030000140040360300348489107a5010f0310480c407500d00c4252154080c0c0304440d0004004c000901e408015246140c502600320074103403000200006801e540e6040c005007100c14945c0030007420794468140c1c2000c2080054018004c1c081307914940c1c000d01c1c813086284d01400d0100090351150b070700811141e00c140c440320142d5007020b066988a503402626903150149002c0a00300c060441c0d4000c12190100921038020381c0c01c1c00e2010200000c0c8900c0400c800d541c603001c8075202580094040c40b0000f80184200081070080440c1010200c0400e40c40c0140101d9141240350b02e03014a00b055910321401c2c440d1191a007056030454045038032034171940b03001c030f04044d2164403982907080003055952981d0101e1809006078040c03c8180301451000041880240158040f504096048480d001d002400d004004001c000403002c2c2a0661221401c002c5003258010746040ea03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962793534 1250 962792284 962792353
    0x60903251d0702060601111c03021b0a061a15070503310b0403050607080603010b0a03080c07050301050408030109020706060f090e0f0c060904020c0304050319051902011d03 76
    0x110b6405100c8103401120a1130404641e0304910580c540d14035680c0d400701010b1905000d241660b5209505558401e07455019410100900112042d600d82407031100f5501149003914246a90010a20614a600d0050820041c40000b408000a9034100910640d5075010030010320b9200c2130014040141c802248004000b002180100000d10414ad81c11260040804010600c00b01d40002141c55018110740381441850780c40f2000300740502102002184c00400c1443c01100708407110010701600004842210b1405546908041c242d840c280c0300a82003000402c014411100c203a001000110f010b00c0c0081001a03544100040b4a5019800102115901d00f022204414141b00040c419441c0500400b00342c1080780000c0c001344962500c0703612440d0300007000c03480414180300b41d400034500201916410680c1c03031442480b081c4542c004035001e0280c08070a564502c804201400c981e60103035550fa6200000c02c0349240a03c840d02406503040c481e204400d1400c551480031040184201102d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962794784 1250 962793534 962793541
    0x601030b07021606050405220e01022203120c080c0d09080f0706050415030906060b1201060f0c020108041406010603200903100504150e030403020906060903251d 71
    0xa0901e43c00c12080025544140e40c108030040d0b00c102a175082d1803045603070000f458101142220b40840c083d01d42c00000b0f003803407060040c00c00f0642c05048a80a154100d08040c13500c500c8548040000e0301005240da0010900058011300ca20002e0100ea840380308482d1620313045005442c681801403246900003001142c0c144a111424062074268282c0344c0c00511046007080130181440c0214040c5d41c070000c0e01c000398010424802e410003400c2540002c0100209030701d40016054651107150004624481180001052071203180c001200d44901d5494280c10505030740110b405280103030054032000000100c40a0f10802408218000c124644000a001d0000c41c40d0120f901d0000c261032441a4041c4440c0010340c0300400d410103036810b000d60000756940e403850310b0602d08409440050400e072038401400b044140000003041a20300846540c003030344e69048100300341032040c0030019030180c00518140008025061050f403030482145421285d41d9203c2d1010702d69001c203880f41078012003201051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962796034 1250 962794784 962794787
    0x70b0403060e03070b0c0a0507060e0c010e030a030206041104110d0c02070501140403151e0b0901090506061812100605180c040b030901090f0302100c05031005210601030b07 76
    0x800b00070b0000c0c0341c059418400140c6400c2e26260f401401c03189019000101c201005126030f00f111039a81d4408010818207c0ca04009541c07490458a1103011664a03100c0b507825240006200d400594154000d020039640c0781ea42a1140040680084e00580c0341c0a000307500c806100043e0030100c5070720500054107a0035120081ca082001c0d03004a041c00120703882c0010a0724864110343c10b07a6040310540000446d200c1150000f4500a94090381c80f04901800083c602c0c101e401100b42d10394110790514040c2d1300e42c2149012180259030b21035011030104a00e0050002404540c010014010945400000c4800350750b0b0130701104400c21140c40755691014000d07480c100c56001540305880995991740e00d4121280000c61180d8014913a14031000f10005031001c83c02d410210000b503001101403200b404528010356507510703512400c81039034203052140507041c1c80b034800d4034401d004506c001c2401901d40400d009040c640358610300030310750300c80c0c000e600720070020400e42e4001c511907000000240b801070300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962797284 1250 962796034 962796041
    0x4091a131509020a050a03050603160e0405060106020706051804060e0a0b03060a11090d061806020418050912180a080307030f1701090b01110f1f0b030607050f0705070b040306 77
    0x494455441441320302600d590002c1519081d1030b00e410000340c940c407000c00107841c11450344c0c03140844649920b004030b0a80b86c40c00e490b6004034403400440c4e00590300c0d040241d0305d4042c4ea02804002880c02c0c82250350000c100391080000c220090301c0096820388070001010380a500301d8607a8400364861036810003d050070804240c1c0301d0302e8036908008030400162124250310455034042d02c50000c0141030380c00c1c8066a4001292028000460703d840c00300e500d0036030040e400600c6551075066403400548a0104180102485001c5a07406001b410710807940081d1650058200c004001d040d04091810546400070740c5005001880300440d240c0a40d03240c006c1c03010910a409504003d103108000001200203d278450542e0074951003c110f911030240121585004c08038503c25922810000110448003c221114111000355031901403400d080302c050241c0c0c040740d059070b40550005000840c0e0500c14409481e140d0003042440d032802c0e845451b003034500902c64005401c0000b00042c2002042003900c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962798534 1250 962797284 962797289
    0x4151b030806010c1202060610110a08031803042601051312020c220c17010b0708190c020f06040f1406041d0603190f030c0519051b010206090304091a1315 68
    0xd0f103c0d402b0501c400c2515140c2c000c5450040002c1ea003c4003050038040c07186c0105580c41207907402c9948403641d640a0105600303500d40c0700c0b44c030002c410304030024480c0706010f82485904c1e40000c0e00e040215654810511007150300d204d0341180201c03070030085640d4600150203901c2030300b03d0f0184a4614040c0c10042102c032001450003d2010300203a80d0b0802d141100c9450448034100c0219031180600e040040e80c620940705064440c2c2014210382940c1604002c1c1c40c44024000ea031034048004101c024070809104034018a158401007140170085481c414400c0d0300b040030080c15240c00e055503440350f07643d5810411400d80180c0045020055641003c001d00d501442000d5a611a8079200e6207502c901c031450746001504000109450006020007040700480c0750f090300011801e990042c0c144581c035072248a0060075800ca08a122500c0703984005411401810b207034025524003880c0c103007150700034400750b5081c1079003d108184030491961011603a10300303880c041d000816110044d14250f0311030032068 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962799784 1250 962798534 962798537
    0xa05010e010b1003182a0b0a020c090405010902090c07140a02060403030f030b060c100506060a0215070903020907080106030b01180911040b03010b04151b030806010c1202060610 78
    0x20585076016034480d00f41030103254207401c0000d000c200e5010ba00030711524070f9201608170500d010104205400c6c1500000f01d4160101703401c103185440745080b072611f1040741040f800680c0318044205551604018254205100700000142205d196010419418003217615aa24030000f042c40c401f030222905800b4050421913010388240040703a800100b440c01103000c05420086d100000b001c40074040d511a44009000404694030f03080615030490f626041202141646e030b040c20f000c11502d0424006441046056401401403151304000d80300c90100c00030304401c10895213190010144c2c03602070800380a401c0c1c0b80d581c03014039814204080c0030340d000700520754100080c541c5021005446504040180d62518a0101d00705000c2d680304c84441c040ca400202500c8030000001030005801e0004004442d20000042d1a0321484241560300d041c1d5250070b04d07100c01c4030050040001c3c1c8508101c960082050404c015a4451130f1291900b9000840131440036078450740500c040d07458010110b0710b50f2941d6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962801034 1250 962799784 962799791
    0x30b0f070215010e04060f0e030a09050a030215031e0901090b01050907020a111203160b130f060908160c170a08090904030309021e13050105240d06080a05010e01 71
    0x890310700303010b12001440b030030030006412808181000525000440842500f04c418031241e0711101d890703a140c2c0d00c80803c00c2c1c0424524440000d850030000a00000c483d0014031012002981945030401940024078074000d51015078002c0f502807444c3c0c102c05002d01c2140000003504981881e1010304c644040e0000c6205a0408040281155000581e642c46035449881d03007954020b00b4020541d043c0803840e0014690002213012049100d020741c0035100d4900400c90140035403103502e200c2141e12410701d000b8000d14907400b21900411002c0e00300001651060080314500722122118041c1400c0010085500d10181441080259046080030f1035501c0d004000e440500050765400e6224450070521502448c4114006003d040c0a80d02c100400c40c3c002c0e200318080030f0141c0d4004d2640304120b40191041c5082040500c175154180300303050607613101401c41c11440d00914503650f59464107100242c4080ca0411031181c08035014095200282402001800031400303916080342511050000c0c1c0601d40c1c50b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962802284 1250 962801034 962801053
    0x507050d09030b063712051b100c03080615070807020f010f2f03030106050c07120b0402061b032d0a1428110f150601110313030b0f0702 60
    0x500c000d104040010f40e0b04000000344850009180c180300341d50041220059041482c07007805000302e8000703c001c108041920b1f500b282c140802881c468420140c10000301180310180c0040d0254cc2110b410020050242505030484100f0420f03950000c003086500c254041004021810200c1c4055804842420a60721484001c1c6000700300c40b0389003150046d000480c0c070301c2240400a180d41d00c03640f01042001e8940e250b8403400043c0c000c1d807000e000302a061044c8200040c0135801045511849540040c1241d000d072541d40070011290818040c40d184036181d46001c09110004200900c0b0482144e0107804025a282490302e910301d13282d1813460070340c99080100c50f43c11503001c070680d1500103810300e0503621211005407505404483c3c8982488403610084082035a60f04081400c460300b4610085a00d0300c552000c050f51074681c044a04c0a0381500c1d070300424985c0d0300a10b1005c2ca03002c2902c04032401c0c60780940d000c0c5040e0801b68410b48a011a4005003d000182120102c0c1d1290360307170005244860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962803534 1250 962802284 962802319
    0xe01080106051c0e03070302010204050a0b0f1209031306120f060b0d18050102041d24040b040b060f03040c0e010608130309080a0302060115140409020a0507050d09030b06 75
    0x3240d42907180703e90510035400d507048240c99000c007081990000c2140d45601d0280b60190007940580201442002140c10000c0c04010300340407540201c0314480e81604000110303240f8958210040c044461034003040c8100faa120702090710800003000d895580d850f60b003c820590b0404c4800c09200440800d0400380240101c103010f1013100c6113540385040006080c1c0c40d0000b9244525002036000380b00d0750000070001410b010002c54484507100100400c0b40c03d80320360100074031880c1203903a20740001003010410901c0e89083d90244010500203000450071b2031601000800641c0420b104070343c515004800e110900c01c0c1407601350b0141ca80c200b000e0810707504023100507040c00001001c0755035010201100004240c070580624000f44489000c844007090240790103034a8003001d018000884440940c54410f8600c5882e4080d02c3c00403141c00702d86490304001c0608083d44c4040c1102051003070410030720000440800c01039688100e241c0e0344441d81c5085150528100c04003400580c442c2108541585002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962804784 1250 962803534 962803537
    0xb03100c0e0a1409040503070f24020c0d030e0c040c050d050c070206041401050d020403030302070b0603060621011113080706030b0915030f0d02030909090106120209040510110a0e0108010605 84
    0x1c030021240e404c0d195503189040c0c0e14510825200030b144111a85031a01040b17508a05150b06a1980300112102c2c0c55a0b9007820490180c00c0000c05154000e00030205a01c0c066841003008154035010f8800915400c00404c09403800c5420f00f400281c1c0c005504062000c45201d8542c1200034592514a070000e41d400154280c000d034001c0002940030b03040c42d881540e008504031031007850100b00541d1625030303c0c20090002e4200c4001502c1000d4030b5400640c1c10724000c5119445600014000094407800c2c003d0f015a46008004d020300b01e6503200c0701c496401d1905130151001e0040c41004c2c82980f03080080307041c1001d540381c1c0000706040c24481319045a9a500380c0c6550301c0840c6181c01f200241d04000024580040e01c0c00180c4140140307101d103c0300a0707001c402031030f4500096850b01442e440c3c4108040c201c810600c605840150410310010051400110460b0031602501c101c804507500b1395211011a07102c40000498907230005090480580c10860b20039009100f401c02c1c03440f030345c074000018085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962806034 1250 962804784 962804819
    0xc03060f040b0a060f090b0f150d02090d080304110126070f051c0b011106220c1d0609091c260406060503061b120a0b03100c0e0a 57
    0x186202c110000c1e0301203c079580084028460f49518a00305991240d03010010141c140030036004030204ca58150060402050740b806014000080501e481d00c1419058020740000b24002d610014501040c400b040a40c4051340c0a04c1c0110f046046d180787c00000506003100180410410b030b241e040c100180900203004869010826040c4031044e0088071400300e40c207100761400d01003c2016080100f281000c903602100e407031036080c0c0301d4001d8410f10340660760781c1d40c400f01d03a4584214402c81405014551112000e1840e074440d41c0703608410b58650054042c00f4000440440c066a0800704205079440d2425195401040795000707806007003a031512202d52294140074078824002000c1c078031440b6552064042c2c540c4044203040c6107840c1407910701038000d080c2511940340b10344946004908042580e0181c8003e040040b00c18500c0c2c00c0b91118442c5155900a041e00c0d6100d0360f908000c00691020710034010400b00d00030001030700d0300c403413030001c0c1000b0059804903000b00f07149142400046e0562012001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962807284 1250 962806034 962806043
    0xc130608150c0406180305030d0507030b0f030705060a0309020d0302030a1706010f082a07020f041103070309060921080f011503020721050408010f1404060b040f1a030c03060f04 78
    0x404510145900c4500d80c159170004121323110006010400c0d10349039021602550f89035400380300c2e042132442044100b01036080b002c2e0740741d081081d041141d85082c030001c00001c0c80354140420406940e800240200300071000640140c0c1001640a1803280e01a1b01103110139140100c500a41c00c02600081135240740d10b603c20140000d6401184117202408281c0c1d040340d42052303040305000d031001c0345080b503a00810402ca0243c514403940460328a80350003404503020701c4600280c1183d46c0c441e4100c0142c404041e06a03401556083c00340045400c10300300d08040521186840d410b00e480c00b800516001c070090440082900b03010040c041c0e50007000044c0c2c16051180780240e1a810700e410141071030744010030082c41a25001c80b08800d002e8000c0050700c11107060360001c120040d003140030300b020384a4051113103103500712030b000080c00200d6a0340f00d050a1540076100082c964411100e0030111456020909010107a000a180285ca002c22540c0d02d414015000703400300c3d08010100305403919000c4c1c402031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962808534 1250 962807284 962807297
    0x610030c063903080105040509060f071b0b18150a11040f0e010e18030306040c030e1b0307091b0507050a08040f1a0c120307020c130608150c0406 64
    0xc1c15104448402c0031100c2080304007000030425441c040c0121200c10811804500c02c0c0e4000a81441c05204041c0f181090a020300b0301951a81246841d03080000c20341e1043c04004040f41c0407240443d2401200b1620506500381242810307031007074030381c0410940b0660740e550184581e00070700b400e0b4544180d048000400086901208000701402030301540d0031042031422030010005010511150380ca049030b0072000f0403505034440400007000180c071124800f18548c400c10210781e0905183c0d2280c85049000d20700000d02ca848040340508040790143c1080f903c4500c00206070440c9010301407540100860340041040d290b20007130002d204a0712000610520002090b60024443c0030700c0f64181480c0e00c007290315552900c40c9030007400c000e170074003417603510002104050140003441c408558ad41c03220b0138001e0403665140518445641d2004015104600036000c8c00c10f62511840d0710300f40507071885100400e210742800e2040e8501114035400030504650071080c088003189413811102500c1203403030000f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962809784 1250 962808534 962808557
    0x130c061407020402030a090204142811030a06050f0402121504110a0210140c091009090221090a023604030e0a1401120b040f020c06090610030c06 64
    0x4032140101d40c0043d40181c000001c0000842c659841001d00610032038003080003003212451280e82400440d840c0030100b03c000d41030f0102c1042004074008010030480c011440190806105085030001d8030620b0003281c8902e4284050318104203200342500e810341c0c2c110308050070703c040c2c1e5116540151038074107882c444d40c1c029440e5843e81d41207401d40382000d16190b603484c2007400000f0740d1291400a094a201d103080e0890070a00114090640500301ca00d002a00306a4914100080281016100320034444000c4001034410f005002401005850744010503810741a035000700e07200080100503c10b541c00110000e40169182000121501d00082c01c10341e210081400d485480c001500520602d0029281007200b0036038000250700c41c01006403264a100c5a480d80078002800d80741c1c01140c082482603e0140031442640c1c1b0144480c4030090002c104038244054070b1049901200c6100459004541040385a000070098a50010755520307010102914684130101e410407180941010411f074000710 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962811034 1250 962809784 962809817
    0x4050c01051c0e0a06050408040603060f030201050a110c0901060c0c140a03150603051f0f050105210a0f1406010803030403120c2106090b040e0712020a08030301060302040e130c06 79
    0x30784070313250340c401410403440c1000d00f09124031741c000303100d0400001e08151001c10000c0641c07845404596060310303014282440c042e400c1d5400d0500700308403c6c1c28410050802903503528941e116008000c2d40e207031801b20042508260309541c03000c1c1c000d002507000d0805c0c4c850041d01c4000420048940083d040d51164802852102c0a00f1040c1d1014015215414040355070301d19400060704c80204650b010000540151042c01c1901e109202c0c02d0340c004940030703c260300c248140d08141c40c40c2e0342d808140c5009803021b6070384030f01e100781010050f98841039040620852a10400405000d002500015410b601d85590000d01c09400c2c07905100d229a283c40750300311034a0294005d460b54184003609009008c071044a03141c000e186511882daa0340d410401c1054886c18180304860401c80c040001d00281d03410044441261586c04c202240c2044901d58001b071984d40c24006103010301655071b809030b0b50f280303031586036209210b014021050000060f011000004c00070170014048400c5801c000990f401d01c62107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962812284 1250 962811034 962811043
    0xb06010e0d06060602010203062b06022b02030403090e040b0c07030e03010f0b01032f0304020a050607060203010302012a0b0603011e05011503110a050c032104050c01051c0e 76
    0x800400150402001081e045e8041d0007440c070402e01a43c001d0724421418072100112000c1e460505244d0209080c0380c03004c9180d035001400300c00f21100e15039101042c2d5415620400522946901d00c031603004c07007070108141e40072803040000c14014400140c0c4d4103040d121009d098102030304100c58114001034203c10540190b05082c0b107031100400030000c9001d048079141c003400304d00c40458000b130700e4007120b034992000701051840c5042c2200002266041c607a05032207075a91000e4801c2c3d9004141e1100050182e5030100105a1a4400c03180542c40c1d514502c00540f00d80d052000c0d081704007103004602c29040c411801000d81d0300d074008009001c59202d41c004640108580082e0422030080c0b0380ca6a90651081d4000c94100d070410800b1110398504001e08174200c0b4031440d00601c20601c10020888910301c1840944921030300b0301c003541d180c410941c808580c0a2241c443d15040401120f0800051203030034400002e0301c2c6002c2c24518036000940ca4003900c81d100b109108420140c0d6844998000d400c20030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962813534 1250 962812284 962812309
    0x8070f0207051819022b02091c050f01021207050307030b09100303090b19080703140f091009150e070308040f0806100609060c020f100504061103070b06010e 69
    0x9200042100c01c00c2c6602074072a40c11509099519101520b0301c4a030030482c406c0f5010308061020149042000418603079003490702e140d40c5c0e24182d409201d0700010f940c45c04148000d01c003190f1480780c090700d510702d002c6050142c54061940c69034414004000c0c20f488038001103920014510f04950340380d9491100750014a0380318912030b04410640c0c100000c811400103243c0641e400f940b235600790580d50ba038001c4042d1003141c5000c02215800c904a01e0841d000703040c0b8641190903400c0100702c10705151030f50544544d04a0b4401400300700d88060000e003e005109d0000c02640401e0706010007042500d94400500d0b4030030800400d03507039811444a4820301402110080c59209405a50780e954503242188213000314003603414140289008100494000860102114600e49074103440ca0f00d010420f5403188006035090360004809802d100180d521038200000064a6442e8107440300c1c144100204000401d4003918619803081104101003000b4007180c2c0c0d8410b400b40303000e403c45081c90740880e4800f0041d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962814784 1250 962813534 962813539
    0x20a0308030a02070b0f27100c02100504030203040627171e0a0c08071d06010e1003061406090319050322050f09190509070b070c030b090604020108070f020705 70
    0x1d01b88941d581000088900501102e440448401062007081e81411040e02d20f003903c030f900c0003024031448001500501e0065019005a8015900c8120210250740c012501140180c100140134451a908018842203015071a50940f9044403190b1460740700142d075014000110804140e042d500340820172119949481a0a007805800681980980c0d580014002211030210b02c082c0480c103c3c9001443da801c9825040b52035032145103607100c0d486c01b1100600302c141001840100b10b41161140400140b800c4855900006c806142a40c4070020120f070a04461103540c0030814000030303540005102c4548001c803100d10300c000b1424500680b035441388404403a40200c0c006c0020701c19150010803c02150815120b44070304c0c007882001c210502e101124a001403080100300444003e03107c0e840360307a100c50603408540071b04da114845402d194010440c126068440700c80c3c00e0007004108544a0380100b0024010300c801d0800c3e6002901001d0700034035071401c00044441c640d807107520070000300000700800b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962816034 1250 962814784 962814803
    0xb0403060207060506030303061804020f09070c030201050f130308220534030b04020f1908010b15041a0702131a0f031c20010e070e0103020a0308030a0207 68
    0x803860624069000b580781a80d040345410001a1386040110880307204500c0200700002c005403683d102e60f01298043e100340e80018942c410b00c20251140e4041074042c0d003281d207a01410ba03802d0b260090a50342d00a003600450346094050158400741080314203d0183e15003007019407070340d40f4088a19020030380c2c01c0000b1386a00440700b41d81071000118903e92884514118684040c000d91000056960304030440c2085c100490000c10203d4085400b007508544003d1003500520300141c0050b115030380c071105c2c402d0703117524940781044801424400c41c403102c0c500b9581210481c00c14032000e034180c01140302d6802080c0004d40c3d0340d40c50780210011107020a50017001c0007401080c81c01650014a1809201e00800008880320140d03813520007024155110700400030108000040f00c4205080090306900c014441d4034800c2d4541400000480c81c040e000403000001c1141e00d9003442890719040b0b6010030482e1070010014005600c84800704c0e1b060340d41011210b41c3e25120560304030b00034444c0385070181c5003051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962817284 1250 962816034 962816039
    0x1b0e130f050a090b0c030408040308212511061b0403050a060c0f05160201050a0311030a0b0a17031602280906090209091617010b0406030501060509060d090c0b04 71
    0x200e0364007600c0714502404014400381d61304005d05140b4401558080e0403614140005c2000401c00750041200e01c03007540362028070010302c5041156a000035160100c0c0b41a4011907026103c40307120704290105444e2030100003100301120016143c11002c1c1c0803030302c0240041d4208000103640c07001c44004640c00703801c9400030b018030f082400003070a04144c40350014410148406043c5e1181c42510094010580e8140061819500559156000140c6d00c030034151181000c104400c05000a107102d002c41d2000403d800e986041000041000c58000400500800245852560000040d144406012589241c0c0c40700c050002942141b0044002d0003000c609004401b45603410600075400c60720118003d101c02510703054203030180e002e031341115500003000e0b20014481100400d02d0600d5900381d4104160440f60902d0b2407030f880700c400d03003001d006882c002600300107580d41881550300501c0c56142441c140281c2c0c00000e0500e01c1004036a00040d40ca072064101801100310010005044100d9059500c0e503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962818534 1250 962817284 962817301
    0x18190b030a0e0f06090a05063301090f0e040203010b010309030503161806030f0e0106050d150e0a0305190516080307110d020f100605010207121e030e041b0e130f05 72
    0x54040400301e88070300a0b10041036104609d00c1c120740c0c0d9500452440103c400390010038252900c0c0c001a560304000c0c0d080c0d0000303509000001818040e000b000c10402c420b2400b070041c10b00792039249071014109440c003801d100200398050183ea030041c1d884a0451131501100e88100c402c0c109072849840f84102c000c03c001410341c1c05a01003200d024039580180f09e0003240b02d10b400d0898501e446420b4204030b000da0f41c074000441980080d135002078200000036000f00d00d01003171454100c4110080700850f400040d4807080221700c04030941002624904140780c10032580910044144400000304651400720201d0740c0700340102108001782c00144101d039680c80d28104001d507515208100812603024404402e20b42c000c20340a200142d0710181c0007882d1251900300c00300c1498401e034009440300341441150042022444600109090207603403880d18043c6580100001c492030600036500d0400c1240d0100d041d16002441444440800c40d203001c001e01101e004103000d001c8042904182d24a840104080305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962819784 1250 962818534 962818543
    0x1c0b0c0d1e180201021c02010f091b0f080705060702033906030c0f0306011103120a14071d0a0e09060a1116080906070818190b030a0e0f0609 62
    0x20402580c040c002400300b0030981d040070b501804041d00603082000c40300d20390a0130810560300500303070713100000764840b41003448401c68060140032034420208040c1c0c848811142c5a683c0041c1204455034140766181409240e52801d02d44506802448045001e1040d13550910102035003100810748000e890503010b075070070508a0455106050781c000794411541d58100b40b402d03644a02d03207000c5e816280401c000d2404019030001454a41000f64030001e40f66018010700240c03280003004103e00703619040001d8480265080c0c804100c940780c0e800800c000810ba40305040448901404640c1ca1800c0002030200c0c034105642c1e000000100d4241c010b000390303228005000c40c46000402010001c0310609511360899100340c81801d0b0740006402c045901144607003008110490000700240d1505410b555694990703000310b50720ba040001c0340e103072902040c20010f05000c041d0304202040c924a03420008600d4a900000d03215012095640004d10000c2804002c4044840d00c480200c03059441c002132082c5d0368 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 962821034 1250 962819784 962819831
    0x11040506120403110309090f040f0f0b07081e160e1009170105010501090303110102072102070801060b07150b040e0d1205010b0a08070201060b04140a051c0b0c0d 71
    0x900c2d1440c040d24103078004025a05400b00007071414a42340c452a064042035507001d04180c9000c42c004aa42c0001143c002c1c1c12071a036840b501e01e080c0c952600a0010780b88040c010402104102448403000c183c0c4030403010b441d8459409600d40400105414085400d40c0501d000c007038125036001c02000d1416000f62510080f20349611404001c5802c0c07402c450700f60b800070b104550202da4402030a00c0000d000d07200121404a08200050500001340c681035140b41d10358403100a0072081e00400c14220703505001c82c8002e0003a0000901a00345400c18000844c855800b02801401c1014008050a10150400d49190500401c140b290340c003400003440d02c1300a4020f00501092881001c10701c811194000c0034129603840842c94140180b221086e1404007008003010300319541c503803001c42c01403038080c003400240a488507028811400d0f901031210a9509801281c420a810142004401d000c482c5000304950b0015900d0780725111007003c078076a03000700130301031000d00e00748046603801001c10b4410044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 962822284 1250 962821034 962821037
    0xc03070506041d090109061d19200d05070b030f130506040b0414061911040b040b071412070b01090b090f070908030d0e07151211040506120403 63
    0x1422035840040058a1040d4854440c0303180808214140c0d00424266881d8400e900c400003003079081541d62040100d840100b100c2c0c1000c160b001340e4004c030110411801940031400400d21080c0e00482e2904140031206415019201030b10203800d000d10b031641c03050544441c0d480012148500c3e1182000c01a68104403818030506092000107094120700f040882e00840c0c220b40030f4229038581c0d8640ba400850001c205032a0082c881609004900c406c12185104805001940200c54144170541003501d00c020300f0f522103560140414003034030418804075400c40d5925580c07140d540d0312a00d08061701d00c031404a921058054041c080d401d81c29000d0007001362a100300301800450780c880503031504803a0030300c00007070300107040d200011810006134942d180c1121060a20b001c10f966901c1d482c514541c000940410074903142e8080380c0c0c1c0348104102220162101001c040c03820350381044014111b030914034141c0c1e00180c030b4201c05260b08080034119006810007030011581c510b40d14049841100045e24210f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 962823534 1250 962822284 962822293
    0x1206050117030a0c11010c0206030a06180923010e15040314040602100f2c0601050a051804030504090c030c02070510050f032e06170402010c06021c06080c03 69
    0x14035040e01000303e61800506846181801c00d0300c1e102c2055910b40140120305100983d41100056503511010354031405080b1000b003806030600002c42000403c600d03008411038184024600040c01303082102d26000c21421203001840c1458010303a02402d04088400b000c1c0c0104240c1792070f00c1c0c04410b0403604c241e01980781c00d08003007401024122240f00d00e10030b05005030041c100a550720940b58111040310044440041034000b00801d601c460000780c0c416a01a028004100b2a50700d00240300302030042c241100c0012a591034100072405014451075000c841410f03d0f0001410140907a00783e43c043c02801e0410410001e010402078000c141c048120001741c031440a000031189040381d4152007a00d0960b50329030038150000701b00725131170b00043c0507804480d814648802d5182040080e0143c000c5e10400300e5050780303150400240c072030808118980807a00b603103420840540d0700b0007a01e881850b4040d40040c0da0340754004200e00300c0007103405031031441da040480003da140340005021564010880654 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 962824784 1250 962823534 962823569
    0x120206220809011b02370608060603090a05011a1801081903050d0c170c0f031620010213090605030a0609300f082e12060501 55
    0x446280340e900c4002015640d00304030341e03101540300c0c035040840c07819441501000e00ca0b5a90000b03031035250744624080c260840c00d030031444074600c808607044111201886c641c0d0303c50800c000105031540041c0344030b01915002000c2040f110b010011142c00c81d402c1002040881d108141ca0b05008224480d4244171f81d0695000f01040381c2040003150494419000804491141f80703a818001c03201c0c04400e0302400000d01209011064600a8141e5040c0702c2d0f655951a0080364210384d14504090403201013072030700f03014062060304c2c000c084071703049449400310b16102c01ca1080b00b182c50f100e2085114035904030b4801e503160003d03415000b4144450000440d80c11040e02c5404a5049510034480c15070705a1001c5441004100c00380d00c81c0b64039a0061341c1000c000481003190441c090802804039403140f4001a082007101c1e03010001040241042c50003030b549007410714042503204045507059405640c10207a02d540c181c600000b2100400c10014002080241810900003c0600b4420100c40342a1f49005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 962826034 1250 962824784 962824831
    0x5150702150d110a0e0324100f0b0307140f040b03061516020109051c0204020a0302040f06050403120c02090a0b01030e0111091203070503190210020c161e0b070609120206 75
    0x103078114500101000c47c0406003020030944800e000382c801860400302450115501c450400020050810040d8036a0381e400e00800061520141d04440c543c004001c0c0042030107411881b08540c102e61200c030400c1d8407a01c036040000d104d008000b400a05142c4c0001720620302c1e620410b100e9000c0c43c002d807a0a2152541d0b0340510810389c0d0008102015000c420f0b548800500d060350180a1340c16a6280c011f08142e183c9026018052086e08100081034010500b0000c101d04000f40300148030b00c030b10f001400c48a803940401c0c90004d010b00b803021b01b00e0329030300c4031401c0341d03c20b074010343d20360880000030b00004c10074039840e40041c0d116001160040c080500b43c3c064215001007110803d81e4410000c610300100011004040e4041203c00070440c0541036680b98040c8a9001400b40600c080c0c01a0403d514144202141200198440d140c810b55001c011464441d5030f5440d0320403141004511580c400d1940b6003000100604003004007100240c51407a00307120b0b40003c0140c810041551040c0146015411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 962827284 1250 962826034 962826043
    0x10051e0901020306060a200703030221130501031d120d051305120a0e03070b0a0216180c0201090b0c03040c0b090d0204180f0302100605150702150d110a0e03 69
    0x21303c075412040802080718101c0c4603e001c02c58001c08141483c00ca07050307600c01241851307255401a00141d000d145c08560742d11840c1c038203250b2140c120030064075118082e84006080700030351144a0615a41e801c5140300030464a07100c029030f080d4403094030b04100c020300c40c070000e0344c10060300c030000549000001442c240800e50304507000c64105005007010b40c41c10460700c405a000b00c503003104002c0c0000c07032182d803514100401c40107048040700140c1c0f0750340550002440c180c4003c4000c00074a00306401008074140382c080d10011003242c15408205c24882d030206078058810810000d020860000400080d208940e0245024a20a00010f40c0c22503032a50b0b000e5050181d5503130558424080d2500d9001032070300b58003c203816040074510f500120032549a0780d0440000e118141d004d038104144228542c40c0a10884010303140481c2c110048242e6071911050b24016900000e000e00109a0034900030117010058901300e80c0903000a011038000385603a081c96801c148420b102184007004084030500d000b00f07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 962828534 1250 962827284 962827291
    0x150501021204030209040c090603050c122415060f0a0f08010b0d05070c0b04050a060b1929040603062c0a050a11070b150105031b07030210051e09010203 67
    0x2420302c0c202400c54080042d02000540203c0ea1100c404c0d000250054440c000c00000b14000c10252070f80d01200d9080c440f40702d03460100d1b0a0150094545800209648101e10060f80e00420b003080c3c55584207900c00003c0c039900302c503030b6a02110100300d05000c0c0300ca542c018500d09a01d5030380c560386030161080641e600e903c00c4c06680310860f001c1c405501101c17000c8d4000d42d8020399a1030090f84414551300c0c4c18240120030707281a50a90810103c0c0000c2c0f003814040d070540440c0c15600074110b011142079040e04426030b80600100100540303c1ca81d52604c2007801d00b620061011003181d81c0316541d880190041c1843d101d0807007401042520f03440c2c1d082a04622070045882d84544010f01e43c0e600d10f425004010050402525540d10720f1744580d2149410301410b80644107000700304a5050104104260311038001050781044410420000c2c5004c43e503440940da80840c5000a4070303a8075910b41a1b04058203041e020611924100800001d2680550b41e10810710520024030b016484020b4601d00341e11003203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 962829784 1250 962828534 962828563
    0x204200706061d1f0906060c140304080c0f041103130605010504021e03070c1407180c020a030c080c030d1a010c02220f0e060601080703090201080f09100c0315050102 73
    0x188002000c0d2a0a86800c40300d100b0a031307584900c0d0350f4076215098100c8250b604400c0004521604e150304009034050401a0784d071000c0015400c00f850010700603030f10550500698014080b540900e0420f8840d504030a41c0309911001c0380d40c43c2d1070030015501454124840075980603040c0b0000107400d007018400c5844912001d042150340e241da010800b070346988041c090100300300c01000400d0100d80303007034141c041565840c005010028501000e00a4100009095905080c501240080800e800080075109507030305081c5511a21a40d00f03002121340207c00301c951060100045400c00390403203034407108a505103d600d125800340340c500111500c0308402d500a401220b22403400750000c07001c0195404e4100348000c040340c079481401094050f00c69066003042c3c568409000e104981d03030000310b5658407030600c0c5001c2061070002d0f00002e0900360007400c075401d8101e0380b03030102d500b02005001c41e2101c000c9404003400040a11000100203214602c00302c2451001c0f0080402c40e0740c404142a804104c21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 962831034 1250 962829784 962829839
    0x18130f090b130c0303140904110d0c0e090f090a0f03020109140d0f03020c0a022d1f050f1620060a080109020c210a0306121509020420070606 62
    0x15554103446d0310f41d0341402c00d002c000040c461600190340300c0c020780c061041d840d015680c645941a00001c1aa94402e0340b507000c0c043c00300c000301c0d5251140404a940962000e075044c000d0744900c0000c81c107000c0c603154090110340408030031703400b0305405421502c60f8500c82c0007505620040c8615031500d4240070043c0100052400c503200f0003442c03103500a011494000300c00d40e00d40c0e94241e0300040c040d81609613103200c400926614840f034203241c54000d820300700c1d06903550100545030f50000c40210041c9505a01400070208030350155980e0501076a81031240108442d00011060a003500d090391060414000c020486000e000d99050400645507035518030b48070010140d00342800200a0340003884c0d2015507115460034403001803410400c03020343d1044c617441a80da81055510090650b11035400800410078411140400140c00c2c0240c0103074070811980c001b559054510001d030143c400c010403140300c89900c0a0351511000701d40700903c803161003410208580742e43d40c103003c2c41d2244c51405c0a43d07060007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 962832284 1250 962831034 962831039
    0x90403031506030b370618050109060504090507030633050f16080c0d0512010609030b0a020304030e04020c032503080c07170f0315011418130f090b130c 67
    0x10490302c40301a40c0d401141903041720281d41e4580032104010742c049400a014000380c4c0031841400c81819016003c01e2800545141c20110b028009120b00e2040544827544c2c1e600003000700344690712000160103051400104440391b907209140d003103002040c0b0b40030000c6110101200501170400c80310b026020000c4541482192003407034030244401e4909039400501000684204002480803400d80a44e68845c1901c800c40104500700184e41600701c81c081c482120820f0012031014074016030b220600c001d001d82d40ba40c0764601114203404405590b43c0160000c01e00214007040400075020a1003040c0c001c070744203062403244c490907011814000d00403070b02e2000443c0328606800000c054640c0602e0103100d4001000d850322400d035110100e409040140031003402500901d04000c501038480c00d281940d040042400d00124900c150910000d00103000c05055103103450ba155045d40c0041d0200d4200400a0b1901c021006002456000c44d400070036170001071410611039803000c40340c680011600607540e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 962833534 1250 962832284 962832319
    0x10509060f060d03021f0e0f030a050f180301060801020306150306130e0a1a061c150510030b0c0307090503070b030402010f03020d0c0e0306010b04050f130b090403031506030b 77
    0x803003c60042e030860040000540454000c0e0300b40e00001707110034034000303840b10600c032001e41032074079441c40b00081d50003c001d204010303070380001510784004407446100e03503510a811100c01c4041d20b030f0003103170381550a046c00015009010760203540b29000640760b40040d24030105110141d480203c0c0c9940e480b200100480e04504000d0b03001d140c40e0301280084490070b1606403562036411500d161504155545030b0700704280790a02c6141d0300d40c65290108481d2a01d01240e488403110ba105004060925540c0c03000611602841e80a1030b00441e000b44a180e00d5041120501c1400c1d40101c07000b10206418004c0081c2500b000030b1104103c40c0d1040e00c090454071036500444003400c4c50024101019024408000c013514a4808c920300e83d415919145040d00028090605040b8140e101e200403e2080c842001181c507010503408288500702c6084402400c00101c2000034011075501030b400210762420401010f0b0158065110301411950300310100b84c0d41c44084082e518010343c460b030041d03e480904103012303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 962834784 1250 962833534 962833549
    0x102120412050703150c0f080c07062c030c071406030114011707020a0204050c03060a0506030a0207080f181f110f03190318050604080f0c01090f05010509060f06 71
    0x7600c14800d035a0499a00e84407807007002d000b000d10300350ba280d45098a440d4146c00c4a00741d400c9404500b0956203910b08242207030014010404040c041d40e807240501c501d008910303085030501008815400f51614992007056989030018105500244194000400c2ca0001c2031010341000e203004024624507070820008030b04094102120078107120501c2c10080440d000c1d58206403058203a603006105403442c80c010031003070322400780500c5030640080080c044192103201034a01521000d0320700c00d0b607035212416058000e11400a010b44101004103040c0034a051000007000040b502e640701441c81c6940104000201d4002d8140200820205508018440c045c1e0003c25600354504203491405581c0d00d030b65400c43e407005107405042000c0584030034019815110b5440f00b0700f0012070b00b08011a0a6031135a03542c2d1405080070744a8440070524032001c002803001c4600c00c4031400002e01c644007803881d00c603001d1000400121125424100001c0c031501c1c00081c001d2103007000e50100c020949030074040c444507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 962836034 1250 962834784 962834819
    0xf0c0c07030203030d0e0d0309050c011d0405180d140909190603060606030f0e0304050d0c1e0512030a020a06110f0423060c0d050d090210020d080601021204 69
    0x85000301000000560b0302030000d03040c00310751500041084401c5040d0641407240440c104024140780101440124100003400801400c0a00f0003006c60640d05d442e0740e0320740301480030159010303052000f0800c49042e01c6000c07000f101100c408681944124110580c0e40c0740130a080041c481405001240080c60400f080300c0d00310005020700100000c0d09599407013954020b40041c1d442c683c84030010044d0961511609680304a41c60040019080707496a40c0d880e80314611410388203480000f410414001300d241d8050051404416043c01201c01d04004ad190b440700d4498a8814004a4680004448080125100f00a069000c1c012030219a5038020090000b03000b10f0041840c10f000282ca82da038002e005002030442c03041641120b0680090f00502d608058007068000da0050102507814100091507240e58051420a60f4490700f81e400c08900410308820080d600040c80c84a55001d2600846c00d07288041581e03450710080e03681e040c0160390301c0c0301c1040e00f00b40f011010001003200c2455800061007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 962837284 1250 962836034 962836057
    0x30303190b01050906071424010504090201030b0612010905100617091e03190504030c03061806090b0405060907080c0112061a040602060f060a330e040506090f0c 71
    0x401039540c0102d05942c0007a40c0c211030180308070f020781221040c204100d02c80013410b0323136181e007080402c400d19014000c01071091501603521140030030304680c000e411442e40400060006500c1d07012100014802d9003084c440c00b8091460100490790305140c801e007413015110646c85100d580701c14a40c1080021000500c21f04e80d07400341862600155030003814580000c900702008540780e420411111400c031380680b1103c401e01004100800028114110140840703802910001342e02c10241c00401c001c51050b4001070219113085208800c2000100155029502400c101d49941d652010010340e100480e008480095021b03648445ca650720490000640810902c0e01048445d80c0350032170022803480305060301244401042c10f00c4559410844503500042c1501503c2d42410701001145650003203004424444c140e0f07038008810000303924080388e1400c11502d00c100e200501701c50000d29901a046005110300e041001040e01c034504240881c0c000c082540c3c5500d403030744801d54440125806140c0121303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 962838534 1250 962837284 962837287
    0x70f17060d03020109060e0708060a150e0702031e0a27170106031b1d060d1104020903100e011a090a020c070305030708070303060e040309050f0406050415090b030303190b0105 77
    0x50008241c0c2c001c0b9a00c0503004030003001c4150501c9c611a0400c81c2c001d100710f00306440c290340712050948507400e2004588400e11202c07001d480d10a02242144600d6103840040c07840c0c00103090101030120014208855036030748a403202c06491120001003800900c0180c10040300000a1000740d10500c8907001130312440c400060480d640344d4494403d1382c40b4140d840d1002030f048004202e402401d1010034810641185100414078041c2c0001d10044420705000c0d100d00000c0044180c01c0e10349034125009040014121004003402403205001703401601813264455082c0000c032001e1020408400c2c4600c41b00820300485681e0300100c3d000250002e05503c10030b4401c1090010100e00e040c001000301d00d0165105690320100c0b41806820b4071440d0344078080001c41d940402001c29070004c40e2034282c1d0000c541501001103041c0000d4098480751f00000e620518141149042c5140d58601a04a900908050001d030300c0d01d504040e00d90000701c442001464180076503445140099016103168041410b015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 962839784 1250 962838534 962838551
    0x100f0602010b090601140c1608300d060e0a0b040c03020a0806061e030411030715020a06110f1305041407050f070611030c07050c030303010b0703030e2103070f17060d030201 76
    0x21494440c007401480c07400008caa205008400060010140700d0080140c0804240b02803641482c2d07600c0803181e011041500490280d1203405543c1201000f014031400c0d01c0c88030f0500a0520008003010180e16106602e01000201500d00a0080d6025401d007911112403a50312501800704603400101a042601441120a200310b4450409140194020513030110554001c40c14545020201e40190b00111030a41d01c203440194001840071015a0026000c1007da002c10b40c940924058019840104000460701c0c01043c0c5203464000100d0700d044406101001034810488074440703080d070314030380011010494840c40380b4aaa0041c00210310071000011841016503200c00180c10a450b0601603000004000c818880c04010048000408030060b42c90740d454210085650311035100c00805040d12007256003100b84040c0000c40600301c00000e101410b214460f02199a60b208680c2480440c1d4245000250944192822403c0f035a100014076900d88440040000050985800324110364071640c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 962841034 1250 962839784 962839807
    0x30f040f0f08032811070b130b0a0c0f1403044104270c03050d0804020a1404020d0e0c0f04090804030b10080303100f0602010b09060114 60
    0x8100400310124260400d03400c001c000a07200000b82d02c80e11541c0e0080c4514038410216900e6000499840066050140002078007601d149100003d002007038003403c1da002800381c40010043c61600008141e40c2c01258660140340100c0c0100b4005c0c20000d0841d20304100050080d05000c81d0305809074400c09a624441300f0300d1455a403040d00050454040c85e0ba1195003240408440318050804c010340481c0c33903261210207900c9450952440d8408d0b500c881021084c58100d0040e000005c041d1050b0102039209070900f0450360407103210488440c03140604100d20a4803034003416010b540c1c02402080707018075000030a50801003000d90207034070950030425008c1c0001c4034410b4031402e0384c1e41409450311540c8281041541e0003e50700031030159007813180b10740004106100310740a80c1e5100c8481c0c180e5480b81c608008000e24141c02c40b440520002041c0007880c5100024001203c0c00c001e001c60780d181d01c4110407400e849010a43e179800c0815040424025802650b04a403c001d000c6c10721420440410f12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 962842284 1250 962841034 962841037
    0xf0d1205211906080303060306060f0a03020301020d021b0a050d0305041401050703090605090705150f0f030915010f15270311030606010507020d0f0201170f090d140d0905030f 77
    0x108480d0300e440704a0440b040e0565405082c008003500806035096260410210313071108001405103104131594020305081d60b4840000340091a009402191034540c050702410080d8007884039000c2c9842c02c100c0e4060140c80c00590103040d291300c44058003482c102c1314002e40280c03201600841c1c1e441400c0c05080b2941c0824416180306101c40d590106000c00c0c02d091040845501418011058210304000e200540b201045011041800880a039861189000d440058011403203c21340800c400030910035000e2001170100e0070103004103e64036040c6d990700034840b81e64100380300340034106042c094500284c9000d590f4816090804003154031210400340d402803416410b940007210100034092410342e06041c00c0020a60210b02800e05900d0040c1c40d0300012031610300007800600b07292082c0942d80031a4800c058050403d40c030583d4a844034244903111580c1080304440400952040d0b03440003a686100d01060440100c0741d01d4110702c0c3c8070000d140c0c0b4000e8004102d00703880754413041114400c103021590 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 962843534 1250 962842284 962842291
    0x90115020d030b03071d0f090607020a030c05011112091c140315060406090e09070b1c0908190201200d0902061303080c07080d05040b16120e0f0d120521 67
    0xd4160842d141107d041c11a481020b8080303402a4041c804114400350001101c82d4103981509080204910601e007c501510f001405003c25031070201e9041210b02070070090342d0240c2c01141c10749010084d01c40c05d4400000c50301c0000780000e0000a003041d14480d00708000e50300080b4540382e246a1004c10400700701181e00661202c000501807410400000b410f01c2201a086407100010f0301290f8039080c8040c890740a02403d002d840c014a40d60907041c042c007a0300511509901144039515440c0003800081600800508103015500382625004141800c0b540c40f0564911003010a051030040c03c1100f0040104050480c2c02c40341c01c0000d015124080420a401148942011540c8042000406080400325440200301d54441210351846c1038015084c1e6055821203001035407202c0840c842a00144a00c03007015050083c0c80c89011040ca41c030107160102c2503800d0715501181d4a0510603c0741003000854054000c00c41e103030340070451900c18001020490f41c646800241e0280d00050900010b03404d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 962844784 1250 962843534 962843579
    0x30c030a0b071b0f0308090f190c0b031317091201150f030b041235011a0301030b07020c0a230a03081204051c0203040302090115020d030b0307 63
    0x7010810b0265005005800d151005183da00d003865a9989034400c40741c1124001381840008400038814850800c6007a2008041c00220380b004026007103c06821190007105613030302c010010010070103c54071411207001e211408448140d405141e01c0d00803207a074007188140f14040e802c01c01c080c0703a039079200042c0354041c400d1030000507a645443e5044a58802c242e2059000245e140010000b01d440c41d61a140d0141c1c0010b14400c4c01c5d8a000740071112968101401440c2d0f03c2d000322401c030101c40b403022a40500c18080f4440d03040b0b9032240301e040011100800000f480354020401030000aa05410f642d030010f48038011101d42010490001f5006121500a44000d51528218501c480c008200c2001a60320954018620030704603116600c0d43d2003200d03840840c030428107002c43c042020800000c0702c61009241e94400a04a40400035100e6110b07210036886800740e00004506c1c006d50058400420300c042d00100540c1d051a481a030140051400060f414050000b00041174102903000905d051200d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 962846034 1250 962844784 962844803
    0xe070308040e070314070e030c06070605070906090b041a040e010b070308060d110f031c050c0123011a040b0415030c090806010611030408100c0909020c0606060306030c030a 76
    0x1020b04078484001d00400b80c8003090706084c82c00807041c0c8040c042d560004224680703521142d6010700420b2601760203048103600814002440028406150321a9004203035170345d110900c65541e0401210103c00ba070107480c5240c0420081000303205000c1d40b50329014084d500c1e0700c50038155034003000b070b4039144268000c0642030000075a04041550081c04554001d40440b04031480e02e40c540c4500100b9022011a03501a500240400c480c45d9801c0114040c0c56003001301850301110131400c010056001400d100c007140d0701741904c00105285000c15a45c1444000051a225078600350074003048040410b8030307826040d81048041004030882d801400030308030501281341a0003248000078200c81d441c40e101801c101d20418240b00c4240c011840d10b04545007841c00c000103203440d04c00c031821132007280d02203903443c807405404448001258200038426009a1103a0500726962800e4100341c0c400c0c51041c81040c1c00160008000f403410300c009c0c0d50805006021140c0703041e14030011910f08400d106003038804070300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 962847284 1250 962846034 962846039
    0x3060105360a0b070c050f030a050a061a01022103060a081005041709030705122a100206010f0519171015122306010e241f02010e07030804 61
    0x14912070b5040203111606959240c503130a511994900701044c001c25108084800900e40076540800503284600d410600b039422080302844c02e0401018021448440c100c102c480e00d07a410748c00841c40466242103824580b05010b08a12402c41d50f602c018000c581c810454880452003280c01c000078601544060000602c604081c1000d00305400b076020070003c11441000300741c13020340f03010032000100c0d034042d80e018143da0b00345881d86052030800c2d451603420868010001044d1800c0220020b00481d040d1010b90540004110480e1101024000d04400d4100100f040000d4101800c854a40c0030a418000c441952a440d2442441c900d6140201c0300703074041c01200510210500c01d0251440c02e075404504403615044c1203c9440c803e074400903000a0301c0c914280003a028552210a4840100301590100d41e11510b22100e5000c050710105150b144210310500e00410040fa509003402000781100807566001e4400c056040018100900719500c81e20341c010345040800401d0041c620036102581c4450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 962848534 1250 962847284 962847289
    0x804091406060c1905031c0f050f040c0e06060d020309031909050d0303051e090f01050903040509011202041b090503160b121f0303110c040e030306010536 68
    0x80c0203000c45110700e00c1001042540721000520080d5004028800f04911140741001800c5010b0b810074a2840b00d000440c842001c2500c1c0e021103030400300000d0070020340c0c071240200302010700204c0307000b001e0b20300c04081130000d8012140c045500120045c4081e14000910400e10143c2e0030545512a40d0780c03000c541008401c401403000900742d0007610300720b4112417600c0001084054000005814145c0c0e803000b10320340101441e0341c4d41010041105801d00c60038140c00c00e60f0346d007105200460789035180202140045402008890465400808500c1923908126980e45032101e4400d080307900c296115256140b2a19104603100081804e48030390a00c180f9000a05040030f07038810022110551202041c807151420744162070040486003a0f480596680603400050306480d009940100910810300104050b40002c08000d01402038054490b9402c010040c003040c0e60044070b043d54075400903c0060491351068004d032040c0c501e141c44c80788009038407147d5106c0015000840ca540341007416659607450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 962849784 1250 962848534 962848571
    0x26030105180402060d0c020a12020d08150d15020909040c140303070c06050a110102030a0c030f050709030312243f08040305010c1e020304120807020d080409 69
    0x40155070841070042c41d00b54005200c910600385030841007503503040903089140c0b080240c1e1480c1a03020041c0c140168664402070343d81d90302d04000400041e0354400140d0305014204100c07480e010082d0641a40004540d40c00c02500404030074020fa0070b60901c9104004d0303071004400b9001710b0217015a10505070800700443c00c181e28010095001e43d208000343d0f000600c40f11040c000f1140d80e440c019031502400c0c0381c21181e84100c8400551250300100c00d00000c0009503100e40414100d07500e040190f038180c401100e06441c011114800403a40c455000c0001c280100307441c0e0f6110002c50400a8076150091a032a481c4424200075401d10315050b10510040d20b11211901000c4001c12030f0881100d40c280d055410161844240006107a004003501304028043d070680d0040c43d4000000e01c0288031a047c000c20384000030540d43c610120414504401c140084101c07001c1c3d0300030001642c250380c02902e91140c0d9600026040f078200b0780448800010440e84030107403020b000c04c0b010120b014482c500b40f8a451 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 962851034 1250 962849784 962849809
    0xf0509061509220c0608070201180b07271205100b03060103120c060c030b03070905060f120a0c0b0d05100e04020d05070b0415120b0f0d26030105 64
    0x4800194840c41a65900e0760455210100e0440302d0315443c91000c0b2000d003500c0010004002559820303000ca960380e0042507542c82444982d0003044403a800404840700308480700c030017070f21154401d07010a428034810303049201c1d001d1201c1d80c60124504007a030b080950109643c44501c450b15294201000c108040c00310001c0990a00c80501004260304002502e44006100c020604c42104540c0c00440b40141c2404010b242c0080c020001c04141034406000f40030031400091007402150340100d950754072446414000e0501402d404525040202846102c8000610712000352040750700400004010051040c0903001c010b544580707500352100d0f80010b98401402d0003528401c3c0b82818008012040e0f5681d51282e012a004084904242030003810070b451740d042161101c00003e004180d0489010381e5a840710316694901100f851411035042c105c0e1800310b2516400001e90329405140e1501303001184449020b0790000c101c481c0c00160f0108500c1400458001c607501c0400100124589402c0c0d013002d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 962852284 1250 962851034 962851051
    0x1517030a08100b04172406090f0705041a0c0604121101091205070201030b1f1d100f2703020a0504090f140109141b010c050706050a0c060f050906 64
    0x10560a02120f404036000741d00400c4a11136a401d01e100100d0410010015900f40003017841500030303801c98042200c80340884015010340c00100129907045100c4a030b80740f1407055a9189400c1c54140003904203c0e1001080781009100f05105865400c5405d0041a004522498a03079040f04900c0401910404010f5622025a450140c0d101c0c04600c0d11030078070211485501c0c1050740d400c0741303200680c020503030084180e41090000007103030040301c45030200c0060012b441e01c2c0d03104c0c010313540c03100c1c95040038179400c0e102c1c4c20450611081c1580b601a1154140341491414000a42c9118003085090100803803080841d1801001081040d41400240f01c0c020f008182c40038006e15003a9181c00e69216810b030001081c0151840191405540c00c0d440003451503880305410400641d041403283d81d5044066440c0390b4000240c58420556020350002084c2aa00c20b002c0c15980d8a00350095031103405ca160180240172662181c40f000030380c0d6208440001e07503140f00004407814030a915600e4810010300750700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 962853534 1250 962852284 962852311
    0x8030f070e1008060607020112020c010b041805150406020f0a09051c0b06010c051f02030f090703050715021f0905010c0f05070f0204020f03070804050609030702131517030a08 77
    0x2c01560700c11160f07644184241d4526030f40da903e07840122071500e6543c031821940b910100d01501c2e00c020640220140035401c80e41449400c00540d50911206c00002000300a0f90181102240f428441907409601900800f80141808564003820990f0f07403188004c500090081d2000f40445d20303149901d2403003204e80160f81c920402c0e071341e5141d8120035006000076051141c0411140104001006003030841d030429160750429480852115010750030a440318048042c080001492103400001c4134811650040b008040b210710b006012490f0740c013003500310f804501807203181102000c43c00340c07107203d0301c2d0401000040305449824080e08645480c0300351000c21201c03084d01141143c0c48410b4030712060300001080c03084440c61000a00034452038a04004803100401000708040d0480140741c440d0380941e060351020b5452254171a00ea10400c10000d42c80b20f014a41001d108500768004001c07000c124144101030358031800c00550f81c00c0e4040c03520100364000120f2a55850b0301604c4146c0041800600c0c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 962854784 1250 962853534 962853559
    0x20d06240f060807030207020a0f180e010c020a030c150c0e0907170109150806070c050d03050c161b180624082d0f010806130b1308030f070e 62
    0x1400340c1c03c0600181304068011409509664510b4000d00050402c5c0c0d0540c0345544c0c0e03604425a5900d00c01220440f4035180140160321404103000342400d04015030301030304c41f0600c0c3c3e56065441200040081d0342590354407030f20701c041e10490300c2980a42545900da22520f08044010070010610080c100c008001185a041c4c080503015090181514441d0001041c10980701d541e0f0000301c0c5d410340c8800041d205503400e1081d01604000a0101c960049040d034694001104082d003d64401341c51003c0003403030030000c6600107501446079003c03451040c1002c000301fa400d158482c2e513581442e081402e01580300100034401c0c0d000e5100c1d0304010100da0652200e41101d07042920b05040c54000310070184080400040e10300c403008180d00e400f082c00070005040d07480c9c203c00182c7c02d44104541c12104095250000300d059000002d000f88103800320b482c2182d000e00207986541c10800c000d0301940460030b001c00f410000030801c0024600c5001014414803132480e200a000300074004280159001d6401140c94 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 962856034 1250 962854784 962854787
    0x201060312031b12020c12040510180303031a0619030509121b010213180c0c11191a030a060e04120e1c03170c13050904020d06240f06 59
    0x2004044800350428101d100710300c4072080080d1142c25886d0186000d41902c0240c45020305014000355031003038500d03500c0e103039900000399181d80251094a5040b42201030800001c0d00c80d820403610f0003003e1500c0c002180d81e5401190980d0040c10a50440102103184c0b440d0481d4544a8079900600c0c8030020821a4a01d2168004910450b030700c0750100c0031200f400301c5101600f50101c892003207008a041a007281d5074556501c0307415140200f041c107039041180403c4c0c080e100c0d50039048016009018404103e000608010390411b4000300e1070303402c040c0c11200040603540c01100c182a0704128200640c0ea1400742c2c41d8201b210709940050707400c100c4030743c280030116040908220070741499050851250501d403001901544452500f003c40700390b410f004c03004055004021f10030481680780402c6442d22411040b00050040002c030f000020140340c000c000f50b02e40507804682040c00039000c2c8440603040d0f1103c1c001d4564060320ad010b901520100c4132200f083c411820070091440011690055050240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 962857284 1250 962856034 962856071
    0x309102708130302030f06091506011d0a03021302040f05041407050d090506011205210a12140103060501050a0b030c030403030b1305090d020d02010e0c010825020106031203 76
    0x102422000340420040442d107800742085001c2c540041c1103c510541c0303180c8481c0d845100311400600b034050021b2092848291032a141e01954050311019400e0582c04241107250001c2098160b000700399070800005a00c1e80c001c10306420070780c0e04000d80d95a0801040410784030055028038000d500e8280840b0340f0080550314150000c0851808540e200d0b02c1504101c09800c1840001c3c00501820000040444040c07106030300c0300384180305640c8105082034001035200c5890303000e05c244031810490084828410700450f09448a405000641d01000304103030384040ea0309070421200543d42e04018051880e0940d0700d8001040c80000d00341c40d5203801000c121130f40c040a00010700707050300c95208021030358a2218003c0c044d00815402c00561070304081081c0d0b11600e03448284c000d4020840404074651043c05003c01d1120300780014410180c503440116a180780060540942e00d29100389100c02c0a1550509009046640d00109087d0b0a50500300307440c02c4c0c10400b18050600d02181d02495400480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 962858534 1250 962857284 962857361
    0x21090f091b070f060e0607030f0e060402040e160f030b220f0204020412051c020304051f05040305101505090f13020105130f08070b03010315020c0c06030910 69
    0x980d102d440c41c0c81c1c041018080c1c1e003001002d441c2098501d2100200006041e4030400450364103014880d00504008200c505942055035140c0006c2e00140c09810203420055000b900d0108460600380c03003103543e22032802150800c00070004990304c104240682280305a03040560445803a0b41c80200b2104c8a8140ca140c03440202501c40b0f03001c0b800c00799920b035415075008100d03112140407550f143d03182054442c015050004140803021030b0304a5914400019a03040e10702c05046c0c1c01407c4811444104140001510b1004201013040301100080080c04019104440b04402061614803410011800d44085c0c000d41c0c010b80f0304104102e040c1d01d52011141d0808859140700c00b41c558140012a82c611038101c0703002c02006d40110018500c0000100c84013180ea50380107a400d016210b444043d40c1e48001e01c0042d00c410030710b69410000b003007541d0050121081c2c11040341c1c10007404c107010848641044030407020580181040c0c54504425000b041d803e010301c0b18100d0040300c038005035007602c4490764 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 962859784 1250 962858534 962858581
    0x70c0c2c010605040f1e03021503040b09060105060703030506041b02030c010608011803120920030c040207050c0114040e0420010e0102100b06040810020a14180105030921090f09 78
    0x31b0706242c40d8200310b03080c08805150083c140c10120718054170700340503c0d401500c0464a40901030b00143d00940301107100c41c180c502c002d0441346041d042c2d0b01c3c12000f42070040d0246900980c0e48152001070700c0c840c80c3d1345c60100c815402454440041070312540c00c407001540002440d0f410865642c004800030600c11041b641d043c00c11104407095800c03610000c020200d00204034031100c2c1012054404c69021034442c0b103000300c08540901c42082c0600050707004e6030000400650050804048541c01102d4083c0264100b900701c03401d0682c0c840009080305429141660708840310480c003088170440c440b101c1e1210710300f820301c00c00d1640f14100003542c03451007920114100e41e0f1407808041c2983d50a084800800c0d20108480e0041c404000080c029440714034080041a442d803461480018190141c81002c05501c1c861915900e1403401510554001402080940941c080c7c1004450f6003c00d0010f00120703c0b41c0c001e480e070076003000b4030444d03140c002c8405220b003a44000304020903004100c00e140a4549 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 962861034 1250 962859784 962859809
    0x51f0902060702061c360b1612050a0f0e1f020f0d020705060105030c0a0b121302031c09090207050309040908070206030910050604060e070c0c2c010605040f 69
    0x1d044516100c090117540103d00d050401c9510135500900712989103002d101140c0c80e19850303082c40c3c0070000b5059800c2e0000c0c0400e88001c0052046802c12558101c900744c0360a010082d94554440d0070115a011034a10b050b0554800002008900e640710701102100e98000030840384003203001c0502e480561880141d007641d0000b07610b0080e120900f0a80b20b00e08102902951225490b2500715140c10090240f40d000c1e1181129842c8103290160103082121840000d603485d1150307060071071042d0000188000c0a100e42d4220007801a141046a440702e00e1462218a6071507199880060040c0e4699000f01d1549005001c01404100080115140d800041f9000199480701c1d18100c5985c0c0900d5101940c0b000c40881042100321000c41c0c02200558903420811490307482c802088111049801981100d048010005050b14050103555161b58041c8410408071582c403604060b0b00e040b840c94121868521845400c0124107841200f1301600607410043e003003505140030b00007d540c4031311403001040107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 962862284 1250 962861034 962861047
    0x80a30020a14011b0207180203041e02060f040305010f0606111b0a03021f0305060619031e050702070305010b04090b07050a050c0706050a020c041a010e1804051f090206070206 77
    0x1002d41c401c6011302c0c440c10f655101d46501c144042c3d12004a442040003452020301142c1c1c401c0c10314400c41c0d100d160f1058500340342c00c20303e8008a0ba03841012108907081b4804005401140c40d00501070001144150008601d80090b00f0001701580c075650311410901c550020540e201d4000401e0b0751b059910311803110850342945800007140001a540040d400c08000c10040d0b240742201d080c50180920756403402d110684800092000510500d56040c00c400a00d072035801d5103a10030340041400040c14034a0340380b0303004200034100c1182d81c00d50700303240903a001100130003c0203403c8c00b51702c0940034100d60130030a4000da61542d0401e0705004020900b04040010403258103400746013500c0c5988502011a106581c40b02409042c6500c8201102d0141c41480242802454240601c1c1c903920b0070160030142984609006440543c104001998081202c42c2d01140c11003003010044d10541c0140000c0003140103038100c04141a202c0071030200c0e8035003807040c1c802c096150030f4102c51a059040c1d450300e036103d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 962863534 1250 962862284 962862323
    0x513020901120e030309122a0a021002100b01050306100e03030f030a230702100203070504050d06060323030403020f0d120906090b04050f1009080a30020a 68
    0x211402d81090034503c2c0404503296000004090751040351040d0864003051781c4143d04454078026000c443caa60705050b42054000080e1061040103d88103604484100500d58001083c0c0b1581c11092801a4401d452050040460313005004644c0d00a0038154651b04045000c40e0030108400c140b0302c2408480310740315885803410000c41e508440114410368603070811183c0c0401400007050072225407100317486012003030b0903280c4405000b11010b07001428508a4502d098001e508010580010300000740000555901d59100b2441ca5a108420003d100d5040d8503140c10b0b4100d42c0d043d030f0001d51142c0c02c601180c82d4070002c04ca0301030701d404a940c4044241c02c1c42c0001d1140c040750100404003a07100c90400070682c0c016031143c0503079905403900e540030741d00e41e0200700345400f5a21846a0240d81580b100d112030501d08540040c4581915010300ca5580780c4168500d05030030720f00204d603403080000f08183c1c950341c9500c11000003209060302000c90240e43c0c0c00290b80b80724a20300949440c1c404e01c3c20f2000038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 962864784 1250 962863534 962863547
    0x608030d090f1509052a010e03030c07080303061f0f080406061a0a120b0109140409120207031709210109020306010b0703030b030a0209040f03090515041e0513020901 73
    0x155011442c07500c030150b2414160701404e07038071034211014402c1c100c1d08025004500180d82200c1c100303444450741c80312000011921507090552964040c04100103032041030106021076030150a03018010b641c0d0b0704050013849250400c403100007041340d003e1180b041312213521042510104a007881c10484649a0342041c20050010754802c40309a810ba0280501c0d40b5100006480117080c00c6d00c07110904a40c0900b410240e13040f400c030241c001025060280074408030500d810307040070005440014461002c1d40c1c0d45010041c0100c0c0c3d840941d1008104004020444040111080c000750180f401e01d1000700101d0960580c5040c480c180702c5080d951001e00300c00035840200016001421516656503821000009510888042d40080e0070b1111560250800241040c034155000d80a4a465520764942541c00702c0101021000c03c1110f04001440d580d40d034011241c00f00b043e100b041c1d46c2d036180c071410070011010070b5012501d03402c12800801981d03907041d0b4611100c08074410050b88d1516a980129101d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 962866034 1250 962864784 962864813
    0x4240e060f0a030b090c0d12020c0f0306070f11010612020a0b0a050307080718062102120103060c110604030f2604020411040b07060b090912030a023015040608030d09 73
    0x1074542c4a03880c040c462141490b0580112540a0700d02581c111018840c40c42c542f04100b0f6003503400000407548507803194811014100c0c1d00d10b881d00c004038a030040907007550020b51024070442c1c0c400300c0402c190301c0e00130400002450504c1510b807410360f01480182c181d0000910001c140010940040d81160103003141d2620102d2045582001d00d890b290b000c0c0c40c10b034000c803800c10b0092158440c00c600070328510840f4800443c403424005281c1c6035a03500800b034152003d95104000004148540c505d03000c10080740128400c0d207071000305961002004041482203140030b80030b602c3c452103261681c44018941038210360107507400309070001c60780b0f03030264035106541c824400e40400066410a100c601c5c0e0041200c0c2004030781c0700c1442c0c2c9480000503a6a2481e212620503800100042140410355074010f05203200901f10400c1d0340c400750709980c1861610302c25801501c2c1d00300c500700701000f0810003071215a014100d07070420580e420000482c1e642d00540a6050120740e0f1000000c00740000707505078145 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 962867284 1250 962866034 962866039
    0x1011011e050a09020f1302070c2907120e06040b121803090a1e0902071b17030f07062a0306050d020906040203040204240e060f0a030b090c 61
    0x4540400028045140c00114414114504408205200307118010072104540041039134203601201800c210106c0c16400c50700c178013030f5400c000107400581d0440b0200014503822070103d40705980441040c2e80c070701340c1a0755413035003200030400d140c0014a2410040001c00442c50040050f62071b44002c07039900d10864220760615030740880d0100c088031520040c00d200301320102c2014120a6412480c0340e072800344038283d560050043c00c06001220214034941140e200a095107040c01c1e640f02400403c030f900c0448181c82c4007411510140f2542c41c101400c0e001010f20383d084035902800300c100c040d02e0b03001d8820310f16540030001900e5014422030790070401f6081c980200241554a540c821041c007150340c01080700110382403040004140c0f41c444030081c11590003501d01025036454034100700007940003c004a07031040c1e5800400c55484040102501803c01c01445000114200900d4050155008090a1240b401040300c807005444124200013280c1d40501c4440e50798460b120030750305280304000e0094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 962868534 1250 962867284 962867291
    0x90b03010e190e0f19111324030b0f0c09040c03240512010b010c0f0302010905100209120703020d020616050609011a040504210309080313020901061b02101101 70
    0xf5508089029180d03910340c002140c05402c1d444400c508142c5c05000c0107800d01d0350106000026040112102d15a03000e084400240d4945100210186420742004282c0200b1041c4090040051301004d094002c194901a20340c2494170021401d554820035922a025546880c81c0c00c0074a030090700b0440e42c684450400005200d0380311006040f05c1041d20520740304103800c1fa00d03030744810010701c2070208820060b0740340d50b004001c03034940e1001d90482c2c180131011590303680103807004150144071001880c0d01daa080580d03902150001c00c0520f1040501e205025001001c0810040c0d8600102802d0a40c2c180c0d0710a4071625441c808180748000038002800c0c038001c00040241400041d4842401800c40d0455881810344803020300040300c83c04c580040c0780c1c108200b0365a007076484c0c03140d0315001c100552601150040c1c43c2d42d40c210340350300292600500f07a03a41030325101c110703e411003401d40076254502e00065402c80c15400c801e0410070303042000c0d000d55003100300a0540b902c01c91580c500d14007100000d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 962869784 1250 962868534 962868551
    0x40213060f120605160912020a0b03090705011404061d061c020a0207120f03080a0e011a0a270e070302150702030f032d21090706090b03010e19 63
    0x30340c600701c10b091045a4491801001640054000038032014100060f03990480e194100b8581d0402004100c101b80d134440030714940000c0c984150802984100c00d43c40280c4042c1e8a00710004d803540c3d01200c071200d50081d0600c418003410b0b80c000e00282500c00801074600c415030340319001c55428400e050b92100c1c244181c014031200114203400429010320642d00301c903401030b0b60b10350410020b408008020070101da8501d0880c0031034400c0c3c00031500a100e034880052614a82a112401c4444406006040100d140d10020386890302c0181e0500401c9040c2d03c01d80104001c1d000c04140c4406a44e0780c42e07103076079100107505032507100b003151a000c1c0d036015100000c008201c2400110603042039000b00d101c3c0c0704400b2212010b040101c240c3d20718040748850500b14660030f82d0940c08a8641000d0b20742c102030240841821003031460036030b004502d25040300c0e0350641048081d050805907075400000901c0030005041102803580402c07281150302c40d00b0f044100e41c54210700341d2001c4414a030007481d00d42c00c14149 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 962871034 1250 962869784 962869799
    0x9030f31030b060a0e0708040606080f0a0303110309070b0d0b040501090905010b0f100c02031c0c0c0b09240d151805060901092007061a0f0306040213060f 68
    0x954281d0740220b081103a180d6400007004500310742c0c3e02880b82d94a4008011680c018082c0b40a9600244201e4000c6200c0d610b5079283c2d40342c0703000d2802c400104c0c1d01503c442740903d82c052080240e0540940318451841c42c000ea0340b1a0381d40300382d111b030160f03048000401d00400107140c4c1c130440d940d180c014414880d5503550060320024011034035040c0d0f2554a890715505540c90b06882181c0070b281e005d811100a414003d0003640c42c00d0100a09a07014040d00341c281604190803008100d1050907501e600c0b034544003a040c00a0b40a000d0f800ca5100b140d41007244010a985013541d128110040049200c003e00802e1859038090241000d08a03e060504030b2040040c400b220414003550409620001e0842010b00d800c030a40301e00b81d03040340d00100003034018030411100e500a803003001541c561012040e42181140000c0b688030440590300150703140a82c50600c46010300350289140126105541e00000304006611010043d00003071180b9150014054910440c1e003000001380014140c0001c241e640702103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 962872284 1250 962871034 962871127
    0xd14120d090c06020a050714041d0123040c1505040506030703140c0708090d06020f030f0702061006050a0e040b0a060804050601050d08030c0f091c110909030f 70
    0x101102e222201240c04242d85100040203100c90390020014500c643c6420780f05245280f808100f1a0400d444001da14103240400e01142411810302000142d40508048032000655400035035a02102c0c2010911001c1220b9204050a481c5440300c85940c0e11000316064546114035400590000341c04410007645a416030701084010055007030110240d80d8000c0c00b800c26206060300284101014402480e580c184481010701c480d2140a005150850007407080030540c00458090841420090402c1030095061204541026100003111292418483e0181c400c0c080c0440d82801c0141940040c00940c2d0349030451640d40b207010b051619255160000106a1001102e0545003441032100004039401e1064005455039003002a0034115182e00385900034a27440031209600a0b0703010b1052607a981d9403e8405280c0725828608132a40c6281d91a021241030803041d41d0900c00c5004604111049001100b01c0340b14010350000c1e00c0c0e8544112b900381078001c9040c80031300320b003540014145150100340ca4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 962873534 1250 962872284 962872301
    0x2030903070227160c03030e011401180608010b010e0d0c0f0801150b0702010207050d0321050105030105090c09162c1c03050a3c110604020d14120d 65
    0x5150f00c009503039034400304c03225402440b40380c40010811261900441d12070380c4080c045400140012440440d000c0515103062000c0e002100303140c04164107040d901e00d861250000a0214400a22040280d040040c051200e481c424500035888980310074104607100b81688003410604404d00c0d000c40c2c940581c83d008040040f01441c0765000700c40042500d0b43c051040e2403200da8140d0040c10881d040c6028804810224a82201070281c0e13200282d400300d2410030030304407200508000045661601041600b1341d4006420765850740c006450f40d80554481c00d510540c4800d480300c2010215101c0b40c021540b030707040341501115000c090340c981000b0040140c524403180d101114000c4080308014090001c3c0b400e0524001c020642c10801111181e001d03e02210100e0769030400c03003030000c4040f0684050040617011000750044003290300700032580c000c80700d06661580b840040ca0103141ca540402d074294001903020309800902c1690f141e40d000c04000f0b01c00342c0241704140f0383c0c450002c1d9100360050305241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 962874784 1250 962873534 962873599
    0x9131a090c010206040c060c08160f0201033207110a0803060103110307020a150219080919020922050a031d01080f07030e03090402220f1503020309030702 68
    0x2041007290720015803103010325007100d80344054a140c100c007915480032909045030580401c0c458a02400700d0090342c40e4407503005210024018546100040481d00002854240040e00d040c2580021418045111250030550510a00e544800707200303540d0981001444880d81c8242e5032400100700550002e18082c10082c1c8052000c40710318002a500b0380030840d060700059020007990404074407140098210041201001481c0c03a00c1e84900d124815040d55001e00802c3c00703036051100c464005c1101c0320050780440c3d000300e40002d0b65400145c1007240548905004c07407424960701000d821114921010a80c0301d0105d946001c054500030701038010b110364140c0042201c02e0315041e95405408220f1191081d041d000340180c1e594003058005161300c4002407158803051141d407519849034802040210150b00c110300004c0303051b400003144140150401e884000030000100000f080b92070844051500038200982c907030351001b02440c518011090081d512640d20010381100368a9407210b807102c000c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 962876034 1250 962874784 962874793
    0x6010e03192f010c03121103040506570c0d17151905040f140109020c03072901090209030d080103200315090d170408040509131a09 58
    0x2041c010840600150782d2035030110b10007904000000b03100e5045405030452400001a520303009014500003600215400c807034030340c022007c1c011122804031620b5492042040780050031000d600b038501640c0d102c0041000109100100d0460140e143d01c54940600380900640307450b043c01144032644d810040c85c081c1c0110301002d5920b0b140545070103000c2e100e00122103150200050388400e01c40f0450444100e4010000c0101021610b0740e624082e0400103801a040072402e840484000302070341c501070b84003080040c4108180811b6607004000c3e43d038402d801c010041e5001014064004c9a511f9403144010030b03910040010030300c060541e0240c1107600c810380c1203034402020700c0030680d414142030101800c511483c01002e01742e01d03110f420f201840403000d400d582007500c5640103444030000a0700c101c0d100b90400c0180006195222015400e80d01100c8014a65404d240c0c6400305513208a018290046040700005804001d010480100440d40402c1c00340d004000c1302c4469041c0300007998103171035038010f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 962877284 1250 962876034 962876093
    0x309060302090603010b030703091b1703031006080c0c0a0b040b06010e0a05040203071b050109031e2a02030d0903030e040207080d0209030a0f03050d0c0807020606010e0319 76
    0xc20320950b141e240010f07020034610790030034262222680008126030300300740d11030001400150b50f10f668070340b5070100c80d08400b10701d81c18060644030601c0082003186941d4020300802004003558109030080300c060f81040c6901d0344421041e41c0c21445500240b0300740b4815178414000700400041820310807400703440750401d1030322244011107003c0502049154850b44411040c4103d150941c0216003120003400c03c0b6401c02a129082c941c0342940c0d0006071601c3e555100640141500715030143c2c007405144641a90701c04140b140a4111041a000d2115098001c1c0e0201082c040c40c211031025281c00804480c21807008000c001c14800c0e460108a00040b800c40d02c5071220b042c24003c1d070741a02c0d4081c00d0b407410501540406070007034210480040d81841500d42180118101c60070512480d4000e40d1003035603c4030022000c900351008414188100441c400c1007000300c03070380440c4843c1c01c81004d18100407004030081c000781c502220a82000c8000c2001d100c0f0f60100615001c052882c0488061400400340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 962878534 1250 962877284 962877287
    0x9010b0108070c110a05040f0b030c01140a080702100204080d0e0a051507060204050d0b01140904020a06050c0a0503040b0c0115030f0b0c04030b07050a02150103021003111204030c030906 82
    0x10309644000200c0d803c81d0700c01001030990320310095031190203010101031590368800a019202403102c036002c01552032071401001c0c103080c0113040040a00b03007000c22180707203801e40e00146445000803000411030384501103201c145c800d01c0001c004c5c1c1088241036403195280c4001c203440e181e2183c1c242c8041003030781030f54014908000e0500801c980e0000c0030701b00c403036026210100065014100490341d0990802011a441c1d44403416107030760601451881d1803a60504409910004489521601c205005400c01005958001001c0e0581c0e00c249411903c811030790356110b14040d02010000c1047c00046004103601180381c01420b11042214028091010050b060f90310b020094000500810a480059001b1541c43c00280d50008504402546010703501e44413a425540c0070390305100000c0000510301c1066504024006201324042240740740c652445d07001840e220031000300e10040c1034489001d0018171501605440d804a6a184030300340514152500070401c1450110480c04903144840214405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 962879784 1250 962878534 962878547
    0x31205090a0b011e1517151011010b0429040608030f0a0504150818010b010e01030b0a080609060604110418020d11070c150c1a0709080f0609010b01 65
    0x840e0414410400e69003842c055491411070494480781e01c0f418070300300091089179000e4007201542a0798629425803031007011117500c07142c0075058606a1381c8903407141c0039560341c406015165544904240c080702c030102420728094996146912307889441d08012035200c00c141858000d403055800300c0024081c903010100012585140075003502940140440786140990744014400c008007410401d04041c0d0365429001184000c00130391000510040500004400080c000f03584041c048009104611130680002c00d41413004d1120750416072100c14800d0152250340c000c2015200000503181286011541180d492301d013a81c100b4050ba1401c80d581221055800980c1c0556203022040381d0901071700c07031982002e50400031015514556508050354025242c070300a0042c6c0b441144100d60300c0345460345004110b103c1a40d1542030105000400c40060b1000c500d4800c8800c0000c00503241e511410b00440d000d01e03140d0801c0101d40320318080c0a4901d040061041d2146280d200240890848600112040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 962881034 1250 962879784 962879803
    0x180a0614120c040b0f09031b0105180406120506091b09191512050d030e0d030e030c03040b120610120507030b04110a0305091b1c0f03120509 62
    0xc400e024403010355a40340e5220210b412820044200d42407640300d800011a40d4000c0709940500365000490800d00d050502c02004c0c148140c500800348220f4400000c3c0140c41030082d11042e0101140a103d040e5640340d00080250444081c2c0c00c2070480986081d969510080d520b94101d4030603ca004140e038104401c4001503000081e26180e81d98031070b4002a071411943c0c09981074116100c42100c02150f181c0000003004082c0310402c00b415041d14245079092580f100755910800d07080029416401500040e294060078582c0740004005a00c0340c038160650280008010060000180003d03c1550f10000b07170000c4020b01444400c9601c4090401003040151501c0c100862041542e5040310031f5079500140d4000400c0c2004148100c5101c0020120340d06130005402d4450045070581c500c582c0b5118266215681c10001c2c403440003000c0a070f002440140d00b070284184010202e6403402340c89000c8081c041d580c0881c1c2042807114616020380007166070500324050502c0c00c0f00281301c10100141c08500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 962882284 1250 962881034 962881067
    0x621150e0a05010b1b010e150f090f030301050d020f06070804050109090506150708120f010f0603050f1302180a050f150f060c0f16030b01080a051009020d0206180a06 73
    0x1510441c040344030308800700345d0401d80341035507600090030b11240b062040c120014145950b2100524000c0c0f100381800c0b20240c501d42d0307140d000c080c00c0e9400904c0002244e0540c0c408403504a030344407140c40080e600c04042c40050350040004905070b0200040030004d8826980e00740c80f0300c12655140c3c41c0d01d00450300c084918583c4052441004404842c0140c01030040c14080c2c1001490180300946002a03540140c50340c101c5200103000402c1a0354420100c0c40151100f85814015410401841c407240d000103440039440a044680510865851224030700707603086104110621450400103901c02400308482000201c41410005614540382143c800410031006003da8421841101071022642000c40105000d2191001140419004001c4171100c41020482604014150714114a034440180e02c950390303552010820200081c800b050000e01c4041111000611201e6800020a0110400310123500804001802c0f031032341c0f640c5000c3d850400401d803a1840d100d40c3e0f4240450310341c803a2101021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 962883534 1250 962882284 962882287
    0x180d080c03040201091d01051302130b0a170a05010302030d08070f03381002010c020a030f170406020a18050a090b0d0b101409060105040621150e0a05010b 68
    0x90a6012240c040c6070020300614008134940e4442e0104c4800d45032810300d000030512000c00404c0185003201c4802c0c0011840e15065092040b001100108507d441c0a03607c40c0020106d05a4601c034812200b1a4001c09912001031150802102290051401b07010980c003038003443c2803040e4a00d0080c0001405007600c1e82c1e9002144e003a82c1000c0740101584015041c1d0004010340050000d43e5560301d02daa402501b043c1d610043c2a95420042c0200c2007403400c07003e690510b07442507002a000300e00030b0309043d00760500d80000f660641c81140da1003000d95000031090010014041886010340c050700048005ea142e0211440400d50084042e01851007441d520082c00c10050200c03403801d8000303074015940034007a40c3c0c3c884400e0307035a2030f01c81104175045031401e9620901080b00040141c241c0e140c81009a0340c010443c200440000e00a204901407942440014906000d00f50b81c01d07007114840c110212402c2000500c0b0602e20115003140e8401c0004c40f10308130002c00c00d4800c05110b064100c581c44225103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 962884784 1250 962883534 962883541
    0x1d0a06031a090106090c03020919030209010b03130203060115120e0304061202041203031b17070c050a020d0c260c09041a0405030a09120c090b121005180d08 69
    0xc0c844074010324001c400c0d500c2d89400943d003102400342544610603a1030158485142034180700b01842c503620140d02d50f02c1d13100c80810141e01c403015114192800c9040700b641e80e030b5494040103118980240c0094151051301e00000303060302d4100018040b140251707500c551030034030100d49800391024036111007550b4004000400036070f40101280d080800140c1809400c255940040b11034140d6203140035004241c940c8403a04502c102c1d042d61440c0e0361040e003840c02e9914000c080160120000402c54018810702c08221028000101b040c101c1c190790041103071010400d54648074001131240d00c140740070300c0b01807078420b4010700745d003e070341c06074600030344001d1244542034000c1200303118010707105941d103045890382814103500f0302801030321481c041c0c0000c60340c07200340b01c4c401481d1140c50b0f44054004407280c08000001981d0f644958101c50000b180850020400f600007144d01c4122540d19816100f420140103442c0580e402c800c1c85500214010008000c403c8011174445042179100d000040d005c1000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 962886034 1250 962884784 962884823
    0x91d060117070305010e06011509030c12060e01021812010c0203031b120718090902090a0e0c120601150c03081b0405060c0309041508121e041d0a0603 66
    0x1500030100c840c0c2142d4038107980391681c2c0d0849421200601d4680c0000c0018003000c07032044003003000c0c44030314074080d4007080c40c60300c66084100f5580210802404c00c8160b890601005d90040e0701c241d0701030030085550b58a603107a07001900359071f1508580100c541003400e800811041c4540480340c0b03115000742d49035543d001203101c084000c4078641204554240100030602c1c040d400218070500e440d4451900d00030a8042c0804c440b241c960294540600381903035400161200d581088c0c00510340000413550110a09607030317060420700300100c1d810500501c1a45400040028541d0413101820b15101c40c1c1ca15001c41120310149108015020030281004200007028602c21041176025a129403804d040c0c5401c00229180d00c00c40c08403c0603840030621003803e160600c41c1080c0902c4000c5c009040c140340c8032006840714480003c0d41c80c0008045002c0d0909101c0c4c0700082ca01314100007407143d481d901d0300032071000d402c900146485407180030000136848024520490069a070001d03a10070302c02440034203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 962887284 1250 962886034 962886059
    0x106240305240f0301020c060c070606090c0c1b03021918091101080711121b0f190213020c3301052b03090501020d0c02060409090f0c0f091d0601 64
    0x40c3c139007540d0708105011424405002c07581c010018600c03015540c1403107040217000d5981c6a00005249803078842020032040d0041030030700031654040c0990303140ca82d80501c1c0d007913240015030000e504540300062003c180300d000000c1105075203e5916180c6c26100c280c030000204c82072482c1c018540e9508000e80440b560041a03441c0c0d02042902d80713210340b411808445030034450a038503048d0404c2808035115002980c0f02040e800d6050b00702c2d0003803201c0290300350030741d80d90380d12082910740380c180741840ca50654564840c0c07040701c45514901035680319101c0ea200c0ba51581c503c40c080038111045618600c440a82c100c40c5c00903012010351490641c3d082000b00800d03202c040c951000003100000310b0865100e901101c0d040024080e89801030000c0c40c050001e424148504488003c20010840a00c010307903d120903101603030900c2c2d1000030540b40a1501d01c08003c081100600103039151240054400040c490307580070f80d89410390510a0b103c1c5100c409080f80018a188050390b0018001405241503404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 962888534 1250 962887284 962887309
    0x30212030c030f070b01081b1912050304030303050609240d02040e01060f0b1e1602031f0b0904150c02030f16050f060403050d0e010624030524 63
    0x10350745000c0459802a26561090700100c115110200d008030600620b0490b4500402c0b162001e02580b062110a0303420203031003455003d11031035602e0002c0500081c0c1c030311361901070b16071600121050038a038240b46960350001d110850000341000c000a0b0b050410072040c1d401102c0300c4010300001d21034000395410354403101a6440d0003100c1c50b00603901680e03035409200c3c101c14806000049450400d1003e450424450f0800b4030f40c545c0820100010060a07044d100b00c08595a880070340b00d4550400040b50540512030103581489666a4284005081000118071700c00032601009605a10300c2803080e8001c0c11600a4550b08210900d4040080c058219051a4209205aa1400c0e1540e00902c089401280402d00c1c0c1000440220301084400c116860b5000180c0000782903500e4590f0b002400ca206030702c80c1309000c0791151500840901c1c250020006804415036840c865040401001a50034a2102c2c09002a040402090080102c1c4d034982980101880c8041c43c01820103080c00f52164858 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 962889784 1250 962888534 962888569
    0xf011517030d0f02030a050709080a0809120d08100905130206070606090e150a050f041e0206030c0904291005090d0b01060f032a02010e0601090c1106100302 69
    0x104500711100199106209005940780c3c401601e07410a4101c00c0c0840d54010290000d00c01001c0301440071510000e4500c0003958080c0078a035490040c440401d0284a50030800600340c89109868100e0a0704a142d043c0b0404c60141088d1145566420b2142611001e035142c2149007881c00760040903080c000c000704090760041501044485d610190b4000300d4410300c101865941250005031511a880410982c200801113018001030030400e52995100e400030b48002c00e02c80f20710040300908450004660354960300209826164a44040300005e1030b809808201d2246207004102c00545101458a1114000b01c0c3c0007100b15405520034060000d01801e804000d000c824080040c0079600cbe180030250b010f1085c051a80030354906100a0b0500000340380c0c62043c5400d0640070002c0c90f040c3d810002820001c461041500704000d40241d0040101800e69041c07400b94400110703240580f40c0080e1100040e582d175041691050310716540e110301040e00c03036402009007280d041016280c02d001c10010744201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 962891034 1250 962889784 962889787
    0x50d020c030c06090106141905040c1106040f060b06120703020a091e0602010c0503010b030402061602130902030c0402070c09050901111813060e16020f0f0f0f01151703 74
    0xa420300d40f4500341c41107a102126039103581090200e4040d0720540800d0800c00d81d6140d02e42101c4000c070641a0780e460007a40d000e542d80c0d03013501d001c4500c5410551003008054003600ca10342414200204070450b01d6500fa5550360a150030090349082c640d04a03407044000000100e250707110144210040d501400071a01041080c4401290102504014842001c02c005004d9070307841c6008c00203400d56802c4020403091000500040000b4031035001260f51142c0d0407502581d4a60302080385030310009030701601940009422489071240d11540d4090004203008408882241303840408000c00da00c181400244010484201041800c1c0c89800151704084442c0001c148000d0724141205d041d044500786c054102400410800c032400e0120f1501d81c1c0041034481031015a00346628682007480142c01d410224195044d660500781c424000c00c4420a10b8030151241d035103907000450b6072940380b129071020600505003901402101485090a51115048000034441c40c00441a074503c00440091485010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 962892284 1250 962891034 962891047
    0x2010e151c0b010e010c110310140f090123040809090f070e1905010503180d123b16060801090c020d0504180209030d050705100903050d020c03 63
    0x41601500721440100001c0348001c001c044180c007a1210310030114140310692400407803599102d030003060f2542d0040d200c9a801000000401d1902c600d24019210b0303e031030120505030741240500624060030018002d440540c44440f02c060885400e840283c480b5151900890044a011800d0311b47c042d00801142e41000c10703030b0340410050030044800c40e0071000203604002c500d54000c280050f00e0801907130382d20030944407800c0400c1d2400740ca004082c1440004000103078400c110300c610011401c111000d880104005a4020f090a403900d43c65940c0c540c2009140c0c0c400604100c161815061101901c0d006400001d0070b40c1c20403840c4c481c24448a02910174007080e80396050480c00d00406159035190202e6240013031400849100307260722021074200000b032055243d4801c042d80d0549008030034440800743d40c1d010f0a4004d01c07400d02103541500034038905200341c540080c080e0140310301500541d40c505030801e00380002c0b00c020000040100707100784a5803c01d40441ea01400c510200f41040302e1401d007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 962893534 1250 962892284 962892319
    0xe01082a03070c05060f0c03070e030c030106030302101808090103110705061e070203030403210b0418021906050301270e06070906230708161103210702010e 69
    0x9200b11425404925082003007401c015080094607440064100d04141905200b4003800e4a48000340000d420401101d01d0340074607507003e02800188600080080240d80e9032440c002e5100c0c0004840d0b44082d80c50401c0036528440146c8440c40c2d040d601c5401e2911344a006801034000340500e01c49070340015800d0166a001600c1000814054421001440d074003141c0d4100f03091010500501020440d00280188400a50408070104c003000c50501f80c140a00001219140103100000d40d25134000e06180f42c40b4000d0280511036401540280c68004015490403180804a9010721669001410410040041440d04e481007601215411010030b0404401e000d15070070f80708110200342440d003101040c000f005070001d41038802064182040424440c00c210a001c201d02d00408400921400080800c100a40781c0b0845e41403d06e40c01e03001100b01803a062080c00301030180b28860107482051512490b400405968280f00719038003907000d10744441c580c011210041081404c0340c00c140078030b00c0d408550 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 962894784 1250 962893534 962893537
    0xe03010b0d1412070b010e0612031206130c1e0f0206221401050603012711040908490902131a010e09070e0108040c0906091406010e01082a 61
    0x4c5006806245880d4103001da100c0c0001c0002e450580b10340000210340d441c41c1070100640e0040f0f0b8034815451002e50b00e0320302103218450b2210b42000001d0ae0006044102c1e9040072055000d800d844400f45007100c10400700703551884c8204038010140c1c0c00340000925041000400c08030303d000c181902080f0241d01d56805a402c280440068156511752040016a0a091150b85c800e000c02d40c03206440c032946800000c07100c94010784040d1901b040c0c00c090101d40d0329148c10000d03043c0d903c6408280d07a400602e02c50070049401c1c0340d0105911020540e100e100c107042d40c90b2168880e070379455810140441680f80801000c444004981050321080740c00902d81151042940e41c0d900e03603100e103d800e41410b0004155411042c07609100b00d2085040c807035030f07650010405480a41c00e0800b140700391907500348003004c100345501030300d465400c00318041141c1d00c80e504600320111810381140c1e80f075103920006403858484003d16a00041200300010a0311903c4c039021b2852620803201050780c00a03220394031019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 962896034 1250 962894784 962894797
    0x15030607030f1b02030426191203061a0a050c03071b0603050c0a0f0e03010606030204090f051329070e13141f0816170d021b1f0f0e03010b0d1412 64
    0x415044564123401d0064200524601050340c0c502040380d141003400c611441c9900e0004030402400200307107030455034090411501c1c0ca52444045907110903440c505650f03003038800311a403001354101c3e501c000380890185c0103007401010002c080600301120200101c0d03410700114524800c02c004010842391a440c20b201d5003020b0074090b43c01590300c0b0f0030032000c201911580d20408031441d00c1c1404104801c00e20541030003849500c160300b401030700d1054280d00c5000c12205000d642c802d900c4001e100c0160f400c810207240c04070303050b0386d48040d19070365134420402c031000003400c1214107800000164001d043d04c2c00361040040403400107203a1a840360f01d094502075503013540c912a00d000780c01c244154201a00540d045600d400300034140e01081c50002900c450080e2406420450703041724150b2107903078000400000c850307d441c0145070104002c10090800d034140c00d0102c0800c0440f90303244074906040c000c000410303d0251040c10881101c0d918a0210044001c0e00702a034012030800100580c10342004041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 962897284 1250 962896034 962896063
    0xf041a040509040308010807080c010903080901051306050306130501060c11060f0c030d0f1e02090a03021e0109151b060f050108150c030402090a0515030607030f1b02030426 76
    0x2c5c5581001c15042c03600440d904010350030b501000203441c05a030f001115005a0740d10804a585030144440103a0700c41c003608400194200c1800c17400301d1895480310246100342000c80720503803112148080442110000c0c02844000340c00031991402103841c10304072588040000c1d049074905480c9484013500c64103c1480d404507a080001c418404051600408a9004404504002e980c80b00345004140803807132040da440031600452074101d01d41e10414060000d6802500c07d0750002c01d4055034400782042001038a000c2080c071070000c10031500d0340440d00181c10b2152128038042d043e000319500e01040d0302d04201c88254039100706840101c0305014490080010000800c071490406140c003c91b020001c04d40e00c4120380c01d204000240c0d41e046c1c0e01c00e03084400080e0004050311045e2240c0d10000d2101c0615400d8840d0340280f01c5d00c10b51581c090040d00210481c108240e40c00905d04080c1302003541034044c0180d2040c402400f142290103a030b045141000016101070010700045242003001c20b888454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 962898534 1250 962897284 962897297
    0x70f02030304062f0d0804050109080d05060103050f040503090112060815090708031e0901034512030e16030602121f090b060403150603050c03030f041a0405090403 72
    0x40d405000c0f44506694030f500360114148000a41882c0d170b808500f00c03100c081109100108003440002e5000344601a0060001540d0324241040c00003e05000c1e81c00340d00182c0b40c240002c0504d00b10403602c83c010790384030010b945005041e41c011103810705c00041c1100c0c115542c400004240b001002160303441c8070300c903ca1208500e4840d6a65042c40b0865000480d0340d0003c11410702d2040f00e01c0440c8450300d007007500c01912140c0c0c15004038001c1140921100340030207041c10045100042002031101032302c042941c62500034948002c40c0718040c044100801040c0b4800c900c184c0c990207600701072b425460820848901c1c0b4180c8681e2070034612190b00035980c01380d000524000413040d1a074031640c001e201d272130040110314410060040441c82485a50020b60b030f40d0310070510543e51481154001d42d04455a06007045441d8030710390042002e48022202d0348203840d000c00e03030340c10044159080f00740030042040c1818644910b045640207000d4900020020402c8080384994407491494011800381c0d8071070307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962899784 1250 962898534 962898557
    0xf0c07020d06110f0313110604030c0513090602031003060e0f0604080c12040e10060f1b0501020f0d240f0e0603122109030306131a040603080a0807080c03010b070f0203030406 77
    0x2011f69201074000d00e40540301c100300500c00300d440706110a0031900305903000c1080c0c1c420403000d00020f00554000400a500002c2445104580c803d000c4098034080c0500f000100c07138195409654088500d9043c01a4000c20005408905d00c8405400084804030544039032140700c500400c101c0e0701ca82c001c103900d54400700502601c002d0b19031149000d4000c500b17185500c03a502d0321000e040f0038810300800c811207103010011320801c807083d010344d218130b03402460319900d40401c040300001030b22044107522980d01c85980e2002c0c29000e500c410707504503240082240c1d0300c1030800896000c95100104119012301ca4000e43c00b440a1490340240790300f26610224510002040c40340746002040030707100205e40d9009005000c01641d800e04002c0e00802d48400004810010792104504081c1803202c80741e001d40f034801c0001c14012048000c000407009540d642a07150742d4a1400e07208400187c0c3e00d805001804e00c0184000c403503d0b8018015140641107918011400f94006032035a801904103600003460510320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962901034 1250 962899784 962899793
    0xe010305102301030b04050a170a031505010807111504030e030609121b1905030c0607050a1b02180a0605041d1b0d0506040b0f0c07020d06110f0313 65
    0x2207120189001460011440c070b0300c1416042c04006001c0034007102480800b14040000422086501c945c0c002c240108140e400c0c00f0705280f50b0407142010300864140101d8070350320045041c4120546605071a0103e01d6210b1680c101c80041c3c007206c89070b0241c4070781101c41c4244030351a000c913817249101e6610126034040d44003c1c14103012025049050683c8481032421812503e9403c2d5010119648903600c140040c803065103151920454294100701520148a07090110200040c010b0981c03d804032416503c541030f08958512420b9464000540303030703203080d000106040e41145d500e180000c00a070b20b00715901c15080d49a04090b40c80c0c25103c0c0e40c8003020003903401c1c5409020000d461040c041a440d68502013540c1d00d0380c042e290718106400201441f14190b58a1403403400c80300e5004011038034189010b02e4100c8403404141c803511580d09101000810320242c46044501c0c240d80030b0182c3e07408682564468000e0314030050ba5194820040c0a088410b01e41003002e07510802c0c483c0541010040031b03040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962902284 1250 962901034 962901041
    0x50609030a26070305092d07050d0b06040c0306090c09080c06070f0609031e030902010206010f12060b060d0c020309040b15030103080a03180f0308160e04050606040e01030510 77
    0x4503401c00c1203032402c0c482078203003150101075006446081c08112543c1c0c042e056800c08800584441c08044031300010146115200d050a00880401c000c45414030b46400403c10b5202d0043d0780108030340c943e400010f0f010f05003608100e901100c5800c001c28056101e03c0800c085d03511003050003000134080b06c41001340a004101010780d44800351912460400207480714012a004c0308406000203444065030010944100507806a4030303c4000000b2600e14241030040c068041a241a4018030501c0008600c1044201c544421209a840040780302103142e6150000346c10720800040d8002070901c03070080c080c0014000c001032044107074007031941c0d4100401000308941da5032850078058118410300400216040c4100c90547e5000b44580e0380f80c41102c0011806401c0381c0898105461b858030041c8100812003061403980c5c3d00c00c0c1c0340e0300341e29078901e420103072010b1040300c050300041c5a1100e1203002d400c00c1e074030058209001801c21032400743c442c1d60f04a0400020f90003180c8550000440d00002d120170320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962903534 1250 962902284 962902307
    0xf0e071205060f0607081608070c0515190201090506100801110a05070b0a06240f0206060901060f050415090e1003051b0f0909030c0d05041203081003050609030a 71
    0x140100000e0030b00c200842e164540c0018224060400000d075a01400b80c2d09040c1c0700303884500007031400c401c0c1251400329201d4204890032588240c24680211310f034a4000191400d604aa00000c1e0516566010076480000e864440c4002e6540c0d9146d410f01181051040a101b180103498140525182400141c216000c075200020b00c200300f40304040d00180d11100301c602568200c0ea0940186e212103803554020189948519141100c88482144e600603141c98401c03d01c003d40c4402d00240d8541c0c000380d803904400c880e0b80d035000e80f89a0050104602030002d207525200c0514100d810301e0f4803900148010786000c42d0303c0022441e405400c02c41418103915040e44005200c5a44c00d24078955618942e482405403400300d44c68441170f0101c0280d44a11325920f0301d02500a021941d14200f08078455101e50260249100314000d02179900b0b0182c0c0101d003264100e03108a00c10450030500c5440071103d280001e03011981d0030f4035580000020540c1000040c1c000c0e08040051692200d82d144003030040c02c10907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962904784 1250 962903534 962903567
    0x81606030e0c010c1b0303020a1703271504050c031c0903170d090318090905030318030f0406031a0103090506161b0c05120601121b0f0e07 61
    0xd60140e42825020840d40c03122442824042c1800810b45080711005c0c0031041228442032003014000b0926600040c0e0a4245004485014916811704115845807000b16441d44078a500d070100203c640c1007110001c01301c0f0b03e2140035194004005e800c2490281001c0d50b003070310b556100b00c490008034a030500110015181840700303d079120740102d8028140002d2480b000e003a4240145c40308d04900501c10886001d8511500100300c9080e080ca009032166641d2200e03192442001640820020054401c000d030a540090041d400d6a0fa00d003c2d001c28a802c2039002c01e418041484100010b0300c40c0800380002d80300035240030402240001008005c140083c2c6064105820001c012001c5540810400e810800282c440311010721441d03000c0c3d420a540c031280070004407004e1104402c0c844c1c0a01c01405980c0c2c1240c0c07032068141000d40e402c2d80d61400707000724540b248044c0e80d40e00020380c0d00d20300200d187d840850000700780d5585110094070070a4a501001108607a6420454006d81c02007000b007200444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962906034 1250 962904784 962904791
    0x10f032c01060603061d0615040b120f070c06020310240f0201020f0703080414100606030f060602030a0c150207030c030f1d061e0d0e161a030414010608160603 70
    0x24031206c241d03942035080110140c1c03084000812160b0b21043d21410b40d00c0e0715612025612966425417000c1a444040d260740e803148068080ba1742c0c0d803050b070790321401927280b43d407040300c2d602d19500da500081d400908040e825410049001800716481080000156000403507400d4401d007410019001500c4105140b0442e4810001c6900101035101503802036600746c0b5043d07481e60b07240d01c0e00c100c0c103948030300d0242003a108114100f4502460350b007141080d10020703074003031041c2401c4c4404201580ca5500804015800900c49051028441d045900304180604404c018401e036101c0420101d91080100354006180000303071070141508592200703000c0c01c09241c40000c0c000d1041000c641a264244000d20490300000c001c9a401e0501010504c1c1900c000503440c3c1e9840708002c0070b4003c08003204000c0b451701503410304d00d05000205a0b08030840f0850301c1d0b90101450100700020056000900444010410301d88054001609115100c00b0b00151f0008121402d400f243c0702512117495031284041508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962907284 1250 962906034 962906039
    0x50405010e060c071a18010f232406040f06020106061704050705150f1b060906010303021b1203070c09110a0c152003011a0c0c010f032c0106060306 65
    0x16410181705070b07019030303698072085070b03c900542d0003c161007060300c94965070a00c1c0d10500e004e05240c0c03180b0f00c8001c004140096400c0f8003010124212400c46074840510807000c04902010040560008582c000910061619440d403900c04803030f41c0140c01040050303544901c1445030340d4010242c3c64441030140005409460259503995403152076000ba2030107652601500d0780d054081e88241c400e45280c04034400d4942a4180f50680d601c901c030b18298449104020225540b0711000c01e900d8103880e0907034090644000308004510100c008201c901d50803203090081c510480c1000e0024103101f03442121a01d0381c00e4900364034802a1134070415105400901000440c4410b5008003602c07038600d5020b00d4030b035004250350a12100812406800529200241944003c07c05c0e107140118103850341e1000099400d820039441c005c49015820804056600c00070301219198000e5180f503d002d140303441c010482c400710007a00e050b02070803501e2100c0300342403420070b41042c0c600030700800025088524040003c140b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962908534 1250 962907284 962907293
    0x110609060901180f0305010912030522111002030d05070201020f0405010e04020f0304030206010603150f3602040f080a0c0509040606082b1718010609050405010e060c07 74
    0xc10041c0103410300c03460380c0c05810022503031060400100b07150320700c1c442c10940e00d0406501034081c4035002c4a0040b2a811740704400c50080c07003910700807100300d2690010b10348031282418442d00f1040080d10178038005410a03515540d6500304004242c96607000c2c64440a1484600066400107000356041da4018494a5143c014000a84044130707402d2800c101e90f00b42442c04074000b841482400050031000004000516800148060481d241542c04020010381c22502481e446034a002d0307001c04082e000410022160741c0800c9000c11315400c0203d041407040c41c4441f10102210319881c808040c1c0208003040329441080340c880041010001a20342e0000e5603480b030060300b0045c081c5074070690361100420144002a07000c040070b07000d40c1040354842d1080407007007614000101c1c590902c8210082a060010b13200381d841c0c41504044801e03e20b1302e070310f0304a6400c0070b142800409400541d030384c101c0042e201c241409021300890140340000f601e0001e40f2840e40c208140200304014001d400c020110018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962909784 1250 962908534 962908537
    0x31e02131a030a030816031b030e0d17070311090d05010e0c0301020316200304081b0d020a062006040c080d080705090409140a0c1707081c0e12030711060906 69
    0x840c1c1b16030b0040d121510703035040d8020448051200c42c0c503001034070603101480c0c256200200f4050844100d400c602501c0004407030315402080d0020486440790b0108880601a402c64a502d443c65a23540e8140003e683c049510b040f4544000d0314280e44450340e041e80b0403414001c031101c0460943c0258034500d4600c0b00c03000c004c3c0f881c00601040000460000038522107220990300b02204103410741c3d82c1c450b50f0741c07106075071640c15000c081c4a50714248086034040ca00b000901803040e80c0a04100d60180c0b51103001d580481705117920341d140c2c2c945a5101c0c1c01e51241400024451442906030114482c01c05020074a499500f4681c00180718a21003840421a0040700383d5201c100308840102e02d002e200d20b8003000422080300c071501c09115501d178400401001e86006001d0b50080340301d500c100741c841d1102c0c0e030b0307544036030300c604076042d008442d944c10107142e8000c0d444145503a6041c00c10510018502085103640607401c40040c1e5003021401c901044034220400180c54021140c05081c120100001000d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962911034 1250 962909784 962909791
    0xe1309060c050a0e09070e090106080601080a0b030a110103110403030507050d090503191547040216050303040b090106060c08090402030717010b120105040c09031e02131a030a0308 79
    0xb038031080000486251203020440007d0101405428403961f40e00d5015080902c01d41c1c0c0c4a022402e1480050141d860b2481841d41c240c4004008040c10003103501c502c40011b61043c0c4450406484803281074266030214028802503102e90382e02c540d1000142095420a01c80d10180b0082000049041000e03a400181003a20380c800c0c0341840c610300caa1440d10703d001104400e10182c031281001809402480080e00c1020707031900c24856504040c2602200881d140041c0243c0c003186a00402c55202d40d05065000c0c04461250802c0042c40c2c0042d919007519540003110f084401055203410855402c9080c02803100420880c286070032202650b40e0307050b401c4d008013202540207030303808400540024070880000b0750000625045107165615601c0c50506a44a00d011003100c1060b400000703990301707091040380401d0350f0a60310550094103660710010307440070a0284000405a400348000036907200ca1030001d1001002c0400078001e81462410f071520841010441e102c0d4002c100400082500300c110103a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962912284 1250 962911034 962911039
    0x3090f032609100914150d0b22060f0b030906040206160c080d020f0601050303180607080d0209040c11100e1204030605040b01050a0b0f07030e1309060c050a0e 70
    0x155800328404945030700074441ca2a5000074a40d031010034843e002000c4074103440400700c44100720300b4260180700c00300c1004410705c038010401b0015030014445035444920208e074014001c0d00c400001e01040111020140c224408213030b0b0301c900801040030b00c12010401403034243c02e40c2d0704602e0f00745c0860b80c5810004002a015001c00500701c2107a038030322818982c4c1d00340e00c090604002a1078103010345c0c0c0c0b16070401d6050054403c0404003a14078400182050488a00030021490400148000c8000d03042d26000c641d004101840f040c400140c0b120094092011030b07072001601ca00e00302c07003004152102c1241c42c5040c414001c0403010788040115088011a031500d4010509080f0750b1380c01403500b03148a41c02c2070f1641e0041404801c22060341c0010380980d00a4150b031605903250010800182400d101d400d007000c074108151210000d208010f801c0c6a4002d003400000e02c400c3d080401d0391460755800c0703a03c0d07c503585c0c400407042113010b114400001819103001030900c0300c04880034021141c1c8160961 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962913534 1250 962912284 962912333
    0x6020f1207020d1202060f0604020405030703020d03020319020303061309051b0a170a0b0f160c050c1201090605092107050c03011103150913030e01021c05040303090f03 74
    0x80d922041008150203901c507900c194040c13040803009468100c141c80280a1001c010085002d5140a000f5075040d40c00c018040c0c8a000c0c51a8200050301d010a8012030641c00140010300d82c00803240b5010030350030b4083e0091641ea12f0f0400c00c001403c41c016549139841850031003170401003000001d0b14060300c1c003207050304003441044400040580c52580e1003401141c40e4418000f22240000c1042404e09210300e1640d50103403030b4280382c0c910182c000c0b01c030b9500c0e50021a507078649051003040069003c902500c180c0320600740c1500482d160341200c0e103007195540c1d154858001042030b103106440c2d01c050a00c020704074806000c0c100c8001c0341401084c00c040c10034040750310310620005100c14242800014003c00020201c40014510341d00700f1100d0780e81406040d24844258149011480d00c9003908d20b40492400340140d400340c48101c00d1000440c110304c1603e1102c40c1603e5482481c0082c08203507203c0d60313116031071494002c012000700d401a01a0b10080d9400300002400d08030000c100301321186600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962914784 1250 962913534 962913547
    0x10908030f1e0106020a0611040b030c0d0605041b1d030601050d051f141e040602031e180d0c0c0b03070c081201090606030b09160c0b040602120106020f12 68
    0xd00d40942c52820004004000c500010382150005407440c555031052400340600138181e030444090780114031410740074103020800111b0480c103880050141c1c0c1410700e07001032000e0301c40000c40c044492480310801b5040004000074643ca030403500384040000c2c8030043c06038500f0b041001c07a442e51070621449000b4201e5402600800c0b00a110b0850040c007a103408808030b40e81000c11101400c40741ca0000a07a001400204028941a02103d4040911041c204045844130381d100e800035800140401d0454002d03056062181000c00c0301e650240c20403541c901c0c00c0416100103c1d0404010b802c002c410b120101300c0c0e8400040c2c81007100e070211800302c07030341d65100d42d40d407030b401c0c2c0f40c1094450b0018070181000030b5980480324010003040c140e0351b100a0800c6410380314641038081792120000301e035100290302d00042c080c4003508441d0000e0001c81c60400c20b4102c481e66084464101558103c0b420717500443c0c02c501407010940e40500400c034910041c0b200c03000049a060b00c4200041800d160b042000503030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962916034 1250 962914784 962914801
    0x201090608073e1b010507140d0f090f0e04021e06040f06090f0b16050c130617060f0f0a110a0503040632061507050a05060702010908030f 61
    0x24045483c5241e03540c08070101c0480600c1c614040d00c048540e404203007100707000140001a5a40d640700c01054140501881d07180150340341e40002d50102c3c1d40c800040b8590041000a0090f4544410071f81c0b105a031041007070001600f1075880c0d41010009840700030342040181c000f0004680c0060301031ba8003022103821300c1c16100c181116003900681080f40018002010324000b0b8200c02101c059580d81440c0e251220b0b902e0780040c105225402c01401d09004648102e412100c42a080c0ca20034400c0300c0300c0c3c8000c80d011652a800380b0207181401940e616013040781c5089018411004500b400c00f408413450b0658442c01d08041c0500a0194008842e000a1441c5c155620403d40100008000d9450b24103005000f0301303d44c4129800c5500a0170403d4808145881000201842003040c030750b58800200b03e07400f03500c0c031180200180d0f80807001078461811300304180010031000f8062000b40c5000315007402c26030b1926901601840840e0300d09802c5801103080c0d01c041c1c07500708020007100301054a074480e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962917284 1250 962916034 962916047
    0xd08060609151b060405030a08010e1b0a1205130c141f0c051504120e0a050112090b0903070c0602030f030a1119210207050706030b06070602180f0301020304020109060807 75
    0x80c2c1218130f104040601007802800006801d40c065aa03171200141ea0700d07500e410500c0c0c0070945001816a20030030407441c1c04003a9030042c2001006616143e5000c4080e1107074403082d5541581c205805154140400060044400115000d00101c0c5100c130700000c60580810312225094a01c4030700703c081003001e0007c45224446030010300c0c0d041401c656420600301000000d95070242ca007141c0c1705020207801d0500078096001c0798400341000782030030b518928020040d14402c00a0b1080c201d42a0781e80c0c103010000300444000c900400c0b00a00441c0c403130b8811701c0e002c44036000c0ca40203a41554008c0c8121348581c40e401c400c807a07000c0c54040c000303d01c0480120104200d4014500c0c445190000307440c621200507800241c9102140c02d410100036417000c003140a800720310465001814940103880c0600c0020700a030003000c585070b0043e003840e1815015456800c00c0f83c0040c200d5001c0070300b4240c0b80c001e442c5072440700d2000b0280200c000311f01d1030800303074000fa04200c0c040c450303c800d0024580004892a00820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962918534 1250 962917284 962917327
    0xa060b0a090e06070e0f01120e012d110711060703030608010518010606050708030f10230102240a0504021203070303050610020114011e12050d0806060915 68
    0xc1d0034410444003014050322400200c91000020b42c0c18207483d1107510300003094040c4520b06840b00920400e1180b02100507100400401419640348e81820031403032184011100f8103041c200c5244000341c48204000141c4007a4048490900d4060000c1c101003034588124000040044032100d82e035204614040c0e01800596010307400b00e501e881c0c2044444204e056400c050060800000c006541c0c41e190700b42ca0b2030203002000b070905807091001a00b00f000442805420840581c0e00341401a81c0b050110201c2c014501826200d019061242e8030302c1d60100010908040310342c5182c039101000a811100c500c900601403085c0d035440350089415502c0302c2c0940300725040144144c2e5a14006810058094042900d111740241c11010158a01c1803040c13040c04150080c450508526034a800031709200243c0c0514844001c00d54550009004848030100e0103240e4030840140440d241c60150103000c605004014a0060000704500c7e0131a66503030030000c4070714041c098441c0d211200c0c0721000003c5400c45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962919784 1250 962918534 962918549
    0x20601091808031513020c030a030203060a1a0a02011503020f041a040f06030506090a030504060c030509031014060307060905011d09040302060619080c0d02130615110309030a060b0a 80
    0x18040026040d0480c444840c205807121078003045e40c5a61501284550841c4a402c3c4e0002d0106a100a1098008641218009040e81e030150b85504e01e03000502030207184c0e0003101c038000038600a003a40a01407040e58880100d40016100c0c030b10340105402607c00b1000611640d940c4110544e94613203503034003c0c0c0d40c4070007031700030002140380c145100001d02807400140c03418801ea0001a02015000854500c090342c10740e1050f040524010080e601e00e01400c2046003030003414011302c191614200509203a8025064000c07401d520780c2d0100724000c00014286500a4000d40c07800c0c800c05410a400030221002072030f00f14005010710b11072564580c1c551054650084030303001484180341c0e00041050140d2000c9030040c0e8007256161101d0000305ca10712034038a0640211103980340b240740c00c82c2c00184581c009000220041c5800c1c8411046600b80e800003500d900c0880b41a0901035030200d840c54111003090b0045284c40d100c0800030380e41e0a1100320040c680e41d142c030340311310082d11051509001440035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962921034 1250 962919784 962919787
    0x9030a050a030e25080a170a0203161101141306050c0c180a3e0904020316020c010203070b13080c030a09050f090f04140c030703290601020601091808 66
    0x6102c04840408008075011395003025030710046112040400c0d0701c2c030710b1079000300fa01e42c101c800031205020a4000414020540c042444143d603a042440c01200040e4800e8608405541079940003614600d8801c44000840f4800d0215855101c400003440007541c055080054480e000311450b54604008046280d4115002c1507080002d8900c111500e4000c101c076810500205141d0440c40c0d103900c15941030060b48081c01660b4894881c2d20300504140c1c40100c0403082d00e411080c0e008103040e82d10542d50180d150600400030b188140c1c1c1445050817000e800d01c0610b144c000b06464548604901801d116421001612040c08001301c6000701c83d001560345050300c0e100c0102c0e0742c1c007600c80019441450b00400e0040d034401103e2a101150510030003d6003000d00c500e89640e216103800a81c1c4075070080344c61051042601960742d08020f11402144109450640d100c004bc0406414140001d601e0300380000900c14001c6581e0007081d0203064400d03d9100280301855003487c03001c0d0380d582a4000c0d200200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962922284 1250 962921034 962921053
    0x111005041b600e031b03030d021909051c24061d0a18060207020d08030115020f0607020706110a0803012315030105040b21030a0f0809030a050a030e 65
    0x70b09500c0001c03203200c150000000030071610030394030601c52060465254001015002c0c2140c2542000040c0d03440190489081009030122201240c3c408076080b081b0800000300d11031080e034410045009441c05a03210805410007840380c9100003034450b030042031102150318520080c2c2c601c484104944050000c04d003c001e540d480600003601178111100032801c44003000900c50403240c040d0b01d012002d5003409840c42ca45135199440250072008040344d0094449060780b0108400c8005103001e440103040d07013611612031400c0a484c001c10303003101200701c0d002001045007041e00805c0d040100d4206d410b021060142c00502c1c2805c19100100050082c000800040b8404521024030500f01c1500160341029440303a00030040c5051140111500840e02000148103a042580040b0b0034500d01421249203680f0f094504180710902070300031905c60340b000c244d2a030095840359091449600c03074104005070381419a1555100c0c4500070300075044c001c0008000ba466442503115407200e03030107042036549218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962923534 1250 962922284 962922419
    0x415020f0303131a040210110a170c070626281d0a050c120f010608010b1503010e01061d030d08091c081501111005041b 53
    0x10007054030b0640703604e291020104015502c2c00d000d00e0700207000c0042504044005c82c2d159606110f80c043c140100304602001864904101004894040301e5031380b51201031503010324110340c0b58802000c0140d0740b442d201340003031007641b040100080d0001c0c55034030303980da811601103800360401e2140001c003041c0d000072201d0f03441d948000300c02c086404a20705420801c001c00da5903401d14410103013060700083c0d880065403400001c03681102511034140e900c1c02864904040c00c490303165001c0141651100e400441c45d00c3c00302c070340c5044050001410341c2154109840d190b0722503c140180402c1c095503168411002240450280c0b0540c002405c42e955101514801050964166000e001501c030b00f681e0308060b00240404001c108640d550762542c581e982c0949045000c120402081c1881880c0700c07142a801001d00182d112a41e0400c004610390034107185c2085c500940e039101c208000c140341300a1000c89540b5220424805441e40040d030603887c00202c5c00b00454090007400c08000c8035182000b07894 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962924784 1250 962923534 962923561
    0x609031c20040b3601030c12060e0a060602031912020702040e0a1104051302060d06150c050714130e0c13090320150417030403050405090603070b0415020f0303 70
    0xc5040c04019208800402001c03020034044106407100204042c44c0c0a44951081d803004100203c2444c282c100c801d01e01482c01d08460340c1c0c0d00040000051842080703020b02d001d0203208010602403005500d800c1a045615502c440c2d5503400c04200700041505004504641d0140e5080c2c980041082100962404990340d8541000c5011545400100d03440c103414502031040300e100704c4442d404540741c07954a50811020f030f402544982e1703040d80e8038440440e2035a01ca10f15103000c000036440e000c1c462000c50130b00e54070f03044c011342c002c1ea001d01000489100c00d84406200c001444102c84012039510a268016401d004611100c0e5400a034038059040001915400440c000e5020703403207180d03281d0f50075a86000242480e1852000b2940700303500d11048120320190050303126005008282d00034501c64500e41460b40142c030283c1c00071303d000c64207000380d26103185e4842c2c22410460042c161507240c004502c2c085d004910600045100c0024444000b13030081c8103091003440c98a081d250340786001014481d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962926034 1250 962924784 962924797
    0xf0305061605071a010510031a120a1b0611010e0706030b0d0506150f0a030c060f091703090a170a11030102130e0a050106050f07080304020d140f0609031c20040b 71
    0x600c0440c7c02609024041e106922900341c03140d078140200c5000750144100083c205903a200640b041c00da4040101e01c600380e03d44808110704002040b91403400c0401042d40401460007070f00c40c0d1411100d121400070005111081340c2c403c0c1000703d44000004001040d400b8200385c081c185005420070000329503d60034191200000840b440d020420410007840708a1031603000090041305d699006104441c01030100c2c204080c40c40c030709051400e844106211592042501d4080130340d2000c603001c41e03540781896580d8007500382404c1408000e1240030340c09a945608441c054140704071180c4140c6662401e404551411010b010074041481e512016071101400403200300d21214070348800132417100d115100b22074a000084602d00d041ca4259100e00c0c2c01c41d031014100301d9010014000c01800185401c04c40800000020050504003612504240c2045e00013400c4c140c0356041000007000e02d8140483c0d880c4452010600003e80101842c092510315900010031644844040340001d00b126180d00200707078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962927284 1250 962926034 962926039
    0x405010b0a0f270e03070b06090705031303081b1204260409050919050d03050f060d08180a03050a0c09020f0435070e010f0305061605071a0105 63
    0x200c0d0b4410400d0307030020381d50103110103503242c1c0b03001008025040481020800c0c90082c002030f40510460304146140c0c4614422100d1410010402a90f0b1501c3c5803050340c44611410083e00e1440c0003000c4200081065600500b0710280c0ca02048140a42825408d044484218503542d1a0040d00100b901070340211400c88070304a0005040800940d06014858608691581d0506003801e0010300e1016000062442c010b61141242d007080206480403445070060040000c2c101c0c0500ea004000c06850000b0801d8105540c401c0030700110342c0780d000f00c8144864100043d10381740e98501e05400010b130385030455142c0c403c8041201100344034021500001c000d2047c400000010755562120b01a401203007052441703854184800c010703031901d030b14004500e5a40e440c1c5000100c40c500d5a84c1c40610200c1d06c111801c0d40c084002407050380400c4950743e014000000740c40214070318603070340c02d070b03903404010b11b07842a104240c0c0c08040341c03500510a031840b0a03403007004240d6030710300f80c5900c1c014003200b48140351 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962928534 1250 962927284 962927299
    0x10f061415040605030c03071103031303110c150f0c010c0203040501182102010302070b010e15010302250309150309030905060304022b021305012606060f0f090405010b 74
    0x40109181c1120211000ca8035803d003035a681c0c0c40f1540c0c640e0001812101482001c0c223464408420600085108051a12030310030034400c1401c00402c43c0456112030703a01540850384a01807540c038103030000c01520040c03040994841c01c0c500681858011020341a40f550700b8801100f41030394002c00600145c2e4001c0c0c3c0c0d0410164040c0310840c00800d054403400004020302c0d400340b90380030f100b2604030400c540181805860030030642e0742c5140c9040240d02c05810314103403c1c00c0c800d1342c64030100b180d001c02c6003d18040d0300b42130908440c002c541e4504c01403040502c040c00e40070404c0501031403285000300080c2e00c52260040041070094050701c0a9002200011044580480e41d0701e40b800681e401540c01500254025180c4101284009013400c6261424502c5400100048c2d40c1c0c1d600110072a01414404111540341550003510410301c12048007100c22140320600c00400b0001e81d850740070f41c04552084980d99400e0200c0d01001c9d030700140b260800740d20f0782080103000c4150071103200e401381503c405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962929784 1250 962928534 962928559
    0x50a060b01080f011d04030903050d0f021920030a080c01020d050a0e0a06110408010e03090a080c01051c060909031e050313060203190915150b030612010f0614 70
    0x3c203e1042400317250000ca10030a401410b510925840b59402403180c00d041112a440e85c03246072070910b4160b00440020b001c807030010207465040c40f41018029500c14960039a015035074440035588044c0209080790003d00c0607501c407a545c1088485005500100326554414130500c0f418082d40c04200d00248a50070140443c0581440744929404480c080740607008900d0302d555080003504000780a03103100d110601010a00210030b10411026950714001150b039503030b5810030f001c06401d05900200c050341090440c1883e50740c1110465098002d141081071070a0b80c2d400d511001000103030409145180703019004c03020190403412141000d5042c6034846070170800d251045510384801c503070508122100380c5603440003c51a40140d60840c0c4012080d0744002020348802086440ca48804d95001108401ea0320f050441d174810205030a5443c240d410405041090b0a41903110103001c40b80181e240c100b0070000c2c1042075000030584011a03c0034807006540d060324444504041e80b02c5849007004000c003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962931034 1250 962929784 962929801
    0xf07050313120206220e01180f050f2e06090801051311100e06030c070c0906051c11090f090d05030603070510050c0327030c09160309050a060b0108 65
    0x15410302d01c0e030040515250000265031001480081102d45060444501c0c02203501c2803132003045400781c0010b60308044201c1801e0031140655042c024003980b441c2c9060300340302000e503c003405141d2094150441a80c0d08055158900e400031641007864420840c00c0d001160466100c8005403c45011030001e0003151104000e04da12103181c01c00080c0141500031408200f8146a184c50340d0900c010b0500030340340e04225012904960040b40d00342c0403004009505c408109400c2d140700d000c0d14204500308420760400e00401c0d1040c481103004503501120440c0c102c10046012041500c2030009820543c1d68104405c880340104001d85d90412107014104e11008054825070581344a98401401490010718140911448030003080a00c010040c01300f0819880387e6080006000d0b016181c00640000003182c00c545141c40402d149803440b941202803035050079525440703000d8018001504804001d804003400fa8004c06035002d004115015211401e000e105103070707002d070701c1214003a00c0c0c00042d507480342171 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962932284 1250 962931034 962931059
    0x803040608160516030818010906021b070308070b19020705010903090801110d150b0c0307020910051305070207180f05010e0402100f0216092f1606020f07050313 71
    0x131001840200d80381c41004644101a059006a9121a03207030226070310000c1389003075952040c4c0a451458000841c0785843e440c104a105004403150003408096003560360b0800e8600c16007401414000c030031030224004012100b1481c00542031090119a541c503185040350190a4a040503000b06586440c0001d101c0303010300589005034103603407060745458011400d2000420262584001c002c2c0c1021003c00e80010303050040100c3c0190800a40d2a2000c1e0310403c079031000010a08603a13034558000401160b01c4900d900074046c07400140215003070740c13070f51000ca26205c9c050340950704180c550100100300340f01980c040703410081030310f20a0025a80750741c0e10380030b000402d980083d0031070902c03641c03160f09a108200b2840d21594500c19540641d0801c641c40341e80004d02c0e000312820b1681e41540e1910241112201031400b441503810040c402c00905a440041c01a103203064000c0d80381d802c41c43c0420003264120395002c0c0c0c2c51178045441d10b4280c1440f6540381c0111401c4500c47d00020300209617445d2612 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962933534 1250 962932284 962932297
    0x60102011b09120804091d100207030c02060702030f0712050c0d080906031b13080d03110a1103040807030b06030708010e06150d02030706020c040c050403120e030708030406081605 79
    0x1ca454002c41d00c1c0950505969a58a0f800e03103240d8400d02002c141d0840701d024015800d0038002c0c07120602c2c0c007152070a500f00803c0e081114840c901c10406a80002d4100c2d9075081c0a980444035180c4071603960021030700b070500c03403c48840700e4001c034034011038001850809400d80714050f1007203d40010103001404042c04060b20040e007400014000c0300c01030301d40307000216801224101d00052400c400680e00c40300340c110000c22064030915440600200c50200400c030304818140c0303800d02c0a0443c6c440182c1c07091007054042820070002c0070100c000081c00300103c82c001c200200841d80000d07517900b80121240c07015202107100c1c0c01045400503d003030050050700d04021041c00607011a8507500d52481901800c282c803107810014070301e05200986c2d018080900100302a030007614108200c0804c01c0105c60314240403105000c810b20080c0046508007096810b484c4007410012400444140040d150808a43c404401d41c84001400b0404a521009203800313052000b600f4144890f025405890501074030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962934784 1250 962933534 962933537
    0x11d0d0f1b02101103030a06090b1e040b0609130c02070608091c030e0f1606180b070f1b0e01050a0605191e05132106020702030321060102011b 63
    0x190210400351800e140700300540d88050401a02d801031300081941190801c403182960aa038845080101d08454000c56081aa00302c4261501c80c02003500c1550b0440b2030441140165500c0c20f4203640794640004076041128001e284840001603040640041d000c0c0c0285640140509140000c03400d00420056002e8507080700a058200384150040d4040c03903460b203402040686800c0c1c0c04514260600070101e4a03403030203010b00414801401d611180320b0b044e0b4482c00c10810321b40c642c420040303070b055090016a86802c406a654902900f422000524804005820400d491510345c0c4001200b1030710b101112a00300711419903a07a90030400440308050321403803022880070000c42a603440051408504c080761418606d00302d11401e1403401c01d92122010701c80c003040d0009100c101c5089500601401082c040302c1d40005a0300d010546101940c00e0000240043c0e000701d0583c085580500680d899101c05006c00110580145600500302d5000e68805025510300003024540d803107002000a80340d14a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962936034 1250 962934784 962934827
    0x40b010806030607081302090108062707030308090a0209240315150a0e0109060609090603111e3006012304060f0b070c080c0d14011d0d0f 61
    0x4c1080c25290600300800000b071090a03800d81c4401690382034590303800b03800754400404061914002d844100c0d40131410b950242c0b0303505510040b800c00d0004091003500c0c0d062610742d160341c48608040e441c0c43c0c0c41480003035110000030100105a440445000c0307042c103c44040010441c102c1041c142c85100c0c0b0985611620304d6030f000601c001811441700c0040310006441c0100d600d40da00710100180c4030a03002010416150b0804200c0c155001c104000a89200b0301d0401100d4034660703584c101503000b0040d95010b80076a0700101004400805023510100c4007030041d8980e00c10702034000728900000100000d42a040c08803803001500000b0340c0a06845078600a081ea03400c4c0d9240c4d401d40c1d4402da0b101d05030301075204c1c600814800b02c84561800100307105480d60f0b454028a1070a1424541d0580040400e40d0102050010b10303515011200411600a8032503181c0000030604540500b010284521040c000c01c0c0c1c503252840f000141d00c0013400c082c2c1d5540210200420011545501e1020b0324070f020655 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962937284 1250 962936034 962936041
    0x905070b0c0114010e040f11030f060c030703230f07051303060504120516110f040e0105090d0203070506060603130f050a0b0604091109060315160801150f030f060f030c05040b0108060306 82
    0x111514090001c230044c12207004d60801e40c0000d20301702088801c0d03c180f8401005102100790103004500c10100c00804581e940c0203884507038020540300a255410209258003c29501c500440c1207940d650881e106845000ba140d00f441006480c1c141c8084911601500e61858614400d80c241d0b200303204030001c4c01c1142c00094854500d0b031032035454004e91007458191004003650b0765104011030110311300001309444c03811070941424824a04000010b5400400180c0b000850200746d240d4000812108140c4a0312412024034242016110007442c4035146d221303150070300000080c0e101e00f00e0320801c8000b0890b640e1a0901096800302c1c640248079000007010b083c01c5c0e240c128551030740b203600942156203030350f040710075039800060a4425555020f00184d44510480c1d0058041c2c0c00f4000e120360b078a107403007980b401c01407590440c00085800c240d41c40075504503080ca0f94011500401d140b81c5071080190700c0381030071850003007644a5584150303d8038004816550052200510401004020781100e55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962938534 1250 962937284 962937293
    0x41e1b111b0a05060c06180d271508062b06020304060e03070c06120c1b020301110a020106050120190f060203010b1803070f06030905070b0c0114010e040f 68
    0x8000311180c1c408800b010100e242e44459010b814050183c80003000340b402c0c00100f41c82c84813554030b0b03400001d400c900b00c078520b0540c100d48070703002d00116070840c042807500d07007040c1c081003601d00d400c49000c5080a00012031869440602540200b00c11500a080c4075510245812a414081852005100d010030b640380441c01c0da6014503402402a440031800f4852010303001d08607442410203c2d1800c3d08150306012040c0d00c1400710074000f10700142082003254a04001d0039401c5094602050f521014404804644003900107810011180880b02c0c2c40c0c42e242c100181c040c00c0c55001d424000303254080300c10000c01290740480281c2410501518001a40105113500c0c00058101a00c0381d50b03941d4040b030f0005480707100441c02013910041d441d882c0c080401503c04190140c00c40b0a201e40d104d244140800781480781800200d40d618100040e0426261420034102099a441a01c2440e00842c04641551064000099800c1c454000c81017a80c0c85281c01d03003e180003580c3c0a891400c1609043c80001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962939784 1250 962938534 962938573
    0x2090c0c191a0108100f1e060e07030203040503040506031312031b1706011b08030f060901080d1e030906050103080d14091c03060b070f11040c021902041e1b11 70
    0x103d4000808a00c45619240c0a801e11f000201c0e02410240e5910041010782d180302102c83d0080340302e113402d40c6582000c0c2c4a90707540f07003d58010180300b008000003242584080c480d410008a034040384d14203400704a0b01e00a8010100c61140e807010118414000d280d1611079095800d502e030702d10300c1e1140c0b2501c0d400700460341d80f07170246200d601c542c105180c013002141156010318412204070000c45114504034050200303818040e4001c099641c44a6003840d40187c10004c460100c11088802026441346403408038081d140284003d007020303140c08004000d10081d9801440700102c844000d0000032103c10106203018800c80d0500b055820400c000c48000d480028007942100c642c0c64041215030700e0b08404401e0358403806040301ca1984000c0d4040c01c000500c03082d821030000842e410404101c1c0c03800c01070b456502030742d4040410f2022900c40e01c11513603158081d00d40040c0154007240e2101d05203100c040201611806441101410b41600300c10910a851001c05040102e0141118018220b179041e0346 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962941034 1250 962939784 962939801
    0x210303110f2d0c01020c16120f03180801020405041113060e030304210c0801060614030408120106170f0411040515130605040b0409080702090c0c191a010810 69
    0x807820b4440d000482005080003615100001000040c0d40711280c06016182c41581c80ca400000a51000204070410b08101c0d200b81054205000d0b01c40402d5600c2c0c2241e083c080366172103130b640366600c000200d204131056010f4000da032000d80b001c06c66614903150b0280d4902981504e0007099003080c0041c04a54803624040598000103400c490516880e080752404085030400c9ca28071500b0105908000d0102c664121001040220300030881c0a080c50001026115056030340e100c00d00d03000010904000b003000c1102c40c1410444103480195031224002082d0043e80a8aa0080c5411101045083c00f106030b04600507684815521914840c01d0103010192900401000400c010710004c0251515103000404002c001d0344000070301d4904000c00c01088450401120b40070b186000940d2000820400803079444580450740c1c5041c0307944601a0064901c80c207103054901c1e010300c0440360841c61041583e0201b092040400d103068036000180707150325400c00d00ca81100703680101c400902240082d07000741d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962942284 1250 962941034 962941087
    0x50c1b0a060f0b091305030d0b01110706051c0b01080112110414010617010e0117030d18021e01021002130803071a0c1303080901030204210303110f 65
    0x3585036107403100c8048408407000da014180e02c40030520014504104101e41c040191080586800e4051300d0700c81e84ca01a0001451101743e0740e4031001e0b4075038084c0321142150f10824088421407030303d45100804540140882e4110039290180142d0000c60300d0248411192041e510000c90340e2034150192440c510f00f100549440d640313450300041c11b480d43e0242c4484c216110350100d41c07030b5240c200000d02ca03002200058100180d90401803180ca1110320340701d81180c5000d1404a483c90003018150305520801e40d0480c14203242140000d43c20b041c000088950368021211514601d24880e2140f45c0000c003450664010380201c0040003007440964040e01e0528007007800300c045141c681c113100785035601680042c2d6408450042016980e21088070040d80300b900703035501d94100081590303210075041a500009100280100307252041e64800d44c141d40080009488002d01c100004103180c07012a00b1807415400681400e2030034141c0319412040354500106050b0003850440ca1010395462100b52411510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962943534 1250 962942284 962942293
    0xa05040305030d0501060e030a02011403041b06030912030e060f0406020c01060618080a0f0312140a0b0f011d060f0d09031806080705030705161707030210050c1b 71
    0x4030704208040c0c62a105900300c00121541461009801e941340028194170a501c1141c400d40141d80c01085501101d007801e030075079200d4031945807074200074044005031049455402c600080c0503070316420140e6803601600008600541950048050703031681d800403151940703c00042802001202c0155034094042d80c0f00604215602080324203540841d40b0071000541da071411484d4a218850365540100000c1c4024054490256280c00c80c62403510009418001c00c800e484519106c99001410070400d8142a0785603858a00d8181c0c1c002d2814441d0301e8041c0c0c020445001c4154019514202d96880081a13000c080542c00d04000300e6034030040d140c0310640401e00910070003c1e0365019081405120351600310b051610001c60140484044e4481006c014040c002d10600640181c00c590f0485003d14000703680340f24210340080c0103035003500002c0c072a40e02044c02c0d20041c0070b400d0142280701d22940c06e4a20200c038210741441030b03450a0f500a2241c0e2001c10490016019080207a6500300261050341c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962944784 1250 962943534 962943539
    0xf0b07080718050d1b1202090603010905150907050901031202062404020c1f1d0c0d140f0d050a030b06030c040e09100e010b1005031e0c0f030a3606020a0504 69
    0x204081c03001075015003071882595031b00c0011443c0c40c44146034021010380080100418640710159134503011111030700c80610650120302544018404140540b40142c9080d501e940c1d81c3c40c1c40305074110b088034010014000c03c008642a6544400e5500e102000320700b40009011070314007004000d510031491055140f01d8003102a0b910800d170700341d1440110305c6a01c00200205414140c450300f01041103910a07a0300050401540c2d45c0d41c0198440c10240c01c054070b101da0a07080211646002e64030038078510307148603584c2d0b00300761558002e000f404118219034040c000c07100c1500c107101c000e01013921004403040d810b01043c01111450689568400e101c002255640314400380b415007280c03c40201d410690f5150614044941064110b0030110800385ca0f0403071852a1074176181a4007000300b130b040480418464003080c000341c0824182d6444202c81c0641036034034105803005030010b208580024804e66480d41440000c6441c00f98250381001d64a01c24004121503503032880c000f50720002401003400001c2c00007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962946034 1250 962944784 962944823
    0x20705220e0c01030605030303071209060204030f1b080a02130c03020f0307120b0a03081608250c0f03050a14030f0a0201200c0a030302030a090f0b07080718050d 71
    0x5010390a407080300a01880e00416000505031141d035041140a680f0400c01c2c4440d940c0e21030202c50100c0e0080e00c0014841c0114035004000c0d124591002e04034108a5880c0000c0c000c1780440d6841c411003070718502c128540d80e8082542c5905800102951085024034543d0744510b0a03000140804050301c0c0051601114001d841a01e42054a443c000110610300c0499072010034810240c801000321a0080c0c09072440c0c0c1c800040e803140d2202100101032144043c0100800702c4240c860100900c02100c05030301d903a0b050401c05042b07c2500f6901100002030004c0d0380d0407500c0c0848180c0c1e4121020b0701150009458480c1c600d050450380c980188002c2241000d2444180d01030045072009900100c0e581441091b454140303121140300322501070081103000200c00c3c0006184092682c0347c00c0140e200e90f00d00d800d4400401c0e60303a10107842002c0401c1d01100300120402c0e824031803981c0d81c6030307400e003030300d440900b218100d094848a010035802d4850501407032600446d00d00130075104450b074114000700c8a51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962947284 1250 962946034 962946041
    0x8040f120203030403120213060e01090e130c0e0105030a02010807090513140610050414060702060f03160f02070e180703050c010207091a060912010c092402070522 72
    0x410310016040482440700300740d441030422000308441003055043c03880d0aa2501c4031001d6900c0707001d0030710070922200c4950342d00800c000302c001c00c0c28280d03521852134102441d200c190158181214012114103008c83e580340b1881003036068500280c000c00d0108040c0e030040d2040078020b400d00c003d0040e0300c3d000142e00e0380c5100f0740381501300c409000400c44800e800481e030420040508001c0c49114030f06949000903500a00317035000c4481f10003010020411040205e0100d100705e610281d00414002040750741e881d503c80045010300d0b025104514400a103001c1140d98100340b40341080141c11200080140f0301c400b141c2150000c6a000d08005a00303901d450103803501200380e000b00c50607001142c06c40c05568040c40581f00424801a091214041d1040f85100002c2002c0080f84a2031000c03410003403035140ca5010500d195400c078020000700310b10100203031200801c1d00ca00f1120060041d61004002071000950801d002d66030014000c26080c80c04012600f0320050b0002c2100c0100e001003a00c1030860301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962948534 1250 962947284 962947313
    0xb011715060c061e0609040b04170d18030801050d030e040f06090c0c020a050d05060a0507030209030a0602070c090b0f01120b0a0f1a030405030d020918070807110c1008040f 76
    0x1070329007484c000119031043c04520020b0049228189081c10030001c580081c1d1640e601c50740c8181245941c0b02c003814402d041d40142110300c00301c0362805040d00c461582c109800e009a03030080c1c4032180180ea80d002005030700c010151008001408517243d0f01e245003865005128503416540011900f240c40b040c1c0c210440700445243e00005035040450800d5041403146031010b0501541c111000c056180c0303030030740c3c1c41d10080d00740030101369584002021a4800d80c180c4481010003015145010014208000030307401c14942902e007140100c2d00000d10010a200d42440030002038014042001048015540c800340e51040801e41920340422643ca55220ba0110000d00802e08000c0c1c1d101e03007000c841560200010b40f044240d04020414000401c100106031541c0340640d200260359544110045071030b220014031802c0813201c1c410103101d00c803a00060321030701c100d015580382c2190350720740a01c10381d507120301482d541c1c0c100e51055100364640c0d219401351548a0300880225a4229a070382e0f0742812003c2d1003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962949640 1106 962948534 962948551
    0x90f080912490c03080a062d0308030a020d0b060a0503182b1e050d09140307060c0f2c0118180b011715060c06 49
    0x81041800ca040c0c02c2c1c00c03012540000d01802010311040110086403000001480c6041c403031055408449201c09100445141c040384800d40620510704481124583c86004c804204500700560081c8507400c00140da541d4115100740c200c600090f00c0c544544d00030040004100e40c8a030a0301c0c1c0005541c20300651602421034014a4001c01040f40d04400510b8501201824010344040c0c0b503102403516a0490000c07100d0002d1440400a03c2040100d801405048400c569551007a00c00912810b0307503260000300007201c01c3c60364001d03030403c80308a51102d2602c8004c03940a0103c04103462141805103092152464801d4040c074060303400c80c07281e00c1310020320315580e00c90810784c004211a5803202c1e452540b503c81802c1c6070081c2c00781142010303040c40c45148013940b00301007903c20349034850700314256511091948030b242c3d1103100380c0546c84401440707038511480302803065501a807181c = true := by decide +kernel

theorem cover : BRFrame.Cov 962769784 962949640 := by
  have h0 := BRFrame.cov_init 962769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962769784 ≤ n) (h2 : n < 962949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
