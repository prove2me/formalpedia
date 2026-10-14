-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3619
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:25.561048+00:00
-- url     : https://prove2.me/submissions/ee779aaa-b2a9-4f29-b3ee-754ed420894f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650719424 ≤ n < 650899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650720674 1250 650719424 650719439
    0x3060501050904200d06110408061506071e02040c110d1110020a02120f0a090b0c1203040809210f06060d06151802130509070c0201050904060b03011d01 67
    0x1018803c1d0703407080e40c1480d0090745000d16030303828000321030898001c10301ea000c610018200e4421480e0700c0c030590568030740307413890030001a2903c02c2c01008149060402119036150351103400c15a05460f038054116101034001c2d4034a440103103070a11019510604100c0d6860750707160420340d4860341c00445000d481c00c0c1c482405060324104440028070800750b100c4202400d4000103a40a007804d0441481500e81050921503c0907003500302c19000748419500080351104103800644800042001e00382d42410112154406510780f1020713029607040c400000f0001c0c007040002401c9445020009140090920840000c0030a08911650a5a062083c0c06820f800030070005a035a214650082800080c1072840e9074010241003402440800000c100030081129a4840f080c22420059182c0058580b111a000c2c0e958488542d403245000e130165006200c101503004004c2c01c04550282030032aa07030b00491000c54010401540301d095404404800451180f03042604503000c18007030f80d034a1300c1a0b62076104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650721924 1250 650720674 650720689
    0xc15010e04030914090f1005040203090106050f0a061704080c061009050901090f12030603210f080601020a0f020f10120e060907060c03050409112706090f0f0303130306050105 77
    0x7085030b44250301c4400031b280c0800d91024503510841c40e480b10039480da40c03000403800b40d8009403110743c40d80c0d455502c24882401e185803800702c8503000301d84089a8520302203000e07205c5041c0e10005034402e10b10030005002d0001c0e4800f19046405614201c8140b460048084039040d52540640b201d070714240004240000c805016120f100e41e0003846000110a443e0341c0e000d12255450411320902d83c0721100000800e19112640144144404005150340d50340c2000070281c540c052201028000d41000b8060643da000030707a00a516441821450741018030300000300d180354041c0700305501061000400c0130455105140f8600220050410300c000c8400124031a02c9410031918190f156004031000c000e01e03485100724168003402410328601e05038541c1207960030344030341c1200288100000503040346215250510002e0a401d280280c4c3c4600d440800020064481c40f10007611039000d00ea828000d50f902c111507025203040c0142140d41d12221001c01c1d076104407142c40180c0d0001e14000c0000b8450130000c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650723174 1250 650721924 650721959
    0xa0605061312050c0d1b0f1410020c090c07020a05040204051c0f020a14010f0f020613020105190305010e09010c08060d050c090103060204080c030a0203030904020c15010e040309 78
    0xc15071819400c0034410b0708003106109040e2024401e00c4510b90503520343d80b00c0f0529440c001c5c0382c80210b1074440205141c0340001640038810b002080e01081040841d0121211078940007122403452140460008a241c29860801d05904c0f500a00c24040c0c1d10a643c0010110144241d034042c04a560780d400300402c034003c5100d003503006003d909503100070400c00c040c650b100364401c0c00362502108040c0c0109040540c103800001500504199443d080c1d81c02558880e41c500d0b29181c1341b807105440303800c001c0d00c4041c0906006001c2102185190840e80104146c842128090810403002d02c94070000901400081c0b241405c025000c00216210790418040c2c01848a180e44810406440700c0d000c0c04200d03003a0b001d050300e250250340384240450f507560f2102402140525000f41e291420403091609041c0c85c0b09915210350302c001400300c01a1804404e4070801c28088400585031034044028508203c03000e07841d07050820302c100001c1030480d074041100740071f940242c1d01d0024042c2c036444001e50009228 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650724424 1250 650723174 650723197
    0x2190f060606020705040e03160b070516050d030e1c050c210a090519060c020f030a050f01051005091306020405060304060c02010605040203070813080405030a06050915040b1602030405180a060506 86
    0x3c000303035404110300682d1960008418a081ccd4604049810036070511041440121a260491a2007404d013503414040c110302c11400d81c02a107405011384000c3c42c0c1459040d4110018001b0100d400d90300050305205801591720202e1400035001201035054003d60300c42c140f1078010400044000c911414020710001d0303c40200b1605401c07440c18003205070b4201d00f006400701c3e4480a101010440703070b2818440400c1151080c0028a440d020b955101402c4d02c000815200d800c2d008640100582d030390785003401e5000014004584005002030078600d010b84102c0c0c01003500400000b0a0204001040d8070a64401050368001c021064654041005078030056414030000b4840d4000326201051070390307144440350310440704107140c2650b80d00481d0800c00e52100030b403030003035940c0d0811403051420b002e4108400140e814044181c6419aa01c80c2540742c080d10108000c6145164008002c2c02001182c1c040c040050082401001004951602d6141114119100fa007804000a6a820301c1d605441010400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650725674 1250 650724424 650724457
    0x62c2b1101020f07061d0105090c1504051206041712011502010f0c03290907050d0608070e090c19121106073002190f060606020705040e03 61
    0x2518000c4401034404403a040040d5401c00141004a0040e0020b00c0d00c144250800305890040008910101e9101d00098405906010030040c0590b4041800400e116003101d5a510390001640c01806902554201e6508640e4030280744102c2c1c040000c00c14491031151080030410000c1c0740500185010703140c07070901d00a88590040c005c0c0200c4d42c0003010781040a200000f500208502c988003540c4044150303401080d505c1004a0a01c00c01d04100885588030a01b40100000b400c0d0110307142c4040140300703a04026000ca00445149500e030440c100400040046961f000d4071090200c0d42c0302c009440d0351300140f040202c40318003800c100c41c034001000e0742c43c821464040e241045100760702814400c210340c0b18000d03007540c6000313543c0d407030180c00024010902a560420070b0b10760b984441d4645420301e4078410b04c034a0340e080207990008084074032107031440c004500e001d018a4a208000f02401c001031042e401c0074008114550b00003103520440d001100c080c00920032508486d40c4078802c10306c0903003c0622 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650726924 1250 650725674 650725753
    0x13020a03030509010512150a06020303060a0b03100801020c0d0e0108040507030209070e04060315050c1303170f0c06040c120f0b071119050c011409010804062c 70
    0x202c01810380a50103040691404401007003040d01c405049400040b140700481d02c010706810424901000341203140001c618505200001404064640c1b1519404810000010380d240e030660b400c180042820000a548440030080550744500b042c21041c0005803400080c81c07080e40c8a440414000c82d0020080d20b001815070302032003002d0034003d0460090181d2040c2200d5651114800c2c90015809410310b691065110107608087d540041c00801c3c0a28041c00021140b64802c41041c0450f80d00246140448820304111110f9002c1c0300d880740d052035008980031520450104402c0d1056104803640072055444115480a8a0003120090318640d0300b048010005140b46411541020140c200300460311b80b0440e6080c6040320380c003c0700034610030a10300c0c0d4080000402007409120300034202051a0f86030140c082405020340f40d021810410010081010700c50254410940060074400e2841e04000403400c00701d0b00c07411030b0000c03c1e1900c1082038098001030703201041295039240340c841791090750 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650728174 1250 650726924 650726927
    0x1103010e0609040615030b18010203190b1507060209090a0e12071407060504060e010c08090d060b12070e01090506030a2405040c06080a0c2f0d0e030613020a0303 71
    0xd80240f003220440d564480b100345820201c000e0500551140003105281e190000c1d00f0704155000e901c80d180f5981c014400d114082c0d0703d1420700c965840340707001d001a0517014240000c2c02224400242c410000380000c00700b080c070129800404140d130307094600000e286c54042801048804240700c0314902e4220760b00707050354290907000a041c0305000386076006040611001580c240b03650781e88804045040003030108032030b940014a011105200b4240b031031500144d900e404a083c8180301e981c0744a0103403001e80c201041450b47c85041c01a83c041c05041d02d0203044a042d540e52803641c001c88504100c400d00000740c103c4180111031040c14040c0241040070415507601a601d0340b46074076403500d0342200e00940c0703501d5098825544940c0c0501e5005c0802864050081c01c52840603140842103800c0500705449150480050784203210502c1d440401d4007850071075006200c0d0030703c82c0c1e20000c0c0110040090300c561720034204034107036908a054401d10f44440d803100d4050506200025000030b030140b010804070303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650729424 1250 650728174 650728189
    0xe10080d09033f08040b2d09031c0213120f0f0c03080304030503100e390f220806041104110307080403140403110405070509060a09091103010e06 64
    0x1044a2070810f403454003000011010726041500342000038034244204030038040042c01c12038000072042d170348190900c20910540c0d031540f003100c5070711030000e850004074218803420012545d140070441c0b03450640202181401000e944071031010304551401010218481101c1c04244201075480380c10a410781003203540b03035a202d000715581554070040b120000004201c0c507200942c40b4612079500d11f5502d1505841c0000c0510407500b010303e110520900f0020340b0320a0980b4076614115103d0203042c40600c410400c1000e8050904603012118003188035101e0030201d401800c20394510b440420405050b050130301040c000c1c7d40c82000c3c4180e00c82c1c00843c02141040038000710044000e0700101c0c1c01f02010484144580c800e071020800140c69108100c00c0c958420581d44c2c0801e4000e50407482d240c556107070000035006071441c0910a558507804181e40074007500072265011006807150b6150204a4405040400284200c000e814103203202c44200c03042c0001200e069628980e00582c49803200410300160 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650730674 1250 650729424 650729483
    0x15270307050918070b070f020f04240315021c090602280801081c20011d0105100312050706110d0b01020c030607020601030210090e10080d0903 63
    0x1406100d1000c1040d03182c5201c1680304054004400488280d00304807a481c040c07860340300d8610070038140460000182e00146d8981c000d50100d0742041003c0225000800404c041000409000200b1387c480b86024610380f10300007200d0040442c01d00088040c0280000d074851810b407540c80b0380d001440181d00e421142e02c1002c07414050803005040c981c80a11003802801881c6ca070003042c22030382c1c9a590b03207141d0003003180340035250700310280c50b410a2a07034480e01c005000050544c28019000390442c5840034852404507404800c100174000d41008002d21280e00100380100c602650900000418500c07003907039151f085036884424900380c1543e0010407152504140c00850342c044c1c690907104403828003031f03025086011081e03600042c0d0090100c00645042c01030f040d0307903001c6c1e007000041149081c3c000c204030741100e4054031219145030000b207088076070b1706154001001381c501c1d010a000500410300300c1802070ba58882e04440c0182c050130403d4a040100344802061203100300c0f6400d124144d0022034100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650731924 1250 650730674 650730679
    0x61214060307230d030917010618020f0f07110a060e0907080601030209031005160311030601110f031303030e0409111c0609050c0117103507051527 65
    0x9000f03210000144001200038001c1c0c2c00260074400500c003d681c1000c0107200f25a4140c000c101042c90988402012104200d1b40b9030b81640c04500c010f140b007007000440b00c02d00480240c0540d40c8045280684010228030f10b0680503e005c0d80340803407103900032141013241900c028400c1c1c00c0d603500c3c030808459251004003030604042e028000030201d030710200408803804140c1c41000c280b9192800c141e1110b0811300003141c1c101800c1801c0100580240d004580e00030b9000c1c40d003410203c400c00d401600d00f852140c80705440d803000103840b0320302500360400b10099911940d620940e04050030100002d23100c03400307009001d101510400035564900031000002c081c8151700719484015803a00e0341800c9882189080c2d0b841c4e002100d20f410a5a170013000802c3c3c10540c0d0381c4c128110b0801d99a80c40c40759940340114404540400c00b034900011025464551846400f4600246032f058410708a85400c1d0b544500c13030285540b90480c00c0ea0840c0e03941500e980034480c074100c07031021100200c41100312180030401174 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650733174 1250 650731924 650731979
    0x5030106020c061b060403030603050c0d020105041802040e0f0105040b10021c120905030c0c010906170a110301031a0703230606040b0a08090d02190206030405010b060301061214060307 81
    0x14584d00c018442c1902c070b940640c4000910600d107040046c01c00c494503c0b81c521408000c105800180e8001c1301b03a4080d11580c4050203c2210383c0000d100003445503030850740809140508000c40c1050341c140e040c0c180c0d5010b507001d1014200c410244940050401c01900241c0c1120080028a00a885518088441c3c62410940a1800f01d401c0400c842d601241600c040d0000203005030a81c00420100100b09001e20703051081c0da2078120000c14a40002a450708000c0300500402c5682e40c1a4000303020b41d0908507043e40e80c03940d50386040c0e40380c44886012142c01c001030350001094907002e407060900400151360030401c22141082004103001000301180d03803041003071001150b01800d0502800e118405626189400e0030490000b07803030910b100c445141103500c41030100e800145120540401680c1c107a0b015074580c0c84924041e070150109807141500104040000600d540c0c0c401c2850810003002c1c5020001c520f4600185501e0a0089a203036800d030b80091010001c06000704010140d442590b0b4410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650734424 1250 650733174 650733217
    0xb010210020f0912153d09200a030209150a08011d04081804180615240c02030f0610032a171609090b060105030106020c06 54
    0x5008903007181c0b20880300e440d004500219a8103000200c0907801800900400c0c007100e103281c08070200b01004000c40300c41d4219048030483c08507501c3d034035200c10890940101c04000102c8042c80640c009100d050382c0e8034100300811340102e50102c00f04c3c4110f4001001d00786440c0c08440c0c203034065441640c1e41508280807040c030302c82c0183c002019081002032552030700c0c9a5490321040005100304010740480c05c7e1172a805102c00a0200d00844e40c201481c1d0302200e58100b07a060010f0300409100c000558100c008161800c04c002465000c020340c03d4800c0644410541c40c0c14500300b41003142d001a03c000c40c400c04040d00c1190103189022189440201120f03070b0000800c01d414204070044e18038690070901c040b006d00400c81680104040e2200c0118500e400c06c074030400840f5407081510914810040324018002081c609124a100300281300700603405103551000300c14024802e02c6010b80e001142e0002080c041d6200c0d04c2141c1c1254402d0340184a500703c042c08114055126880c41c0c0c0b9413581d180100e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650735674 1250 650734424 650734453
    0xa0303052a100b030613060b01091205070602251a09120c0f01031a010809010e120d060f052206030b0c030907090b10110708030c030d061e090b0102 65
    0x144003155540300c020b0500d403980020000c06407140c02110038440d070881070400c0b049070304900001c030000f034120308046040d6107110010303640840c10340c1000b0a01c0b0301100701003040c000002100d02c1111525422101a00d6016030807080402c44403042038000c15140c801001090314810400f41c03500078440800e440c00e0300c4d410010720340c02013042c00d00700300341c1200b00412000d2600751000c00d51948282814840690100d0040004068041050b8107101c03418000c190102400d50255614007514000c50744a4078600e00c00403010740040b920001c1c45400d040000c20541031303824014044400c05854994045104603154400302451218000020358844002001c80c4290f0100c0307029240b500c0c0042d43c2c03414010704c101d00300140f64203d1100d403410070825203200e03118560300c00301404c00340c6403050300460090001030a0000340d0748120f400c0d11010441c60402400407000f0007481e02c14480401040b65120a0060058980c082d1200b5044001d80c080112000fa500000c120701d6051046c0c6607030000c50080d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650736924 1250 650735674 650735737
    0xf03050a020f040f08010c1412070c020910051f05040e1e040f110d02030319030207050a030503090601080601050a15050d05040b010f0b040302090411030f0f0d0314060a030305 77
    0x2054130740400c000c0b8204100c110038821602c006003245010314100c0c054103112046440741d076204481c0004a50002100c284c440c0700364040311035000706010014108450b03c140140c40700c2c02418424804180081c540171205220412480010340326641414541040f0b5409210010200346100400e10380b0030601520b441d190038807441c8596852132084110717082010a500a6000322800b6489621710f0f20050b0f60004141d074007000d0124118100c036605c916046003c0d0040d18030003081e91103454220810150040f010710701c1130080108440751030382d0b00e01900b940d4400a01c0f600340c01001c4801b0500906040d0802d102c10f080c0d20f4180300b443e051041c00300d1012a502218140d03403848104006102c41e8103464541c1c0020401e443d0502e00307013130464001800003200540300402e0381042042203051501c05004144041c421401980c00641d0141150390f110518000c0400009141144101d9070300030052085002c1d480140101841074150b607026140f0768003003c0400b100f082d0a84040100c01325140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650738174 1250 650736924 650736929
    0x40b04050a14100509012d02040906091a0328020406180506040c020307051207050106121505012c0c041206090209060102060717041e05010c0e0609010f03050a020f04 73
    0x3c0c00b1450300116140219440a4070842080c0d06002e103490b107114540c08250094a000841104404e00c1d100ea924020b104541c411100701d0306001c0d000640bd034039070307200f5070400049491580310f0103a0035081580360303500c00c02303030301700b1403100401600c0740070107000f903000c3d001d0320203840024200d4840c4600a021880c82c030a0081e52501e910402c403582c20580902c110321380c550b00044d410a265542c4094039080c10a4200407500004a0707040d09010f025040080140000141902e44c0307100c030b043c60130381c10280d4040304110a04280000800f080290f4803408002c2c034541a409814103840c1c20300d90224006801c1c1a03480c007003848049101301c01050f00c9000a4414040042e95140d2032050064100d0000c1c0400c5c15904218100035400d5001007021250003000c17002d200e040c1c0d5451400203003500c182c2d03156000350700260308000104071055021545081c0592511540340181d042042218071071000880d0001d0340900c00106818040d40080e900000040405030800700f00c2c0d02003848541144c4e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650739424 1250 650738174 650738213
    0x110a030516141c02030a0e010c06060911182b02040e07120201090b0421060608030301060804020f040504110402070f05030d0204061704030917011e020a090801090209040b04050a 78
    0x300c0b03c0031003640205401c0328094140061410042c9024001d4140500086268103201c0b992142c4001c0007000d40c8104d02405150004015030b0a2150407005a60401c82a040146030f00e80d07000200e510740403007261081c0b2030440000291401c1051501010004c00c1000c03a007041e10b48078490318100c414003402c80078000a1203020380401050000506400c602c5c0d0290380740b0541004180181e95501c11003032020b4449119403005a1141e14040c3c0050101d40e0054085010200001c610581e000303640a004030300840d10000801e2201d000c12003103c2c3e060754000d08880290036030004a00342500607100245c001d0b403000100e54055198907045078401c03c1c02808441e40040d05114858101c0300c1201102410f800410031850642e8010340f03407070418021540003116010000300141d40135001203c00107100140540341c1d007003e003240006904041c0c0b0720404225420400f21300c041c014071401c00c85070740082c4251007503215602d8200400d1406041a9841d00820010f03101240114126803000c03401c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650740674 1250 650739424 650739433
    0x70201031b26040b040f0c030611030a0605040e07091104081005090607020f06040308040c1809020312070f080a02030708180a0509040f060b061c09020a06110a03051614 74
    0x1441c55458442c0681ca000000814501c1480080b40034026090341c0542d0210a102c501034081c20a0f03141c000482d44010700480c101403a90802c1d10560001c4c45c01441c42d00000c0c440365403510100000e50b403a905c150341d45a80001e80c10132000195400c5003a00c0c00010148034680390702c0c0c0158070700340421001104003090703e820070300040c540c040048507400041440036003c0e603c224402d840d199080680050704100d420400305050040d4a80c02c1001820003000c2c00307107606148040750028103e0007801368400d0007400c0150b44804079050440d2100f9a208000d5003a50f489680c0301c1d03000d40c02c0035080e4811440706003e10400160001d0043c84044818000024240307001400c01920718107035000b05000c0c0c1060030910000644a1702c2c42c040c0d10307500520101c1c4c84400e080204425014548000900d03904102c2100c9840d0038691094000358001d56149450342e803180d100fa5001700da0800040555840101306c080444c0c45003000d0314031079001790801e05800c1400c3c1c507824605019481180303100c1d0070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650741924 1250 650740674 650740697
    0x7030b011e05122206050411090414071a04030f050c030601030c2405070308070c080a0c03030e03090d0f0602071506080615031c05040905250e0307050402070201031b 73
    0x59101d19440072080340c12080304c421038001e00d0312070301401400900c6582c48001060030007010312a08a60040040e02940d02460b25040a004180c3c114288402c1401020070115000441000c4950000030700c1c400a0316151079681c680e6110074000b107050f0348074001d40c02c14101903902440414001c50003002d0343c20072607003806043c1003002850702e40701308000d00e480c02c44454140c000041da80c501390181080340055880807400d840e008400f00004054a4001941c0e41016800c5a610a003260007640c041000003001d4100c907a072403003008215980f007045e010b044400620054100038840d07100d80c2025041c140341361349440c588a00e4040303066420341c54901c240000e00c010011203a1180340c1070300c18403a001d11500440d407540200303c030b01d07405032804441c410b0351a070040d4200e500170710408030100a145030a001c50340d45100450740d10500102030f100010505c601c201138540e0840001000360008c1c61a00c0c040100039402aa0124107142d210140e0104205500c0704482101001e611a001210b5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650743174 1250 650741924 650741947
    0x40f06090608120a0e0f0607020a060201020c0709090809060c07091a10020309010806060d0e0f010c17070f0f0e030d0c060b04142a0c0a1b0e07030b011e05 68
    0x10401d140f1090020014005080c005602c001c000107aa84181d51821070f885501000c18402c1c403802d10043d40107143d481c40012440c0d8158010038010900c0c0e0250380c0f0309a1035420220540b011004041c040941c141305078141c0e49030250007800c04454513001c98101956440c0d501d000c0e607507061a4000343c0d60b20080c1d5840320341070200341c0e4048241c0302e102440c03031b09807100006403002ca000fa082600a03200419081c000e0071382c035403007040c6510008045910120007094128042c0110500040c0000c1c140e902001401d0b0384080064080d0400303480e014000c6c003010034216082d156502d905c404000d100d03559154140c409100d00c2d0010f80311035440700402c01c4a401c10788151a20034a41314003a070301c1c03c505002c110b182ca418580e0402c582d141c103da001402c01c50811000f140744400b030701186900155480c1d0800c00081c02c1c003181c078800c021141240c403807460303007203400500b921810070000c12450024554a11943c01510044030506081194011b40320021403075006003002c04003c100001072a07164003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650744424 1250 650743174 650743183
    0x206010608100e190b030a061e0902090f070e060f030906100b07060203090a020405010b03010303020f0604030504030201030e1c0f0e03030c0c060f0418050402100c03080114040f06090608 82
    0xb04400d0280e90342a01d00040f424901c40c000f0b0030325540140d03000c002e400c400241d170015012800c0060171191003550307070f090043c01019041c1000044682c0c81141c04c0c141c44960280d030704403e40040c924041a600c2400c004401e12005180204001103102800c25603a100700180048442428915031a85441c11a603860000007604030303c102581039004002c2800224201c51482c0e9000e00c0150716500d0302c1c2d400602d002682100254403030300303040010412516482c05141200c0c0139508480403140080b42c2140c80d400103a80140c009102000140095400703034205d00e10084004007120050002208550030702c004401a29000404d004410880e4030ba2000341c0549001048003e1890844003a451031b5a4201d8100524051400442c5400520720004180d0f401801011064503107c441100c1c158000d00c01250224400c082c04c40381d41f00340c0c92098a4014a070b9034161030381d4070300f81d081c480640800d9410400c80da602c030380c407089030140c4064280200350042c0b469041c007140550402c0020b80c01e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650745674 1250 650744424 650744431
    0x7150b0f0414060d080f0a051c020a051206030309041d010b01050c1b01050706060308071a060a06030f020c030c060402010f051222060513110d030c020f030106150206010608 76
    0x540e0078407482c5a5480902c52034580c1002080314010b004107007610300302256010311000b4443d60030022526400f0039401000400c0040c404c00d5958860f141806024400c034050134007048001003086c0031402d070070030110744802d8004d613000702140d06044c4100d0000b01074804c000400d100311120f10300e20700cac1645002d0044175024403003402c0140c10440c0c5000020360314039400502d90a021000142200d2690095084811140c3c02270424040c0903181d06001c1e503941c0c0203c000715001d80b0244040b0304800203122031140107403002842d5000b0f45150800440251440e41416600c0560070403081062000410060000c09803410150130300749400d000151801144401e900140441041411144aa403d4449601507001101c4841d050354200c030048084001f20002448145000c0912240c0f2000c4039203200d625120f0b8000c1c1149074003160500c4201d040b41c990040100e1161100b9000514006a20084190300640000f03201652944c0001902000d2180c120158000b031005000250344509650761 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650746924 1250 650745674 650745679
    0x60d021611091012260301120507090207030e1203160c05031002070203151e010905060a0602030405031f0209060a091503051e070c0606060e03011b0219060207150b0f 73
    0x1241483c01840e40f030000c61409004103040c030140200c01e81074045d0b03080454440c01c2408940d07169030b120140103000c2115140705407411f1107024000030380542e40f8001c071442d05505a03124240104240d003886407124540340d6078045030105200c3c0141603025044c1d0b0900c194010132404440c945420185401c0801340c0310102c0700140100004000350f10000782c922001d803124640700b1102d0741c2c4c40c500d20f00342169a4100303e8406051310700000c2c032100396403c00ea00440044a81d180c1d0540d45981c1641e80b841144500c42d05a006600071101070306520000c0c407148400e0050252404442c140090041d5015480da0408203030f000f80709008101501c260803000d1840e5040030080c40c2846450700401d002d10861092815048100045a0350f1080c148002855407101c2d061200c90345580003c3c1c80d080744600554043d610f0203964664000c20400c25142d0450310b500603185d8101400052807003101c1c01003056030090f40810400c40001c0184074403010601d00b8003c001102030143d0b0030440d26512280f0f00c01d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650748174 1250 650746924 650746951
    0xa03050f0403090e090f0a080307110a0312021803030a050403030909050c07020f0f030109030e122109180f22050c01050310030f0b0412050414060d02161109 69
    0x1e40240f41803060394004e40c07000c0d0b41680d80e0705241e441c10b45122100c892500407903144408000702d001c09940a060b01d40c640c030900d1240b01c0111503a6484501c0080c0001c6c16400d84c4184e400b980760300034040d20b503c022081c007040a040021a1441c1d00440e40e1000007400000c2c10014164411000c5016120401e0f0510a0742070640f0034200303038002d010f40684140545900e0441640d00c0340c0641d903101c00013900902c44281706041c064031140f0b80f10705640c020b6180300c245150801c0003044845151690002a080b404034001c0410459004001559040f0403480700254080f158000190721520600b00b500310b05140c9030f01c0b2044008000c0c5007025004500111741800240c0c08540014441c0c07080c6041c0703440360786000710380e41040f12a0740301030410254200280144032104540501c510f0160343c0340d03c60140c004100b02d41c80c3c4603511509080f0394007110281504d243c0440100821400340c500035003801d07040459031005190b01401111200c0440080b0400f608050780c82590115464140c2d9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650749424 1250 650748174 650748181
    0x303030417090a090911041b02060412090806100801060f030819030f020f0304050d0503010f030f020103110c03130b0a0f111603030c150b151804110a03050f 69
    0x900e00d109190522010581002c200a0071640f81c0303510b07003001013840100a00001c0d04600740104142c0d08502024000c80c00d0940a03c00007090302010012110b0300d50041806640380d4544500300003a0620030400c0206200300016802c074200003250013031030740341840b602c0d281c603211415084505507842100400802c00e8108046400041620220040003680540e5910b0721541200203200f401c0e0aa0700c45880802d9800840d00064042d500ca24030440407500845a11078082d10640424402c10f0385020020740240002000150070421051040c1008161195801c00060b103603002510140d01680c03000c42c1c24420002c01207140f8000b0a49004500d1a280c1c840704000c104030a484170705801c5c0903440b0700c0351190703c80801c250b0030501121031510105c6504ca140c014503806c0001c50a45100a0041d1811100303242c501c80c500f1000310080c58050b417111210030307c000503007100d40d00d01040c1c01c502a101c2810b440e9409006580c40c00c0c412003d544000e18900582154809004c2c42001580712040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650750674 1250 650749424 650749433
    0x1d0409140d08130c1404091407060206060a080a02010c030507201305090c041d0303070201051801021216020a0c150f140702060702220204210b06190803070503120603030304 76
    0x740c2d13050f208104000e00ba05204040400e0240200e000c005007041c0300c00940c140118004500f080c01d580066082e80c045440b040c040106007200b50140c040d070b0381c1003400403c0056014142c1407191503c6410040c6c00c0540c2ca40f1107030843c2c226003d03403844403061000070f0802454981010340b001c0105a00400c41418900720321b42e1348107107003038000d07016a3f83c0385801e902c4800120701103590300c2564022203949103481d8200902800e0140c1d00559034115448900381c03a880e0600a889194540d5140ca207455513400c001462180c604510722001c3d1302402501c1800b00d4034040181025201200d0441107603884008000e00680e8844c0e2010f08100c0e08140180004d0800300450320034940449481e030725a0041e000180d28852040000305548066281081f034140b1340340c01078000c03035034800080b095000801452460b008500d038402080000d0100020f10146060981b100351500d154816080d0350780c0303c1d1200c070315540c8045070030386856001013900d403420558942a598001c0080d0302541c01e50410790b81e03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650751924 1250 650750674 650750693
    0xd0801060305060a030206030c091c050c040209060c10050601080606090a0e0a110a0f09140609130204080f030904060618230409150507050405011d0409140d0813 71
    0x604010142c6620114075a80d03140110302c4085c40d0001c2007076540b41815109600e090b4003900350300303020310303200703642003880400305205500d000b40c020014280b1200d1840c20071009503c01d581c0a41c0c40f6000b4807002040010400c89101e01c0018200002280e042820000d0018800101180d103c4c610411003441c081c1c0365141850129400007440641c01c2d124448c210000d401441c4842500c0b0001042841201d540314003084441d502e40e8803042402504c82c0c00c0240c02070240500345411000c20810126141041109242c40c2c102c1032400500b040e80b0382424a0414221112020140d0300116500d141031515204403c000c1290b4140344202d4510f54507145000d100521442503114800035000c50800519a16550764007030007402000302c811241340091400484180390405e0a02c0c107030024280500400c00c40f42a03900c140c540d210408800c660408800c006200465042a04c4060140c0010b6080001880c280300d00c00c058915034400c01c4001b030250310028220062255a4144103003c0340f0b1225 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650753174 1250 650751924 650751929
    0x504170301261c020607090f0605030c0c0a02040213170102040501090501050c0f120703030c111e01020c010935070803270304090c0201060f0e04020a0e010e0106030b030d0801 77
    0x21100d8076881840d10b6101d04102c00361000d001d0584005000300c10b030640c081000c40c0f14036110749961400603203a4041c1680b441141c0601d07000302d001000450310400503040601200d4151500712112089a640490266000616002d4110b80e5000b010301540178614011805900303008001c41c106490240000c001924522909040c403c001031101544101031150f10101c8207014121faa81e01c038003c00707400580d4004107040d00002d06d0008542c0200788135082032103000700c4250060103140f40c405810000b845500c51840c80540d030030082000d84c088280268202d45001e1010020b8400140a51542c51113101c41e886942c801194010b0701e40001c1c0300140d900c0c07941c000142c1c5480e0b59540603054401205030448554a030396140440d50014130000003441030742e800c0304082c80f159038003c0040e401c1c1c40c0c2d2130007078208540030f42400b400050500200300e540103000800d590280e030f5655420340300300d040a81150001100d00401440100c0c2c16001d0a020154184c1c000c0c500f14100c00f4000f04081010b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650754424 1250 650753174 650753219
    0x3140d0e0d02240301080601050405060609010c031808072d03080301060806060d050f062d0405041b0303020d180e0415060b0d020903150405030f0310180504170301 72
    0x40512900304841c0c6010f4080283c442c100b1598a584940701c15503110024402d00e44100c0c04e28001840c07906116084e6502c0800685622410744043d540c1601c00c01c12400110b0350703800e10910700141800040029400a08000c20070011481e9070700078540600035882582210008002d03000c00c0042c2940085038111000e03440c250f91107440f2100092218480e450861500c9400d24051007074680101d41202d005200850300b004840610b0010070640407544810410603134003001c000000c50805401ca20703032103481440da14009040e0146103c031443c0c4241c20560040c0e00c1108000e6100d40c1180c0d140710440c40c01902c00015070318000345c0740307010940108028188400103a800b145200710303070000000b41c0380c5960b056440c2e00100740d40000035040300060510030320400f90b290380c00c0d5500861150055030014040c40c039120a0001801d0564070107031070032812400f104000190b4010701d0514840004001c3c2000c101e50501d4203040c5096042c01081600d909020001003080074801c0540c0c40640c51032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650755674 1250 650754424 650754439
    0x602060109091b030b063105060d0b01150207060216151107090b0405060607050d050c0a0203071203080609060a090c120906021b160909050a020a03140d0e0d02 70
    0x141e141020600300c0842d440303103c6802a440100c200400b00202d944104400c4e01c0c00142000d14654070004010504003141c01c4034410400b00b1144040c070380060350300240241150324052120b80d10800e40b032400342d01c1604514040070240c032025906100d05002400c1e144001e01450040d46081442d18419109070b4404008411640c0745540c001c580e0104d20340760060980e81407039600c16810002e0303d68840c00c54822490704c030016611b4a4481e059030302c3c10340c0081c000c1407003030380000c4290f4007941b29018850081c0704d070450001c016582048400064102d00d034042c40200610f04e4040c0c1480401782c01584194103a0003003207825200c0108404c02c40c0e80d07003030010070500c0000500f55202d60b0303107030211a007a50500c0750001c240107158000301134422030702d5555180c42c1c0d082002103032aa401404070605605084004112416103500004000c41c02141aa1540051680040c02280e1942d0007140c14601081c0d288405590510007003002008a0a0202e03094070000001201c140310140001d104081d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650756924 1250 650755674 650755691
    0x150a05090c0a2c100c2301140f010905100e07050d0506091603050c36150409111b1c0203132105100504151b030b030309040f09020f0a0602060109 64
    0x49444145da20b0758010b04c1c254140b2071070306455070000441465403080d541c24454040c5840b0407159a6030f10812003070348800b40a0742400e4090002c1c01c00135040c8060b5141b00d041c089400c034a090140c6010b080c3c1500d90680c1c81d6144c0e080c2c1c40c00c0d9640104058403c139000c80401100307006200d4400e06a02180ca0002000d645d00b01c441d0b40b603070048180202000c1541401d8104405400d00d03025481a00118807086115611003040340e80c2124088a007002c0300d00f4441000980100e07003107803082820490071941060004030248043c0401180112110740c0107810300010031284440e0010201c80074806189030000b0b2112411401c43e151240004455100e02c202001608400c100400c0b08e502005a86510381940c4054000e07000a507802d449140d45100780b4070f042d41c038902c03441c481c41a515070b10f0300c6800f400d080203400410103407002e00d0309800300f002102c00c140d0303440c4200c50844c5610080002c1c1e80146005010071032168010144c000d1592000c04c0c040c503038000985904484590360081036055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650758174 1250 650756924 650756927
    0xf0607030b221d0d050c010e01051017030403021c020a06020f0c0f0301150303020703030906020a201908010e010b09040305091203070606060906030e070e150a05090c0a2c10 76
    0x12240110f41000d00807201d0b6002c142d130b4003078020720540322030400921000300c0c0742040908854094a800c03410b40d146035002c01c60700f10020044a00c003003400098a0803e6500d4020803400a00c40c030b500c12030001a4501c0c001180b609006010140041d0b100410310361105480842e90b0728001c0350441c0c444c104000b80c00c8011340d03007504071035900440c440440701a65a2031030080d5551999000482c0820b030814070124a1a06c00076444085a81104201615804000c01d511504901c000e100b600540c0c401d40c1810b0b00302c1d0042c446c400510300c03800009022102c0c82c44035403c540c04903009078410310700d1005100202e40d01c14199255058115085980e12002120981c918407624500604d00c1d07051000c00180340b03420840120464000c0d45040c41181608010303591540518040d1001804592010506480740314615046264014080030682030310303080002c0c0f0000084842c0c070b107519000181d1b104142e80c040d24500b0444014144c42000b0340e41c80700100e80a18010031054001c800c41b40355075401e80d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650759424 1250 650758174 650758211
    0x102010f1505061b100c0f08100e33030d031118010203071703040201030507020604020d080a09090204030f0215040e060f06220e09070b18040902030f0607030b22 71
    0x201d0300c08840c480c40005e01306001038182907031414041001d8507040200580900212403050b01e02c001c003103080c1130820850fa141c4440241440502035030703c0e120301c940000540d02888034002540e050300d100c4040d44007018a04000085c600c0704050401102e45074070aa0102554844d0121000c40c3d2017a2009200403072a42c01101d001070b1902044510310080b10303081c0001140034038000c1c0c1e4144829525608181d9030340710180d50094200304048a4840030603414005040b1181c2c01d451f01c03002043e036812504042c0d030890340013642c129200c607032501b045182c0702c0424184c045581800c03900341441d02100c01c15452004280c0c900587c41c100303242080d591041c08441c0010401300c0c00420b1410001124081c104041c05106110011070000c1008a4030026000307084030300100c005031500308038403010080050000314041d00306441d0a500001030340c0611081400c1c81005008000c240352060006040e030300d032100400e000b044900003645500800d0724030040030f0504900c2c0032031000505030816031389 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650760674 1250 650759424 650759467
    0x10020d0c0f1a07030f060b030c07120912081b070305030d020307030609020f03151e0409080d020f0d0c030204051315050303160308090f070614041a04050102010f150506 74
    0x80b00030450810070080e40680c00000740a6070f000c010000c1d10380340c15000503148000d13981c03400401c0092100c100000e41d00b0b0500c500c2c039030ba940b40c4a950305944006078801d0706c4a61408545807032010601d125251440e035404011143c0c18002410308034039648915032684150811841e03001d400000080005004e44c01403401040c09200455445881454410540e0000e8a045140c1d407442c03000c0c0d4034030345042c10302100510740903c076803609448900304002c010301c042c1804070381842c401d000d09a176a5205101502032900503451190340c5140352551801101c1c100341c80758040c984107020611003500c9040d07901424982d00707440020001c5c8100c00c00b90b621180d41c0e02490f4580700c00a10380340c010151400e8410443d100361035030907590321004040d54440d04108040b405aa000c440d0400145103d01d04030f80d48031450051092800e0f840300c2400202c4202c804130f03c8524880003808000c00d580c24415000d110315250801c0000c0034110b40c0782010300b900c600c0790764030480000c12000007020300c2051400c407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650761924 1250 650760674 650760713
    0x25030b0310020901020610180905071707031208010b180420180d0f0305032d0103021c0c140f03030c07031109010b0702150d0c0e10020d0c0f 62
    0x2070012800c541c030300a50300840c422401401514003040ca5141d003ea41c5009036510701c003c580c11800c1031185d00c4010b09008005032207610540d0300018040c1c40b01001c0d4501c2c0c2c0104805407aa00b411030401c00e0140e1112810305003000710b03000042005008600964826000c0b00541303103e004500c00002e0060200d5000c031040980c44400a0600d540c0b00b00000d1114035800080800344640140c00c202d50701540d00009049425a00d640000091041d0021039000e00103c07a20f94184624500030b48100280c086038405407000d01006009503d001d468030910844041c1d02414034200316526013500840d035100d402402c10051076000c10540d5654442c1152040150449444014450380140c2d81c42070f40c84140c1301c1540b0034151400d01c1c107084894505a8802d031140614108040e801d20040c03a500a2101602540501013401d20100c1400755135021203e640e141e100d807014041c204130702e20f0b4240500c1d50640d4040580c000c8200e07084417a0208054011400e07100030b40302414050007003010540c0c201c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650763174 1250 650761924 650761933
    0x30807200609010507030b030c040b0103060e010314010b040c200f032205010302070201020d0c02060702060f0c1626030f04290328140c0a11010525030b03 68
    0x524140014801c2d2003021074000900c05034903600000d42c11510349001c01c035056042880c0259440c102504179405420041c58006007069460300d0320300c0700b0142a0000c40c1d804503031200300e10500c0c0090080100d28482291f0400101070712050141c00c40a6a01d10a00c2111804013042c0120606200100d113038030842c0103499984846e80020803403403140b070700d0402e02141280c2001c1019482882611035095041e00140080c84141c4015203154580c44d8040342d0080081122a0060310b451001d8810050140580340c0c40300034020f151780c1050b010003100c40c1d2900d03850f042000f8003000d044004139100c0e20141c03100f0202041d00c0e2590300314451000038108840e400a0001107070400035400d1203a07251021212181c8486440f02e58042e84010f4900c3c3c0c800c10300c071280b4280b000c0455480f5104241c00d00c0d10001e00361081c8104500244001c9a1040c031544000c038203803541c26004202d0102c4012040002c1200e07180c1001d08d502054402400c64003c1c000140400406c0303400307603000316281d200040456 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650764424 1250 650763174 650763227
    0x18040b03070b0f0c1908040e090a0203070603020913052a0f0406090312050406170c13030503220810090201050c01051f0b090901050114071a01150c0f030807 69
    0x11450340f04c030340c40300301c42e201c3c1c0794692000100e41c442d18049070350300a8500d441c0031301e003440303400a02c10701510031642d6008111809006036401c02402c0001c180e01d850251b20b900e403403c1000250264086003a580a003400100b0415410b001c500e103c004c4400f058084042c40c0783c5503c00403602a143e18042041400a000700e68140c100c2e8007a000c4911441403440b942548260880c0c1c240903612604012810220503032404070361118036154000b0410000c541011318400c8001550f290b81d038415a1349400014008903014402251b0106103035018100f0603169290807400e40d2345000b040b100da008a5074811207141168403d000f201c400004550080c4200d051039940c254003040c01c03052120030591054400154003500c06c040d680c25180085c180c481d81d0786080c1c015503106030f640d080011100010450000000c4d090401c4c0c1c40e0800d4400b28500e010360401d0b060799620b001c01440c4a050145501000c000622690001220039034140b6100800b13444814058840c0144154425111700200185 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650765674 1250 650764424 650764447
    0xc120a060e0721082a1525020703060203100f0e0a1803020d0831050f0a0f110a030c06050a0f0e060d05090f16030605070518040b03070b 60
    0x9501034a0031030300c0000040c0600144981030181e01d06004111013801d2006210514001043e1321400744000c0c1c8480c03201003010503490406e0154650380e0304180303400050004416041280c0b512010416041c00f0320610101801f0f56680c0e19403000515440c0c00200040c455a81d031801c01000340980701c15041240d03240d25001307102d030034115220030070f81e89041c0412007500e20316040c0c0941c4079010b4000d803544490760300d0201c5a150009140c011507456050b0100302c4481241e4040c907050a941c01d99071070426517407401c41d040c540b09504484180d404000008040f51130041800c82c015448003c01c11324820b910040f840e0007889500191644850740d2000070240c4d0802d0040c4900c01203a516601450390012061702c2200f041c80c18241c0000d4140718603441d01805921050700300741803208035203400340c400203107034a02000c1c80d103040d07204204090204104000d5004d44d5801800506050381814400c00c2c0ea0f051050140034200e101c2c94aa00c004003d5031810700440018188448100d6a10300c4041c42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650766924 1250 650765674 650765683
    0x109140d0c082401031109040203010e0d030905240c07061103070504030b180303150303130807290a0c2909100207080f0703110303090607080105010806030c120a060e 73
    0x180369845241d080c0380251103802e10314085040e06d50106890349030441003400e1001e10030000b08220b8041d980c90b200400d025804000320f1003041160355022548280e549415400d00303600f501c01124500f00700e1104e402210005080c9940503599000541d200c4503603040100c00380c041c0060305160000008144428103134080010403c0d00d0060074070700400d459201c428214040504400c4040c1d800a001180100c810703464100c00b469001801c0300d083c483c407250b003080700010691040d01560b2028408014000803405041d010420801d020401e2a001c10094912031007482e200c2810007422514035010400e0042d40a02d4040398408448414584d145030303440070040607a1102158403460307c2444004000e402203408050b4807440041c100101e04006581580102c1c604905100300c0c00342019400b0000c03c051440381d418003000344101d0804c040064288001a000350b410044c0340340402030103031000100c94031581002c0d00c913580e120f001c070700016040c000300c55001442d4604014107090a11030005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650768174 1250 650766924 650766943
    0x23906130f0203072c1303080c030606041d07031103100e0414030a0f200709020d1b02160501080628120302071502191707140102030f0c04050109140d0c08 68
    0x5080c00e100d911004500303000341c00c6c0b4441c0113000550841c005501c044405002d0b640008015243d5402c0c80d44070101070090103900c040c0c0c10607a5056008110b0095894024213905c100103800252440c244804000c0c40150f450161a049290141c0481d08010382c10000080100300d280640c0c6e11812200c4009001d03041c890318820010320000ca003003d0010700c54000006280050004010607071400b042c03800a0742002030503d210554440fa13804d0f1902c403c5001d401d070003c00c1d90140230000c408407410180405190041d5040080c3c01c010000326440b540003602010100344816150600b40c0d030a04610341d10142c01a111542c1001c0245003010340004000c070580300c502d62194204069402e003243d40d489144444a1940031000c0b200303012815070030300440d02681c05e5036414500134551300c1b04520903400301c0c090a04c3d42c1d40001040302544041071481d80201c0401072191516140c000020f10761074090140c1c280d905028000f642c210303901d490340700f59403945c0721800845155851510548884504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650769424 1250 650768174 650768249
    0x5091302041d010501090f090506030109060c02102a050903070f06171b03240307030f111e010e03010603021f0807090510080604023906130f020307 65
    0x480000c241036001d2510381c1b00b640d2650120081ea2860604d807400a000040c06003174240d541c3e07142e04000f0072114003802f000018103400400d03041880044400880ba0f55408801441d00e1081c3e90700350100c120210752020341c0071807130496140c000c910000b90410b0120340c407000003031060701ca000502c10b4000070354106075915540b00032170036524084880000f2041d111109402e0710100700041980c0030041511800744002c0c51050b400d1559140482e182c802941c00a4910120425003d0204071043c0c0412441c0b031015100061918000851681c00d010039140950600440042400281e20309512002c0117580040400154510f2825610101041c1c50702050005400030300145045000780150801c558001d85819904203410000301e4003280041d10352940705030200409649800c454095a1a0000201c0d10b401e80e40748254120f81c89041c0301c9411116a0002c0703042290300c0b0007000d4184803407a0010303400074582c050751002a0070981c0542009051a1b1442c181e079000c49607003400908001c2a6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650770674 1250 650769424 650769479
    0x1808010605132f070804080a420207151b080103081c0e060a0c11010b0d0f0804230306060916030b0102012c0105010b190509130204 58
    0x48820b2500343d6210120b40000300c09009200300c420b4890006961804602c007200f1403d008590b510303c1566402540944070540c0403034802c0080c485004000405140c9202c4240c1c1810103d0966240c1c120740040e450078110154500c1003450b640300d030121180a544142040500703507640d5880001442034400060200703810030748641d40e0764006c043e41816603410031085810401800c140c84001c2c0d0545058402c00d0b40c4613000036014000401005020308480c400100f4031140c0e0100007000031842060708070041c0e062000c3e4524544524080c0c100094000265030a00404c0d41014421846154005480c6c2c140000b1003075400b458420713403001150f50031020b5483c0c1d40c5503a0100011900191001d60402c1b00c801200d410301da00950111000c1e03c01030001140d9141030301d0b41140044086002c411a2454284030300c400c001d420300c161800740040040003030400c07100120030020340001d9a481002c0c0040013074851150b9580030f11542d00000200340c1950340304c1d203c4100850030301c2e100c00d25455030203a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650771924 1250 650770674 650770699
    0x50c220320031e1509030d050c030105150f04050a17060c0306060313060b09011e0909081e0f0d0e0c0d03080604180209181204050117071808010605 65
    0x400701454100c120080040c044004503440100c0802c0345485031160621510034400100305600008078412400400a03503100d50f680088101074810003010482c48c54020001449640d807200c4480c8052481c1c160b144d51039015800ca000d11a10454025651111048100141078111010301110101e20130f020b9030450344401400c80b1850006440c0f1079072000d401c0c80000c80b4803280c003500030083d078050380011a903055028040b0300d010380280c00ca40c3c05920f60611042060b500c0c0c80300f10313000700005a4204190440ba80701d01d406405080112203804025800126190b330510040d1000e080783d508813580d64800d01604000103203501600c0c0d4900e8000d12410600e0762811b00c0d00c081200703030107446490a555580701004001e042042482400030ba481421502684501f029203124080c01880c9600c3d1403036201c1ea051411020300e050301100c807800c00c814010350742e00044103002e609000351080303129110400c0a072051529259407030b450745030280e400280d04505402c00d0040b036405513070b540d25601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650773174 1250 650771924 650771963
    0x80d05010503100b01050706020c19060e010b010215040303110d0f02070204060b16060b04241a0a050406050f0c0a15150305070e06030307021207080d1d0103050c2203 73
    0xc4d900001940450b1040c022032006c1405070300200595840324058602448502d0030103501480f59aa0540d94141c0d15046e00310000d01c01d200384425074a0900040044030025020702c00c818200420040801d80c0300d01d07240b00002203860503100e82d0340c0750390010311424070b9a9000b00d0003904500c002381e108a0034804000342600d110000c4440c5500e4115203812a918a43c80700710150240f60f05c06600a0395850400c40d2101d01c040710040c15a28504015020344d20304a02c41203441d13a0252040c01914080011480c0e080c2c000c0d080743e046400c541859610707034403550428901030150020842c00c5000300103002040100e952004000c5052641d810490308c20001402200e203201e5000060203540300303007418004d6403c12252a03030b0241c401000c132071800000354045034010066502e040e4842d405050140f01c05003040c003e5401860091508110000214900c80680c0c80c0e00f14038141815952400715051421500444a0000c95903540440b004e0645e44159000d845902c41690305040c0d00ac00e01d040301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650774424 1250 650773174 650773181
    0xa0506070318060c020309061201170607020a03030c1e0309030f0201061202010c02040609140907090b0f0f13020c0f01060b0408060f0703090b01030309080f011506110703080d0501050310 82
    0xb100200c2c42640030949565918000b00388440501c41580300a11001010350744407401007141c14140e40403810154074046501400340003d16242103e50407200400480550002c1d604059035090714000c20304400d0803000f6282c43c000140103d403040c0e580401c140044d601074000c00500d41c400d54a2016126000ca4100d003241d407240222840b0b07070080000b500166114260200029000500c0001c0103640c50466008132000900c0c0030303094132025002c2000074102880072600030207007071505101d884203100018440e0000280380901c07071811040d03045070300c0d1194401c0441d00f100e08a821540c804407001c0b0159124460700d031056056003000d0000c100b1681c080c0c00d031801c84424070014041622007110341c1019200042003030007003564a40026000c00e9280038140d00941c001d803034405400703050003c1d0a0031f107182028a25240d07810050b1100d50a0042c0f00c004040b07565914002d50031100340035141d03050010951003e4100080802c1804503038046500250403aa400c4003210090801044036034141e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650775674 1250 650774424 650774441
    0x70e0d0203120c01020d020406030603050d031406040c03090204110919050307030b1801060e0a0c0e1509030c090906090c01260c0d051003032019050c0a080a05060703 73
    0x1a0040b10100c810002c401c8040d122000410002500f0031802c14507550490300254005d00c0000e854441c104203000d82804480d00402e46458144440c00d880c0150b0005510083c041c140203030b5441441031540b42c803d52000701541e60060050110905c503044416907a088004640e12400c009072907a152250187c1c01c3d101201c0300500500002482c0d40c54522034548014140f2a40d52114a4601900c11080c82080c002d00004050302049003803000c020400c4a000b01c00000c14407000c81c5d211009543c1e461151b08402500c242c14075600c2d04001b0103c0c0c1032009512801d90000c8445040c003a03804000b00706644900d260b6801c8504191008004545441c4200d2881e0f0b2a010032a180001100018071615071151000a1462411940107850070480d80300b01c0c3c241c0303c1c00880c1042802090360141c48299104104032405107503541d104090303038490760100c0c48038150400f030f0041c400420a0908c82c5101420000785144030443e0341e0342034240c0342c0f070b41040b04803640c1c040d2100042c40a40203210b005507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650776924 1250 650775674 650775679
    0x3041e0b21070e130207060608030f0a0e0402040621110708090325030605130f0b0a0f0b06120402120d020706030b0109030c03020607020d0b07030b0f040c08072105010905070e0d02 79
    0xca402c4200c0d00c45001b5400f8907401c0c0c0b00300741c0319400403800c845d003040102102c400c0104440d40d9010320440042c02209c0301200035208500421017042190f40c41640310b0001c1a0070b50b2015243c40d40e0203044001008140341c11342c0b0009010401d8010300900b4030103084140000e0302074480303035040302e40104003c00329076000c1c5c40303102c1c01c4080c01c0c00440c90036407050354002350040c0411001001602c41e103180d4400ca100841e4200307a407004001e042525030003249000e03080f000b4113002d94885032001036403900032a4450340340a440c681c0003800355581d404070440c40320010390039104419a05100251110405e009043c040303414442d14070704d154410005e1034102e80e000406440c6030b0782540d007044100d9002150903030380700748002a0b540100d0070a00318140a0707200c0d501c0c00141c6507060b03400d014040499200c800c0c820707468040d1641c0c00c80d400000490740060107191075440301c0910000c1c8030b114804000d45007000c07841c040000c035181d03500b580410b001d41456200c071a15181860b0801c00061081e05000f074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650778174 1250 650776924 650776939
    0xc0d0b0303040f0b030a020705060f0103142a010504051201060f061112180405010f060e030a05070510111b09011e090e15040f030f0f0203041e0b21070e 67
    0x100e03c144d084080c54104200e0240585000e40f541c8131b00b4076140c02030b11900342d0040d41d003004000b040100c40300c40080100e484054492406107104c1c1000e20001c2c84006000710950000411035a0f01c600100c402500000308441400c0c0118141c09000f00464001d1007a401408400443c0d20382c052041201110194402804020380c6040100142c0c0c000391000811200e02e1881c081300b83e80c0c0d6000303a5028110110348a02968034012008004441c40301c101d13402034020300ca861000c40d0001c2900400d6443c00e84104401100c2994115103420f035804090b01280289411001484a0180c1c500d089a81c12220800544d17214008204151152450f0034402c0c550254100480f42c4180c0125513925000c000f503681c00312901001c032984203c00c075011039200642000c1c5d20100360b049200c90f440480e1518101000828540c406950380c452070280300c549041d0b0280108a2015850400300a48041400203481d090125003071181ca41d40d406104460122600024010901ca0300c40c4004100b0b00030b2820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650779424 1250 650778174 650778179
    0x90a180911031603080d021c0f110a0c020f061204060b090114010206060904020a050a03050606030105160807141c1d0606031902370806010509012c0c0d0b0303040f 72
    0x7842c0a03401030a00c038015940034041c0750b113070a034426031010a0300c88c4a5000b04410001c0c01c400702c1118080e8a042c804400d040c407000c2c00c11030341300e05001d00f019410f0301d00655002000c1c000440e240100f248000140850b1410401004002d80203041009002d0b03411000c03e9884000c0d41c0aa032900c0f40703600b4016071141c80051a94640816030340d03000743c0042d01ea0595a07488001083ca03030626030300300751055032110042c080d181c1001d10030260310801c0a041c0551702c0440001c0100b030030401a016038104aa200d00d03a155080d107070400c968101002d10324801180c202c201c101405000341c03071024003044030007000d068489000820528800d00700107018000050201c100b0381e2201c060305805076002030840070402e46804501d110740101e07001d400c0c2991102040c003404816040394035042503180307030001e900400064540c00714080c10b440051880b0105619004054100c1d00f1003410000d0000704018103011505107468000c0224919a80d010700101c600c0c1c200741682ca21507842401d0803070340d211004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650780674 1250 650779424 650779433
    0x908010c0806090a18020618012303040b1902030414150c190207080f0705210604080307020115060f09090b0a090c0c150f05240402090a180911031603 66
    0x101a0342425081e0071200c0b40c0d11034010443c00d80106541d546030038030f405250320489d81c2003128185040000a084098101040a90728083c003015200400114020b004100024442501d156540c03582000440d01d0f0314040c00c1c1a400030401202d01c0d0740364095500e000403651020029144917403051120750b890400c00901e40e860302c0000090000840c020102c000c10010b2052202d520717031250100042421302e040200300a0324400c000f2621302c140c5c105490006444501180c507552040d00014426225502d2440030ba02402c0c8030423106000340000c0b84003080341038100840213811003950380e41401c001e803070b04020411504204040c42c2d010003208010405540c89800240c0c11103031519040f0070b5600b07196940c170102c92285d521102d103143c54034801035241107a40f04990f804080c0c030140c080e8a41c0d801c10251001d9030341a50003405107030005031000c070b261030317190114000b018450000d0031300d0801100a98010700c400c50701182c0c003403040d181032012441c0c0013802204211400a44c101c100b85503948 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650781924 1250 650780674 650780681
    0x6070b01050f0604030b0a2711040906060e0f1603090515061503090321040f020f03010b10211104180f050903070b07090b12090a0b070908010c0806090a 67
    0xb4540d446030042202100080001c0d80341405640342d40c001250300e6019800c16094008084400400400956200d1022a1203d802c1e02811417041e500000c0d002e40500f080006002130303070048025108141d040c001c8040050304400c4c0309001d10000e07035003020000c040480a44a84200203030090740500b102e00c05200c00d00ea66560400302c001d00d07000700c004121082120344d4008580403200c80e003001c503540007000000b041c0c490800008141a01043c80d00b03079a551820000c1d0304c4040d006200ac80300c900c4480d00c2c00d40c4110302d200801486164002c07070850700188540c03440c90740058000c1c07040f44014024841800b40c45203c003040c01c031003400c1c10704203003c011021041c15006074009455200303006400c01a8407425003d0885500074507030302e103520304040c0404100603111408201d0100030401160f400c0606581005401071f2a056050300d6105202e441e001010360040c10024002040c801140c2d00040c035502120542d2000380000b03140c003141551969802c6942c150866099000034404005562 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650783174 1250 650781924 650781949
    0x70503010b0a110f071d0702012003271e010c09060f1b0305041d01050a050f030133170a063c14010f06050309071d04060b06070b0105 59
    0x40c01c0f14003100b13941d02c3c040c0c504102c961080b4204000d03150307038200c8411807401e0242d00c21103500083c094200c080b5404200010300001c00100460080080b5201c0444994410540e5074200d4001e2003198071032401980f078180700f030b80d0a50140800042c1158058040c0102104601c16895a0350111302e0a1020740700040b55004071070400208059400a100025140e8520140213070750349500c480c1811881995a403a60289103040114600100001e560703081c030800c1a544141c88100c51001c0c100042405004030f00e00d4076070000111111800840c43d000f08080e00f56141650382c48415950b100c0800040c2c10000c481c904507044048498003003840794120510650680e2051b8040ba001e0f01c08205030302001020f10400030030640907504101c0c1460195070300300a9030300c2d844c40d01945011600c48002807d403085405100300480020404503003440071000404451280d0a0000c26400c40c02d8041541102c0031125245005402c9045081c10015905020360060300310141381d0921040150054401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650784424 1250 650783174 650783207
    0x20607060915020a021b091311040207150e010617121c0513060509010b0307030f0c0503070906030201031505090a090204020f0a02211303060506040908070302030304030206070503010b0a 82
    0x1c07a0b49022036100400141d000c903405004001485541d0140700780700320030300901c1021a170040c459403600040c08202e1842d403180da080480100b0300003040281c020703d01c0180417820b1507512100745030030f00d800c18407401e8005c500801c41c0d207441d4800215110082246444903621002044485501c150f004107d002817031381240443c148114200e0b0b081d1142160841004202e40d40c5c1c070750030015035010311604145810002c1c0007000c1c012012030394580386c0c1e03c07016002102808841092000002c2d031b0384040c00700607040d281d441e07841d030000b030b0060240351000b240003c2c90003607580200c465450b1044182c0e180101986607a44501c11001d000d080c044800341c4e4051740c00c100c04410b00e562320004041903c001e802070140101101c1e507114210304040440c818a500c02c00c4a0005d80103100d040d1b40030780381c0c0100006150344404020800800d00d00d007004012100009951040c940c0020180d440355201e5030031076101d652402811a500e020070705c40c0c1c1034480320a000c213050403070144240c031103d032440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650785674 1250 650784424 650784443
    0x3130c050603010311040f060b091905100824060904020a0216060e18040b0402010f020106080a0b151203041206021e04080f0c0a090c0c0210050c190206070609 70
    0x5400020711035038001ea004580d03040c02000012000d0501d03029841d01a11202c8040140515181840c1c1481c400d00c090140b02e0b000b100031306060b000006045602800c40a41265100b5012600c090510003060f5841080c40e00c004200800300444141407010b01107024064600703040103c0144000303500810344800030342c0a00a081e00c5182005c3d10032400a0130640c4d600150020b801041c006040c4020000c060906c183c21308020129550000947d0090340c2860511341040303800c081280103085035040001c0314041c0d07003012070612039400d100700e0049248403441e000920fa0002080501c00c0f054900c2680d5170070920003000a18040e0491890b40da00a030350140c40c09491101070703003500fa107203001003040001c08942131141c110200510255a08100e00800e410741202000400103a4644100d00703440d41c84a40102d8990300c030781414000e80741c0c040d0019078000003a20000d001a00b0006405005106940b140f080104d8803c0d01511556001b41a0501e0700c08683c44101c0a030810190a84070443d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650786924 1250 650785674 650785679
    0x100c14030402032103060103060503070b0a0809100e01090308090d0c02010305190e0d11030a0804120311070605040308070e0108220807030801150801050f040b030c100314010807030803130c 83
    0x1007601d1341414560070800555481c40c00b40d00150850f01e50740c002c0350095010720002c0c0410030150080320703907000a90420202540d55000c0003440c10b0042400d0b400c40d14140610749692850540141d200303103120b0380f500021f40d500d400050ba540d80f80348198000240102d140c0501550007070b031145410682035101442c0c8045140c03c01c00a072010780c415080c0c11381c081d070f80e540205680112800391520884000c1c41c81c06c048214001d00c16100a00054250402c4203a0032070710307078083e038892000c440300c001d0700b19110055400d04500801c402c035010380104075104000f41100780314000b0014039100584900b441510741c181481c1d603c2c0d984064041e900c0e0f024118880108032140b025291440c07007a507400600b90f05041014400303402070726269080c0003900700140302e686c3d91420000038a080603a800070f984107400300080d2610b03142c40d1025801c6426003104141480d8560052a29104c008074120381c0c44c1d903605c00300341da500781130321000d4501d440a001185804e00000c000031000c900406900c8001034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650788174 1250 650786924 650786953
    0x112020d2a0b0a2c03150609013c0302040c0c0606080105161808070e01170307120302070303150b0c12130e071205010b040806091c0f11070e060102100c1403040203 72
    0x34080e1105161200c1b800f042050300d1604440c41405000e1001854140d90301c0400030400b0070f00d1004a010b00d8021402d4001320980403c0c1004008640051043c0b14160b883c00000c0e10b0088500c1e400d49840b41010070108889005025450083c20038002d1002081409201102c04102c04200c0b0207500c614040700044a5508201444c0030700100c01429550354540840030302c1c07003031060021085541042c00f894000c03618906051103020b400341009a07850744d080c601140244181da0240303372081c200b0000402c640641c103020303111215490048500b51000b00340b500e000d5015280d20700842140c2c0e10400d100380019000a1604030600b400d00c00c1150f08100e44040c2030b52400d8000508400c4041010403420388100043c0e81c1262103a4050b0a00300307014402c40e00016140010381d000d00c80da50b00c1400809110f002c85403064640d50055444c00354888280c048030314816280b0500500c961805101d00640912030206049020389560b100f42075600d801008507000207106a9050040215200240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650789424 1250 650788174 650788183
    0x181424091c080301030503090901080a050c2707030b040f060e060f0d0807030201021306050a020d03020a0c0f050a030f11150a0b042d11030112020d2a0b0a2c03 70
    0x2507100c1c5028540b12380c8024284402040140d100d0742441e441541e44d040414000305440c0c480000c107541e51041c4420040042c0149005101352441c2080c00c4c108100c211070340355101010b0420704a506100600b4821002c1094449038010315100390b65104c089840c510f042044622046d402602060082025455065583e0081c0c101500580d40010f0750780710560050600b0700113004603052841c144035140d03800a40c3e4000e40e2180005141d40091442c0b2168003450a0011865026018400e41800707032400310b4481d00c10141c01c44c0071680c40000041254055080c07428a03a00c070b2401412484090800d085510317202410030010b0959501140c1215100c82c021484400740b101400b40c0c566180700c5140c0844030403022030f04901c070315100b982c40180003503100305ca044861320554180740c01e001e0b0001412880c400038000b03100f00d074052410079840c0c2002400c0c0c0c0c070210442ca96902c3c16640c0e0044403645100310101000011031207030090030340c03810743c2d46e8950240e0f0720031449611404810000c203162 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650790674 1250 650789424 650789429
    0x192301140703051804050411120f0f0106030c06050708070f0f0605160e0301020c0a0311030f121605120403030513060204060903140705090f07181424091c080301 71
    0x71800903484c0c0300e007001c10108a54000003540d0400c5149050740310a100c410804503100c0c410a00a000051411400c0040380d000046e402c00351400b4003649070200d40208001e11080fa04402590400030303505001d40180c0f603109400554042c030f028281d030780d60f50b0849598401160b11052003405503003c60a58851a8422583c4138841c04402c4400326001e085205059400ca110303038010071056440d0ba5010a423000340759030605000c601002d180e03440501350300488092040415002c104203079461144080b07140071b081c000d84003555616035030030708032594840d00348494030741c040600200380028070951005034005c0101d010000c4a102c243c3d82c11080c1c4e40264000c40c00101d001d04140180080c41c2c040d003d0141c81d0740000d04410b468140882d401e10300007404035021803442400501458040d05800c901c586014070300f651070325218000031803260003090307955025000007410004180003900d00445078030124071840e81030141c210104103191030b10010b09100c07540034080c05400034032800d024601 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650791924 1250 650790674 650790677
    0x4051006050706060e01181a0a12080c0a0507170a0c03080f0c0d050406031a0d030c0816051e0d09230a03080409110f0405040908042102192301140703 66
    0x904081300702843c0144d40b900a40720100c002c5806490703001365290701c2118203c9500302b000010111071820080c040d40580b0b103074007030980600311503601003040215078141913505000307813004082c151000d00c0d41d907043360b40c0c40102000719623281070001c0b0300c1d18006480b2841305d008446282911560016042078125040790011410106080c81000d406000c6c4041e4040784c1070b5208650f689510014005040824014040c071007035201480c1070002d00401ca420707007030305914128075540c501d24040f40e030340c210036a11500c0183d0703021744a0600c11020981d584813003525502c103076401d41407000041594080101d1040b80064103c13400984d500c50854520040d070050f045581c4807460a41454195032840d000541d2041c8204081103640d507407001502c007a038009507030014051440313140050892040b901f24060f600f2841c1c5058290340045080034a056100341c42c4d00c0070400c03508c0c0340ca120810090140545c2600c441c01c40e006902c0d02c0d4000d00c0c1c40d86805141c0001c2e003000300d85041d003659000a0082c0e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650793174 1250 650791924 650791949
    0x80d09050f071404110d09030c080c030c1b280503010e010209100509060708070204110c01090317011401080408040b120109060f180b030c030319090504051006050706060e01 76
    0x10200c1c8041e0700f640b0321200190b4061043d410b202d000ba0b416449400000e5650a41e0749506006240c442c400e4080d055070b010110564802d40b04441c0795817608806500c0c111841126240383c0010403221805419050181c059000075480c441124030700510541c00c4140412044400280c9543c01d000b01d03070142d2400400182e58004a400313004440181032a0403050100401c80700641c0d440c0c0100719110350390008102d075201d50302d07440010090403601100c0c05200c0c0c2c0c00300d0076021403203044d0302c440e0070340f4420307103c01030203400350f042810200c4000d00c120704045d030310070541c0050740d409042d0b850303400761048075440d04e0140c85806405054002d800c2d140510341040005001001d11403149102504c080300d840969586011681d62a0300d59400340d107012030f9102d4110703e0554a0800030700342511070041c00d0b2502c903046450402d401d90381c556511000202111000034240c00d16124246c02000090800080c2d6414002d0580d0a80e00c500c0040714031607903401d8001410b840c0103c00c203010700000400359 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650794424 1250 650793174 650793179
    0x6141608060909061b2205040f0902090c0705010b331305010e01020f10021c091e080d0c051306030c08150301020f0d0e070e13080d09050f07 62
    0x10140300004061078000d07581e2005000da1102c000070007075440814050035a4200d9500c400840c124015180030404102c0444c40c0c44400308048140c4806903102560100a580008082d28041d914900380107504030001c0303000304960400d04c0c0000d10f41c4a029200100780c001500000c6800e40b070a40302c003100155103000b0100c1130440e609180e158101c6c6044d001d41d051090480c0342004a01e8940700309814407280144280303ca90080c01840150190201a2418060311608000195218112501144004211018294125100310345000b40c2069120a50f4880985520b410307110700d407003d9540b80414000340980000c01d00034035010394007a559003915031424400051001c500d5401980a05040011075040b0036488070185901182c41e07068004131302003d0b00480c0c02441540700010924000142000b03854000341c2240c10003500c0c240c202d924090344d81099090000040d1100ca1880d1462030054022403045c2025090a8414080c00070303400c0c2c55940c0c2c403490850358908207101604101c004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650795674 1250 650794424 650794427
    0x3090108090313051009051f02060c0c06011509031209030204050705030603150a0608070f26070e06300607080c0a180807061701060c08040302040207061416 69
    0x2035811500c490300542c2049003010154460350344a01075940980d03150354543c00003c0c0700f0358509000300340117030010003102050700e05090f40035555030190016100c0d10b804038a244040f003044448110f1100c2c01740030664241070085020715101903100080094a40012000c159918160300600d5040d8641021052840c41800107a5200808250038000d0900421050307072004182200f040a80d0b01b61002c0d01e03901c90310a50000d0010790005003441c80b540e030021480103041b0184100b5034000501002b00b028061212803022040450181440d8000d50007c00c080700d07070041d64580000b0024a204501c40060100380c19010700003010786007011820700102a84041400440d80150340e03454650f4240c900886040300310710940d60b90104000712282050510031303554038803101130002d810540c0c032a20364680e80100002d00d0800702c45030101c4400c1c00010b09500800e40c5449c4140c0c8016444d00b09490758007000002d402222081d05c00c19202c456907200741c84140711003481030400c04104221140031000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650796924 1250 650795674 650795687
    0x140403021504020604090203090a05062a04080304060c14100f1505011b030c0609110316060219020402210a060602070e180a08030412081302011709030702060c030901 73
    0x1010010146850140b101507200c1c41c08480540d1051000942c0d640c44035410149401014003000d0070f240611814004207660801c20108101c05a030103031f078200380d8102002c2807079114511035180c055000304010001640100e0802141e6800b9281c98580810354092036400c29400d60001c1a200e503036a408101d10910b07510900420201040d03d845081d81044000b0b06903800c00710920441410805459041522846084400c260b01c00f200380302c22103070b0b440d00390010703400d45003c60711900071042c044c101e0700020001c003000ca4003e40d00600f000811044401c2c1c22a0758035009030f81103a02001a00c1c80b0144010054540404208054182d4507000140360103c2c0c006400030801c42d00031030405c03c0f025042c5c00101c0c1d040300783c000e05100c1071420038498900d807420394600101030302c1001c000c01c410f014240e0003041507900c00b41c0754140107503110b0340e10441d10403404000a02040c51040c02d00c042900280c046a80f110f030030001c4902d070000301d8000482c1a0030030345800302705520009440c1e0700340d60b1005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650798174 1250 650796924 650796943
    0x13501140f0603150607080304140303091203040f061d010f0c0c060213152601060f0f02100e0705040c0207051503061f1220070605060406080114040302 67
    0x100036040a40d20019182001c0391071002e109860110104042808048100b148800c00400146d505c40d07852411000f01d800072601995020300800d03059404c0c41010044900c540e2440001d040c0020032040044003940000d04251080440203091000080c0d0a102d401804201c04103122000310700305008c2c5003034540070300c2106615420011291041034000c0320029410b03520031405a2289490003001c6c0c9940c3c040ea000308500d100c44003c943c50b082c0c01168881a040c41508030611051100d09a600d4081e028406c220000c0c54422003a440d1a22a044406070341034944141e4038440480c0380681c069400540c414640794004550800051800c0e00c641e03121641d81f030026000791482d0000252907100b0148408906a40c00400a045940d4516080c1c400c0d0039039659030001c4002c814001050f07150b0660864044901c0d2117142241d08031420545003101c0a922621440c0c400196a04000b40401805164116444150100b404402806106000600e00b42115020302d02414001d01d00003141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650799424 1250 650798174 650798189
    0x80a05070510050901031a032e050105010507080903010603050111040f080708060612010e01050703090b070801181d070b1201061107032009090714060903030405010e013501 76
    0x10200d202e0b2a40e0000f00b542c1d1070300403d080005100600ca280701200301401c06009a0500500c2c040c50130a01001e0389406a80c2e60094003681034070b038201c121800302c1d08203000d81400300d0018482da0000690441c02410004000350003c9440c0e552652202e0a5400c1c1d244a1186407101103001c1c0b00600d1030064100082642034024940b161501004070380360300d07001d02264050400d080001d031a509007500108804004940200720500c2c220b1001401030410301c108071020040d0402062007248107580440c1030340c5c2c001000c90810100865400c0041410018040410360b403920b401e03040c0c200074400c150007003890040c00380d50f49103220b0998000030700580100d4140403032101640c801100025045059a500c100c4030b1404003c04104541000301012219034020000420007510000105010742100c0200c440c00a07005d41c500100920341c020400c4e02c0390503510600017004150701c10701907000c140c407060404400440b400d100c491504000801c0e070368030b50107079540f0054009170010601401801807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650800674 1250 650799424 650799439
    0x150c1d0414070e010908030c01020405010e04091a13170306210606090c090d060b132a0314040308040209060907020604061a1011010b0f031c1404080a050705 69
    0x1107021900c0c1c000140c03105007040701154459a059001c0c40480004d094820200d0381c4445602c622a8046c2d0702c18045c41d0b00044030000c1c5400203040c280070340380d143e175440014403104021035612004a19030040004004605031020300d808a110034076101d01400003410320584e28600041806201d00c040c80e00312041e0b1143d10a0004400e8010801c50780113801100e036040c042e1610483c100060047c3c254143e4000d449040c001d0400c0107a610402400c0802d0312017075034400f07001c1108404c0382d082c3c60035040507601c0381c1080c541d2249041c1104a240701c45040001d41024990424540c6140849089020407082020310040d8a8008e4903958460800c44065102d464071040003511120080d000a05c8075458120520614a4580b40070700c907003501400c003400d903605401707009203241d8a01040d140c555180845030b00860400c20300400c80e80001030014640011503214a0002400e83c0303424400300424102c130800c414002d240140001c08030040241711240960905070700b0b054a41c1d011a200c0c415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650801924 1250 650800674 650800691
    0x15080115270b0105130e0a05010f0501050a050918100306141620062e060509130f060e06040b01022b0c02040c030203090d02190f150c1d04 61
    0x25036109500c00240703a503030086000e036200d01c010303680c5014030000201301c2e00a05001240484a80300300b10b20031000d0450921181c0d0740c4e000803407010240d40c0605800240108003990400380148014200071740702a0205580440e59148500c4194003590081c0ca40c450070346040083c40307414050203919003e0f81e8984840c40c1004980c0d00c0d4602c800c200d401c0300b030000840040c04880000c140007000703a40b0450548041d031902c00f04c0341107113050200900c0b540d40c800c088001001c1007030440441c1030710325a0711903e280403c42400c00c034001c00743c00c01045000ba207400d489000e00c960780c02808001c0c04403444c200f00c01c0c14004200825900307880c0d03602d811980260780281b0001c00304803070044640c0001654420300c2035002030455540401e120060341140c204580b0703c95142d450350040d4461a01c00061324110840b2080480e20382440d204d030074540c44682481c0740003003811400885100c0e07202d040c1c008007911081d000c4100f82c40007580d0700b0001c101c40b0041c0b40d13031419014480c4044690f080314204807122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650803174 1250 650801924 650801969
    0x61403010605091314010806060112060b0a3020030402011d04060902031602150408030406050a02043204090807140a0b0901480315080115 61
    0x60610f44a00c01e0101c00c140001d4100c2139801549034000c04404d1949541e103840b0047c0ea01c0c5d10030f0b50228002941d03a02c1c642d40c810640c0c8916426107081c0b100ba0340c80d1402d940001c03282c1c480d41070642d040c0c40708880c030000100c0ca44002c1180c0244004140030500140701d14042c2c00c1d140007996128100d030420010800142c0e4041c920f92600b2050a5095199602c00340200d8003c00d40c41d080305031a240f00006001050300303200907824800909500b111a01b41c00c070781308460980800d41c0c00608840091020800180341d58100c1039110400190050404c1da4444042c040c0003424008843c2550040600c0404100000380042c0b03109020740342408004030315178034058140b00b02e00f00603101c080c061614000007035050011003846d58000c4007070641410140e40e120f00030b20041c40781081801e074200440402c44029085031400d00385440b4074014002051080d1b005007815258200c3c01c01d41d82e10071003100701e1901c3c400d290241c801c540c00043d49084601c0c45100e042c466800460014250884015040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650804424 1250 650803174 650803177
    0x91009050703060806130503040f0b0c0d02030405090c091c0803070807020f0a0f0c0e010f0807120c0e061207090f0e010b0d032010020909070c02030c2101060f061403010605 76
    0x6d149405080d83c80c0d9000c0c100142140544e411411095104400000d41002c0c1000074000d410160707401d0b16500140c241099940340300d42d00c00c06410070031034000a44440d56000180c1840c20303001d00f20514040c41c2001d2201b51204c001012074110101005000090360303c8603003180e206a030f9000805007541280c080ca0780c2e9075003101e401802502c800c0c90740b400b0424441401002080450481c442558451010f00000041c0340944141440382220000301c0114000c0c000311083d8002982444003818554840c156050041c0000e03084038211480c03010002e000c0110100500c0449400141ea402400e90719064640c590a440701580c10106c3c003080e29030390701c0d4960b52800d070300d800c21505551401c900c1580880c82062141d0341070251802030380c003610301c54000f01a2139a08462800300d0b079482c58000da51140035131001035016800511810200d0410304503140c1d860946540f00012851403401d036600b91b8100e9000b00c509011400d41c1045a540c128020080d0300041ca00482d00b150705203000101507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650805674 1250 650804424 650804431
    0x61d030105250f2c060c0f1002070b010e0a020918270d032c070317030f060f04090203010e300d02030703021623010c09090203090c091009050703060806 67
    0x2c90700141c40321100e070740c4504840340202d00580750a49a0303482c02c010b0b5442d4849030000300d47c1d60007100c0c554042e080f45442103030303246940b002642c2010b9003001001030105030002c0640001c0b03a820403c4e020541c0c0c94030411079803401c00580b0b8141902d840c50142904100680481000080d84803440100000c003050204c14105d2034500014040d021440c1d0790b815607000259030301a1b8036249142d403e000e40225140301900c0c02610581000c64080e1601034042c80100c07600f0708030345580703000314000c0c6c603204000300254440100b010440003c4c0c1e800080c211035842c10002110b40c071002e0f150701c00c40710218844100f102d00300d181c141459022a90002d480c0702e41083e00020590000001321403a0090781580c0d42c0100c10f00c0b040034440d015142100100c01602c0c14128001c1041c442d41c0a51041402603600a01c0300e40d584900c0340d49040450f42c081c4d0405000c884140c0140c91328902e00340c0742c8404e21407060000980a00d5260b113440246001c03204003070109020182001414400c951001031495013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650806924 1250 650805674 650805707
    0xf010e0402090d0c06020609011a130f06210218060306070c05070e0408130807050109210204151404050708070c0317072007050a061d030105250f 64
    0x280d421080c00041c0035401014801044e500055030085080c1ea8002180f034031481400000700140b44503a21030144c1903002e4441c06900c0800400099040000c6030001859035006040100c0d9407a00c40d011a114403100421b4141884007030b4401100b035103000002081d586030a005a41c48034103081c4003194660b03a0040c02e01060240c010034040c100002004040e00a00c0d10040400e02400c152a1046442d8407003184912100540034010a81840c0071440d0400c480058603004a601d00d848480c1040341ca1b2082a078401c1c20031040c425000da121800b4041da02210711710314003c2c8504202071041000070302ea1103980100d1038182003040494114901541004190504200344585840c3c100c03a559000e01007090b540c800380080c4084960805d400c50682820320100501480195048503a98195446600d61121401204104590041d030140b44280124181107240600120100e400d469041d03500c841e9082c2640c0c4c0d02030301550503003030044903c0040e2501c0104600307a032600034a1516081034045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650808174 1250 650806924 650806927
    0x20f0f0a05070f0b012d060e0303070f080a02122109031605070513090b010b13090c08040b011403071809060e03131d0705180414150f010e0402 63
    0x305074014000d89800d554444009800c1507500d01d40b01c200701e0000c2c4502c1020340d05612401c5226a010a400d8850101070814090414900307802150601400c41d40c440d05400108010800300340201004050309005e00a4240d540c001c0d070030300900d00202c2c0b50541680000034000000c2e0f603142001c903890349a40711440390780307a512030501c990b045100f00d05040c9030030328800d40030030200030002c1200e108480085800c2c40601410340c40240566102c41d90040442d030110005000e40e0070610f01520849a02801808525403952104001c80326030300e03510404078033301d80d04000401004480103409080c84030840d0b03414042003000b196461003140250080005400c0881c2000340481d40040341e003540092061110350208010141c4076400034420f11040000384001184401180c11000254101c08046144568400000301d416410410258040491401010003030740c1d11070040300030900038240000c00300c1c2800701c011000e2428a60010f801006141c100f80d240760782080000091100654015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650809424 1250 650808174 650808187
    0xf03020d0c051908010f0231031b0504050604090b04031202090402130911040f0e0c1b01240807030209040519050d02061f030311100e0c090604020f0f 66
    0x940041c41c15001240c02040104515010491882000040740c013850000c01130981d842003204d00343d22500380d801380e860391031142084800c0610642d000c4c1c882002c991501112791640e07505050843c00c2072500c1e0b411416030f4400c3c401031805104071608417000f103408001120703040d503a04041010081c0b0150170300081e20398030125485503070119601e6800c010011991034071801d841c903503030301c4044c0210b502491401c101c048071a60084110340c291104400c00100d02c9180c0003080c00901002002d034617000a040c402c48180340c49541014080e20321290000c030307200103221512405040610154108070b50a00004c10040354041941c0c0c0a0780c4e010b079400398040e900c07824403138544003105620521210107079544000b800408030305500c44804a5007030700c0a41e12080c4185071070180714031341a007204001120810000c1d0003500300b00001144141502c1513510604800d03021102c85004c0c2e040103070498500000240390460b802035214130100d40c2107040c80c1d401d0025081074000d0301c82d44004100c000030744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650810674 1250 650809424 650809433
    0xb09060f070f0e040e0706050c060a090c0515090406030c2904091a030703121b1212090209010305060a14090606040213030b07120b0405091c17041b0506040f03020d 72
    0x448100f14038001101c0f504d47e69103500900c15070088146408034040c68012400c616400e000c0d004c4036036000301c1240c100505004c00c00a004425502c4000c103505c00304400826a11140a0303080250300030444c028406203404e107642100310150340844170407810040c244041e2050f1000303480544002070390015101c560340300c0031410141e40c800ca540d071503c80e0580010410411001c41c0810301083c2c0d0b216001003404050302d00355103a0300f01c0700500c4c4410010304030b01101d02c189248000707600c08241c0444d1840083d00032802002003030f0019181074000c202005103503119800740d904801540350f80c110311403038124403407902c842c40940154400c40e000500e22074040002c808500c042c503004000702c403403030500d040c01400001040b0000e6268074140704a0021510700381c4901d81c42006d00c0c3c4040c004240e05200c5900603000d80300201002d00c0403000d000d842c04126500350724400c5106255418180a42c00c420088004459121302c0c45aa0100b100340b24075026088040c00b140c3c1d040d40e988015588603c1c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650811924 1250 650810674 650810681
    0x412030c0e03070e09010b011e0509060405042906070c0b0c120a050703092102040b1201020c0a0b1b0d0908090d06092612220b09060f070f0e04 63
    0x100d641441003c5001c911589108240350150721100000c02005a10b40e006446166004001500d42091a41032100c2540900d00404c0b81c901c004000d286440d444070001030803110715015080591203a030790b91f201144251222804140021a0300c1820264580d6a0b60b0280c201800703503482060010030741c10174170f040411034820382c000480711003916200741000043c6507420408080c0c0000f00c42d40000a038402000da00301c041c0c2e040d00d500705c1541007050f40074840500126600c4980280c3c000c0c1d00541d074031000303101806200d60312002528054440d414a00501c00c0003410982c48950740e10f000d8440141071404661034080c00c4680400c0303850340c604015070345004043c086500500084e40c08400c0041030703400714018500c1112400400202c0c94041c840f040c0c411580910142c1c800c0103250f034140328107007a0580c030103078102a402c48401d41d89298241085818412030f404410306052000d00303001400800d50002c100c0c422524145800140104150b50f850950340c00d1040c2c220a14946403250340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650813174 1250 650811924 650811947
    0x20d050f0c04091d1c120504080d090c030204020a0513051504060804030302091c06140702190c090c1e0c03050901030905011407050301080c010c17092106010f0b030412030c 76
    0x5060710740b60645008201d0b55401103000f505d00261120054403070800041c41414003d50f040034920341061040341c0790500521072402c080d40e20203084d084c00001030b030701c03400103100c10300c0356584050b01c40c81c2000b0050201c42c0d4a8000c20304c44c02241c00d04031450110300c0140c600300c40c3c0900d00310301940c0369810154000d108110115802426880c03041d01022040b280e40180d161103114100b0596915010b42455164241c54000060304080340c0d1070019007140c840f81d00c4084c011070003588000e5440c41040c2c11108986025004185820203100b64160702a40e00103142c079190400c43c0c42d000459400400034071821044e103040c156643d0300702051081c01d600503800c4a50303009c10081c41c3d0901d410060041d0300240706200c294440c81030722007803652240076641e86040e80320000000181c04080480b00903042062150380181d04c50080288082c58201c0324a87c1d44c1c41c001c003510741941400c0c4100e0007201203070090510194100706101c0001c01d0141444060310791b5140001c0d04000104040f200c203003898 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650814424 1250 650813174 650813231
    0x60c070804091104061b050d081819060605030a05060a11090603090a0210030608120309150117011b051207050f070615062d05040f0801020d050f0c0409 67
    0x500500b03807500403e0f0051043d60440d4940d810010801c03c99100c05030500c400082003500415042200e20b409441c0740c64110000c46042c0309502030a40000346401c031010a0521907001c891040c10074400d40340f140c0030150070150003800038416203880d1a41e6904020740442200ba9543e0010500702d19200159024200010251640d90034200543ca90781d02800e8805c1c2d1045003240d44240400f80280704040c00c0381c59000c003a1042c06011520707035089030001040c840b030300e000d039014032025010303040300c414060140d4036500b0404000c0340c0c0c0030030f084441d0100440040c2d4102411081503035086420707101c00113001c0e13070019501e91361003c00311200d02840846044c0c000000c11081c08201c165001f020010608040340c0040c00c1e0766410407140d039141e61062841a0b901121540550403242403845041d503041d04107030b45407a0741d81c1d88403420600c072907100d00080c2c0d501040a00c49510b85029650700f04860070789101c0e0500702034151811038807036031144407042903031083c0c58806d5440ba000e0f80c1100d502c40c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650815674 1250 650814424 650814431
    0x9060f08091204090c0315060f050d0204080f0604050f0118020402090a0503100b0301230708150a0306020a0f09061d04140a151a0a030c0c0c230a0305060c07080409 72
    0x4d404446019003003400c40034011904003100c2010010789550072030200c03034280d51200b140c0008001d0985040e809400e40c4000950204070103d0b4841c003c00164003241030300780092065203054102103060140c00c1b010070040303905060400803005507240d80c1000d007030b40440e8010b0b52118400000348a911341684102e406000301c1c4200341c500c54480c1c1c80358039020000e034000d2140000d0301510700e07642c420704100180c03245550300204400501c580d100c1980306a40b100c1654451401000050341140a98001c4503000e40018180096a0b03101c40982e00d2015542400380764141040d002801800c02040799102300885880d0307121a940e40c1d0340205004445003580d40805040040601c8081c05003000c1001514035581d000141d2a1300c5034441f4482086444242e6041c03200a060440181000d24003560400052400700f50100d0b05200c0300c20002c0040c05143d4144041c010803095602004143c01840740220150400120b4408552301d0b620210a124080ea11411440c1c06a4180290b80007655841e02c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650816924 1250 650815674 650815679
    0x120030406020d020a0c0603110f03040605061809060403110705150706050f0c040308032707050405060303071a1312090e01090509190321050103110109060f08091204 73
    0x48010001d0700d146909840301d0014800007030340d07100c1440000500b50110340f0000c1040d1480303648024650b250815031b03140740c030b800c0c1c207540100c540080d5400e884c66580c407070074051645000d0341941d09035480c040c07600c007013464040080c64558100420180a22a94280d02c408400e4184400703400342200801841030a058181c6603002500300581c1100c009103440b02040300410b0b1050668440c0071103003c000c2c1341a065681e1146c9940001d4400c8203542e4240101444215500d420000840c8640c801000031a29050400060b1480940818000d400804c000c0002c0760000d2010004e4100c41c90f00755005132190901c0d080c0c400c40307225000d81300103c004450b0048a612101a100b1a101650354914507600d070b4100380c044640c160b540c601e0710f5101958414100c1040d40c07d04254030301070300704a01c913242412240c4030601c40810504401641c3d9400520400442d00300702c1c49100d0003841c0409010b4100603004d00034400c1405080c1c00e110241300091604113081140030400845401c030f258482d503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650818174 1250 650816924 650816987
    0x40f0203013306030b0d150603080301030b0a05070516020609031507111c0c0b13080c0a02040e060f06090c0d110315030f0c040b06070b160f020a030f0e01 68
    0x441c80708801e15503000b00304001525074400c1c0100212088010681c1c00c0440c019602c0c0c10018880e000b039501601c0e198200000401c007043d02850081d402000300401c9031078000c101f08212600184041d00784402030081400c00c41002d40c0c401c0c000b95055a250303950f8891500001d24140100d20405048611601000640340d40080032080c800904c00460344200c4020010750000750511120364001110f4141460101c2e01f00510f15401100301610a44441c042d41c8410007a40d00c0440e0415481d404a02801c0071801c0038400d00c034403452070b08090841402c02021140d24103001074031640c41241c0704004074a40150312021101070002c44903013040420a2005c104000303800455007007890200c3c01481325064140800c0390f030075a400c2800503201245c42c00040200400c0d0b00908281c00c03480a104060000b440009103c0c0220115000d4220b40c42d20940d00a0024880080e10b40854000803020000a500180355142424190801c0702c0300c240700c807004807480c094004504c410001c01c68031002982 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650819424 1250 650818174 650818241
    0x504050a020102070e06010806010c06021303060b0319020a03060507051b0a0b06190b0a0908070b03220f031b020d06051518010b0c120301080d08130506040f020301 72
    0x81c401c0e02524000ca0792042640007008045407440c2c00718800c0c0c1c002802039031045149540c801c0c801c400060402800c0100308018541d50f0b00b0844100e69542507071105481c3c1040003c141d66180900301e810000b01b5404a441c18100d888014005500ca0380468015401442a942540c0b01c003011500411800d1000590320081c80c081030300c512860303c0104404c0d040415090401c2180c1100b14580145880740700b241c50f074440300301e0b60301300580600c003c10010420300c00d1000070000d09609035202c0c201a081d10a4100070700313441107041e42141343e02e440000d41580c0401e80c940c0d0541019003e10f4100f280003090400e80f82c0000358451000c080c104e080140544c0300c60b00817001f1113035151280109000b4880401412154400c0070421035004200301c81ca100002d200e455101d505484c510720300c0c4078540e07044c2e1b002a0007841c500c0d0001150b030020742d503100b05d1306503101a41c420400c0705181a502c030307142c03595000350029100010000d110700942d03e09400031041c2e4180b202d0b102c034400340d403140040c8a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 650820674 1250 650819424 650819443
    0x1c120c09031a150a060203031602071a07060506040b0a060c0c0b03090607020607030b060720030a21020724090f1d090a0b01170a060f0605030f010608032b050405 71
    0x129210f2442d155072402d1080401c02900c1564008500d551201c10403603030690f21184042d0214401c1103408290001c102d288046414001c140f000c1d00c4000520b000025100b00600380707402a4502a200c211071360f100c140b0b070780807503041d0b061050402140f410311642446a6800440d440480002441400c1c00e0003d1901d1142e440d50703084e2560b64030b400e6021403d0703d1551072841d038000410712060022640044c07101c0885070420304112049100e000205e0308080340c100003954943c2c0300302d0f41c3e024198228003025414180350304c05800001d040c000b9142045082040015402000d42074111fa5540a01036000c0035007000342184c80358a1390790b44807003514251100203c00404e025404030b000d0f0b03c000610442025030109040748543c0c202500b0b00c40700e105030194080c03c0c1c8100c1e058840880c0452280422070074080c0070201d0780340d041405140c03601440325410002d90785032000c20085000c020050f03038000082400d4603a100243c202403d0b1014200c101d0640b4100e1420040c40700300b25001404aaa = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 650821924 1250 650820674 650820691
    0xe13050606010201061a090409050607020102070210080915070c33090803010e060d080301060e0a12051506040b090a0501090b151e121303021c120c09031a 68
    0x801d5580400481c04d84542e4400d4008505588007030266040c41c42000c0c109008001d40b0014100c400ba0311403e24146007916080c016035400a0310005500340301e45000c6c4060700300c0c00e114144c0d05007601c215644180318404204440203690100759042d1182d000c2d561680e401c10b032100c117290519120120030722410b000000c105d41d0118002100300b0070500031010b82c01d402514081c01e50b841d140c3c50404151000300040c0c1c1c4046041c0c030480000381c0140141d4041c280c40c0c4d0325910300c1d014003000d11006503882e42200f1001003940c0070540000b140080c803c03842c44031840140383c185e203e07000884c1c00341004201890380201c0d164100070120341f1581c4524100c0784880c00603c030b8903901800707120b0648001008450000310801903041d04000003c2104174010154040c0c61030403081c0600c405659206a40903440307004c3c0c60f41d01c20185541089219401e25101102c03ca006d0a1a0000744c1103070300500803a500c0584600307281d02c00034000d101950055812104a0070701f0181040c100301c10b004100c41900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 650823174 1250 650821924 650821933
    0x605070f020a02061902010209120106030203011127030f07141c021309020f040204060206150a06022508160305210702091f060e04050a09030507030f090e1305 70
    0x1042601c005401400250043e221030320f813500002e03108a85130304d40c001000543d0b400300158681c940b1628401c44001c03c0c40e0b00001040b5040d0301c109429200c5400020090031070a028080201203041c04044036100c41080c0c610b1844e510b000401c0c00d003918089821498041d0740e40010380f07205111158409210201da211141200c01e420310046444099000b075040300141e95080901c66079a032181e1800d50005060845070700c0b40c0030025007a41d0190f001400140c104105000301050440300b00180c140c4100c2d0010892420000c0080d5500c4000d8004203846440d00e81000d0590340e40f0117030802030b010040540f00e03d449407491004c0f10300d0052001b00e900b407086041c846c4d005101c0b0820034248900c0000f015251141c00d80030071070701580203441c0440d50070400100350841562007481c00000c02c0240c4a0902c2c4a04502c108812100002c00601005040141c0f40000a620400b00d0f00c2c01d960605140031074a038004011204041140c00c001c0d2040b03042018450300c2001e01d149001e1a520030012103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 650824424 1250 650823174 650823197
    0x90621060c0d051b07140f120703030513150902040b030f0609060109050f0708093903060603030a0807120507050d051602100f0b0a030c14060a0f0c030309050a060507 73
    0x10f0744c1c54408a0000e80c0000828880c0e9000101044508505100e00c02c0854118a94941c0c1e0b050400112a440349441600055298109509409a180c1c07211403002c80c010301204a864181d05801c0ca084c58150182d0303200d014508559443e845801c400c035015044803c1c11030780085882d9030324002c0c1c40b0000544207a5000140d003c0b041c0c09460320171039081121003215141e103d0f05440341540549200464095035160854803e1000c00b6109031104103500041007a01580d00c4030407402c2c203500d42a00903044001042484c0c1c4002003101c5002c1c10500c0c090925659003501242c205048482d108022400d04040c051a03650000140c030402075645010841511003204807603140d8100c814840140e080b01d10380c0c1c3c995a0b02e0303034044480c860002034085500706225000075088034854004a42210350305400340040b100ca00300c42c1f95181d0090b14600e140403c80b0001030002e007101c112840410501d083e020080501c41e4001c0c40030703950300c13a045984940f203516140300500400c54400002030000a0341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 650825674 1250 650824424 650824441
    0x8060604031a010e24091003123612060902030a080702030610081f0f0f052409010e04170a050304141f200a120f0209090621060c0d05 59
    0x2d110101040171440555181c2031010311554040082450108400e40c000020204014248032070045040c1d40d61f030110100050030095030701b0915001c12031041d88a1182074944401c886e4414141d404450501a00f03818610740000039280100c0c00039050b004400740503041003819000341c00218400c4041c1c2d0320742c2d40c4001229041c44650f10030703c8556480030040f9101500c001403060302e0202d040c02c0208001e908030040c2020754200c1081184416a0b4000300304101e0031103403010074004810f400c00c01018600340c0015600407010700550720002049804501040650440a089181d558a806490328840720000d0020f4104a5040d10f4003088402110b1844502080e501301000007810000400020301c140d50005142c81100d0040456128070072502120320000a032002c00140e680703459032035000303c0b511401d50b984400b444841d01c7c01400f4003d9a03554126610364400415030340d0381d0140031900d8800725450f10031a54616280150800d202d4009143c0c4010f100f20700c140d42d030500458641d200e9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 650826924 1250 650825674 650825701
    0x30306060302130b03040203011b0e0102070504052502190b1509010e0703091b03050a0c0f0501050405220609051006020a0f0803040c030b13031d1008060604031a010e 73
    0x100c1d100d0465403d0b8140b01007107120000d107070090b00290000542c8062a61031b10721903440d120366180441c4030203001450560b8104030190242400b51000e02c904e040c610f8485401010b401c0d0a5511000f0294104d034030142308004041290040312171914040745541041450810180e0300042030b101503403242070942c10008521b5040380e9050b292408580d841240c11030081401c0c1000315045c294050012440c80c102021000166000e440078141411103468541c0304180c2350783c052032081c80000c108010036070b000003c0d80d0031640240c407920390f5007a001a007803803000030300c100d80c524041c80c240340421000110b6000c43d04c11041d03400100c111540303c4401361f80d54900031300001d0019909000004c0001c0c0d5990296800c14410481c10154903160b0b91604c161a00845004482d8044d00f0240400c0c10b5000d54402c92150a5090329040c9401c14808100c1c0040b0b000baa240034030070031001040c4191100000c0358000c0d50040e01400075650829011402103400b84541e520005804011580d410745130341 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 650828174 1250 650826924 650826937
    0x6040803190e060a050712140a0e0d02060705030a14100306060501020a15020912070b1809012114010906060f2c06040b1012060b03011203050310080a0b04030306060302 74
    0x90090031259102c08211000c2d01c0300805c039904201c82c0d01445403000200b4010280d80c80c0300361074a40d0383c0b82740c0702c0c1c1e90808039080500c0101c42580603100c1d115900e60082011038102c08a86481030780e99962070f802d10060308201441a185400c84c40420880b8a030300c030000404e4900c00c07507090100d940d94a00480c1d803401d504d60302405a4121062502c45214158003d002d000e4001d02124500b01e00c454200c0c0c148070740c0c1e500911402800152400c03c0717443c1d45801c1085110101c80d0800b040d410162198080b0081d44e80341248038007172010000920550401d150803240800b4000e00006915203024005400c0c5846101d850035885a00400e0780c0030119618070301e040f5540720b000d20103841040b584a19110140c05d094015a5500360641769403603900141c3c15443d8503840340c0180700cc562000308200e91080d44483c140d0301090005018401807024582c0020b80c00d440c00341d489803034450760000300c0c00e183c3d440014603120341c01c010720030486c0c0d001245101c4c40c069201041034039510901541a8800d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 650829424 1250 650828174 650828201
    0x915020a0527040203071706041a090a0e0714090a05060102030a0c17040f031b0602100903031d0715080915040f1709030706260402010c050604080319 66
    0x1400107080382040c81c0340030003040c2c6106801900395605280400d003240d1007030b9003c10005078201c080c0d504802513220001e0708100182c074200501400c018500007260703c1801040c2c4114240e00c00714840982c0394200a10080440c41642c41c440e0340d9046506d1030720820005940668801c03070009013640b04034800c05100d5441a0051031901f40c40444c2103542054290084411004e0203103621500114503002d0070203801041c401020b15402c5050100180c19010105004000850010700c845940401c0d80c8143c02d192140c081000807042c50f0541c0035102c914210400031103c3d4580d50000c1c0000910f2104440440ca068100c80603800400c48549100b1104182c06070301450070070440801c00301c8034036403250080f8038032481c1c1d400d55030b00c61089030b84000800f0326a00340483c40c0011483d0501c1150020a1141409550310022a102c40810b40b4550030012000301c2e41c4002409690140c0003d0300c0c11a4031605956440c0341a261143ca982c0050325226450391b4652000104a046031103003821501c00c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650830674 1250 650829424 650829427
    0x4020d051b13140f0403170106081b03040201140d0609090f0b061e010c15020a27030b0103060903050c0d0206010608132609060c0709051003080d020307051c0915020a05 74
    0x1801008950940c003d072044007004107c08009240300540019240070701039035514107a05007030030941020050f42d520443e07281a43c0c20000d000050782c1202c58031121954001e8000d4449064105490041c004c175400300800704d0604017640100710820600c104158410041d60780f55482d43c40c244800408580d01c0e4190000c03104421041d158050740d03c4461252081040981610a42030081e040c0c1e001100d04070085104510300109102c0310b8404508100910f4218900d03040c50750311110f0303d0741410300c40076120603a114101c000b410311a000304c0e1f1840318110111054402c02e240006d594a40c01d204110000300c025021824403240c0850b6500034940101c84070080450011450319090290661b40011010400c070344503180c2c85400260040c0004079018160700c0b403510208070265080140300c0719040e150000c1c00d0000442100642c1c082520380ca00060712a981e01c441a00d0a1003220b08007007691780c20781465102c4048903000314010741d01c9000c184440103154080c0000381e0041000c81c1005c980b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 650831924 1250 650830674 650830681
    0x1140d06020322110310050c220e0708010f05030606150d1409030d1407140f040f270c02030a0c02060702090406060e0c1305060304020d051b1314 64
    0x6154000e503030400085220f900668590341d881d60400981c4100c200c0320111072000700c00c0a031801740503400c1d445108000500c0b003850b210700d008403944511600c00e02e0341d500b00c0c2400b01040c0307406402c040203480306458410090911001c00740201c10300b44180c90f00c5588005021034a42030110f0202e003e110050408452400e480c0e9801c0419041011088552030361aa1091104074024040a004001d080003442d515118411f04030181e03440040c00300d509240755424031a41030f030b0100740d1a42c84a0751a0340c0b5500c4449040081100b44150740c05016514551240031414100401132046141c503609040d041b5400040d040c0001c1d68402506040560001c0c4111451180500e01640c2c3d03147c80200218607200701c60b80003c50200050324182d5985588802c24411604171441c02e640000c0c594601c2424528460701903140c0c4181c0e030050f9409014040003017011502c4030a0b0b0900c3c00c0da423050503902c0704501c084030a00c6040c92201040e108800b4414003121036240740c40f50108074180311a00201c0e41d078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 650833174 1250 650831924 650831933
    0x4090213061806140c100b03010f06050d03030e10151517061005040b070b1503060c030a1503060c020609070f142403090c1302250c090212060901140d 66
    0x441344009202d904404012089120300103111080c0c520b4038040c1d001a40b00d00440038076007181c4c000621200c00703a107041e03014070003561094507408881ea41482c001c1218104030a001c1d0400c01c03095070400455052040c02c452324502c030701c03c41c02071f074040c0716540c00001d400c408210f174824410f41603140700031619000702e003c0c0c2c204070018480c44411420300c20301d0241e40700440c0c0c4240e442040c007030b0742c00395400d403d00c03094035039010100040d000c0c110010b14146c1014640701f20030380b00107001c4210f016a00c8100340b0190b00c401d200c0800a503003104080005140c4c600c2c01944404088480211a0040d03260105403681c41d0700a0000381d40d4540c03821b0412150382d80c02d00c46402c0b9004410081c19000030b04800700c190845005502c54062400500110302a003014041780411a22002103803600501ca4255924440c0702c840c0c1d0310780340680e005819003010303051801c055210380e0002c2c1410741c00060480d5010340043c030428090441552600e489030317a00c6100300b5004280f500c00d16071054440400701d0104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 650834424 1250 650833174 650833187
    0x5100e0d03030f0612140c01020d02190f020a35120c010b150406030b06090d030e010e092e06020d0807031401060c02030c03010c08072304090213061806 67
    0xf81c0320b45074005042c580390f2104c02820309801d0317012546589580d5860100c1e1805000315510303011301f8002040c00591200f0042c3d1507500104050104009100206040c42200c1089562640d00900039040b49602c80b007803031010500c000f014440d00c0e2103881c0c0f0305030480c0c01070b4011010750410401034549101071001e01c1071140e0114001c450300350b48610408405903190890000f100240746e01c103940c0c0d2458000081c0c1510a0380c1d419610078641884460002d44a03500c401d59141d034586003421002c0c1288d00140d80e11000c4c041c0326501300c00310f03c0401038000071070807040c1e03170841d5020b59206000a030445100034400c0c0d0390003060b0040e00101041c6003480d0045044a80028860802280c8011490031103002034109a201d4000940b100d901d4000391701342413281e41c104241c15002402668003962020741017903405080c92081104ca140003981c2203808480900701da01c5c0e035140c09580c1d90307076232046c50020b0340100440c070101800e8a1400280e880c0101100d070346040c072003038054078150310301002038410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 650835674 1250 650834424 650834441
    0x40b060117070519110f0a051501030309140105390303250507170307080a02120c0c0102160c03140f0705061303151e02070b04020d0c0302120705100e0d0303 69
    0x50200c40c0b25131211740442401040d20b201300100081c64011118140185484044030707002c19180c40030401070001c40d5004000d001501e84d81681021081690001201d039441814a0701020000d28180c44800e80c4030402c2c0c1035652000c428000ca01d540000b0480e6840748819252011000400c850080303005c101a640e200d43c1f16001e0030468142141a00c9100900c00b07098503801d0310903000002c0041031604003034011f410031883c590440c200740b211800c03901007210140042400040120b400003080609404559002c40c0c0301c0c2c0001100b002d00c2c40c10400204c0c40780012103445c40404400800c903840058402c21030303c40813005000041c81d0009006c499441546004020b081c0e070b6070040049000d44681e0f00c0d1819046400145a03040a9141c400e50b40f1900501103100307004002110101d2075568002c0d070004d0f0102d03661002c030700d030307a10b04a082c048403a07000a40205c280503103000081d00104000003103900907924802014030a800860b00310841c158800d5200340c4c100d240c40c020038400d0340810003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 650836924 1250 650835674 650835677
    0x1b03040f0620040801050c03090d0804081605030318010c0906031515020c0a0519090f0f0c26040f1b092409050108071a07060203040b060117070519 65
    0xa4400740b03025595441040018514452100040e08004c0001d0034801d403603204809850389070440c00c01e0000c003070320b841c1e000500004200640001c607041c0501c190407280341d54071094103e00c1080c414a0071945940084403c50411010036011864410741030084580e441050b60b283d42c6e202d4103106041d00107140e00c0d402c00401d000c41d0754011031030700d0305850011034002540e001001a901c01070304001249003a40c00603805142c0301c0130521901900c1910740015140c452002240103100825082c00904400c1c0300e90220350f0500311010301443d0402c540320030700000f9103005000000401c805d0900190141d5004240e818040a03000c081441c0c0f207800f041c01400c0940620000395122100000d9440b800c8400464500c01070501000e9110300030010002e01020030244039a62400c9001d507111981885851b01602e011000d0041030040602119160b550000045443c0e0815003400d88505d603046074407038081101007404107000c00003050741610410b415651603251440c080c01910104001880150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 650838174 1250 650836924 650836931
    0x10110a1b030201090203010c080a0b0d02090c0a020c101e11061503011d06060a230105130f060e0108091911030309031212011e0302040b0f06030703050f1b03040f06 72
    0x5006940070702950011100d107036289c02c20303810f19807190000c6034209070317405100d180420903100060300c03032003810f035480b21001d04030680710a003164082c0e007003625100c05a41d2050084108201c56604800120280b0104843c030808889891805440d8024030804007241c0350b1000703000407203003510a01c00c40d040c050081d00110789480109036801101c0741d29820700c1010340020081080f40d0401c0c4500400400d240b160604030401d91209811001d1680b480340350421400103004202c40c03941c00340304801820441a0b901c545569441c000707085042061344203001420a42c081036501317000181d0943c0403103030081150300d481c14a50300c0512109040380401d0705400700340581070840d0780c24080b114012400300102940c590341d882e03803901e0007001600603108501d40446400240c0d0106003182065a506642c0081d40112500001d0010b908403510903510241c000304026843d545500010700070000e94402c81c020340c0f198640c600c81a204c0c0c900c8520520806e000180201d410303403014091803805001d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 650839424 1250 650838174 650838191
    0xc0403060b060d050406050f071d0f18040b070201110a0503190b0d0c090b24070302011b050702040e060618100e1608010f060507081b010203010810110a1b030201 71
    0xc3c42a21822034058503001d81e0342c1e0410020040038140c055116117645820842c8080403a01003100007400034185025a0480350001d14030344134004d00d10b0448000d101e04d80c0782840c0ca0310346031202400c01c0703035000019420400810041080f030001d44101c2c00f5262540e50450f80d81485c90301d03011200100250001e03442d0951560142c90382d40e115140b0f280900760040e02c540c00c8c03c1c1d8103001e48044290b01340c003a00d01208001c441d88251407422a800082d00c00c0255200300509003203015003c00c010703241052003540d100d1806d403504170b0300400b825842581c050140d60301007041d083c1c40c0c6204480303c1e90803544030010080c0a480300303000b50360711817038214000904540f25440c00b200004111005510301d085070100c594055004460503005105404448030040c6c1130100081203400742c0c10000307004200100301750030580c0d20300e104541c00e8141c0c0b6000715120b41e0354203e0b05540b120f040880ea803100c1e16103291000081d640d01d00f1100d60240640303810f1803445086c0c01c000c0c400f2000d144198115541d54541 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 650840674 1250 650839424 650839447
    0x81501030f0c030603171303020904030c0816021c05030307030c0915091a070201020307020609030109141c030e07030228060503060f0108040203061512030d061d0c0403060b06 77
    0x940071800303103d542c0011541d086160080070402007140040010905010030a090880302d0000d1042e40c1e41695050741945035850b054890005483c002800d03200301084135103080e241d62491008690003100c901d042c1c090668020b0000a801400207452500b003000060f4403680281c1100341e110341c6a01e050215982daa04003042d1903540b1303102110024002480c2004a04000e502c200c0d03104c4410181540390244550000c1d6691045d443c0082c001e4002252600069800707510106006130000c1d04002041d018184107a03c0d0843c4054900040403405000b0b18018072900c2034040001484c00181002070840c0c0800c00c030100c0c0e01c0720700c1000110045200080b40500c0381c140d0f00a14560301c034103482e81001c008200e04000c5000b01c8034100312a031804c101c056680020082e400540780c500301d0030003220403408a0b401c1d540458200141e0322001884901c200c08503400701c02190000e060110f0310301c400740c20358101e0720300c10385000e038503031071709010500c0880c0b45580b101c01d020b2801441e661403c3c420404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 650841924 1250 650840674 650840681
    0x90506040201111f0203010603380f1002100f14060d05160801020910051908060301020405031516030902010c0b09010b0d1a060a1d220503041401050a081501030f 71
    0x13040443d004001040001c1c1c00d8001c218413030281c803400c00c0c110b02c4416100701e440e0b0744035020903540f030800003101d1045840d00300b102848948050200034120034103042c0170303690394006440c0003000c80c5410741041400d8854800c8211442e100f0358089010b4441204004140e200031006450f280200d030380b200302e0010301010120081402d0300001da200e800710020440800d01884c0f43c107060200030001c040c00034100f49080f401141c0207040242150701ca81c00464028007494100e10f0b018071a280030441407000c4400c1d01489004001c1e41507012894a12040b4142c40308070400034041451070032044001840305128941c44000320000080b005031010000300e070090081410b5540840000d140000320710544010350b4004002d4031025000307450803000060b003c4072004100b68070300603040030428081500081c4034101e54516800e20342a021030a0150b1a50f21900c24621921600710ba200a594018800d55608a501d51641078550752984c80490440d0030401040d03042503074424403901502c11912 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 650843174 1250 650841924 650841973
    0x1403030403020a0c090c05030f180f030d06080111040b0c010b0a241409060a140403030801050a080615090414060c0a090605030606090d05030d02030103060f0b0409050604020111 78
    0x38003c01c01c44820741018040f00815400c000001828038410502c403580003422030b900584182143c0d09182c0d0f42172104070b001d00b03100c50354034010701544104000340f86000014100751686500208040e0b90fa50610b2800ca419175802d80d4210314042c40200400724110300a414a801c100001042000c1010001520803403503401c00600c8010401d0b40740070956031480a15040300e030604094103c5000c4502d2040240504030a00d84242400940503000500c1660720365982c0342542c86007621542c9070301d03000d04201002d0080a005030351100000484990006505026001c0c0352500716090144000f4001400e80041040d40c285806081107412080c003004110710a990025140d0b85844c0c22440051001c03490394030480c1044014003e1040f0355940004858030507404444031a071620b81490064150700850030f04403d000e01c080000401d0180700e80280440782c1c1030315010003100c0c04850400088641101c1c020303106920490001740103501802040e10f8040280742262078007030020803c0b1031030f0254507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 650844424 1250 650843174 650843177
    0x3140a0507030e010c03092108120a11071a060607050d0f030b0d1e031b03050403020112110304060902211e0307050d0f0302040b0706090b0615040b071403030403 71
    0x51a00c00c0c140d01010110b0f0407803013444e000c0c000b0240c9440051154450380595281d544404484103200d0600704035a1400703d0303010b10200e444a1803001408130f0080704480e200a0b584c01d00034400e0622500c14111000ea43c0c0c40709402e51007495a000381100007100a0078103420113400c121107030107c0c1d000c100c1c90541d044656915416621040b81c0101907540301c00640c0e0040995010150004a19440380d1911035206500b00360b22601c04d04088a401191090211003008001c180c8028503500400030b00c00d5074000e890301c0851002e420f69000446e040d814801c982540c0a0022800207004c9030800b07240d030b0380010311548544a51100c44481d82c0010700d0308040c0e41d840307042ca001c5030181c003504850f540f9011102a500784016610350300c0c0c68060142c0c0d01810000b001044042d0b10b4041e9058601511140d9400c07a1506105e2401e1801080020340030f9502d0300c01d000000e20f25203042c1d240c103590000316181c210308091501e0704044841d003114204450003811560b401c0e144d4442000a103100d80d000713 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 650845674 1250 650844424 650844427
    0x61d07090513050403110d20030706050106050d1b0518011e051309062402070b0423090709140d020d050703030f0e10260a020a0f050c0d0c03140a05 65
    0x90715020b0906c003598940704203280c0006c110600e006410009006187e00b080d5482c1039403542d121362550441c49000307002400585001c0011034559032040281140c0ba65005040101d000f51102c1420344412801c403040009400704942c2095400b0820343c00302482040c186400c81c24802015000404942c0d07909400050010440e900f4080c7c1100c4508006c104d40c020800c642400d01021241260480c9800c00c44000e130510072207a0b00f0301c20007c060003001c00301e000b1901c2d43d0b00c3c4c811030042161520703088182241000804030040c075020b20803501800703041d1030307143c1000d180c10480b042820484440b1030b4000c0c42c81e5900070141e1203282030720602d40e110b84080e164040c1540b40181400c0001c090510030080b00651004154546420f1203040c3d04807400c081c4200d039041d108192028202d8055812840042001d0240080c1150050b0080360100c0c0c1701c031b084542111100700d4550040b01880c0c40a42e0003a60000a4180101c1300000b100b030003850a0b000d49284900000607a600150601c0c000600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 650846924 1250 650845674 650845681
    0x6060b03092427010c02030702041b0c29010306141b1c0b0301020d0f0506010513141906020d031811040509190302060613061d0709051305 61
    0x30a20995048101c1c142d0340b0000e41210750b12540040d00002d101d4907405606424100c5040d111004044000700800000d00850f801d100009440b40c0100004030b00560800f8500300e81c0c0c0006500044256071581c9c2d070001c1d410b0b0151284e4101e480300c010440d403500b11202d112080c840280c108240614019070010039042003101411241c0d00c0010529241e8090f0b08030b05106d140480c80c1124401105c1c00a003d0b0a403800c90600c03c002d014440c81c565141d8400203001c00c10340c199401c0015500001803041215688440041d42e072840b031884161045101300400b0b02c45900c01030a012410400901003170146200c00030560680d01c519000740f000740c0c2c40004247c2c1103d80c103015400c3c032003004940c1d00c002501c895550f00b5a8100a0380424401d51301c541c0001e64004007004a1420301c0d81c0800744560858140c00c0194442300d0a444080c081c0702c507014001080e4031a03008500c11500c0420344810900c80840900e0600350300604440200034182000085550b240007800310070a128100006a030b04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 650848174 1250 650846924 650846941
    0x1412040806070906020a06020d1806050f280906180f06060902040312031a061b070503031305100207050a0905010e0a0b01050a0e0604050411030103030f1e05090d06060b03 75
    0x4000705500b08006150006210156003c00c0d4102c1540d4406400f688401d80222103802600c808078000e48200b400b5a150b43c01c0c0542c80d04990301500c0003200070240d54840500b542072a43c103c09002182540c1c00c2c03082851880140e10016455018810000d400803819410751001c2410b48402c0c0e80107005141c60f14144400b5110340d0005104001c0c0440c0740030301e0f5035528150003414500e80c4042c141d4407c1906510300525022200c8500002c080aa4484030f6606880340115985041c04e02d91040c01004125420000100d620640140c010080c84030303e80030400840c10b0785010240114000d02c2000030340b80d10b9204004020300309102001c01c066040a1415201030401004000c1e00c90a101c482c400c0782e41c1250031503414003814900102034401e1480031910340e04c0385610044d0060f1804014013811403903203000c0c41c1030300d01ca82d07102c2d00c1c0c100310300c6800c441c85500e103540740c91a800048c0800408d280900018805540041c110100d210f020f0389480c2d0403103500d507102d443c04070000002c20500c2e0713 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 650849424 1250 650848174 650848183
    0xf080a0c0c060206070e01050a1704051b06070f0212030d180b13021e061b160e0910021c05040c0501020f0f10050a1d150a0509150414120408 62
    0xb048584001c0215241c0384100502c418211030780c9a0600000244980d01da03440342e4140c0d04858071000d55000755007800c3ca8599641d01a1070503021105a060031003001d41e00d8901c0031203080541104a203021000300c0c3d000c21034000c400d540011000d02c4200f11220030903066000300d02a4243d034020960205e00b0904180341c8044004046ca00d80c1c002d49900300005039070701d11107410030000080703040c94220703070a10205225204881c02802504400780d25124030000014107100107495172100e0200150303441c005501c040505480d00300c00758100f0110705052499541c0940040380c2070f22210384e40a92280e01010803508284c4003903450040180c0240155601001140c90304190703500203140712004840040d0300c81c4035540c03442c400141c4450110b000688960414510302006242140c003280c1104001e0795140e1019060700076100d90f4800149440056210b990701c41c4508070060900f403d00c0c09a41c0d000c200000308102c488000102c1b05200c15201007090102c04c2d46103500840d680c508108106292 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 650850674 1250 650849424 650849429
    0x5040b0a1407121e0e2e0b040b04020403140c09090c010e0612010b1b010207080405061b10020d0e06130213111303030e0901210f080a0c0c 61
    0x14100540016015451851180e100d4514507000200c2d02c1070078200c20150802d130906000c64158021140b040b0b0203554440703a02e4441050844901480c103440c002200b00003200c031040590782000c10340a002e0096005602c840e94010400582058600006401c0380c00c0394105841d1310484440d40030300fa81040007002c0900c141154403404600c0c03ea841c150351840545081070410146030644e14407500c500c029030b005a111280001c84a60715104241201d0f001076008031480e0300e19000c0024102c4040c404c03209a190006601480d00e4103240074000d440d40a92511890740b01d1030800030f00d014006100d40348900301b0112003d81c0d81c00c8801c40700000c0d10700341c1b0003c2001e900142e003403011120325600f030a20300315416500340d00580c000010140062400c03000c043d400000003e41c1c0c582403041b400f50402a6446921011041031043d400d0100b140000d010b0304906401001c0c040000701300c00034003114094030038004c0c2d1180b00c40311740d42d002251300054010804640d01039080c10800141c121a07201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 650851924 1250 650850674 650850691
    0x190f0c05030d0e010f02011a040903050c060f1b0304020310050919030e010216050d0204200a080714030709090f020f1c1b02060105190e04050d0f02070b0f0d0212070305040b 76
    0x2040381c0812340146200b0f0142c040c58400d0317130b5a802e5407007018090710694080c002003a0a41d0b605203440c541ca0611680c080320518044c40c249135503018654a4a0283c1e80942d8024000b4141001000802c00040001070712004051081001450480c400e907290320107050f102e50345103111202031000292900c840543c08403103428a05c5018030441d1201c444002c0606d404030340206107480140b80f80900c4804802c14508013000024400080700d4000900c10f000d090b4541c1c0d91586060784048444041c00156041400900104400c0041007101c1d0001d4602c440c000c4001840c0401c50020000540d11801c503514900d003003000080c140140d284608501c20801141c1d1320341c640264440252542d0050162500c2407007503501a205140503c482c01e800341c41004100505810035091466865800144a1000520341c078003121442d403002c01c1880c11512180ca116090185140f05a00e0f00e41190741c030304101582c00c6c0088541c810100e52428002c00b50754800003620708060900c28000d1400910004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 650853174 1250 650851924 650851931
    0x1b0302010906111e0a0302070816120c030519020c0301060806150a0f0b2b0905120a0e1c080a08010f090506130b03010e01020a020c12190f0c05030d0e010f0201 70
    0x42d100c48241c40900c078a440e040c0c20786603175104880e000782d000b0f000c0c1c080040d00340540425009085e0141c129004071003409070030100212060303104110746001540c40010001001485103035910000706206507110442401034075000e40520000c00d08507000d81c1c1c00107101c2e0340202c06110a134038144034405080c0405581802c6d64a080000242c0158100d1080084144000075419203241106107001a0840d40b800c82c000055a8510b5003005400e00c40c0060320a400742d04982e902c2d10036080700311890741c00356071981518245039800708a00070301c0c00b85040c0c40d0320403d0030400001584141c01801d0222094480042650501740b1548001300c0d0740e00b00303000300b51402003408070325030b42d0302000e02c032008042002007600e2032a900400e024214001880c2e0403980081014100c540d0040b403844c01c0c000003614078603000798040008903540c0c020071082c0120002c00794070040c0402c00b0403281c11f000c1d0340504015400d007907645c40030a191656502e0a04005049100000095a0702c6454084204190310090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 650854424 1250 650853174 650853187
    0x1006020706080a09120c110a2402160303080708071110180f0c0515030105090a052a03161d10020a061802040c0207080a0b04031b030201090611 63
    0x40d58403800e500400c0c05010790034002441d00907080d0007080140768802000c0003600703403401c0040c08220301060100d410021049007200b0506001c0c420004442822030b03901c1c903c100058012404030441c0c0003c60843c040c1c5048070741d00c40749034072404000398400d96070640e040ca40380500504902c000380c40a810031800100d2030102031400034a60a10405545000600e0311050903001d600e004200c1c0003e1480120107003c105110070301d040a02203d4040d50440706600c40204810507d200900425a1281e400e502042030360700242d00c2141d101082d0400b40007040c0030064000e4026035060503000c2404000001c216019107407280c8540d0b0301205003003a40007a00860320900b01c076030f14008910b0086892511001038984204180c0034055003002040000400c4c00e80000d086002c0000160300540c1402c4c84410540c5c400200c00c0202d80c4082c0203402440c0705950341910380c0401030001e400300819001126100c0c02c0c001c041e41d0011b407180d00000741c4036904e4540700041d280000e1168840180a2203032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 650855674 1250 650854424 650854427
    0xc0a020d0216140609091006081605030a0f110708040302040c08060f0910150e0415030203070e0a0b06040b07050f01151206061203020d0e030a152c03121006 69
    0x10482561503650f003040d400201440801e409000300300041782e11512110a1006400d19142d0250a4130010368031f00d10ba071354691a00d6801c0b850807002240c0010320410001d0030a1506034803000910300801c001007621b00c070340080ca650640100720190760b20b0000190400840c60240b0400c5c00c08030160510080c1443c200001800120102c800103024005a4000a01140001c010003001d0441d5505036941000040d000a05803c10a10311600891a101201c101c038440c6052110440e42c1c0100101030290a10706c0c046401c032000341c002c50101c0d071102105081e03035986401400162051070301d0141c58000c1c90403ca480c10858103045e03070503171340f4050400540100c001c408100b603884581110b10030b003022b880c00d10002c2c403c0da40306d60340c0054044001810540e000c80d91001e0303851199a50307003110011504051b181c5c01d940c44010725240424104a0511405400c443c01e00d0816502604050781a004204004007000041100d980c2000420b81079481094142c160400c59004a0122031030030400d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 650856924 1250 650855674 650855713
    0x314060a090b04201903051908032a030403050a1e12020928051314042907050c010608150604050402120f03041a090310020901050f030c0a020d02 64
    0x9401d081c52284a0034151040b105101d544604c090409200c6031a483c41008200c100c90000329494002c1043c00130804080c001c0807241990004001c5145448000202600d40203148041400c0601800a0b5030446e050402451103240680c1300d9964030961104028000c1c07029100c0451400d03c49510b015403540c1c00041c18520245503c00142e4031001500040c280c00702c1d81c0f210070820b070034850030703000a082900c034050200e585c10b0320f2404885010710401c030142c03200c1149031041000c4a10000e800b00c0d81141e42201800301c5a0110340c4000309003003031401a12000c442e44000715400050001848100b48034940081c0b645901918003c00300146001c10f40c2d0010706200d200d280c4441c04501903685000350b100541c205d0b82c0444131040d810b100680c0c0c5030f4003d8400c45010144400c0d4150385010000222003a00b60f0040250005581c5d820705500250044a51603040010500c042201c00e81d50700300942c0288030080f08907441389003160000745440b980c014041e00b10741086440c00c034500c14220 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 650858174 1250 650856924 650856931
    0x4060e090124080c13120209090d020613061b0e03070807050a090b060c100e0c010804020d020d0618060204080c0103150b030a0209130f050f010b0703080a0b0a0314060a090b 76
    0xc1d100c3e24688860140c1c8a09000f0040c8454100c6060800020f28524102880000743c5c070a07203c40e201d5a9603450100e4a070410300340640d0240c0c01500000301c030010b40c41180368140f442410001040710020001c0c10b50070f29010280302c0854000d09140183c0d03e02000f143d801019003100610340f940c200004070b46000f005104002041c3c1d00c900700700c800e6503200c200790740540900d1000c641d285e000c20040320010344000e0281103664082d5914100b000c0d4454552a0300c940e07006410108010711759400c1c00303d50b1060131816030301c0903541c9491030310070035560f031110300f02d14018440940c540d030030080c075582450740c1c400c035040c1411f1514201807138400007402d0300d504031842c410b16640c40b0360fa4805e080c6d01030f105030b011341903006401ca2480160809240d0101509480110082080341e403024007844aa06080c02005c5800b40d080c0728000001c0e1090710340682c003e042a00114141550760085840031449804c100c03003401d0740c1003102c0f06268040111301e900509508003800300150640307807202d07030902c041c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 650859424 1250 650858174 650858177
    0xb0901050708010f36020a0903031101020306100e012a060509010216030c050a0606030c0306051008030f0703031e1b0207060e010302030901020702090109060f23042004060e090124 79
    0x1303000340010240071741c08400700703201e0201081d03560340f5030300c0030041c100c1c1001d01080707011801404a10345201814070950340f080d84081d0040840c00c0c800c1c2800d03070741c0c120340004e120304201303140c259880407510000c02501503040c0540c07000810800c618001c41950801412400307260301c184529402d006e2603094505150340c26040c24441000c0c90f0801904003620481d0140c000c0703080c1034000040020000c0c0e05811a4010902002692a00e10003007004007594414030005900501100301c0c025402c0d0014040c4a209081c0002c44180c0090004242241d41c403445c040c2030b1381c4501008125041d06030080c1c03e00c160f032010b481290305260000d08a8080c281070309040690110004824480c00d40c1141d61254004060045540c0d5404a44c5c02518580c000c07c0703201f441c480341c00540e1110448090008007203001c140e0040f000c221042c040280102c0c40a960f944143e02c100b81c3e002e07001000200040e1003907a44030070b0b0768030140c401c0c48510481a0b21007141210030307501d09000007110038000b8803004100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 650860674 1250 650859424 650859479
    0xa030209060d050706020a060f18081303060e03071109040305030c0a03020f0313050705040b210102160b010510090302220b03240a020f0406080c070b0901050708010f 73
    0x31140410b941d00c1e1601e40c000d20510990b04081100d80c2c000034800c43c018402c00052108804016400b01500e001d0a040203d4048403c414000555860040c202402e407440c43c1c1c82d1459580e444400903104090301c411419007000604005001a04010445220302690600d03441c0c10181d4004000d4400200003646c44c08003c01c0560209120b40c0445181c205190740440c2c03282050125050b9500c082c20080340c1c18890103400040608041c0129101041c0082401100d900a20704541e03001001c100344140031755017001800d45d640c82c007001c2c4040c0b66010b9140190340d90305100510410303204101500c000c1c8100e0420400050340c0f55070010f1034141c51420381c8240e1600018001c8050444005859414081d411942407803501015810000c111041901f4081e80c035030721180c400728840c1c0030070069004420402801194000c1050b1600310000c2d501083c0350107410b0b20f8031208120255038200c0709945507001d111843c0d07400025140035006031008042d00c0c0303181504a07019507043c03008103900380b0b46 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 650861924 1250 650860674 650860681
    0x1231002160303030209150906030a02071b06270b04050118050306010609091a09041b0312020114061c140709050c03090d080c190c050f0705031e0d0e040902030d0504060215060a030209 81
    0x56101807240038224041c100b01c40c1d54540a010e4000244e00d509448011060003040700401c01380c9040d03200b1542c80900351071a042c1448011140c10404920020f00c2154056000503e0386007000201d000340301c00c2c2d60f40340d8802d040c43d03e110b040d1020021020700c003281300703001c050250395802100760b08594403080c103044500220710f4400240050350300c043c003662a0121111085030301034010f900001702041d07040e21680c0d50310082101140300740b402c000c1d40e80340440001000076940722007058018042c1c0300300d416583d03540441c41c040d01c0e0100c46000d0300d41808010300044880c20042442450150300303280c4000e280c00e02e102da03494000d080c0130b00da4600b0030480d8900524010303a190841c190b00802580c080c4030640b556a47d80d0016031040c04e01a22510103031101078041c424040808600d07000c0a400800341c204001c072501c440700715140340e00c5543c0707840500c01a9010070040b6004402a00c940707403a145400e1020f4184403035045d07034641c0b111030748080084590300c2c408410256a41150301003c1c60f107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 650863174 1250 650861924 650861933
    0x21b160e1e04061803030203060a080f0303010b07050f0105010b1803030a120b040207021806100c03120c050409180203100b03122809030b01231002160303030209150906030a0207 78
    0x3d9070303d03440840301c400480420301745a8540c00861240c0c00540d42c3c2d240c200d07542c1000f03698a42c1c2001c803a04084d00203100512107060b01500030300e0014001c0c006c6500c0c580c8030044003402c4030820307070180d061b01c800004c0b00300000400d0010b010000b1002c4000d1818042c210340d0145c8000c26022088140d5503a4042d441030030f0781d69034141d500054015040408048480703013610039809066074420f2150216081e4081c14612850386095100d03855621000f05000501501029100024040c001c3c0403082c1306c0415648034a100392000c085149002e0740c04402180141410000864100d041090a10480c0001d90701c000900c5c07421484800c03c6035a4a04500c2d94004d0001c0c10030040700010071065110000e4030340e0010140041d680070b09014926640e0740e040050b580b0849564000c007a0380d02c040b00c2941464100f1820b1742c110501c2c01031310a08920b00740078041503009904200c001c65070100d8410b41034142021030600c00342214401900e0498408000ba42600004040403849500001c1700070402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 650864424 1250 650863174 650863181
    0x4020111011808090301060905010b07030c060612030c060b0102010506010912060b0a180b0d031b0c0b1b070b0405031513020d080318010b010e010c06021b160e1e0406 73
    0x201418500c2d05070b064504542d05a0008240c14880d60034040081605103c501c25941200c0e46604400e1802d50365a42c182d0b41c2c0007842c50252519580e030900094150001c000e4190020b00c01d1f41e600c210005c4031f290600840b89101c0b4014110380c5031104000c1642d070800d45281c155040c0444440ca0f03451a441c3c0440680800143c1b80c0d007018881c4000180b2120201c100c07500c1d490050801e0150900c00400d001c0303960f0f40128080d000540180742c181c43d40f440ca101c2881481d01500c621201c00b5152a60b020195024540c080e00c05214a03042d6144840140a10000340005806051a140c90003000070342c0c400203900324843c110203280101c1c60075840c0700700020701580d024110030442c5101d0b042c80c0400d504200d074842c003240750200c0c1e541c110304010310840c02c810b00141c490705101020840115081986000121513060b820082c4600c071900300d0344000e9820b420040204008001805021140070145d0f02094541c0111340901c01328400301c042118500b40040300b951195901d504060014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 650865674 1250 650864424 650864441
    0x20706020f0c010b09090a02150304111203040f0e0f070e1201090b01031e051509160906080d050406020601140a15020a1b0b0f03040501140903130b09090402011101 72
    0x741c540000c15008005064001c8180390500b12074003220ba07610000425190b0403515802980040f0b11004080c201c4042c1000d0758005001e003099180030240c0c0d101041c4c03018403440384000e0307a03400843c003009940d495201d1034018200c0620054460304043c00c6103240c41c400603104201f4000c00b600701800c0c1ea19020088000054007000a0000c5815070400b600c05040078041070710000321061807040c0700600005100c071000e40c020001d04040c0d0b100500045030800187c0102e1840c01180381d0403103008000e09440c0040c00d2200c9001484074a0524143d2030424248918011f010b41031000f0820242c0108a050440c0e5000a82c02c03c00d80024001510242d141e80060044502a0000c810140e90005102c813245106840303400650030040c800c00b1310315405101d6110410004c0107042e17a2040d4420255401c03920410000c01c20745e498076000c180c0b220040b201c0c0c0503035520215242c000c0050300403400c401014101e00c50380c80d01c04c00c0e0010400d281e100802c080c0c1400400b98400f12101c4007540070b06030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 650866924 1250 650865674 650865697
    0x80309030a15090c09020309120406020c04050c09120f060f0f011a0d020406050c060907081209120604031101183305010b0a0314060307031b0b030109091a0f010902070602 75
    0x8513a81c84580501c029001511458000c1c401c02098043e045240c1045400f074840c00c3d0000d048100d42c0c58200006041c006119a1041c90207100c1c000e52a01c403000081c018075507030700180c0718404194038403034a0300340005c1130010342003e44010703ca20350509681290641300c40303544070030001c01100303003040305d91058201500c000740c800140001c0d8140d000b0058000c141440e410345269445010f00d1994a29160050242e2604403c086080924030f010041c490104007400c000660540310b480c690900300112016000704500c8000396040d103c4c20b2040080303e030103c514082011019031036468040313410500905091941c0e0120441e44603a03a104403203003500001051201e50b8442048926942141c03603c280820306003003000d10807171598040148203000103001400f5803172550319120b000780d40c111003800c0d403a00401e030041500310300c500c010b501070580481e02003420b031140d00c2c0c00c0c070001900700c00c8110b0442d01c507418407814200400c415411111103500140c2c642c101410024000c0c1700301d049916 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 650868174 1250 650866924 650866943
    0x5180408070b13051f050f0c030a0e010906060914250c060e01060314070608091c050f04330206010501180e34210e0102130f080309030a1509 62
    0x4030b1111104031000c00322000710001b0300c810749841c061828002815140f0f0301505000780300199503e40154416041003402a001003840081511241c04442007500104140c2c2e8440004440e1211001c1c0000e400103000c440400401e820350361081d5140c0d030020440300800546c080000c0c03d0140e5604500c3d44c41d800800200200c503560708d4000740214555200c40c1d0a4040d01d480064031030b0007441c0c59407086185c6e80c040c00003a5141010b24050f0588540380c0d5007800024461070440403074400c0a480503161520070300a200480c03020320802c660710110300e41b0410303803908105010383d603001c10f0481c11a0001c1c00c0000807961230103a1842007c0b003680212030440301510410110401c0c5843e03492180ca5100c00315143c001c82210700620207076012940703a0118541071041c0490307001c0c1d00480d8042054102c0009031a681a43c0b0160030784c0c1c004040e0029108100c4014454038043e03000c40801040000c1c015450304402c1303800300f0386540f0a0796005e49a010107078243e8625200607080200455806a01c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 650869424 1250 650868174 650868193
    0x70b040327030b071803260304110405060a05061e04080f0109021801030c030809060706050703020307021b0f010e0604030b0405061f050a27020a03020405180408070b1305 75
    0x11001024803040c3e5003210450701080f8064015501d117540c1103190b400e40f520050464883e94402e80240e9407800d01c042e10010301500100303030030707000d036015500c41c00c540b5228a081004120690b20090301940c46444041c80411a80c1c0d1520700319178a040b603490b034000c0110070010742008203004590111120340100e882450000e10190700c03e01e032a5100b1280b2109580608207461518442404010100f081101d41070011034807101c0941203219004200600e04074181c1e481000346c48065804002080d00401800000c64040c8100049040d4040c203540c4600ca00740b00040ca5000c4a158840c14030a009165405a403501c40865019507000003405550f0308003031502e650344030b000b10f400c508522410b2504141d02100e16a861003110b03030003800465514100913484455214081c3c00b90310401041d0003140c2110400d0000e00385842c0d00340c03001a2142d01d04030520036410060710b0f07200074442180080000003006a400d03981ca0b141c00816a034129030391410f03036500c1d442c0c180a021780b0340c0c400c5801c034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 650870674 1250 650869424 650869487
    0x5040b034201090e010b04050607051f06080d03050f1306090b0705120a02090315150a06181e09091704090f0c0309051b030a1a09070614070b0403 64
    0x40301a004020703030b9024001d40d61000500320000d130a00480c400e241c01003000300300d1450a100504042406141640c182a524000700f8500c0112140507030b0260351150300802c0412008c0c40f80c4d49985000303080600c40f030310b009407007045407050052a01544040c41001c803020702c40c00d42e00c4070900c15480b2068007802d0424074409066500294a2030942180c9200081d00000a038000e4400848010740180140031030b5001407036269000505000751002100841e010581da0400100300801d0551a0001040118407046404400c035400248102d036121451401d001600f40e568001c5551060000514103d00d01d016138614500d13201c00e00d0365220101d03011a10707000030b5202a8500ca0103034400c02c01c0106030141941a40c40720003000c2c090350040301030032000f050804c4000484080050070342d40c90209540c0c50941d0800c04400c090301400010080164201041115801030156410329020f42a0008040d004600c62003600520300240400410304144c05040380b030705107104c450020100201d01001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 650871924 1250 650870674 650870791
    0x70b0c031206031c0c02040e0a0b0415060e2a030c0409060e15010c0c0b0c06150909060115030f020c01090c1e091a0301050f01080d05040b03 62
    0x145200440342080102d0858075001952025801038075115207201d111488050b6911220f036081a80c02c951943c1c9880010134050012030040c46c40344c1c0e0506d2480c282820903151400001c1c4010025031719050701030007160224403030706921590a00304003114001c2074079200800e1210250500000300084107005000f4600e01c003400a43d0f00c4a9002c000e400d0346c6207400f0f11001400e80710354034030960a80c0f0a006a511032118804150300030740d403400907075684e036001701100da0011500c8209500700d1814007400303101c018801d181d17007007040f00c0348682e41c102894180e4841c001031240040071049252044400c41c040c0d08180641404003000310744a0001c40b45603806010f1105017110b02035140c0c10045116011440840081070810144005007420300081d01e008200c11707509908540140500070425070740074020184921544c401d414142d514080305a0f161451220390f14040c000141700520204540d001621b601c4a654004062030301c41d50030032071800070044e5800040c584050020342d0548840c160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 650873174 1250 650871924 650871937
    0x604031a06030610050f0102070806011d101409090a0f08030703050f070f050c010209060a03020c101a0120100618090213091506120c06021617070b0c03 67
    0xd4402059032071000301511084200c2d8041c8103c11022002e00490901c5112505e44610600464031880c0d25920031070700d090001d9110b246c0c4519152802c000da9641070202c0340d040f003503811800242604100071280e45581c8010f116003d5018100000e228220410a05041ca60090004215a05141091591030303104640c50070200c0d0905000ca9400c0d48121155441010150340311030000400d010126120750104621201640d024000c0c45001d6030368900801040340f1702d840c0141e031841441825400c1064640c0b18040c40c1c0d140070341070400305c49001800c0e104c0482c2443c0841000c0d0840e412a9600224201004c5403440340f03000c51038409000398010820b07240b8424084a1176a500d052250540e00645c10094002035062070300b8060001c1504100042d52080c4030740e24804902590550031111940d12180e50007034000480c10900003048040b1010709041d00c007070325050f40310516031081c108140c0305d0418040321134a1103e07807002007405541c000c3c0465124455503103608610b05541c0f5000007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 650874424 1250 650873174 650873213
    0x41a03010e06120c0f0a03060510170f030a2001050a1e09020a0e1e150108070c0b040b040201051909090516080408030901060f090e0c040515090a0902060403 69
    0x1070101c1c42074a4168016494000e40200602c1c0c3c00d403004c4103020509905d01e0090b50000b02d940404400a4000e016052080c0903419034041c40514100007082d040c1d102d5100b07500c0540001c050b000e0610404022111000c2d05400c0c11505006104d86680020136100d6200800d03518250510644001c80e420420629650858411480090f01c02c10001c0b2202a136000390312104042d02004403401c1c0da103642ea407021403102500c070001c52220800107a03105c01c969940450520b0498100c0390b41c0c01000c0341d908800c00e840c100001401039901c40b81031032400b41c4083e04640614001800f10380c071580c1250245050036440800c0031035086406403500304240227550040d800c05000900510842a482d80e05450036915000d803600e46844e41c04680d4005420399003155207414000c00c40f0800307080898000d0005400010706003c41c441064102032000c07402621a90030403051010040c1480b1344a00c018104666070350351611640000d00043c410107800030740004002c54004140110350031400785002e0030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 650875674 1250 650874424 650874449
    0x1e0c030a0e0d0504060813060c08010305250b0c01110d0b03240f07170c19031a0f0d0204180c0602030a05030a0c050d09060f0f09080406080c041a0301 66
    0x1c00e80303419202d640c0c50340d070310000031001d0004008682c0704445460f000040d45c440010410040d071110800c0d910100b05003804184404010020020200704444d00d1840d0460304965109d0b0b48200740030403464030300c18288400c00116014191031429800700d2024101043d02699441712442c0041c00b41042d407000e03500c01d000c6d907003000420034014a024104500840074003000341c0e546600c3e00000542c05490081088020203010b600300d0300f84006e150040607540341960300c0303180c85c0e20070039a110300940e62082054101300e840e0500d811a100f201361a40c0086a5484200c840d8401090f503c00700120040d500509203030344030844a1030b41c030707002d0b4503d40685130700c0307880a8960105981d2480342042800001e1010400070740c10104075804601c80b24241e00e4228a40342d40c4500240c1030b02e0b80c0090039a401680c480002e0207d5002c3d102e13100703050346448420701000046881f01d41d09402144244400c2c04070540c002150444030001b00c40140008005070010080045480e03042c0b50424090100070244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 650876924 1250 650875674 650875691
    0x2071404140a02070c08030307081501320c0a0c0603150f050603130f1101021c120b06070c0308090123070609151a09060103090b010605031e0c030a 65
    0x8240c09802401c00030900070001c1d50712810320030b200039480200c054503403034104600400c80f000c2c18001140a844181c1e0f502c5407500f8840100015281d4900d0450f0501880c0200c90f0310002c6c5c80010140e101c0403070b400f11081d401204900301d406100d80040301126004044000707003048900c94001c801e60b60240d904005c0940702c001a06c6010b0014010300e00f0707144800408200a02e4507000465001c0202054a4680e1140c0e03a503040034015600400c60350f204524850310807959041040c400186c070301241a0b040c010215101820000b25012554840c6450300c400c11228ac41e040c2c11104219400b0001c86102e50f0350b400e10342c44d03a0700031007011800250300340203ca20f1105420403c010b108a2208054a400050303552840101003402044942641c41d012072819030300b652003400048122260030a1441c00c0b440c04001403104001c0640b4103246c0341c45d90040100b8054205030741540c145081803540d949500c070030307203003580e4200c00000c22554445040005100508020714000c0c540faa0040c006001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 650878174 1250 650876924 650876929
    0x7061e03020306090a0903121107110604150503040f0206070c090e0303060a090b01020c12010204181a092e05041d060606160602030901020c060c090a0b091f020714 72
    0x21003540c140e84d106031114040707000c245103607012080c40c500c242440015407115421034030650321080c4990b003140d42c01260100601c43ea4100a0116401c100e904610f000e003080c014401c10a40248450200302003c800201003218070500d030740c4041c1d0018682601c071207151500c8a10006240640d0342103c0c00e05510000070940041585e000707500040500d070040303080101c4007009210040e19541188540c0e000c403c03c030303124045445249280c40300003603a680d0a1042c180c038080c1c11400980c800c1d0f0710b820f880c90f914900d0412581c003a0501101c080380705407120b202110302c2444101e206040c0440401c4840005004040302c8401c82d001520305003c0544600e040d840b034011385c64420125a00a040000d055252800041043d4186846c0a401400c119201c02c0101d800482e044d0b1101c2c0c4d800510380010010070450f40354044240c8580070b1414101c640070071242e40c11445140307a052004908000e00d51303140d90ba8440000554034040e01018101c0300003e64038202032294892001c7c140032940c3c800d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 650879424 1250 650878174 650878177
    0x807021e010203090d110904080a0e0105070c0510050712020d0801060806091b0f0c060a060b04080709020f0702040507080f0c04030308060f010c0b0924010303020a0f020f0307061e0302 81
    0x140c405030080d506040000c0300344008500c07800000c1300c0075a421002141d9a40d02d54170380038066070094140c0e5440345543c02020b8188020071221605201061080400041d40d140c024400d80d42c00740c0d001d145120306080c06079058041c04800a0000c044980910007803540022181001782195540700c0850344c0e0303558191401c080036254646c01c1a01040021500b14001d032144d1503644a100c00e00b460140280600c51060304000100c1d0404d0b080301050100020050181c000a0f2103603100447c9090703e0459030658443d064402d646043da00404c3d40340d0303000300910a4030310039a000782062015160410008010020480e05504004940c2c030205849124090545042e030303a040d218124140c0380c203030400050642c500748060421440807070036000100c950071014003c81680000700b12507a0070030494903080c2030704089600802140001080802d50015090003220b800041c110103045150000c16001e4031000413140d0148503180c400114194052494100704100401c000d400000c40c1c40c0881c00d1727 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 650880674 1250 650879424 650879479
    0x7080409140c0a02190c0f0f08010b01020d0512040501091e05060a0c1205040507090e07140303071502030a0b040204330e19080d03020a0e0a082d0604080702 69
    0x145d11901010304100c01c949a61542c44d800b440f8a0700520b545e56900c445e00c00d05940041c490041d007454200030200d405d00901c0420341c82400940600455680010030b28013819503001c031071640183c013040900400b9031001aa098101011942000d200304549110301c0c056281162907101d0100080c2000f1424451a4650302070b6940d0044e0301c0302071100070009000050800c0d40d042c041c801d07002440080c1c0d44640b8000d0040c09000d015581e00d000a0f484002184040c945d00075002000500700090035039080d0255504215001a144c0d00c03424581402003040b1021180c200b840006d020a079042580c0d416007a9054180e0403001d601c4d0100792040808982e05401d4003c110810000562454500000030110068200b0030214a60f0358450502e06044420b0940100341c0c00070781c56100c1035014001c515040d0050b0b54200e43e00d440c0c4a0100e03500c041c0c0b204805100c1100e40d41158410007d0b4960b08042c005500840c1c6141c10700f4148a880c580c0045000c903c11524103004226460920481529 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 650881924 1250 650880674 650880677
    0x1410140409060e10050601020d0801031208071e0905030717060411010210020d0b0f060c06011503111c0e060c0d0c030603050d110f010204080303011203030207080409140c0a 76
    0x24461a56050201030054071004a504a80700c24000c071101c0340800c80c0c241c100401d10310108441c00d1a0001a00b4000c0071910b21081184420060020032036155002000500c540b0f440d5507682d4841c80d084900c420481d524036403000880a61010312517011007800191001141030303909013607480810100c0281c1d4904087c0aa410160015000c5040303100b070354030f0440c0e060054400410440c2c0141003280e02141c0188403280d0b070781011030300d41d051070750042001580030348040c0c2c40c01c12909a4a40c0c1c030039051007003106103c402c54004080728840d4109032841c100140e8a50384032803001c2080c01c0d5181001362198540741c9480441d6800d8100001c20038018010076100d0b52178040410100703030182508a454030300303040d114640000066000c10032050350349200c1c0e90740c3d18007111540d0114242551402c640302c0603801440b083c0101d01002c0103ca0464064680201c5244494074050b0b019005150b000781492202040c00100e440b25500300e90001244030300070420b15a100e502802540c005d5000040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 650883174 1250 650881924 650881949
    0x50105220c0b070201050915030a4d0c01061a0901080a05070314043017061f0c1208041e02042d06080606030a0b1801020d1410 56
    0x2142d000b0443e8a006150045c81d20740c01c0000700e01040c000c2c40a488614000000b00241c0d014284501c200340700c07150032200080c02100c2024140710910001d5a82c0d82170341880c0010243e85400c05050355420b4840d5251384458a4100b507034000c09851003011070a850302c841c0c011103410420201e44030060161148549a00c40c00d41020080000811400505a8074486030061950444540313204511840040550004200c03008002c0c2c2c20140c0340c6800700c40f002040001c0785400c070700302c05003085850109918542c3d0b50000241024088405400341080326032030440255403040c0100d480070700038803100c48192003c01c0c04580f00102144e000d0018003c40d0500b6100c1d0030f801442d1000c00b400103001058140c00c401f2428200101070905c001d604c0b01380308d1003640480740c0c1d000c1c560003409284003611162405402207906d4001d9108000e02440a0034002040701290700b55590042801500071500da20304420050018404900d2036800c40c411040024291140580c580c010ba4131507804a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 650884424 1250 650883174 650883179
    0x10f20070b0a1806090525060e01021204060905120d0e060a2106170109020d0f0c09150509010b0325020c0301180b13080708070c050d050105220c 64
    0x380c034034800142c07241e80407a0300c83c0c511071540d4040071040c911060007940002044103041c82c0192a060360a11480500c10a101e4420408240144400c00b11403040c10102801c601410040382091210b0640d501064800300c0e020078034030741c41503000301581d10503180c1d0242418980708465a41038140c0b21500060300081d20001c282c1400700151080c0c0381d07141440d100c0e40070340307440d00c0c20230400d0300c609240400d90360201001001c0305c44840b2803940221200030040f9040342c0d00880d1850150210240a21140f0b004540402c01e5501d601c2004081003d82041002e90115400010718524480c451149040f5000030079100043c40480b4000c800180b8100703030b95841c292103200d0501182c04444150b004021300f40caa9a1420300800000c20041d40391403a03220102c0c503060300700140150200f40107000c2c04520a000a40d240c003241c00e9680c10950003070301e07407800380780c070300e001d40842d4000d240c01c00a552072070420000c05404c8a406481101001c4501c1c05c04101c0c080070750a40340c140500120f0244204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 650885674 1250 650884424 650884433
    0xb011715010c11040f0f05010f050609060f120901050712023c0a080610031b1b081611040b060702060c0309030607090303090b0304152c010f2007 64
    0x2082c0348180714500c04000d980d5003800040c121080c03000f0383d100c00c9449000c0000503944c58407600e805445100604038041c1e05000105805004034103405014100026103200701981040a1b070f0495442030f91444c1c004d1038803908940c00703030400b600d44102080d10080ca40e0000c0d6041c1c0281c42990305180e60709048c42420349006001a07981c07001e2030184003041d208075044004500f009004641443c1c465042d20304081040c848000300d8a02c400c0c1c109443c144080009042c059503070b400b118428600040f00e40024414040200032055009007544000100d60901409806090040d80d008440c46003000654005100a48a10322041c55000300100400c800500d041009000c04500f070000716810200c0601c082480d00304196201c0000c41d0a214080081581c4809400c028001c01604a401d40c02c11355149000d6422101c408000c45880c1d400d84136018095001c00d0000c0148018451340040302c00b060340d402802010140d0350710b035043c040107070394032901002c40030316900c000c00800785840030315100d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 650886924 1250 650885674 650885687
    0x20103090201110f1e01091106070c210b0915011a0706060608040507080106050306012105010524040b0f01030e120a090e0f07090504020d0605130b01171501 69
    0x12410303c51841070621540d0003c001003241e40780e085000b80b80754807081302810707480b0002e9000d021a42e818241c0d0b000c00a900313016281078800c070554490782c60380301e2458070005101841d0892248880f84440032512050302d084e88110742030040c91350265584480d4111a04c0394200c1b501d020444e040d8000403c5644004005d031700071203860003c89070411080b560b03908140c0f801a031000c00010416410300c001e03c00144140c400500c0420001c004072850840800d40b1040b0503c645510f005801052904921025403120b03c85544440208064a05506486080382d210300c00c009560210400c00030241c00c0c00d1041320400c079002065000c180c1c880c400110041d003481440702c811030280003c1c10034030f0304d81140035040d19141e1340c482d06515070409620034100c0304e00504407800c03c0da00b0000d01c8401038100b036444059500a40340583d40b1081c90010350701622841c0c0c0096003000b0300c130121010020340ada0012520790406d980782c2e1424150b007002d4000f070001c00c2d14941c02075505400308080c550300561 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 650888174 1250 650886924 650886941
    0x20a090612020c06150102250e04020402040b0c010c0e030106060207030b040206090d030f08061c0f03020c0a180f2d11030f06010e0306070f031d1207031d0607020103 73
    0x510140c0b0b0100c05404050500800b550910b00f170101601d0480344540c0c052042554004c2a804940364075240c0030069681410b56100d0200151407200100e029515190120f0b4054a4103081a903504c0325020308882c020b180c00d4099100080014814100600d010301854080340c903070b035004000701b904580b64582c0f402c40141c000c0368803074410002c11136207481ea540b001c0c9906d80287c899000740074240801800f8078000400c0c492080355500701e180104402010207a6600d5080740c242009003519140692412800c45900e590001d5a0b40000030044c418403140400c0b215944420b2001e00c62088080c0142d400800b01d03d8100d222415140c1c000c6040803216080e40d004150b0080b400001228900c0700c59030090f03803d801b100105400b045010b5821410311a03002c0741c103600400d82c91400180060140d81009913120416031509942c4440c0000048105250592101501c0c08001d00622541003075010704412404213aa0914002c181c9480401d0500800c0000c0c041174902840b0f40d004400404040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 650889424 1250 650888174 650888207
    0x906030901061203170f040f03050c01090c141807020703021519090801140910330f0f0b1209151512031315120e0106060e04020a0906 59
    0x102000120500d0b40d00f550720a8134084d86130710388141d0960f0080d40d81a0301c01401444141860818000012808910240c8154061034025240c4400440c034034003510110001409081c036144000c00c4407440000c20024509084502004c1c2c04d041d4600d110aa59040b60f908004d6000300e9010001350400c6082c0e61a07010041c0101840d108050f460f800c06030151007544c0f00024000300701071111460900c182411200c141e08000d10514011040a03a68413000b403890000c103440b80d108400c08041031903686030700c5502203030b0b10514a00720328a04050200c00e200301c02c483d90030b140340000c0d2956401100402c0c0c558101416290025a0b41c481500900c003801c03641ca00d00c00c018500050540441d081402000b10b09800c0100402000400c010f60301c402415084940041141d000040e00c01510081203443c9000034101c3c520406000b43c6245818007d25103146081c40c04c44400e00e00c0641c060400c2d540705884881c500c030040000d20049000f1071700a00c0c0450721403402884140c0c0555150003041c400e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 650890674 1250 650889424 650889431
    0x30b030f061b070b070518030c100e0d08071a1e0106140d0504050c0108060303040605091311370203070b0901020c070308030114010810030f020103150806040b010603110906030901 79
    0x980d4a100c0161000c86001c40040c1d4045802044032181c503002e01f4500c0d40c100c1c01001034185c0e50002904a168411840d414050115450b650780d86030821090700b841d80007070312151144544c0c00e100507024020800f92000b01e040c10002099402160b481c104544902074001e00e09a0030300b03406455a00945400c0b0150300c80a00c0b480030344800c0782c050390f40300714407038006040503d040c08005403121130701502643c4203401c28030090000c0c0d903015056071100d0104452000d40410140446401050107180c1c81405031400101180c06481c603502082203001d91448401c0120b40300030314008604151140b140040e00208050300c003150075200b44a8112840000051401c02c622040501c0c0090640c011a2603400c080010810300c1e48078035500000b01020300744511513242003030801044442d80d0000415404404080c1015079101c0e50000c42602c1d13801d4400c2c42055240e0402c0b40d03a0354012207003203070740307030345100001c90b556100e03002e040e9000405180050400504c0307400c2045d207400c01011011590369 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 650891924 1250 650890674 650890687
    0x91003210e100f2a17040305120712020303010308120714041235211008010b040b100c020f03150619050d1211060405030307030b030f061b 61
    0x15400e494407021140c035200c00c6151025208054000304c1043c0100303951001c590b4114000b00c0042440c41e52041d8424454420381032550070000050080d500050414483c11040030b480140e880002c03d5928003d20301c0c21a022603500081b641c6e4842400000c101600c244070318088100e08002c019044051404c240c1000d102c564040b0901d2380155000c03e4031050b4044044040c00b0540e101443c8000000c402c40c40d002c2c007070004444010300d001d012001e00309000900100e822400d00b20002c00844c10703440c0b400e4241002c0031f000b840d01c1d800d030140e020705500c0c0c010b01034050b14140c8a1080850806801900c80e0700c90540141c4030140b983d801a1b130031201020520015580c01d1260140100c00c900d101d49442c180502031000c0360003058505d000d900c508400c04d022540e6010b1402a0061784540848100e8000b00000c41d916440e0742c240400c0c0307100300f0040c4410800080041c4d031092803140d808000003000326040654482d440c002805136500074002080c0c0b146000030540d500d05e10070f280342d24074144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 650893174 1250 650891924 650891929
    0x9050f03100c0302090406061103040303111204030510050a05060f0f030a0b04140c031f2007030e1e090c0a030b19031a010602030909100f0311091003210e 68
    0x14102d6a074440000d41c0003810042c2d500c0c00d84209000350000c0d240551303031542d501c0b202c103a82e4400e07804040c050100460394181d000600f00022909503501c5901c40c2d49903580ca2600340d9071000415a074940c0319040000042c403d20313141c03241a201d140000d201c3c03140300440409200000c0a08681e468042c0030340014400426404107405009078403450034031085000c440d42c80344c18101b1000b03210f4400d0b041151569840d0001410f604080d05400000080ca88001c001d42465140060441c9020320f4011400b01700389504881d00e441e60303210035680d604495504591a2000300b4400c080769901400c00000b244003002001c0140a2801160500285541d0800300145042c420803c10581d5040c3c141001d0003044504450740206d880000564045541401c4001c0d40780e0061005403405142c407440042c00290b903280c0480020111149038040702078803070400d403482e280ca0b8030045025019160200341603101d081040c0c0122500006684c502501c01000344286408044508003003120b98850400c040c1e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 650894424 1250 650893174 650893181
    0x50702130b30071e0e161b150e010b03030301050d030c020f04020705071401080f0402121c111209030304060513030c0b09040507020106050937020901021006030309050f0310 76
    0x40071003007078941a1004c454079201066506070810480840d100b014004603100403900008007003d18248180f840760040d5036200c0d070031a001406440e80f030f0403050340f1141c844190300490b14810712174000d0081c0800300050603034911081c8030b42600421540c1155000c64841c0c2e2540e0500740c402400c56459a00860014003a81c000c1d0b201902c058001c4001001034401da4110402001c0b800e080c40c1405107054034601001217001003001e4010744008460308050f840a00081544d003080c14071201d100e0183d08401401044000742c404218401c0603080c864811030481a01c04501d401402140b600b800c1c1501101c00350424420401030700700420000c00018004140c11000e8140c600f185900c40003008204000d88a014042c881503900d0302405118907180c50403030903070040f01004260391100c0c3d11000002c000e0b03900c503540030034600c03262085450b044581e0010700c8040000d80c00c40d01d41d18003040010b41151001d1000601145204008116604000080842c1540018183c0300c122401d44440401d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 650895674 1250 650894424 650894429
    0x9061c0516090b0a0f05060d0209210717060412030b060c030705030d050703020c0a1220011b0519080705070503130609080d0203031b041203050702130b3007 69
    0x5242c0c860f50001e116040c280c580a006250001e00a4036061038403010070701901c5404150450b84c3e0300021600c4140e215680c9050503c4030740307c810300640040c8404c0d11b03150101405400d4801565101307500101c00c0024042d4062034114100744034003008124280d00800d03141d014a40c002c8028000c00d00d1440091000d4190a80184007569880210b4443d80b400c68800030714100c2170610601c810920041d0000c3c2503512150f20064550f00400c0b918400d540010512042080c01402202d1010200a040d0000b109101c541c59810000300024071095820b4040d851042136211a110203a000301e5201c6d2800742d03000881401c045152502545405003550700c40b00501a142000e5002003000300d80c00407042004008010107050f0680316000000d450b0300c40507005003001e44020003d010b1600000080b10000d20794151754003055107003454040e1603074001110913441783c481d0605542c51021240100c03611181c2c0144100c181096815980100a0750424500c0d0901e00721aa06201c00404108104c007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 650896924 1250 650895674 650895689
    0x1e030e1606120c0f0f03060b160507061b0605060604050a0801020309070636090903020a38070c0c1403160302090c1e2709061c0516 58
    0x411906100d0003901d0403401904140c56140f5286841c4081039010100e46800000c0e45441041c4203010032084020341419004070304d50f4080080d0156900240c0700760340700401e1050050b01c3c64155503010a0b2401006c0d8a01c0180d2403007003291010000301554402a84071000400c0c0c41e00701916000411240545904200e0343d80e98000f00f48412000200b2070b050040c001848c01410103140b0f20418850160748030b030040f043d0100c000340703002003148507900c2602500000a04100148480c140259648603840c41903c5422040004484d000d90650035251054401c4022008507110410b035440e594600600f44020407001601d001c001800c00e034108002068007000441d100300c003032810541080a220084405c035012080d00300016125502c90550082d11911140d4541528242950003000403280c5070f4900c1000080809141600300000f40344140c84d0075041c003000d102e032011b000702d101d070507221258404440c4c00510000d96000011858052003642903540b134501a00a04015048503008043c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 650898174 1250 650896924 650896963
    0x1090c03050105090706120b063709080604030c0f050609011d030301141c1203020304060608150c220f03020114030f04020f04020403020607030e0f010509011e030e 72
    0x81030003400d010f01a0405a40406048182d20300f80014142c40034003e0308504080c0c03030740e00503070440d80c5900544aa07851100c1503099160b2800c0842c004031032207002d4402d04064486000e040c03440c0b180110005a40b90900104000c1c1c44940342078600a80d010301c01c8a80448401d81c0000280091020038040c51041d40041610480e041d0072200d007410010f01901c0c80c2e4402e10042200036084010b031007100509440701840f07182d40300200340d20000e4540c40500703040c5001d50b0364000c6550541c0110f100314083c003c02c1000c15105c64980351aa8000707036108440e00b04603404a400b080852000b45007900c1e103a442c090318807041e00000c00c02c940182d8000303910152030803000c0095513041702a0703010184400e5100c0c0e1551600340c403000076140002c2d002134000e12400e00d50049a84840d41298041d540040082d40c0344e00036840e0003840c59820600150040d014440700d0301b0315502400030b560542905031155005c103210040c1040900c131124a0381c81c10503484e8043c1c0c201b14841440403416001340d005286 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650899280 1106 650898174 650898179
    0xa0b1f0503121905070b06041a15030103060507050a020703030e01121404020406060201020f04120507030b090f0c0907120f110a030911040504080f031801090c 70
    0x303603010700c0384030540c1001d0600c01001d85501d40c3c00c002000c0c01e00c08462421140c0340241c032002810115614003141c254a03040d001100440c54441d01617011401c00750029074020b07651504010100000001403080c0b0000c0d004166000140381005441e00ca4000310003540c410191201408100d080034134481240c2c811104100700102d0880c00703000e9400c40720b1184600d2001610220b22591902030002000e030300600030b850000148c20b101c1c6052501e0074011941c0300b01e542c04110b80d1703030080c010040005021313085e50602034400c80b40141104034620300801d241008008400e88034882d42400c1144160744150310000110300b04401042c2e03402d500744c08202401c540008512a010082400089103078198070080b40e03e80600014210081e99409000807543c0c15103000c3d1882300100301000314480c40380e00035904282c0072401800710341079480c3c0301421102c00140446181d605041304 = true := by decide +kernel

theorem cover : BRFrame.Cov 650719424 650899280 := by
  have h0 := BRFrame.cov_init 650719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650719424 ≤ n) (h2 : n < 650899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
