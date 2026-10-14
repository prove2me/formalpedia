-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:07.392537+00:00
-- url     : https://prove2.me/submissions/de9870fd-815e-4d6f-a28b-30997cfe16d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630035971 ≤ n < 630215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630037221 1250 630035971 630035983
    0x9040906180209061c1b0302060c060a0c0206040c060c020f0a15170708012102090a0615030b010e0418050a0308070815011b032d090e2403030705 64
    0x205905014070711203442d204002046201520b4180a00e140128910130103440240c036455103a0400504d40404500c41200c401c010301070340000b0b421a102040d1082000000070381d0b1406110b4000c030a00010942c208126500c0004590107050003068400402c82c03207015443c2140141c0c0040c00c80403c104019001c54185600c5920900007203d0340078100c5d21441e0310901480708001c02010924090511031f400601144060080b0a8560300e801e51041100710f0b91492480c11a038060410120340c9001e90621008054500c40c0040030380d2642403414a41d031185c45600310046d0161070b21003d05454109101c010303d080107880161001840c01c480100e9000c018103a1054426135885145142545d0010f160b400090b01d503100442890b07940400507a0000b240c035007812010f00c1901d2690541f030030100c030030384100d19041d02025401303104ca0080c0381400f200d0081040b40c03504c1d002c0a00b0350341d418030700c80401d003212065081c0b241074600c01405151401071415040009017120308103549911070a003810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630038471 1250 630037221 630037241
    0x90f010905030c010b06120f091e160b030f0115020a08040803040302010905090103080f03060f120109230312250201090c09020a0503160207120302030417061b09040906 74
    0x180c008140803c10303c000340545040040b00703840f22410700d90310340a00c00d1200c0c005000000c1d003400e0302001075907821040000030043c00041c1031030441c40c9000c1ca1510744803810440f03c18100103e030503000c80d130b120841e401c581c01185420301c8052140c0c030300090900b45c0c40c51000404110b009100c004804924507501070400340414078040c541d118035510000d04001c1c0c95601150040e01c201004101080d0348a054131a054030b4001400c0e40c954038000094480c01a4070880d40c2e02812210520200b0901503015a02c1d8900c510015400761482c1c03240302c4034842141445003015881044070085201c0c6010206070001c650303100700e00c20040c010307069000300040c8010808c0140e540c0c00c181001d102c004c2100c41d00801c0110001c52902c1803100c0000c042d0300c00104a041c0203104480314003001d030b01c208007000003481c070350001500407509894000e490340e0184c4144000700d1450346600c030071883d0104085000c0e01070382c5001ba0a5807400c046007501500818605540141d40c2e04000010840c01c0c060a4000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630039721 1250 630038471 630038473
    0x5100c0e12031c0b030d0507082a0106050118060c14030a0503070305010b070803070f140309011e0e1905010621020310150612090f0609150b0a05010503090f010905 72
    0x81401100d2581c4200c601624401c66130300300702181c0d680e0b45001c50741c818641c00a2401a0b5030300221304040290380300703803c1200d4500c08070f0041c41110040c4500550030381049a8000e001c4aa600c00c01141d040b600c2560f40b29210400c0c403c208180f90250a185103840d1040c00e40228182e01c244030241150000b5200101040000003042305495040c0b20729170140c87c042ca000c41c10210280c4407914203010040910b000e000b0011241d1140134000d66030040c0751130f50541141e623280340049601e03010382181001000d1400c602102d1055091050141c5034002c0038900040c40400c0c0c030251010702d4103c0582d41a205035507a1030f00801c01c00085400e00c0c1e010700040f0501c034200050b502c1851329007000481d07003440340361500c0382481e00c0d04424100001218624070b40ae40c1a10500b05043c0020944080020020381e03e1140280410085030050400b0714019007070144c02100c0c801c886000d40d82d410601d50b03031000215030144070075030107500070315048207429048850302d5543c1d9000c2400c45460000940b12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630040971 1250 630039721 630039727
    0x61605010212180a050d03052214010b09130609020111060703140c0703020c060c01110c0d08011706010306020f0c0a240606140c03070b1311010c05100c0e1203 70
    0x54565000c580540f88034118004010444064640750340b02d031361801740320b0101a262008103004242d4240060700b00d1030103402c0c081f41009070f89091005c040000000300380e507508201d01d4000514240c00700500c9410030809a03040c2e85103555428000780307000e40d07049043c04600ca05504140030100015407240c01c0548002030001d00062071a0001e03000104055042c0d182002035800080c0d011442e1f40c0da000d026504c450300e61212010f0140500380700d04503400602004980701c42d00f8280029000001103003603c44444c281d03210003071001e10300c110450b0028070354030140c01007000510035401408640700d280c81c0d05040010f0309118a040895454054400194483d80c034125011004242040f46060880030401c040c039000001c1d01402c0d0000090804001c082660000d01000740b04036480150b10a04109151402c181030640c20902d510042c0c512440210f123400d2030354010081000903581107801440c2c01c240040404025009001010041240c500700c0c048440e201d01160002c0e603980c56020f551 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630042221 1250 630040971 630040981
    0x12010e0106080606030702300d02130602071203050307140d0f0e0106120b0406090606080d02070f030309050613030605070c02090a050c09150f03040f0b0a1a061605010212 75
    0x40c0b4100074080602c0f4140400602040c2500002e0814024100704110304e03003050020524111110710f046000d51a07140001c105062080c994010a100b50000c05e1080c0c40340d480f080126a140a035020b02900101c0f00a401e0000c207000720003840e0700411500d4a0200f020444c0010901908115030714402d0f140c9680300804a81840d00500a20485000082000a1600810624100c1140c2001d055001440007080a106035600718912040e00070344148286961034442c1940e42406401440c018020240d000c00da8074004004017040341c0d015601c0c5140581400200a4039038010114441085000e00c00000018600d0142c5480340e5002d448134014030750b46005001200d20001c0c024003d44d443d100c06c0010306800402914024a025107400010b140c9030b8101014034482c10300e050007500c0d004010002080b481204040d415031141400b13101c1030315043d06143c15901400c1e040c40107804024170200050629134040e04881c608120686013128081c2c4455003207030301c00d12000801c08882c0e002c0003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630043471 1250 630042221 630042227
    0x306010906113307031b0309020f03030c160609030804140f090903040f090207150510090509030d0c051e090d06051e0f0f0a05100302100c0b06060a0c0b060612010e0106 74
    0x25a01c01304508003805480303070301211580040101c4011380c050580da0080401035450b215840b6002304000743c00c0b41d640381c8507440c04a030355010350181601c0c1c2c165254008149a44a00301e007004481d0f110401c0c608090401402c4200681d8000c1d016030032142c1100d815000303980e40684140a060f10501640d41c2d142400321102c49842107401c0628440d004100100005e00e901c054550203007800b0784000381585a500041c00d075080d4a50040c0001824103040c8900c209000c001040c0401c1c00302000c21a07120102c805407194010b0341d07200d140c4240f540c10080700b107004080c01405d440d00000c20120413150b10744e0350f80c0210740c030a60f0241900701e600c0f29005520b48140040540180c1098101c40d03c0c0d1400ca1700321240302000520621001d0f44402c0401d2883d480c0c0061680556402401e04503a4503010b13000030410101d408064a01c2403841c40440c0290421504440b441c0305180d84201480800e030315250f0043c8030281c13031140c200d9010000c1c800f994105150071406004880300b011429450a1401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630044721 1250 630043471 630043573
    0xc0305071115270f01020c060a110a032c010804020f031c18090e03180301090c03140d0e0d0821041a07020303060d0f0c0506030c0403050111030601090611 68
    0x41401100c01c600c8100d503681c6c00041040c0300ba44c0844210342d44200703051003113a030f00903450034120440c4600f04000c4200f5403c400d54a49122881141000b016412124103480c603820003c1c40e40882d80080200f07026044c10910269001c201500311040d01d02d0381101c507040414610595000910001c400306011384072889005c0003401000340a114056441000c5601c910a100324844100010f0381040c1c1c0e26202034010803030b41d5070041c1d80117070031039900c3c103059500b100f000000c3d0800e4092400303407062a9005500c882400309028100c034101085a80d02c1c5445540501010041820f51440007400500040740760f038840d5101c1c2c50100807103040d88100d040c4070b210140040c42590802d000300030094076101048510540c00401580120b449070030980d01a60322034019030380048000042069145a2100401c110303403142d00204009440c06200f2561404183ca14034009281c1c21003c00c41d45116410380002c41031410195030700000f80d940c4007070070550b415048007081804107150301200440c1c0b2441c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630045971 1250 630044721 630044797
    0xc2f0109091505010503100509100e060907050a0c06020405150403030f0518010f0c1b7e0804050d030509070e0c0c0105070c0305071115 60
    0x1404600c202d40040c0c2c004030101d020303081c104000407001030034604a80c0a12001440058142c030080e003818040c000b4108010f024000d440400b4501180c828200064890312500944c1c0d6402c0c1000c40e40702e811240440c00c0401a0b6020340c00380004103560340c036240404440812070392130a544030300d10718028201c007039142619410321800307219aa002e45a180c0b1501c0c401c0d61b0034038005641c900d040b84d0aa4190725400c07009044a00c50004030300700c8500b0b40031680141c038007458580b6410300042141c03010a20a9440d9860780c914059000407201e2005030b100e075103200030300e18402100c40801c451440340020b000040382c03940505200c50707101004a0203455114030b90fa85270001803450710383c403919510011150501c04251341d07003000035021758003030080c500940103c0303140c2032a6040c98000000039410034421803140703520300030200320390700d011b115080c3c003859158803410700309003440e191944002c200b440116041462101e400d01820314000040980005065041c80c01c0700b620380d010604c2c9103014103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630047221 1250 630045971 630045989
    0xa05060301180512030403121a0310060302031209121b27070c050309041119050a1704020604170a110306010b04030b0a0b04020408030712050313030c2f0109 69
    0x7070140003060f0041110b000d02a03039410250750f203451701e107400c030341c980c8003a00014034151500c04041d08a802401d03010968040840c01c03100440085c88200d0110340083c40000c0d4107078885501110743d160404060310039402c2c0202808040d0340040b03051824800d00c0d11043ca0741040480b04010351b49814a108000070100d21034014075031300f05180d00c05407800701804030070912044d00c40203000c00c4070400071140405400303803050058404841c8804d49503004210b0804104141d00e02d4502e42a2040c01515584901c42c0c0c0d0ba0300c0c8401444c0803a541e01c190150080e030300030380c08100202e410180c1141403000c019007040181403510b29130034070108440b250341400d4400c0c0c000500410074096079900382c0d820350b81c00100049240e00ca006d07480c0d000300b001d0100d031a0000d0001c200044c90010100150a00e14002c0400300e510409001007290144400c030b9101c103102d0f081a45c04c901291040f9044070149100c0c5d84a21038070740c0e4048a119070044810704004011804801100955034010312940003004440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630048471 1250 630047221 630047261
    0x1203041a030f060d0606030c08070512011418030d020a08010509251101090f030c1208061305070203070f0b09070e040c030f0512030a0225020906060f040504050a05060301 75
    0x8080e90302011000f5120500c100041c00c04030041c04650790101c1e008652080210b0b1701d0a5441e4811500d0741154401c06114040394606424051011700420b80301c00c10031504034200b507544401001c2038441002d10400b86e1322050102d400d08030014030040c0a480b0154540d04125850103080082d03800c0014000c43c408444c82c000300c0c410171805109100f002546041450340e5100121602c0e005042c2c000c0080d100e9076081d10007609240d00300002600c5c0c41c2c000c1029000c040407550003598800402d40b0715a13006a064802260079025135444150480303002d1040c0c03480d10019840d0000f400c1c401c07503404e8409001a0042c406d0f4103404201071401840c04060321403d07490688c86000c6085014400a45001e603100c4070581005000d0056449507108541415240c0c00c02d44c12100081d0000f185010040d20000c10007400c00c90a45811001c003640181620400d41e690010700c2400c0c0c215001c0481e10901c2404041030039912401035521a0361050390000d02d41ca02001010b094503a800c1d2420300003c004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630049721 1250 630048471 630048481
    0xf0f030a0303051308120f01080f0307080a030615120b0d02130527010e010b06161203020c0d020102180d0b040609110409140f010204080d031a1203041a03 68
    0x410503500c855010b003000079641da160382030700700c40c0400088000c0c0682c000045042c003c4070645112402012090003d1812344c0c2c075090071a50315180040d90559a620510403000014210401000ba1030b115103400b10391a0341d0344082c04803108110000d14042180900d04a010160703601c24202800422549503201c0045500404d250300c1e10342d4410a01e8680340c10000300d0103841340d10a1207101c200c1c00d00c14505001e4104890340204980c0404441c5c0b5420110a40610b1074041c05135101071210b9062181c0d180301d61703580d00c400040400988001c0c10707000c0c031141040c01c1042c021001703104256000541d41e4014880c100c07003200c0d58029211b10840304d481c4801c02091041d0549903005600010018110f9410304041c0d110072030404035550300c03d092019041c10021001052004080070b0000ca4002c40303042c4064a00f80d004a00411000360310005c11119050700c40d80022803c05802e42c158905103060360042419a004000100550391001804020300c003480340408a9044403202c48508604103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630050971 1250 630049721 630049723
    0x62b03030c0315050f06190c060f02030402060d0f1d0a0c12050a1e0b040602120a0c08130206090a0b12070212030103230604060506040e010902150a12020310050f0f03 73
    0x440c01010f001d000c40031408080c5407a80b8007140c208045455a87c03005200f0700400901d07107402c00c074040fa20107080c00f0381e100301903143d40281c03805580e0050030700b0301b007048280c0c68000030510704101c092807603142d0807030307450404810b90704c0a10b440d41100600305010050824000f0070b01c3d5548103101060b01c5e80c10107030100c3d07804038904c3c0e000381e07002c10485507100d02c6076540d10640000d40005440b074280302051004024140d030040008060f08190001240c0e55201814200e60394003510b01d000c2490031000404984500143c240c40510050540e8240f11600f40400c81c412443e800014040c5000100c4c4944400e0301f05034a47d10015034401860b60754221100b510480c0410720006004408098210a003011181000c821a901d92011a5050310700340c1414000b4100c04e4591070701491604035515802c10044c0240c6244079005003c47c2034808240c0c0f2081e10650020041604000c2e400007006011001c41c0021800b56141c0d15595020b54180b10400c84615603840c0107603c10b44145140c1c114a4030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630052221 1250 630050971 630051011
    0x2d08090114012103180605280e04020310180f1104060c081606090302010603020139050c06030a090c091a010e06130e0109060b040501020a0803062b03030c03 69
    0x3d4558102481c0c1c02491500382c5182e40c00e4149040c560039400004200d0b00c0e840b070023401800f00e00c6200407110103410200380603000105058080080c200200b1509181019001150050100d800e01d0548503034651381c8061801a1401d4030b00c41d9a1118001465942c050103003036845406001c10900d828038006026190100c02080103011081c04281c2142140c601c8004020040c7c00040512410700c552a00034002c11031804100d002c25060101c11800017503600421106c858045041d0340070464a07451026080c032483c40840d40c40c410700038200e610341c9500005d94094469801d000c0f072480c001d0b10b04140c14000d1a041100d03100d1070718412000060595800713900c046030a08141c00440e18000c040340300c5201c2d018011807040190040010840100200141202d098440810041c0d4892155140900c181d215050050b4000d51001002c0b0b52034000035504068000e01a0441c05110203070300b2070105802c80c641c014518601e5003282070640600030504490300f5403408102d0b1151142a2042801d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630053471 1250 630052221 630052259
    0xb010801050f16020111030106030f050f0601020d031107020619030b010203160b10030605010f08010e0a020a0b0318060c030a0c0e210f030c07050312090901062d0809011401 76
    0xc18443c42d0410058005c0d80002c0c81d0081e4000718980d250b840d000c0140142050824544031646017600103040d0402074284e15014100507405004480d4003208120040d12a001d8003105104007001a44010b0340ca00d001801c81d100701e0049403c0c50f41c51910098102e4400da05804d056410401840d4041883e00c504a20059030000c0c810906880e115140e0380140c1d03064200410080c0b4010011414420030058001200c2451000384405170300030758001d44520740c03071500030741040900400f4880b02c40017101a42d8008556462051032264800400340780c030106440b41050300d600002400101c0c0041c0c0170b0006c294a850400c25006964000819400c11031214060721044e040c0d044204490814800a51280a52401c0300d07100c4601d144010744554481c41040d00c00c2c03081010408109503048242c449050000b0946401603280107410703240f900c00740c24812402c5800f540508411003e21351160100303079441e0b0f02e1490514140c61440e08499180f01c0369100d00b418040100032031011035a00c601c5c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630054721 1250 630053471 630053491
    0xd0e010e13090b4809060706020d1a04020903060118020f12010f0f0b030a090f020d0b01090b0a0b03010b13051804030221191407030c0b010801050f 65
    0xd450302401010040424041c0184012084818001040c020101a5440509510036007400081c1c42e40c1c015040b80c83e00351139114413103144507060010003800300940400c51025108505d04445541c0b003008981c408400603003c40c2d03a659000d60b10106440c0c0c88070744078000303035001c610b0440c0740c0d40081d6484a0520860303a03003802d1245800035102054050f07075582c051101c1e8040d00c4540c4402c42c813003260300034003032610b0f543ca030948c001030f880c5142d1280004071a54165a01d03d141c0700c488a14014000340c040079a4101c000d81c2030480140c80341442c1800030350154100041d554140001c10303081d00c04903203516110341c010900a03c80f2040400899044413003024595075101c0035422141110892903210782d5000c4243d08400e1910f004e00801a0310841c4a41c0c01d41e980c03400c8200ea00554000004500040c1d44424011039a249201c1d020810289040d82040035011304041e114030a43c4c0d20801040b4006140c1d04807820403c01c5402d64240980242c500a000e18034015141250042c2c00034540840c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630055971 1250 630054721 630054739
    0x1a04020103020d020d0b0f15030708090c0a03050c040b0f01020c06070c0b16060c0c11010e0409050f03090307080a0816060f02030f0f130c05130b1002010b01020d0e010e 74
    0x2168042e40c100c0d0750315001c0c00c6041d074660302c20785401030040c4040248540995506220b418907441c29100c2c1c040081003e4040741d0031516200001c5403943c2d401800440284118a4206503d45d546202c400c0154480c034002c1c030100d5281400d00c000e8403c10010140200308020000075680c0c0c011413945083e84d01641c0c8252928061304003000c1c240510750102082e500c0000c1c04a103d08001569690b506008034030900040d40064000c0300d40f40660305000d041e903026004202c40c250303ca1310300c1c1c091070a00200081030b20016600c4490805001505100301c40c0c0c0f0002d940b2840342014403581c03000744140c2c03010b000f5a2040c1e44480e00701748510040344c4041e40b0510400410070020358403c44260003240411900d034609200041d1a410082d10f5500c961070042c400644d4040c1d18512600d80c45a002000800a9250406018900321909088000c07281c031949000d00c2030700d1342c900c0b0045901d550b5001203040d18000d000a070a0010310f2030420304010040902d09050398118106c00d030001c4040c1c4a2180c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630057221 1250 630055971 630055973
    0x51225200301091b080d05071109060607141c11060c03060604030f11130509100506121603020901150903030c061b0e030c01260601030b0d06050106090905041a04 71
    0x4010300a10400502080b40d04100c001034010104c0301c6825074900104840b00c0b900d0700b0500759464015541c0c010b100e981e0180c250002400d040342c900d5007000024148609140c4e0a80e160440e410703402881c0962588400b03400540c0c82d01c1e0344007a0001c06041d0030b21000780c0d4045940300d0389814000305401500000080403e005031202c0c022034004507080030004055400c02d203012a01502800092445403031030023800000c1c41510706c40d65000b0320380c80008000c0b090021400002030a002020b65500c1a001d03940100680d0301405444041c0c80c0402e00200741074154410080c0010042c2c228003400c50740244030303038122600a86031005aa8050401164a011503c0c041c4080c05215807000350100e00c1001c502c03026508005800c1e0306800032802d170341440440600441e250381c440c1d03012403d0417540c3c82030300c00104818000ca9400c0079061401103009116030020a4080d81c0d410b00403907600e60f40317000401c907181d03000306208050581c0800c103201d01d04040d10b03030000c1203410800640e008540c03840030030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630058471 1250 630057221 630057223
    0x304090905150a0b0102010f0c02030a0f2319020601120f060219050901140f0f030a02070623060d02060a05030703140a06030309050402030c070f08070512252003 71
    0x441c0c800d6690030b045030602d09190710750013030500740c44218055800c1c40005076111909004070b003810a40c40d4015814406034220464104800790081c1c41030044c80c00070324501034034442c10b8501004007035441e035940c2c0344e4540030020070495410f901c800b1900480d00502421104448048115421603040d004850071800d02400a200300d0340d40c1c85440c2081000d80f21090f421001400381218240c0320396441c40d80e51150342140b885403000d4040142800c00c103209442281e030000c1c40d041012514010b0401c462903451100322100e01c81c10720302c118400020154420f540000c040d5000600751800384408080354046070f100d010302034481d801d1101c044006900c0364880d5108450380c5076030300f401084605248840ca001010706001c1607000402c10320b0b02182604060003140d01070008210b120703181002c20786903104890001141200e441c48100407900114004000201c0481d04401c1e145035071b06964520310610104001150313901d840d51080150210b890514680c0781c80f20b0301d6140c0b041c1c4c10319800010b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630059721 1250 630058471 630058483
    0x1b05030a030534030806030a0c150203090315010509090f03072a06050901020f010e0303041106070c24030c0e190305060406091e152309010b0a050103020c0304090905 73
    0x684401d4406480360034011240102111218000d031210742c81764460305c0501d1380342c01c94860040d100d4540e80d00c0070070a62103144542c1c800e040c420b02c1a641481030038400281440c14020300981d280501c0f50040c0304031f140c8071004d26000031216008040303041880707590f2601c034003070f0420143c540d20403841134007a080d51f001180b039500d08040744040b00454807000060090f410114a0500520440d036011180140500c100c4007081ca10740c00450a599031983d86440c4843c1810340c903038200320b0521500000685403e19800502010f1890014072060912442c0b50440241003035000c0508082e16581d5464004d9406c10744220b003a0740460100060f14401d124074101940700410030b02c9500200401d21295a01002119201e03210809008032100c405545101858202614041e80101c3c6110640c07ca603005403480c3c0a501c2405d0084c2500364400c0d40800c0088032501400c1c0d4542241c00c911b407400144900203003600342011401c0c030104e90541a60380c040da00501001c141d84030404000d120080143d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630060971 1250 630059721 630059767
    0x403030e010c1502031303020c0604030236090a030212192a0305070204053d0f03030e0a05010201020a1713050307030f020d0f120515040f091b05030a0305 68
    0x4113660741e003040d03a1540212112000203900502410b00c5003002817400703400301d400716900107040c00c4403550030300784e900705520080303140c1c902da01000c1006100d00300b07160300c2891096010101900c085e40140c10081c0c10881c405c228a00341300f0003081200c140c80300e03403599241180c041d454035000a50b010f10803995141c00e0210040508501e000a54081541c4980102201882518140801d031500704412400c1420a0041d1116440c2400c00c9481c680360744410858043c800011502541c0e650850000d01c4081c070780003500002d0580b106000c07181000c1c03000c000104400e02c000c40c50701e072900c075000b000010107a51408a4022160101d094100036564880b10940c106094036039803541840c01805ca03985002010780035004035501f604080d030090583c83c6090b211500c804a221481041e0b0800038030006000c0d0b00042161001c808494442d0710501039000b075003910000303c000281c1881c0c04074409400c0c41c0100c012030303103000317200b0351b01c0110f200b60700d49074541451703500c8401c41710031100c41904103e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630062221 1250 630060971 630061013
    0xb012106050a0b1810030b04110a06050a0201051f0506090a08010f0219020c01051204061d010f0b15040b0c03040b03090a0210020a030f140405030709060e0c0403030e010c 75
    0x109100e4100c0303250380288803907202280c0042c0348a504904c414101c13102110a803000381c00180302000800e499002155000e0301c9202180c203c00403c40004051200d907070048000204e01141c00f40d5810740911555404c4070310000201080000c041c00a140f031956405550701460002c640d211880d100c40c104080908440c82c002d0010f00c15400c03804000b9042841034004006101c0140740d08180085254100010103942d03151a00b054100000c2c035521001d8407c80b211740ea901c90030960030581410701d02400c1548000400e008940202002c15610241e0300148a040c4681126004100b104200c604a59220408603107444c90103203e00d0841c0259404404080c0c00042040100c001c0032030122102c500c00c584007103107000c200c0300403030351244101300c02030200d282e800403c40e000d801044085690b8660404051070940c8507804282030503901d1788604009600c07420103014400c10820301c10b5215a40100f5035040c20b05d5614005d00007031540c0145414000709002000a10442c4c10414090b000096 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630063471 1250 630062221 630062231
    0x70b0a050c031c0b062502270604050a1406040e0705061308100903122705010b090f0606030415090f050c01090906120b0a020d0501081e07030b012106 66
    0x8854454501c03104840702c405440c4c191814031500d000c0c820f03a40d100550318901c5079407192004900e030b082a000b10003681d0051840300308107038032018a041060071016014013000302c2e082502c184410703141d003e44440443c1d0b0038050000c05c002d00d08001c42da849a005c80d400b0401c012040342283c205901e507000141c22580003e0340140c441c10841c250740c2191001001c45200005c03685003c01180c111010080026080ba0048000e6020517000740c052420071101e5418001041083c58030703580c15011048a807651603942459003440c004a040c0e070b21401c6009019801e1905500040c250b110003000144003040341a82c2c01d0600c4003d6124003401075108641c1040f5400c0703414200c0d030b01e411026a15000800c19400400c01140c103004803402c4843c8854460380c4400c407680c4d24100d10000800102e16281c5c248121407440c40326005960003000b82c1c1c00588000c81c480041041058041e0f240b02d06036500a04003000003a4410240d541158500798841c0c03406a480c1c60a48c0380e030f4031b002902422943c200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630064721 1250 630063471 630063487
    0xe0d08070b090d1205010501050703050c0715110c09131b080a030804050d090305030412080906040b0a080702010507120905150a0b0a080f060a09030908010c030603110301020309070b0a050c03 84
    0x1c00f0b10f041403403900d4075a201e695442c10078007620024000c0c2c600180c02840707210b0000c0c3c02a8041c15208103400c00740d800032515a00c1d1344006589200505001444244003200c4c408424010b14000d8402991000641c0c40d141c0420062441d003040c0c02804000300240003d042480c58034941c0c09080c2850551b0a4451907003401402c160003a20142c03014020408400500d0340160b00f8081229803040195003024900300381140c40d05c0451a00356078241c070401a00340640c0d00c5030000c0024043c2c22158a449040b407040003001035000800010540e03240c202444156a005083c5929058060f1004100512240750841c146094014510b41080040d4180851800036403c8246109015038a0440302c6655803c0c46680b000d441003003d55640010000c03424412454000da42881e01906080d4150b550fa1f80a003400c66441c8030101000940c0da09080c000c114108d82c0c900c008400c210001e6080d82000318180c4d4941c00d513803240850032240080c42130040d601079410b89038134802940a69440d1000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630065971 1250 630064721 630064723
    0x907081c0905010c0b0402010f02010b04020c0a1e2a150305012c0c0c01060512030c0105062d010e0a030c1e030c17070f030317010b09010e0d08070b09 66
    0x14140c0c0201d5110000407a86510681e82c05030440e401c40c00f1883c080c2c0f11500155103007856002207408654072400003007040d844600040c0745111070000200900c007100c0c14040e000c80446183d04421100d0500b405003c10b40c000640200306040301801c1c0701c0c48600b01c0d10781841d9a80342e030181d004040c101e603d0424098060703005c40c2c102c030080080c03021910080003000100103602c0070004800000b42004c90003c51103030010b070442060b003a0000880f942c807180011969a802002070070180c1c00010180d2680c20280a221b4001800b070303d610700c00300740c1002000700b5400484048209500d80d1551000240e1080000d200340020151082410645908005102104a005159000801303206400720038205840c40d80c2265001f15000c032400d800e0442800b484001104000e4007032041040200e4003000c410943c00095101c0e40380e50400381c3c00c020140342c2d0840140c2c409034250304140985a216600031704689000d10049455440c408410f1401481d0340c054070002503c0807065008214103110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630067221 1250 630065971 630066013
    0x90f020915120a110d0905010b03190606150e0d03030b120c0901080c01091a09060a0806010806041104060e121e06090102030112030c02031e0d09090209090f090708 72
    0x2e00385040349842e41c3d0141e074075068a01104e0040300c10f6a0412207943c14001d1680003940b51441040040b440c44d107504002460611442003042c1c410120740d00070010403045102d03540003040f104a81c550b86018042d4007402c40440e402200d40158603551640040610030350103c0e8007070800501c0b101c84126040d07805d0b959018160042c6000c1c0c0e95160021403514400680c02c070507480143c2d20120200e0410344030139010b81d02c64001c0ca41c403560601c5581103944d00c1101a02c0400121b41e41c100c0e16141030400144883d001402e00741c0610300c0d010200754840102d038201e80503601103042441d400180013001c0340c00c94680c40222403080c05032211560000950340450140c031101c89086920b591140b104a600b02d200a10610303040c28007001d203a000090141d003807030001c103000a042c1d5140101d107045802ca43e55905106013040c0e0031501240b0800d940220b0803001a00d54900110f09082c9240e01041c41c1400241c4000c8641c6d00450000c1d0000104020b188041d04214046d01c00403001c40070f500104007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630068471 1250 630067221 630067237
    0x81f0f0c050a120513020402090303210703050f090616020309150c070e0112060902010516060608070914010902030919050c010801150203190201020c1b0405010e0709090f020915 78
    0x84590f010003952044034007810380182c070a4101c0d2034200f84650b08110007580111002501800140010000150070440c1402d0491000c440a5054640780f00000c0031500000c1400010030101818000c2194000030002d82c80313006440003109075041c40740309034618081c007410b49502c5145400c04000140383c0300c010706403074086d403800c4030304070f986556a10303103540740034042c0840812150b10000041103e5802440c10306006051045ca001e04c03041000042c0031038000182d43d01c0c2e803908d40400000c0c0c01042101c004009001081013002e484200c982c00c840e034103101c1e2520f803640100104218110602056109031a004001c0100340c00a00d0450307158501381d03030898041089280001100080000207480e000d02c0745d03000e90314051742c000c2c280101c42e5045013080b08540d806d03c100480e00c001001614500094420031500002100c4200000d80c2c50580001c0900901070051148690700034103982c00361101d0081c003082e0041e0032a1140020301078142069804003800102507040b2107031000a002c51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630069721 1250 630068471 630068477
    0xf0a0803070c051f0f170405010b01020606030610030f0213051f0504061203030216050706021e010b211c030515010809250305010518070906081f0f0c050a 68
    0x4075920b0041151003103580e802c61040c0d1041c02d4209105a21617240c00d1034041550600f01c120709450b0000c1041c401045808442581d52007086003401e68040100c150300490880083c6158039040002020b548074030310004050764501420302045547d4000344010040396280100583c1ca0030300007640d10784130440d40200d1011500701020a45040c6800f404003075920f44545804680d1a80d40c04500070345c807818505008815400f9900300081c018440b03c40201080e90003803d542420842c2108484404c4250f521568508040f402064981c0c003100020349008204003050b400d54603040c1e41c2000191140f0144000d200d24000c142c20b0b030103070b001724010700e8040d408140604520b001900c0c1c0d540c0030f544841450748520003040540d20120305031000c100d0314822112071140e60f550307403d0a5506c10344018403403199006103101e02200400154004043c081c20900049181010454980301200b007002c1c0c0c0d60784108049030006890342c000e182504071076101005201ea2b5034900810701d4000c40010400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630070971 1250 630069721 630069743
    0x80a1101080106020f06010b1b01091110031b110f0303070f0f082701092f030a0c060c081b060708090115050d1e0803040b0708160e0f0a080307 63
    0x802c1c130004202484600070341c02045181d00f0a00d0b090040d80280b820390a640d00c01c140300c40110786080c000c01c0d03500c504c540c110681113084c00d41006024810074880a00305441c1c078000c58000c0e44252404e44072510030b800d0940c2c40c004000030450800e02c0c0c0074003031400761000001f030145d03456200031030911441507560380c2404c1d28618441140c0200055803800120719400c800e0061a1600b20080910a100840001001c200f0b5035621440e0000304038a9098007240342030409000b01002e00b1202c0350301d40c110090000100150b449495030355150040e1020448165180003c100300307401290059040300c3c0d96000422540510301f0380c2c540d4211541d00c001850f03480450000081401003030303522214900d0154019051009003c162120f0307101c11341e103c45c801d01c0d1400d000320754405c15110841c090100782d5a00e00c0d1508040d585080b015001c0420060b5000410030044a103546640000b2018501400e6030064100040c0500441e092a541e02c01507e030000122424000010f095a500c5a401d01c0c40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630072221 1250 630070971 630070979
    0x80304060212090c030d0509030c210114090607090602060c18090a020a271e0312020706110c010912112206140906010f090e0411040e012013080a11010801 68
    0x81f20300802c0c881c0c541550103203084011502d000b003001ca14440c0748080003009078039119041da080d05c0100e5003210003404110b0070300510305d40900c820b46d80a880f605002a00500e4910029030f03501d4002c008003c404d5000c41d0f03038541000c1140c1496950100186550403508100c000b082c000d50103181c0c0ea4000c106c0860800781000d0a2000e0403071800c0d0300104455500b4900b030300e00c0948001d003100c1c0702c00d12510f4000201c0010780301c14814207503110030f5005003d1941040d17005015800880303034103840d96000f88100041c0d6030340300c8180010f031071f00c03461454400342552400c50a5040c00003540395101c1c421042da40000040003400004048202e9014803050f69100c001c03012102d403044461b43c029420744000b410703a500961032100ca04519241140382140e450764014080f0806035421a030440c58101c0e2099949414000c0e01c000ea86500b0003000011135121881521402c9054007074009040443c0300c0241d8034200b02440000c00303080e0165039408001d0314080311a20b20300350000e804116001c00200e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630073471 1250 630072221 630072227
    0x203011d0c030c0d090c1202031009170c100632030d05030402030709050c07060c050c060a0f09020414011d01060503070503150d030206150103090f080304060212090c030d 75
    0x14007403400c46440074a15155126010940e90002480d64140c0380c49030446130000b19080041c0c8010440100034008103030241c13040608040c0c24201c0c030311019052078940d8000c56911203110800440c051202c99580e040030b0601c40c10301044041080140f880e0050010301110203118032084445500c028000030120448101c83c611b001c9018180c055015007111050f190044005641060005044581d425528507a140913258101c0700543d41c03440200b0139004101340c6005040d42e55525042c4a4101222031546541d58030000b058403207410348a00c402803c084440e070040b4030940d000b50040c0304c0032000c409060803610b421b10840044005100d00c012001e0105030382c180c140c55160769a980345441c2c403182240d0740e4201410f0820105c0500300306c0240d0380c0e2000b00d6405102d101c0c1c3c01914440c80e06542c0c07000c80f204207048140c10b040c00d014501740002c030f40700351040225a0010125407aa1203a0a040001307001c0e1071862a28221070708280318070341d00d0000d00303051030300421000c546100080003012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630074721 1250 630073471 630073529
    0x150902010c050d0f0e10211103150f010e09040f080c032d0406020a0b0402031c0305060f01090501020712060e070303050403060e030f0405062b0603030908070b0a0503070203090a030303020301 84
    0x51000107c200306241800c40c401c003600f02c0295007824012411401c040a2104264815100310a044800c00d000203840d05250f00503480181017401c22420b1040d0b03400108012880003000180402804c0507583c080041e19070941c0c0038001e0040032242c40b2808450040400342040603600300c102607942884d5070300382e845001c50302030b16804c0e80685000c81c034030b42d50f06040000242c000c1b81d1601034404800244000d0344a4010307103031059980403c603400d020083c09030500e914003169040140d081000d00c12030b60006115421906070703030401d00d00f801c8941044401020b6441c58040f050113081c03000001e01d98080060010f603402035004101c0a8040011035903280b00c0c91040e2405480300344010042d601d070890241c8210395000410401c600ea098120110041d1030b1299440d00f907030303181c00900505078410441d1010b422018020101d503401c0c500041d246008021104081050000003c0c0c240361082c0f0541311891000362100c0350080c0c0b80d180144c00782d0030074040da44210640b0895410f00d46000b00c0301c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630075971 1250 630074721 630074749
    0x30109030e09150402030a020715050603122d070203100612020f04021210090b01050702131d0601060f080c09010c1103011e0b0418150902010c050d0f0e 67
    0x38901d441911002401884680202410501c2c0702c070301d07000c80190f100c5000a40c480c0d6506800140e03141d07002c0c034040020403d0099603404e81403404042084a480019460929402444d03209460703501650410080312196001d080240c84c050714004c802c28900780c00360040318421400d90b5103440071790b00180d00311764440c805c201c81c41e2100444440542091425002c09540281002d071422200d1900035051003400d4511186510310381804001007980380c410540c846509180082ca0483d4030f80000b1030740c1c41c180301c002440315911030b407408010100c811500400c41000b000d1720150340c0d680c00c006d400f0782d82940904001c550b1404c00a5154120041103804292058407103011420300d98540d80b4561320a1002e0a07019941d91780e00c407441343c4044840e0b030043c407281400480c0e843c051400f808140d4440c40c0f8454980502001c000700060f4034008106d11110704424006951801c1d0f00040300ca543c10402d028109025044880c0c02c01644541202c104e20183d80302c200e190070703901043c046440311040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630077221 1250 630075971 630075977
    0x613050a0201140d1815150513181406060f090403030c03110408030403140601050d1506120516061b0b0c1e03101406032206020c150603010903 63
    0x10320600540c0180703c41e00c00700241440725424804034425910490301515500902c0d440026600c0c1c0c200003180f04000d1003004031020a1142c8001800d03c07005141c528010300d4072074140807080e072550034542e601c0340c6900c5183d4924045007031070301c2c1003000b08a19000e000c0a900c0c0034545c009200c07410003400c420301c9004040c5c070701d04d02075403651401c800400080665004043d01c85c4910000011038502070070250190b50055a940c45c81e600d402c541c800c0c40d807070807030344079421160040140e50f07603a5070203c0055400040c10381c40340307030300170282d100030a1a500000842442c82d50b200060110000b0040301c1c3c0307500c60300d4000c0450703142c0c0b005840b0303407a00440480b840c031401100c0701d00140f42c9054881e08a02021111400d041c2030b680c45140040c0044102280808007208102101049900841c0101781d0f0b15141030801c8421804104140710003003926a2100110b66101010b142811a0a81d0306400c081d003151200810f201407502c40684441c503400d80c01c81400030855500d418400d400025516407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630078471 1250 630077221 630077233
    0x30f2a040e04150527010506060304141f0b1002060405061303020a020d03181403102f030105030c03061311011e0305101d280f0608061305 61
    0x102100e030340000d00500c00c50b10000d10b004021000f184502520703005d45460f00d400f0001e40ca2001030b132800e0465420b0a403e103a81848180800758842204030382e0066003005441080c0001c1185452034100081c001d50300080b68011164000c0e95140d06ca030300291400c807120401c004807108200c0e69050140c9028021b6080000400c0c0260103a4910041180c441e0040c3c58215056800080c05000785840c00d41c0456103a041d00e640070807190355490094070181d00300914202c0c401300829a12120b6080c0c2d016426601c41d14244040c41c00c078a0344441040104007801940c240b281c0407401a0001c3c45064042d120f0404202d1b100d280c040341c1e070f03403190b1200c000025003c0441c0c0c0340c40c000f4299a544050510075400e000d0043d010301c0c122851212086610045014182040c0b1038140e1001d0b035000ba800c01c0c000c1c84074009085003a03c0003e402c20f0806180fa02000f0240c060004040781c0034110305c80c0d00c0e107451020800c00c04150040c0701116004410f90742c0c00e641c0d0301702004408a004900411a40100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630079721 1250 630078471 630078479
    0x503100b1b1605211509160e0402041b1b03110610140f18071b03090806010632040f08060f060117131a07081005060f0a030b15030f2a04 60
    0x4081117645c404190801c40310200da48181e00024520039800400300882401704000c00c0d400e044c051f5000c00781041c0d241919200c01010024186100c8208101c20f01c180807102d481498407500075060000c05010a980707290425048000c00b120141c4075104c2da02c080005501d465160074450300003d20f4001e01150440300740a201901020f038018444010320010a0200d00028401417014607c0c0340b0944441001c54240f508103840c3c800140d200e4002c11220207026028101c030301d41010700721105034248401c0070769500310041080c00356400003450125454000201910006070840c090280ea1144003c143c54040c01100e11030103011580881e0700104022903424030002e0465200345004142c21207001c825089903280994096a02d5000119160280080d00401070b1880008060455141d49450481075480c005400350b0600881815900ea41e194807a48510401ea0350301554107640d5584c914014107101c221140949800482881041d41c0c10b044a0901401080d40c01300c1003002d6044c11b00e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630080971 1250 630079721 630079753
    0xf09061b02300702030a081c0506090112030c23010c0e1f112401030605070e0907030c1202070813121707080c120c0c010503100b1b160521 61
    0xc00a0704a0b0940714004500010a004030040c1000300c0061012300356210384c422091080d80c4000e00b1a03441002c494004202e00e411075519a0711007980342c104a4102625418032032008040c0c203882140000d0391400490f103407001944640415034981d140c007080c031003000c6c0c20b02c08241c12400f1000b40c910291159807074043e001c0d07080c100311440d030401142ca0040383d0841d0301e100c117440b0009429580340303068014010488240521a4071070707500c0c50811048a2198001024090041e00031814140e0307504209800c14402c0e0700f004c0e070510340c1d58400e40d5a06c0c541d181036843d591185480480c4810703020804034094104021000306190890182c05404020612880c8103a0000b01c5c21280044100590f882103003080c01444564480b0103280c0b9210a40100042e003414461100e02d4104803082081000044080800d40c05649500303038802d4071414204824001400342c003084107c0e605c6a0a0101003404051443c035094440c243d911400b8011004410821a1303401c1d98840340a4001d016681e08501c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630082221 1250 630080971 630080977
    0x90308030105090c0c0a060b01030e150637030605070215011404020403050d0801030501060518132f01021207050d0e0307091e110306030703060f09061b0230 69
    0xf5401407641c03801040e4205c407490040d00e242e0482c1d1075030f12140b02140c0756805204207407110500308050105c80003120f80301000d0380c500400503072080d0b000800d00d0705280e4101045009201c0040500b600044281d00c03441c0160800b803008a81180c10304002420548c801700d600d4904884040c0044066420300c0c0c0280c0004101000d011b07000b55080c80004040b03281000010042001615038180d2035043d81042820349521341c0100e406801459070010b0000c001070902640828000101842144540f81624544002d5010080c28406201c0214011a01d42c419280d02c508241c00b141c2c203c941040c1012501d0007030b00340140454008c0c40401d606607010f00000301d0f200c0c1c0001e064521098039618110b00300c9000a10402020007007880c1c0340c10319140362080907503948010059509504d00500083d6540c2d40c0e9000040c4100d40300c606500300150300b41c1200401643c844e900f0b0299803405c01c1c500c00c0d5510b01040c0c0b10014400c24465000c80403a0a40380d410000740741011401011443c0c3e01400b082c2c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630083471 1250 630082221 630082231
    0x60602060a021e0a030e060703050705090121230f04021806011103030108070f080309100c060204150f0219030e010e060409020d02040f090501050a210203070602100c09030803010509 80
    0x30000c00049401043c5010041294809a850001d02115900b100d90f00d4a24020300e10402e2514001c01d220f4595004001e0301c4210400b4a400c00c500c0c1c440050f800b0003080c6440440d08514281901a986003a560444018504450803c40c0340c50b607604034040001807095401a4000394201840900f070180044016400301040c14201c1138101011070351859540240e00041d002d030803505042c4000d0b00c0b055080e100030310002c0000c40c01c04005400085810a103406c85c0f60034020030001c4441000100d0b0150b600900d212101c500c0c80307204595002c1c011a03041d05104d801402001c403010711150512845180c500e4055450921070400e80c4015038100011940300c035404401800002009003241c0014070301c02181d03034800342e10380d07280c0100e407513444d17445800c40e801490404e001031005480c1c07180904126000b05900c0e400381d2514034034aa081c100c1c8054080d415014940c804148550005003036400c3d00b86100b410403403100c10520480b88090103001c01840d41c1400c0004020501c0e02003202a008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630084721 1250 630083471 630083497
    0x608150f190209090901050702120423031905060403030f09200303070f050c010215011d190905070501080c0c0a0605090f07060c21050a140f040306020d0f060602060a02 74
    0x31009142c001082200115030301440e1b07079119030410075841c1c0d040c001d2040d41020032a071a404e2034208a0100700b4103002032141d18006550001d03500b440c0d902040301d07020141c11440c0c583e080000a051403629180211826000300c1d05040407410000110b2080006403500400904034034104290314482200600d000c0c6a8035100501290010031044041007070030743d00c03510040900f403c0c00d40c000b81c101007050401147c1444000d004206610b0114107554501d0a194840f02ea83d41d200c05045410340032040301201d150703217030a0411041000c00101001610f409803205500c5580380340380080c50303202d03401031301d0a01d800444600e4001130594002c217030010381440650781085112562a07103002166848080080d01c0c00014500788517004401070318071090303090102c0480b099440c016001d8400c1c10001001c005203074620001190402050721a940c007881d00c0542c2d283c1e43ea0801c540079411003507452030b0251628400060a82c11841540304a0f88241c01501c00c0395105000e0074000e402004c1400d5030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630085971 1250 630084721 630084727
    0x70210020c120303010806180715050403080f130906120201081003080a2106060f05030406090804060201060504060b03041101050d180b0a0b010e0310020d060504020304060608150f1902 81
    0x140c2d84001c07006107182c046100542d103a43c541001c02d841c120010b4040c1c0541b00503210f0710042c802022410764265821940c401d1184404060210350900c40c1d070344007424003c3c01240e6800c2c0c0d40080c0005295820f481d0a489170050f440d08026030484103036200d0bd00c2003a00041f6184015401034500d26030010020b00d03c5148640d69850f1009107074003c00581000481070403040103d00031040011070500e060a208000c41c6090a00140c8001840c2d10013800348040480020308100183d00300d414455805036025031140d944000c064043c240c40e008161146040000c00b1034288041c100741c901c01d039000b4a41900c8c82403014010345556005103100303403000c1e03154032108500741d072144002e407883d0344102c25100c181d20f4001c0d04041244c881c50380c118108a07070642e5198491307500007000b14010b035000300010307522429240d0030001000345502c0f464009001104100901015512010490b60300760199801c080703011003001c0c100c0030119014400481c0020100303540380f41501545100a895501c0149 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630087221 1250 630085971 630085993
    0x21507030f1b02070e0a0b030a02010503061c0b070906020102070803070e03070e0c1b0c090f0703200403050f0d0203030a09080421050f0703080d0906110c06100e010b07021002 77
    0x610516001803880941c4c480042044013000c040c4450f588500c880710100310b032100310400a03481e1840710802a0400c01c021011400f20780e42c50110800300203941c0b1702e03150340c09081d1034240c24220301100d24070701180d41c8610000c0c540340180219050907922160321461590380b0b240544140c2448004103800d4071540c0404a804403010085a0040a0114010740c07540c0c50b14401900a1500c0c82c102d860319089040c0c0340380c1da0740b2545001038202c1d401d00030342d800f5956000000c0b0300810000c81c0b01141034140100e03e5151882d0034009009881c060b60a03580103110610950341d0394011000c8490050307100300001000484d0507808007500d05d1140c04010700c1d1641d02c4812483c10440d062915410454080d400b0080040c204005110301d0318900c06408440d255032a241e40d54014030901d4040540c94120380010806594484913172808c0381030780c0e5a2610b078980030396a0b032040101c41d80361700b5850402c404192500c2003903143d81220a69010689088195402d001e20b400844c08400107511400407410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630088471 1250 630087221 630087251
    0xc1707020322031a0402060c01061206050f010e0112020105040b0a120b09070c140a050105040b0a0b040615031e0e0d030f060501090b1b100504030e01021507030f 71
    0x5014050650041da21480301e1244040e40c0d000201158042004000342040051504904502070300d84030443e24100c0d540e0380c00070030b03a0351203012480700695280c28070105400401c80c0002d81114098041040166100700804a04480a014401d00d21700c10030300400c10010446072685000384103241c41ca042540d2030110720919040464030801041d200074051540301d003144034940c4100c0c002c036115107090402d000d003d1b01d01e207401c0e4030180c10b03a01c0c3c1c6800002444010000f542c0d020358420001c11052610f401d181c00e490340c01340c40310311007503007094829505440d09025450070703a16030502940001c510407201b80d000b012841440030401c00740030000d075240940f5100b00b88400d02c0010161003d0805400000e048071044000ca68209241a00c00d0199980c0003a40000791460004001e076a200700f50301041810700002c948507024424000448405c0085801c080c0c09a88641c9908441d40001c0d001681c41d40001038445000c1003250001a11f1684242c100c164401150040040c0310b0411160361 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630089721 1250 630088471 630088517
    0x607030e06030a090209090a03050a180b0408060f090f0c0906010e040510050a09060b191803030e2e121404060e061b070201080c0f0d06080f0c060405040c 68
    0x22841c5155134840000650070000c0e030442d8842000c0700a0304400b0070564025000d03020341104070b02005951140095084c40100f0310310003900c1c00d8000c55840d1603507403000590307034203007119601030320180040030904030403000400110801307200000d024102d5075a070030302c00314a0000304401d0420403007003045d00790764540d8801c2d140036607003400420500904050038490500c1c0b59030300c0b6400707061400400300001140d42090319105010000143c038500311580b01200ca01d9807092100364091000c0b07400108040d0814138002007080290307800c000c000020104d2400d4103130340c406070741c0d806905020f94018403445400f040705541d6105d500080d503800c10b0030708000007c070110303402c4a0f02c1d60f86109030340340c0d003108024043d071010113100a00d26102034100c4805050081c0342c002410700c2140320224003030221b010140c403240c0c2e010401d40c1d41ca6007071100c0c03045d010f0032403485581c09a0207103a00c1c41140d044041450840c041e000b618140c0ba003880c2c1414000180001d109000810420300344200c40c9912111003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630090971 1250 630089721 630089731
    0x51b040b0421060e060403271e0e09010e0c040204050907030b04110a030b120d02031c0605060c2103100e0c09150a09080c130515061605010f020c0c0607030e0603 71
    0x43c4000e10f0686000b80058203440546040c030303523941941d40364030b0750008a80c20a40c0c00c1000903032291045005c040200300c259420000c040003980f02000800c0e00154400c0c402070024900700c80e8500b000c1c0c81400101e02c00c81c0900c540212210000805a50194201c51101e00d0090000900c0490041811020750400c01556001927210070f0038901c0c903c2e050380c40c02021a01c1d42c0190518080040d4065541e01c40e81803002001003542034449108001640460002e101c0900f07070590300d400f4903111644401c01c02044038804483d4528071400d02801e4400e4a20410300d10618070540d906200c00710301445402805500d04400070071100c0450b48501421440054542000a0322183c3c4490068038004880c0c103c800385900244054055994590824000e007845d80c90004007a16034100c4100e040c1044014190000c10016120244000c8018200d01c0640604000c2001d22111070410059104184c80c0340341c41d511080000c1e007503241c0758000700350a61103030900e880d080d41b484d00810401e030011a8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630092221 1250 630090971 630090973
    0x601090219201903110102280219080424230d020a05090a091e02030403020a1434060e010210050108070315020a0c0b1509010306051b040b0421060e 65
    0x50f0b050401d50000c084242e011150300003541030000c21080c28035444080d403049010002c4503e03241c074005000344100c10100c110048050032411450401075075660081c490700740c6003440d000a1001c0c00311000e03460f0301244910b507690000b000300fa0105050304480d0840f45080c0c070070104100b9400c680540b00810881d120750712219100e0a050042140e160304961240070041d0401c9000740c10360b02d05803804400700b26240401a00d0351100d050880c5000030408004181c00b100440b22800100300041c424000a0b051100c444516040d15604683d0310381c285c0200c100c401604000c0c021280902142c007159030040c0f04843e5012011201074013030718400e90208803182c10110041c405e01aa92050420540c4402c01c29032400c010300d2001080d1240c04100070b828400401c0100b0300e84002b00c602e101404c800145400900d5071079003000300081400b41c030640000450740460b05201c09a0b08140c604840d1b4451240703081034030745a0f44503030302006240750001c1c0c01500c049020000c0c3c0e446c45030f0000c01c4040c41c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630093471 1250 630092221 630092263
    0xf1b030f01060f02030406020c011202040308070515060a05031e0c132003040b0f0711160f06080f0a0e0309041a032503080d0b060c0d02060109021920 66
    0x340701403d4051000c400c0000c41d042040148000b5800080c0031007074410a19000c0414035119400074001c1c09503420060030040b00080c1142486070008040e815600b00300109003182d100c1e94100700740c400c00ca104d41d1360903805c40a001055003a01201221020300740f80c096512400782c2d4000110f00311a956040f410040e6038a00a4a81070822124042c072680704100c583d10310b06040c0c503500c2c11003000501c0c8050003082e102c0062744451003004804c240400150071a644885106455403071a11540960701c444045028002086442001c1d003030f000d01c032050740c0240c1320384412880501078082c240c52a94603110801c0710078580d456038800e655134101040c286081400207041010b0070080500800814201000008000641c081b544107044030307803040400d40d0394280b42c41000003421201e03500e030340d20060228078100003010100710300011441c0c83c0e0980d8050f0381c9504401c0704a0140f81c02110740c8404000b02d400c0c1150082d001a03008240b03503e48070110405c0700501c3e0303107410100c910b4011012904 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630094721 1250 630093471 630093479
    0x1401150f0207050a05041d032703061303183b31080403060c0f0c0b04020d032003090307090911040915050106050a0e010e03060f1b030f01 61
    0x1010044903011098030140020b079161200255180c0100e000d1940309075035030701c680441000008501940307059020182c90712212441004280d555000d10594200070003400031980741e1501007036491041c0d03a1504008001030564a044650381c1c032000c4610560351010030081014105550803040c43e50f114084100380d0300102017907001c490f5105120324120701c100d0040c4105043c0301403401c40c60790048140030f00c94071280e420200120903000800303022241d0004000c0180001034026107115074854880ca0325152040e40202c030801e481400113014a81e41e20081001440c119803596a11030191130045c43c22048a40440c1108001000c2d0100550000915554030304061190388000c05504404101c0e22000741c6504400301c040c440941e124680d20562301040142881c400d400003210908200710944e100c4d20301078027552050031050b01181c8018047c0d0400d600c101110008600d01070090903440d141c0c0e12106021980180030180f003030003401c505000302c4808102852040004d41e4010742d00f9458 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630095971 1250 630094721 630094727
    0xc0c1f060e070918020405211903050403110f03030307080709050616060b0102120f040302010201050a2f0c0a0303090c150203030f0408070213201806070204140115 72
    0x1095014802050000381000a1180c03c14040c01c2103407548101003a411841454100003803185800450b8040d060421440401a02d660074200c04141c2c2e03002c940c0e000d41c00d0151301e140910358540040019000b000180005141003410b6000141c0180004521003c001c00090442d0000c6a00c5000141d003103041100d490360111004000b4801950001e107032454030014803558005881000e0401500c807041c0c0401d5900c00c101c0c2c20070000c3c0103000c0707030344400014243c082c55900c00d1000340e0041d800c2038003048403001181700c0c8018180e5966901c240c501c15084504495105000c0903903070f401d10902c64406a540240058002c03d4861360303000902e442649001013031042e44e41c000b02c0010710402d0069401c690000120703a0001c04912480c4190740c1c840ca8130800300c2c0318044d0006c3d040203000d4901d58001c1000d4101001c4540540305200040000e82800d80060040310130850321031640e13800071106424944000c06009001500103e4114041c0c01d01c8485400c0a0f030003002500004051803903030645c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630097221 1250 630095971 630095981
    0x1608090a050a0b2205030d1116060f031a121018030806011b0213020309010b03010b100309030309050307030207031211120d1b0f1706090408030c0c1f 66
    0x1412a141d8400b14101411042d881c05902c3c2440594003e141d03601c071028004001c840003e210090446056a8000b500200080c045000c0b100040c412004034060504a6220b400256121960703419400320400c18114044c1230045c88122000400b0150a80c56894200790110104064001001010040401030085031080c00c0e01d8240038912000560000c0e50043c4515005442464061000e11040079000722401c00b5040007580140e400a8090048071940c001e944034141c000001c011038411141814203031402c03c100694454080804480c02c503000380d00088480d4000d14000490700302542e101851644074070001d5002d0390101c1420000c100d901901143d410031180f4000802000740030750f5a039117864545200c4801c070000b0840481804044d88250b0301d844000c0e08401c02e05003a07100207855034607840a0240001c0c1d1503092070300e4811021140c14001c80c0041c14450155445454000e0750f9000a00403c00d902420003210750050f404018841a2424a030100d4000b98400800001150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630098471 1250 630097221 630097229
    0x61508040b04060b060415030b0a06050910081902270a08061902070f0b040b0105040603050c0409060605120321090a020909010f1112010e011a07081608090a 69
    0x12295104010004003442040c1c1c0e00958020f902069180e20280018104e0145030400105040c1030009003a6403a8907420003d04a80e05a54507601c19803109000c0305c051007001c203195002044d6106401c680c9201e01d40c1c2c00d5002001c0008260a8480d0441210980e407000306441d20900c110096070141c1110004200f60880301100e00382a407a05d04242c9589550005000446c95402e484041011022980484450980c00b00d42c24128180601d8004401003054a05403041c144000001c1441d0070700344240c5050300d420000403c501c083d03010400000d0a1107540c11030310b25840d1f0b07000060701e07101d03800c0f4042c0d011600e802450b00c6010191082011130b18490a4075020a001070501030342107808510084e00c180c05864014150340c0d2200c02c240036261861320b10b8071852a2100d940096040d00028102e40030703007200711800c2a6625401c000c5d003c1028040c9500d660080c044445401a1440040c0707182e6204580c424105517901c640c80e661241c0340c480c140c5e8000710000300d4204d80e181081d5140c01070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630099721 1250 630098471 630098477
    0xf04230a09020f070c0905181923010510090506100f120b0a0801090b0f010311100c050105010e010503101103070e06130909030f020a030507020103110d0f0615 70
    0x244415100140000c0194451026002d03030024005a0341151401200c000c0390304401200e0b40d15584240740002424101c0300c0c55240b40709050b080d61000030100304a00714055402055401042c10b03168802c0725041c512210000d0904031030001b901803001e000e018032a41d042164580720500e13211054050b5100148903c0c4150352880d1846001a003001c1c0310300da40700e072900d0840c0380421520702d510002c0604080f004e900030300c9110001101c1c40150004445103201c1e00b4011525200d010362442508800c0c0001021014400340b00c245604100c41d1041901350780d841c18899800c3c15407034403821aa000e8110b13000d0030340c10710300602150a00b04603100b45015106d070204008056802e240005000180001d4100000400d0190346070317645105503030307090909011121105650740041c00042062240071000305170320486100600b800812800c4425030561902480d04c41c45a0044004040d14000b0002d04c100c18030140080380c20780d1240e0410310045040c0010401d0078a0b001400700000b2405e01010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 630100971 1250 630099721 630099779
    0xd0f0e0114090f1507180b040f1a0f03130807050601050f092e05090a060905010506190e040906140a0609022a030903120405090709050906011d060f04 66
    0x495a0000781c9040705400e000c0c2c1c90b130381a80b00c42c04100e62020703031040743c0d981c81080180085100d50b4000000d04c01c481450451901199440c0f02e072003004551248944000c9909108074400450500015a0302107280035014802510b565a00c0e1f00070307045004280c070141d01c01401407019040280307002d15034640c21a00e00c801361170105401002c6e10110b00c07030003004804200b48200008540c800c81e01c05080000d0a04015142440b40c0b00000e00152003580880d908100000413507046c044210f403940c1410026031901d4003508101a40c0808080e0a810703002640e0345800808250701d07202c0e80d0201d80c1c0c0302d8031512850400c28041c3c1e0036500c0c0b907001116418410461502521039190680592804d01c032503100003860080301c414110300810310915014007a0b550554102d51b80d40c0e00910566a017202d84c1029a114140200e42d5008240149500b1891440200f1410b42c0a43d641801c0b84400c406041c01491340d81e80030a100d42c00c8115449081c500c041414800540844826448403000c4880c030710f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 630102221 1250 630100971 630100993
    0x30c050d080a0f0e0d060209040506040204050303040b1809042f181008010c0507030f020601030305090613090c051206090702030306060706060806250f0e060d0f0e011409 75
    0x18080c810820b140d01440183c040114076a402404404524080100303010f24a082034203280c17020358403004016125a152400042c5585094802d03641035560140083d0305250500c03011000390f40c44440c000085d2040940480c04594035661001d02c65071140041071886a104403c2020360758800c03124844180001c42c0944468445204940090b49011060145500c440c0c2540500340d806802584055007060081114550018000d280c03440c4a55600200540407450481c0c13205030a0000400081041010503824542040900304d440a45c4108101c0345503201415000c0320584828000030900214913069058011010690b020318207a500707450174600031310000d46038803000745891300c1190046447e00a0114550001c4080c00e010800c8551504003c031000044000104e06030180d00f043d86d0441c19880d10841c10000b12241e0742d140c000310f140111007000007540001030104030040d61902002c061800b40d004140d05030042c11700001e401c41c8002414000880014010103680c1d0029082c0340d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 630103471 1250 630102221 630102233
    0x61e050405030313020f0d05010b0907052d0c070f06090b160605040c0e01180507031b140d050f061008010e0403080711030307080f010909020105070f0f0c0f030c050d 73
    0x943c041d0b4500051400d813001032000800f0a104051219080398402c544c641c100700055224090700130701111280200d903911403007102c50744143d00c900029841100f0807c224801da600381c5e5059020140b0f41d09040c07011419220b403a01c64640d00014000c0d503841410809a50016440e5001c1c000b040c802510300f07150700d61059400b101c071020040c050743c4d1700c0e0f0010b400c2c404912940c00203441400f03047c0d8003551303650887d0030300c1e1920108800140744c64840441c0f6800e00910600c0600700303020321000280003c5203001c0d1401d40c401c1c3d1b1040031444082010401d41cbd90180b191506c150b510302c00456803414210180300c4084c01103028a01032203400030044c4003d1005c40401948158145040301c0596900c00b02203d41d02070302d0341006058800401803010b0380e80c200a00d244140f14103107032015241c0c0e81e403620354180c404406010f4003281d410000040444c4650307400d598810300071110501c07190b1160b0340742c2c0c15812895100c107070003e0355804144204016101030b00000d0904075000c034a40d9145803114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 630104721 1250 630103471 630103477
    0x307030c15060509010b0c0c180f060a1d09120f040902030a060e010303020a020906090c0702040e2e0f02040609120c08060a0c0801080f07151b061e05040503 69
    0x207081c010202908000040450704100003a0001506465955a4032800d400d1981c001e0b91018160303004110b00500e0703504007101c3c40b414440c150a424003071620381c001440c0e4034000c0588070b1a080840420041080c1481c7e00c1c401001e02110258041070303240400040b410b201c4000c580d414540e60400045005644000545040e64034480c3e00507940e86a030b8a03031304024401340d400b15403403140c2c07140008103140e004107600e81503600a4401103104c0e51103000708103503800c007103841ca598a03405102c40405030030158400c1c85100a45030480e60340d041505c00680c544021404030004220607100c2400b40300740035005030413286058400035410181020030160071000c071802410768039862495918103001c0e4541039400149413a105640b10b0782402c2c45071401506d03600100e00003180c580400019a03850005803440c40e643c548006d400d84500b00f510724480400b001144130200101616007400c1c20b01c5010520710923a119080008001da01c030301c48035200c1c168131024440d02c6840e003c1000003041d008412 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 630105971 1250 630104721 630104723
    0x30905030601141002010608331009020f04051f110105010b030406180b0a0b0a0501050403171b0706020114060f0d02120a08070f02032b030903091706010906080307030c 74
    0x11100105118413412401445654041c1800d84508a40d000302c45071680703454a2405101458513203044c494036250440800c05a90142220400302002c011540042e405070aa009041e9000c0746040d58400009000c024041a003501c0c440c550300100c0c0c103458114049589410041c3d0081c80b06c3d6240c521448514000103001030710b0a070300c481401140c1002c0d80350202c076403544088420304500b8462190001840b142c40c17001d0240c03851060202707280d80108151030840e075000083d241e4140345008024000d130410302c05000c1007513a44080d020f1710b80c002c0c0407500180149900014144880082e06042028090809030145541440940044c1c803074040403540e054050361000c1864110005813450000340c0398001e020840c01140c0701040140606286014500850841b0a11810402807040c0c40a000e02031008064421494003507007030083d08011002c83c040e0038503090309a0740d03c48442405400d54800b82140c3c002c44010700420a2030f1060001801031180290700380820ba56018000d0254400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 630107221 1250 630105971 630105979
    0x3060c1c020c07060f390503030f0103020301180804140d020307120b16080a05072c131e0906180609050d05040b0a05030c0408070b070b010e190b01020c0402040f0303090503060114 79
    0x900345014844400158026901c01f0469544e4540505030741c1c4001c3e020700040344070f5400c0840b40b42c100c1c08055401401c42c3c0d000b0030420703e098034143d00c1c03645440b58104400c3d0442d0030306200310050f80d01405181c00174000d074915a400c1d0000c1e80307400004081c0062040080b4000e0050307003803c6591108100d40c1c4140560000074441d1503c1d80240c551501d032b0100b5803800580102c4500040c0c0c4004441c1a0049059880030494000787c00d40e002580c503140342407804468081001c50128009810040034030303000ea0400906801002c2c9642c9042c0c0406405844139519600e4a004000c0c00b0805201c0540341d516099007030074109501d405403449151101d400700500800030500103440e04049400a1140c5800c888509968070030100d80e075000142c0075685c2e80d01c0b00000040441d03010201c5841401c104007081d401030028051180280b01140034070341144100041c019854680340300130800b820415032008809461464000d0001c0e03c203810083c001d8000030700400c2002a20501024018800c171 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 630108471 1250 630107221 630107297
    0x40c0b0f04061d040507020f1501141306090501031a0f010e06061b031207110703050c0411090406231206180f0109060c110c03060c1c020c07060f 64
    0x3070b8600c0303c2000c1100105600070f00d0030061180781900012041c095000070026181c48203401d07075182120754400d20590440491240c04007082d0f190401210520604044000072140d88031807100c1c0840d0b500740c2084454002c451000700204901080c030307541c0709a0703014880b9117030b60500c95044070011300070384840e004050208070200b90f031480e40100420740c4000b2044036110701c0c0462501c0c10042c0d080d1101c0c40410440d0881c04420381000c0380c05e030140e0350800c0c007c21001c80c403003060000402c2c2601c0320070102141880220410798031401960000c0002c5185210004611100b00c1356030408080018030032014070541c81d528010110300076a000180010940c0022540040355041003020f0320560406c0d482c02c00b80c182041290790014900c154245e80d41c41c1022045034171169102210211140d0503446540002c05441e21100108203451624030349411140c41c3c1c0c4507003420703a00328084000c0c00381c00c150010302095900044000040c0401e00e8600180007014031062401c0e0354042c0340110700c14400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 630109721 1250 630108471 630108497
    0x30610050c0c03010e010b01080919020108100909240207030c0f0c15020123060d1403040f0e060f190b03060409080307110f070602030a0305040501150e040c0b0f0406 73
    0x28440010881400f038000d1000740071a540680c000e06589000c00c0c0170440d0900841c0d1a5035000441d5030b004800196607081c510503a8005558045009190300d1604a1500c00441c3c14461070058030103141c030070b00e020444a940c650a04100002903503294421610501803100420380c400f1f081c03883c01c2d803c00201038154010f41001400914a47c03c05d0784030450300d201c0318000641c1503000c642d03500544088103250141e0700300309000c201c20559643d40d01204a6404d03a020070003d40b0b00755a40706000044a10f007981d901c410341e00741041684400f13080c2d40c4d03c1c01004294204107054008601003260300b21400302c20b89800b20100d000500587c942400d0210000c1d1254817154030540c5002d0b0042916512840d00100041031004c1c0031424002c00d002d4640200340901d130005164003528501e80265051034076220048000f004014000e0754a503496042603100302c114522044003500d66050213921901d46400c00c4a04803000381d1000300892010068004d0114000c01643d007034a5440c50104100859 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 630110971 1250 630109721 630109723
    0x3150d0501020903060f0a151d092b0e03071d0901060306020711030c0102011e0b0a05060c1e0c0306010306230f01150206090c15040806090c15030610050c 68
    0x180407030f0150180310700d109100c0350306401c0010b280305031a20b84082c03002210150040781c0704203061203038156607042c19610030696503101e803806901a54000c1201c907500400740007901c0c0105d01702c5d102034803d8001441500c0d071f03a031300150030202c58000307900038042a89001240d007140c1c080300c51031004040ba0780000c2102c140b000e4100d200110740100f400d54440c005402e10000c0071408504c4c2d14032078410003100c0c8410794018007640d0b46003009964a081314100007031240026101c104c0041c1c0c2e110301007803404101640c40501a0082d9002007008203461000400ca14100407002c54030f0b44250340c021940320006980004440b0b0640b0b50000000c5951000c1c241c403000500c0d88549140b0340c0300011801c00091100304280c040c100d542813850b81081d840b104101740d07110300050b15444102d401c4140c4031181c60030141c0f100c1c0d460000c148001c40c50595a02600c505105d82926030054070b8014204c415224034104811500581185d10303420b2640c148980001c42c00310132446644c0c01d03c00041280741c6072440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 630112221 1250 630110971 630110977
    0x4060c050f0105012c04021e04021b030904060f30050a030f0201150e010905150604060207030201020709110a0f02031b0a020a0b0306011b0f0618020a0b03150d050102 73
    0x824203009020f02d58440c4099940c2c0c3c0369118108648115000c00500d100182c0c04545000315005003c0c07072915100d422207558940302d4824500d803c5602000580104c1081d10300301c0e60007100c0b600181d03450300e00709403c210641d002c1c1d80c03046811080c12502480151106040c40312413429011283c00c0912142e0441c1025411861000e00103008044000b818150003900d12118100305034020021480b1400160030210028001e0301c200f44858001400f10107110390040b41c000705036102104c28191b10b60b001480940c4142c01000060308804410421541c040202c000900764ac030070244007401c8801001041070058850701030400c055000421906070090040321070326600c05044031181e450502085603101c01d1890224040d9120321340010341c004581c0b081d64000c8005a40c0c2e03c12440c0e24105000510324100c1082d580b261120340700100141980c898000b030066004060310070b500c000d0042101d0340c08140c0c04110114010020410309030110440b100340804121680002c140703550414a0082c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 630113471 1250 630112221 630112243
    0x20604170717040e070908070f050904020607140f0606030a020d11010e0307080c12010c0806060f120a06031a04240204090c09080d090602060106030b040e0d03020307090e060604060c05 81
    0x100041d000c6489a1903000c00c91045c00c0a4540180c000e9644003415078500316403080498a02080c1000d0210b0f14040d40d410b90007500040ca002c0c10620300e44c4507010b890340404444000340e8810b540510500405010781903201400702c000c0d00e1480b001e40c0100d0009180840020302c079545000340c03440c05078042e1050000c10301c4094221141d9546404003655520313500072640b841050310340380d492201c1005005540741c0707480d1a514440c4030749850061000c1904607840f844d2080d0000c3c0041d00035600700c0c0345024031030510f024002c00d080d447e600740f11020180d80300b25840c502c4490010070010075480c402810140d90300c4000003032000703c5400000000d0150b6000b400701d01e030800100c0c045850b44a0b480340262507001781590481c10203140280d030500303001d20032800507801107070040211601a91200600c990064404a0b0200326803682c10300b85041048400c0209502205000c659070388420b0403009401d410710058010708000c030024406014a10a0b10f08011140c55401d08101003031250005078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 630114721 1250 630113471 630113513
    0x1a090d06091101030e2109010210020a02011401120b07111002070f050c03240c0702130c080901140103061a030d021c08331809010605010206041707 65
    0x1030541c80c9030070100c6240721450035000034241020342241140108181c0500492048160300c410b207058007440309070704044000fa06600403a02c4501102a9600051074140319031303070000607410700420102070b150720180c102000600c2296400000074036480c207515003009103403d014105103e01c0302540d103040454441c01e0500303800030403070b501000030640700442083d200b8000d0313800b8140d441051503900e248901d90406040710345211409d100942c258001d0700005030340065442c01a19070003160a41303410000c800b0100340c1e03401406d04410f503c0000ea98000480c040281300c0f0340c40e51085100141c606000261460b6502c1d80c8403035504084182d86514844060195403e00c5403d840c00380d1214000c400036245004051070700b0716001e21030104240308050040d41c480c5203010030701400d10110304090042c10400a01c0020150035607038040b000700d07811440f030000142131500740800360035180309a0143c1e0643d4417a00512001400d8015401d158030348020720507817110220b041c0400c466242498144007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 630115971 1250 630114721 630114731
    0x60302070807150204090e160e07020d0c0215040b120a020a0518060706050708010e0915161101110702010306093c0203070302030603010c111e0f1b01020709061a090d06 74
    0x1215000303c2d08890304423440c04801e00c07003540c4642c1c0302c114010859882d00183c00003040c0400050107005030002443c0040c00618502c0440801a02d1591003500180403090b004102800791290a89005500000003c415803c0c81e030300300d10143c26400b031101d201000b41444841d0140c035856174800c2c1d8550941049081c4800c2c2851003029060f00028000d4404c552350303030b0300000d0700e0000001d0410880d00005007809000d0341e4500c8030032281c0b403115110303200b0040c1164405648003024040c03068130f40c170201030555483c1c407217100140c2111f00541c44042c40034104112607044003035000d5201c3d442001d400c1036060701c0c00b110b03912222000b00c0c805001c00b42807001c41803020031a4994080c40c8100790540080011503c8401c096076001c0035030017416060391103101641101000015100510404076049460700c0c0e0747d00c0803642c102221020403c1880c204011078480540e410042071009045120007000120306040d4160481c85000c01e400160601c005440003075a00c5400e10b58000075005141081303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 630117221 1250 630115971 630115991
    0x71106070b2224091a0f0a0b130c1110050105180108070b0f16030c0c08060f01151b21080c0301031b09090c081204050105090f180117010606030207080715020409 71
    0x40c1707011007a40c0903030524450000003002e0074064415020b01e907400030309290040340505940b034090305400404a080140d000040411130208004041140103211408a010341c10041032200c6440140800c48003c1d001000402ca0514080741e41011b850240c3d907640e80e00c074503601b2180030611580c000b0482081c4400ea000c014107a0085101341c07102d1044018070107056a07400000e558810603030303c2e0008200750000400c043c0e102c01080e490300320498204841c0790f40c0390651200783c0e00c0701101e0030b0f21136404080c203030070492a0301300d60002a2241d9003040382c2c01c0c0c24540c8114591b4041400000c150700420541d0300801010070540360001c0100600c1403000c0001031904040704c990601c0f0f2005180f11341609291040410b109440c16100e06944480c10034a0110030020080003818170f454002c00b5004080d030304541c401c01f0302c40c0038003a4200c0046540341081c03080d07402c4800c1a8015410503105224000c0010302c020221030742541c218041d164201540c500c40402440340364440b0207124a001c0c5010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 630118471 1250 630117221 630117263
    0x40e0a17040e0c0f0a200a1104110313030c0203100c0513050f03030d09060e0a0f0c06170f09280606050a0614071106070b222409 57
    0x200580b56820181102501c030f520440485001d0f00c00f10201100062283e11714840c071586c0340e858a0101d0460070000c00000d14039441c14035000341801d484000808a101e14541480c0c0036903040c010010407224034518000c07080e40e40c4c481c1440401420400b00709a141c080d0b5404000034248601c0c4207070204900548030001030700a40c055041ca100c10403184034002402c0c684010601d20b00d64001c0c000c4c2d458902015020f41c0103020140c01110340340d685c4c40e82c84490303400400401c21100d21075122504586820701701000304520584c080800c01000d0308003003440c4802803c04507004104a41c0344d1400e500d03440c966504000d960040d1540d1002400e004806403000700411080241c064041004919111400c0c0411003d490003920080366100c03e04100504510b0024204640600500b0310482c1812002512561003840c00384c401004520600071480c00d000080003034090202c0c94158080d801e6950342c2030514100c10140b041d540c081400c000440e400780c100294042d800f00b400d40401d00240000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 630119721 1250 630118471 630118477
    0x1608030112050c040e1002130905040b01030c23011d180123060405010c020a03050706090e07020f0c190302030a0f06060f06090513020702090a1a100e040e0a17 70
    0x54810340f08107100040e15007828418400400e128602600b10040340c640700d50003a50010300721074503d01c42c1035030001d40d01041e842410300681c441d0300d03076041c1549581403040d0000890f400c950a1400c45203c500101041d169100c40d150b2003e0030096000d074034480c400c1e05501c5500b110a9082101001d50ba041e06018858180c143c0e01104591034145100300a01d02c02e00c00007200d4550060301c100414026580500d241c00045480108140c50030781e02c030b80e40e45040510f40c1d40004040342691805000301e544181c14103500025500c01880b5800305480b07066a241c021900f200d014001000c100f542084040b0010805145c020f002c9891041d010303e45003600800c41041907400d28680100032400e405100d038024100c48999036003001c00c6003403204008500811260030894a6802c001c6100161100341c0c4a5110f000c104000140600e603800c5100d000c0d900300d1041510031810700e00015000b40d08050020035075201920005100e51420340d407540f50510390755001c0c0400102001002c0106c03117141c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 630120971 1250 630119721 630119723
    0x6050d060912020c21030705070608010911030c070b04081b0303150307360f020c010501090b150c030403061805070605360a090c0215040210051608030112 68
    0x24422120b05400822602c0d07003140030b1207650000d01842408607200c6030722000f010483c07071401580c0c90b010b25540c41c24503059407540501c0101e8001c10042050320014410031880d05040c02d00d042c030f50710b031034000c0d841c4602c584d001c006d05c1e0001400114092100840c103441070f0901d41781c4420324001c0c2c1180402d43d290011901c410200b0741c3e40400b085503003070229200d0f04540c07524000c2d904200078491540f000f00303c022003000c0e000c4040203105c40f2032000c40c09040381c0c400c40000c00607515803007044c40d0350964105030004550242410b9907200307591103180c0040f01c54207443e4201510741ca000c5c0049400c51040354400307441e250610540c0300b482028410043c1c055071064042301c02040d40d442040c0c401e8018240500c00d1288001b02c500241e200d00d0b0240c1c411421001c0070315040d414a400001c10300ca000b6085940309550b42d10100c1249901040b241c01c201c25044414521468135500084400900312500400c00c04003158580000203603003a4080b07101da200c5082c941740c1da101c45801141d1000c00030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 630122221 1250 630120971 630120983
    0x102030c1309151203022406180115200303041b0e01030b07110c10030219030e030702010f051c2726040504090c0e090d0c060f06050d0609 61
    0x100008240360144200c0c007070404403010030703451149045040e0981000801043d019405a0100a6500011f107d01070a801c18000b0012545040c248240004140000100083c1c0d0016a0041c48802c500900b000480d40943c60041c080a1058154003100b80c400980c1d4210342c030001c41400108031169039401d2a45840840c00c040c0169540c0380b004400c8401e20000d010a540302020400c1d461043c6141c41d40b807d54401252010030802c1c011a9130308186800d075200080c1d000c5102041d03a26141500d4004066501d1309010300058070105985a10a00400130306019441c0309610943e4080d1040e1080d82e1005180d001b1700c2002c1407444030280a10020800700560201200c150a4003001c1c01d0b01802500040034a80d82d1032240346000c035040c101d28805901e40c209100008240e035983c02401907092054600c1c0107451300d00390b1840440c110181c1400d08580101070030110f00340c0c0c801c0d4010044d6030031240c040340c0d20034030790100d4000b0000c0f504801c0d0020707421011131051144036042140c10b0381c8500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 630123471 1250 630122221 630122257
    0x1050a0b030703200a0b0703030c0801050102010c05030c21040606061b030c0f08041e0e0c073309051c080105060f0903010b03010c0f020d02060f010b070c05030102030c 74
    0xc0101078640d50603000040200003940052100c0f55010100c003200800094035005d0215154603101e2900d41298004a00103522403101643c10b070351000d0002d00400c1c1c01c0c0001d000d415a245000341031400001d100e6071002d43c000c140340b030302c82100d074088460780401002881410b0a19061880182045010302004100701c80414840701c07508401d2410742d190107588001400c0d0507640c50080d01c08038840c0c2600c0c07001042c000400c110802141c10f0314106650f000c8200300c10301d802c082c015000001810b0740d080d240305020601c04100080320b00c500500303a0302031030320030000440c4404440142d600b82c01e0600070f291241c41c038108007000038488050342c0c0d005c00301540b5400927a4201e900346824000c183e080780c0c06202c1c0d0750f51071420344040d22958a0081c00451200e139085d01203421030744845400c00006414140a1041e07a80500107040018100d2001c0c19482c5400000488101c006101d02c2800d0040000caa030140411036141740b002d850f009000359920b050030004c50383e00303400444046800305101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 630124721 1250 630123471 630123491
    0x30c090501062307030e030d09180b011b0507032418110613120b010e010e090a12050903070b0406030b0301090b0417070f0b010311060a170601020a060e01050a 70
    0x1030f481e600e00a440c90b40320f25520703400c42c114009140e04081e0013202404550340800c0f80503034060224010700c001590f21985800e14105803581130480c85d0000c500014a840c00e07141d803590740019801800110007000c0100504a031074a030385880100d5002408548a100c040703101042c0f071b24511a441240f41c1014004001d01c001b010500510a0000900e00c940c2241100030a052000c00781a010040c0c140c0d940c41a0750ba215806104107041c6001c55007040c2100041c062281d1a05c1c40380d0140c04441c600403030f1498480005076541c071032210043c00d142d04d4030882c83c0314a4810300481e00c6015000d025547c000703950342c4510080d5003007402050003007801d01c126050507080520540d651305401260710505038665032a00311040e03101c504035064807401041b0410100c2c1c02c52900c0c2a2852280d16400043c0d803460070304005844d8842001d51290300e04002c10707061550310550070602e410300c040440b206512160b00607480c000000750020015428140000104c00c030651050380b03e410400000c0c841c02c454 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 630125971 1250 630124721 630124727
    0x4050603011515050f0d090302010c090b03191b080402091501050d0c0309020d0f020913050309010f0e03010f05040b0106020607020d030f021c051b0903150916030c09050106 76
    0x4158140407507041440d01c1000440f038540f0301c6441003865800c10358580b007014058810a540070a000c18001034441203030008150342445400c070b0f95040c07490001c0d000b9080407510700b96484090300304440c01146000b42074040d5203941c000c071400500380b9889210441d185501030300d00541110306911400c40fa00028010400400340707110000300581d0707203900d05040d425603c002070840c100c0d51001c0555a02800e001620f034544800000c90240014050b544e48910420440c12002003103000e40b803060b0022440003520000a50312990824204260800c0001604494184080019035495070a0000e405184110396105500580c0a041c0048080c3e0306c0700300503a550001600d41e0030040e44294003040569100b60300104640715141005898817040c01030303c422020447d408400305564034414002d1070094902200640da8040b1181410316078804e00294490365401c1e500c15002c5111000501c064074248a40c4031019000a50306c00100d440303080c41802800e0078000c811007245414000711b00c480c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630127221 1250 630125971 630125981
    0xb031b041d0a0e010e0334050303180c01140c0109082b0b180910050103060509060601091a0a031d010209030d05160326011413290d120c020405060301 66
    0x4017030000c51a1004496410000420307000e0130210b10b6400885003105007030092480b10709580203400460b217a0910601541644090310265031450f40300303100c003500698020b0500100130103000003e64540c404e50070103a01611407488000c10418000a44d0009402c145040b910162081030821210b484181402d80c200c0f0892032109502113030f82d5600007220081003001e5544104100700342c4103140c03034060340302050701d50a070412521540c84004000310342c50100042a07000a09181a01086141500c00c92031101c1c8441c5200713164100081d40c8110a000f6081039910030504802c0c10006407450710403d00039000030701002d205c4d0044460923070480f4030480c10b80349108480d030f41c20120420303240c0e41681c8010800302c0c407002442e181c1046007459034a0440c07a41c0200088258010041035000400042c40000101da840451801ca10380900f000e050701c040f40907000e84951841c00c0c044000004e05c020414940c010140048412030700000745d402289104812310030f42e4140665224402014286c50b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 630128471 1250 630127221 630127241
    0x2030a02300319170f04020a080313030b06010f0915200601030203010c080c040b03070e03101b02030427020c06040c091a0d0b0c2715040b031b041d0a0e01 68
    0x800030010441c500c40c40c5e1401504203200500076498250b07600000b03410342c1c01160243d030038000c000104005100c40c2481003a8424400d1910643c079030017021010f0180034050140c0880039000d985206512401030300070800340b1409421107205000710780700341c0daa10542404228003030b5090091468440c0e008010581c00f0b40d4081e0300840c01e207030074402d5410403070300000c2140c01003100802015059840900804c8050031600c2000724407805000384d00008499031003810300441d4000c21040090b00c00c130802030300350007183c0c105440d0403454100c031040c0a40140c041c0e5012501940052208020040070342c042110740702502800003000540d1a900c3c00d030400211582c00c6594030082e200060501003035160300410801840b81802d9860300080035409420404841044203254103506030b1501e0706040c189914210391480c40c09050a1110750940405018021081212207241ea8081e000c0410f50b4007521410108070185c0030034098540c808a007e4641c140102d00e42820780c441d0345818000c180c3c400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 630129721 1250 630128471 630128507
    0xc011e060503151009020c0a0311240606040b030108030c0d0507080306090a060306020f0403050609010c020c0603100b19030c1d0d0602130611150402030a02300319 72
    0x1424815a507546004001001e6182900c13210002043d60340192000c3d18041040e800207242640e03851070040d103020804048035450741d2080101040f082c1c11111203000c401c2c00320300e440c8800d88561003c600300b402076400c00c03280d05001000210300b074003000018007126108407003103a002c0040790800751264818241e01401165003040090401c1c140300c4549900a1048480060110364a803a124201d0b084401d400d0ba4007040010100244001009101c1d00801020004c00c000c0d010340714003035581c400f20101280505008030006140c4d54040d005840141f12000c03e143e039400c1d4500d07244085002411506002ca460803182c5090f0360300c50344d8680c1c441041003041003a8840d01204100c2d41c202052011204560204030040c0b00c519506640c00082c5aa43ca5108042080000043c2084140402115840e05040403c000742c0c1d00041c00c900303586e805681d20309501c1014110702140e00e00c0405400d900301c1102e40040d42d500d00020051010906080f201c0405580b2140f00702c40a0800e031500c140e603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 630130971 1250 630129721 630129733
    0x30209180f0708091905030301080132090a0609050d0f1e110a0206040308030402121915060e04031e0e010503060423070503100501050f0a230c011e060503 68
    0x180d5000f803072140d400000d0041110b0340041454041501c26601800440e401d801c003000401052109004108151414002c4003401c121006d6244a4604a44080c0c02d1120080b502003490441300b80700400c1c82c0c61b0070040030701a803507a0f800d0003a41d83d0140c4a85000240b0075803061444903208100c650b100101c1c4120620880155030301c22194454403000007080780c01111003d1005903110801000114410145c0d1034032840e15004018400012aa41c0543c90308414440007221034006c000014840c1d20002298016041504c0708000b05110b03000720f806c0c40c01c4603041c0030038150080c000a00e64655495001d200440e00001160b100300c1c0020303081d001c83e0307050020800902d4170703407c5101d250103e00ca02c81e60900404100b9004403005685c41c40103c0c1d800014421034110700040e1070040d00c800e09046240600f140d0300d0650a21410764004100702c4200b0502e549048220641c51000c0260b245654480c190300f030b6032500178011165952545a051005e201d44031074640110b8044810003009000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 630132221 1250 630130971 630130981
    0xd1a010309111005041d06040c0203040506120709181e02041d060d1a071d0a0605090d0b18010f1107080a090f09090303180c090c050702060703030209180f 68
    0x24600801000c2d5010700c01300384400720302c900302480d00010b0041000b5040c102800d00505000c110b4020a8911003190000c010920554807020211506180d0340300e4515501c0d960390000b2191500190005880c050980781c182c4590102504011a00c511844c00c0e01c82c80d4000408840481c4103511900d10b60800e040c8406101411030b041403640500007514168807100956a83d42492081d00840740703100d1300f00000c0c08900d6a111071550002c0c04413500e203c800750340860002d10365034054483c0000f01310000400c0181e50700c8540d0700d14a40390b88030305042618240f102c000a130700800700541c0e41d465840c00c81e800031082c0c09c902070601d19540015419150006d1030301c4070442c95001c40340d5031041c81031500001440d611514000c90060804000c000340c0d10007903103002000d84009030900e01c0030f032a002034628081901c1c1102c0f8401c884c0c280c01d000894110020040d200780c014110003030361010000c0b40440c14540c2540082801003800c5038448545090480b07100110312080c0c03925040c000c15003002070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 630133471 1250 630132221 630132229
    0x604050402031e0109020901030303051b0c06010506071a04061a0301090f1b0806040c0501030f150512070e010b030117071d0709050607051605010509030309100c080d1a01030911 78
    0x20b03d810f04001c00400d161205402103401c0e8070081e4011000695544104500481c418204c5034114100b00700382803070f0ac0c17540c6524580e15401030040c240f0851000840e1010842070700740030b4031300074011202c0003181e15003410010002c007910b610705406c0300e142c0641c404952a040c441c40d200151310950440010100c1c0e01c40100448d50044142060b08200d10041600482005014400d51180a00c04102c44c10280010190b0303c410162035905400c01c288030010451251482c010345600b42c0f9403003929a81031641600e803104075803040505003194400440c0c00360300000258140c84210314800148900d0151042c1d540d0010703c6840d8038514a49600c140c009088000941c000c3e9091030060390180c1c442001030403d9200030300c11617140c1d00206007000800d2039044100000c05003420f105040c110541d01107600c0c2e11804450f988185155200c020903280114508014183c104251756140e1400382c060030010541c000ca070104c0d01c80d0388448030030258400d010750b03001154000c042c42c450f030404070140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 630134721 1250 630133471 630133513
    0x90304031e020d0506090f1c0e013605030d0c0302030403080c0a0b1e0711030d090611130e010506040b0702040c0201060e07030630031202040b0f090405060405040203 73
    0x22603009400c42441c101013031040011900464040c2c1c0609402c503a0354036100d1500241f801441101c0e0007000c100030025410100c00d81045c8020700f005460807080d081c03080d08400c0c817141083c040b00740003a00014814401c50755402503030000c0c0c040f40c0c040800c1c0c14060703a9103041c00f080100164010031040c4001500c0c04013800b001c541d00000c41e12002178a568400000d2400c6030b204807141d0601441180b000282d8140725004145400c004000c40071000c280ca0b02c9100da15002030880340c441d5607000400889602c01036520782c0c902110790b240c0786081e40800c0c80395510300c0b510815100c00f0002082c2840c140c400c0310125002c0340352070b07031406004e41d007800041d007414240b100555596500001e804030241c0b03c1e051080300e0950300003c000d4201145413080d0304441c0d00d800307840840781c15565295110807040743c043c982c041c280030049580301055480030344a590003003080304101060360051081c0340400f90044420449092049030744030011300003124022500a50f050384404101641e240344003401d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 630135971 1250 630134721 630134723
    0x9031813090204110a030f06031214090d1209060207050a0312021603141b13150f0f0e070203070f020f010909090c2105030d112205010206090304031e 66
    0x7142502150b0005011540210640642d94a000803141c10407907046c8a0210301600d581030030840a400d5864099008003480c0c10300052250312502071410020f800c0035103d0240c401822811310703c04620b0118500d4003108184008214003d10204005001142d08000c0c0c4c1c0d0b0203480391413101c0c6036481c1c1d002d502404a0001095014a40c2c0780c0703007080305200703503103000c0c43c0201140702c51590317584200c1d4902501e100040074100d001210740030040e80d46804215611403d06808078240040d4031207145040354035808080c1110f4035120008000130f00c0c03e2203000300d40d1400010030550751601d49c1030380c0741d00c6140340003848603414403031800051401030400c000540d0180340c07a204140d12844120129410101c0c1903c1d9800c280c4010001801041d0100500c0300c4246654007044825603200703641e90050002c1e00168507182c95400b01517032948030a481da2131095904905400c000c0798182a250030050282d00d005010310390000350109000001c440c222507000e43d100707209646140d02140c0711581e07400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 630137221 1250 630135971 630136009
    0x80a0308040c0305030c0a110402040f1403071502060601031b02030316200a0b0c09130b01121103040507170d110f0f03180103050c0d05060315090a0b090318 69
    0x41e010001c00c600300050706c1854072006c000c0400d19410b041145055640c03015191060340100414804000301045c000d0403203902000c00300f002c0501000007800c3c20700070380054000034402c000326143d46a0004140e8098030007a00d0400101c0c1aaa042000c07543c610f25242000d64000c1020503150100c8000482c10001a40340c020f00e040215400705041e142c0720505c3c4102540811394640a010074070381d0391500580b01710f01207458580c40c4004980c4045074070b10000b40a0307a41d20000d5504ea4001d405001041000c41d001b040364901c0c0c00c018412541054034141ea81d4894070101003140740e40c4003a00d0008800650044c103d80b00340d1641102c070000400c02d4030666000d0850503840503081004042c2d0309600320005035032641c2002c0c668910070008035002504040c20704043c001c40500c01003c890060103141000325407981c4500100303140805110044500419900800c040000007191031012544039243c5840c0b0ba40f036544010355079020340314643c20300d64024036642e4114a0004050884041000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 630138471 1250 630137221 630137243
    0x40b09040f0513140f060106121b030905150601050d0e0a0804060302031e0c1e0714010b040b15121312120c0c0f0602030a111314010801080a030804 65
    0x110208080e50300940c1c05240d011000c8180c1010407944e04c003081c40545084004002c4410724600da142e891406100b0035082c1301c000144101c040055410090a8090804070b00200c03812a080003801403c007008103031603500030b980320600030358050040b150050005079035840c1070103054000400141b005c5084a8420720440716040300244100018000030131860710b0060b1241b800316245d000384807040030b082003951100000c0000c16100c0c0c10549182092a100018251810b0b400c03610341441780320400b07410302140081502c550341054003c0110729400f83c4081c42039503008024070003420b9041c2c01040e034245003800001056580e07503001c0395202c43c1c42814850354251548940b225480c3d5000980001101c00e810328540d140c0c607016000f140c038194605262101c0e41c80e250f881000540b00c500414668000020803110180364000100c0b90303001d1380d050703a1f45400b00c4c06010914401e501c1124081c4140d0492506a90b0013101020304940e00c0b0009481141c441c4d17a011580380305c00410840c0d03141c07598 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 630139721 1250 630138471 630138491
    0x6021303170d0e0a050712230f100b13090201031d070303091703030a1505030706090801140f13050a0807060c12380301050c0a0905060f040b0904 64
    0x8084045885640310700c10079524141d54480000340c074008030300f101c01c075030209840400064000403600d00310358824a2807400311031286440c240d115800c8501080c00742401c0c858086000f000301708490400c10500c1154810800c1000901c2640c0e05200c10680c000464003054446000d41d4004072a050710514000400d03c401c00d0203042e8250000c0781540f4298400c00086c4205030300f24160802400c0c1c03108a1703244000a5500c0c43d6600d21009281081c0c8030340311500106003100c0b40c080300000c6c04004084e51040c94442c600144104882e2150300780540c2003030002c0c2c3e0415075001129003d401843c40b90032081d0b8a424402c892074181c0c0900721080d1181e82000c20105a800300501340e09031044001080c5e00c07090101c002d100046210061840602c0c0904148203002e082c520034009440d0541c4000011101140c001200240204195050b5003081d0400c500d1012103401041c060055849054a81d81c666084c411680203001483d41039180c01c000c140194a1070b503016020301c80000300042156910 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 630140971 1250 630139721 630139733
    0x81008070b25063e0304030f020a021323070509090705040302060708092e0c05070302030102030a0b010801140a050402030c0d0606020309010215091c0203130b0a0e04050402010c06021303 82
    0x41c4205003901e00f20344102005146650138984140318280f60f2940702e94030a0031029013043c48042c3c4001c06010481d851101c0c04c50080c0034491075590004c0c404c0340e40329044c1da00710000d01414400c0280c038080004c500c039038440e0300d110600c0c022125955071038105103d0070300748030071010090b00c0101031001c1404000010303603c0030001d0401c0c0784604280303601c48403010288540d41c41440290300e42c418611001c0d035450007401e211448960a10f1800c120744500b030303007400b60030301400da00041c1d0554000001c100e1441c03451f4204120144082e80e51680581c1d03515000e182d640c40881050b42d12800000d410132451609401558220140c220b4984c605a85e43c0c0b600c4c0100c4071076910800140c5c00100b0380480315a0140607032041e48840301031030b508600e0403040540e103070301010303a49480e21141c2c0c14010328043d00c20420b84041d4030500da20030300f04c5d58561415aa1076040545040c0000d010802918540d04007400b5050203694103840c1c0540c0c0da665544d492029402c21103000301215214000040416a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 630142221 1250 630140971 630140981
    0x212070b04090f050c070f200d060b121c081b0706050a061211041d032107030c0f0804020105160f15090f0b04081306081008070b2506 59
    0x405040700241038010b400f43d041c103a031401840f001c082c0d8000d2111801240854003001c0c2c14907407103103800d46040e0041c4541640080070300c0400e5000045900307480c042001c254056003544400315480250b49070020442c644e42c8144e00d42500c02c1d03600400000c0810350041c5406038101540741180030052006084104454015003015680784d0b41303d0050000c84403c0384100c00c05880c01590004e660110f03906e50002c90006044d400f4011a500c000380b4a200b920a404884980c0f2004240c075500d41000440101c0d1201100c82c01c00d0600e0310002013120b0501074429410a2440307610303850010300210b43c1c29500010010401da06000f820402c1141540340f004070040400d208039164004003025040603402a20010015141d99242101440210328071460b80300c0a544c1c0008600c101d580d071440d1041140c001c00d03140510101038900c01041c4a43c0065203107100d0b440b5201c4031203041e903a6030744a035580d5646200306080c1c4201040200007202c50a10498210690425005040e00541d603400003211 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 630143471 1250 630142221 630142229
    0x20a0b0c031f0b0f0702030c06070c030c05030303070801031b1a121b1e0f031806070215130614130c06020607080c0d1416091e030212070b04 62
    0x18400104000070300064005042c041c0c00d0040c180c0d0b250604180c3d0702d40e124400c0020324149004045045421941e0801060000c14009048651500c0311440c228800c6010346c04111040045410040381c07905000003502d1059803140e070f911f90241d1a548490754940c1c40c0d40e100c01811450048049410460306842044c114080010345070342d10b4010b2903d821200c07003d0702401501807071645101d60002d0340010341c1c140d00c804d130070603c0c401c02c550040c4640d244154003c200884801204000c0d18031254181e5107069603003001034420b1a0703a8014126105c3d00c3c8500c444980c1182d54020907010fa4030200e4400c10140f0807140045c005085811810591600302d418a1200141c400e0441c10444c10002c42401054503000503d010300300000041c0c820b00c00280402c000d1740c0049402e1101a0303007030300320012502d0014007000850034140d505a0b140800c0317030f0001c40418020b80002900f40390541c4e07465244560900c0b001d2440b8110350070484e0341884003c00100030f03c5800000702d50781040d000240020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 630144721 1250 630143471 630143491
    0x906040f09021519021203010603150815190b0a030b0601030b030604110a1211271915061b1b06020d02010c05030f1f081603051b03030d020307020a0b 66
    0x24076a038224400ea5401301d042d000e402c54100400c21281a184c240c00e507810b40d40346003008980b1094480c03425908101542c413104440c46501408440445c50100d8980600051130120425904d400d0030001602c14140016810004e00d80381000414003420800350401414034001c100340c20300c40000391078a0001d65042e540140068000a081c0c504080d01c58010841c6022030800b4910680b9038500310340486407500e01581c00320389280d1014140312001c0708a0564101d400a0710305041c80348030810f00a469150880701d01c0c04812845000ba1050340100300d800c190380d4a2030000380c2d03001e41601d07000340810440d04a8510101c1c4e0382001e401c0304d11000605526401001c140030038140c000d080d10300c42e95000050210030418047c04101070348603164442d042c80184002240d800c0c00c4402055a40d900c1703802c260041800c04081c0c110407500d0a400c69000b802115002c1c06550180ba2005007254501945a402006988510445500070710b9001344540160780780c0380096168005130f00c0c000c507181044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 630145971 1250 630144721 630144727
    0xb130506031905060a0b0d021807050403080d050601030e0c24040f0810051312050c120a05070606080111070b04060e070603051f0b2b0903090305060f04020906040f090215 75
    0x3d40305c9640300e1003911031011280300813800c840740c01280a4124881e04154030181c10000511201d0240084600031070b03100e05801c1da03900c40a034414002740001c0d540240001e0820080560511000a05822404009080c0306d18031301c4d840002000c08091055550080d1014840060203680700e450200082007800050411003107843d5042c0d04546008142c0403442c040c40b000200400e2802c188404c19904608200c0d03591401d10014a00c0c4c6182d240d91030741c82046c0042d480825a5000018080062041106020894440300e8441c2a03035503d00c2040c0e1404000c1c4882004900410001908180074103c006550100303540c000f801c03c200c82d00328a004c69100e00c24060070250000003182c04449030003091310402d0601200003040c0c805d582d40d0004003038400224850101d00c40c0e02040420303071440f41c10404103440780740141c1000342c0361000352482d0181500041d18201e01c00041480b86038002c0140c0e000d48d8465040200034685036000c4000e40c2d0f5160720000040c0c68030b291001400b000e07030f00ba082e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 630147221 1250 630145971 630145981
    0x111070b030a24060302191d0409030513081c050c0c04091a0411120d02101109040e1e06221406070305060307050a050f040e0a0203060a090b0a0b13050603190506 71
    0x2007171110015841d000c001c3c01c10648a1900680c252486048000322740205004400341801c444902980c44201d0540841d46000109103074002811640c564001501000500b10300405540b503015503c0006800d070440254200245000e03444001ea07039108542a4002c04c010408181111004980c00c64200c517282540311024a014403200001220110082600c1410020000c2d00c030300c405005517000d29100c0d043c0100d038107004d01c213441d020100a07004100b000307540005130313568003400e003101184440c2d00907051700603200210710f480c80380b50540343c035a00404000c800410400041074060f1280b00750501c02002c00304c41030213291b0080c08a0741d0085200c0c100001018103040056200d640f080d40003050030815921400300c0c0c402079050441d400103010350308021450a00855130402135060043d2020412005950b901108042d4040d9030703401d004c0e6941051400444040c290312540c4080c06696a04035182d6540040d42d010074050b06986072094030340e098600800801c0e2080f00c640e004001081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 630148471 1250 630147221 630147247
    0x8011a0c071503270318051002030414011b0b060103062d14010e0607020f040e1f2c07050402040b0a080f04020114031803070b04020111070b030a24060302 68
    0x5000e0b8a040703007841c1604c1c180001c0800d50309190360000f014001c2280c020060740c02904201402000d02070309a00c01221010002501c2c2d90003801500300020b1980b4046005520801075a00c001a0400e034000c00030a00d0b1f100c51209038002800b10303040644070800401c41c0f4028541d0620500440007160071900c00d44203510320081401e42042c42c19098060b6480c5031070307074040c4100c00303400811b8a80680da2034440c00440c11040d105143c00b500541492002583c09074006040c2110010b00c00342082c0484c041840441990b04600003a002d2160509d03e0f202e40e105080742c0301e026021208100c82c0420740e50300208007030381c0040c4c0c0001500a80440c1c3c162045070098245944000f00d4030718207000d4a441c0d0f0019088040c120010b454120000c0002140ea94160301100840403c0300c003201c0d2192894a070071040402c04a07412130001d0701403030a00814030700009207002a00e40018015003507a17505841c240007071000c000c0b007040070720240c40340d8007011070080d941e0f2000d0007041d50051fa50b4803442d0060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 630149721 1250 630148471 630148481
    0x3130f030201270b1b070f0e0a05040506150609090c0301051201020c0a0311120d06090e0303041101030f180501142401051324030b1008011a0c071503 66
    0x2080e8500a59403100440520703040340d05031040f5071869a01d421031120100071005c00140556007901c00e240700814003c035001d80090845060301c00948580c2c3d1030b120024240ca0099038003e00a81c0408045a03444a000c541e80102c41d074042e040078100b4030b01400082000320292143c410f61600040140700f40d048c010621114030704008025481c1206038480c440c0d480220400140403c41d100c44603140345181802004410502040c3d00d60b1070b05046100c040040690340300c1d101d0154548011a001d40d44044190792155402120001c51100d6110054001e007146241d02c92201c0c0c0d407071200031000d42d40c00d00100c61441c007131000021340002000d82c520001c0e8000d00850201c99000c100c4c25200a00c0c0c06203c03001c403000307290003900c400300c40c4103080c5c01c14819009003c100040592541165005041c412921003041c0c1d0203002e20901d92040c008905011040c520006950a0040c0903402d50700304071040c084942c01c01c040c40c1445081c0e045091020581120708580e0030701c0010710005a1500038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 630150971 1250 630149721 630149747
    0x30c0210030c0f03200a03060315150f0b030619080106060c1103070315020a050405040203091f060501050906090f1c0501050601020c0105070b190c0509150301080601060c0503130f030201 82
    0x400c11485c6104c003050740f0301c010038445070510b40200183c0d01c910030780700746c2000000f154000c819039005051202c1f502c024050900020000d1029904000780c2191501d03801030031541e040021a15603250b0348207111015440c110080c0c2c0c00c1b0802c40d40050304c01000d10a510042419580354180c1d030700310349840361041591581c1c03580f182d404050180007141e040c1502e08040082070a006a8490f68402c080e241402a0340c031469000744080200144e240c3c010030400900301011070500c2d4464420a107000c111000d60117028009103052080a8060070290b00401e2109802800740d031121a08000080d03000c0417120f03104980c014040b0241b820440240500394020009002801021380301800081160090310400b40105800a0124a0314a000140d210401038540e00034403014207090b0010380b1607484640c4084c018440e0088103016071000e00305613416524802c1c05031075240d1038010b0403241d07020640d0050f20039010405c02001c02e10100e800c0040240307071607011242c010745540000740040c030b50400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 630152221 1250 630150971 630150977
    0x313050607300e0d0302030f030403110a030e1216091e02071a010b1204030305130c09061e050307030b0403050d0509011a040207050c01031d010914120a09050607030c0210030c0f 78
    0x44d03030b000203402000345c4050130f007502c100a850b5901c41c103040360350310025040704031031713014580b0304905050f1700640301c50f646201070303500b800c0c2402004800c540d1900f46050b400b107410f80c0d0000034404500e5940202c500c00c10b0072070f881c040e15000d0a00d00000c0781d21005017161540d407544c08240d61501074003032050041003824000c4d428084024105002000001c10041c1010340c0c0c1e40024580d5041001503160841c3c0003840a445c03d0348460704034000b0b00d04d90044c440c03000b02403a000701100d00c06c550400b00707540300500500719252442d41c4800d0981d0018004405010701800b182030b01803414403549201d03d0f51580007140e044003441c48407601c0c42e0a2860640501d004101402c04100c1c00074042c90b110200b8600068000c4d0f00e10200703804450392602070b030019424a0000c41c1802090341e007201c41c1d0020742054551218540190580e644501c601100c0818400c1808009602e420341c041c196481c0641001603c40000f5400500454003100d201c4000c00c1e600e008040d20964090746a5400f185a42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 630153471 1250 630152221 630152239
    0x140111030f0301050a0806010b03060409020604180903030b1504030f05010b10030b10080403051b2508010b0d02030d050c071d0f1f050f04020903070602060103140313050607300e 78
    0x74110027041e200c010495030185031100021803c54440790103c500401f140b031510582c20305452150310140202030001d0300000e0914505260520304091800c8240c8a11010145094556a180d0055500910b010b0f00c565686443c05099522030110f40310b6602c0003039400142d600c2101c000c00455441c20030309942044170301c104110020317411100f200c880d100300490031800c0719103007030086207020840441d81c90b80144003180000c04006040004040d110090000e204440c0c0324414404000748a4501a41c0341c6c1c098070004480c903000b04c00a080c960b103904142d401282c0ca8440a2100c0316041c2405144401d54104107c0110920f0450301d410aa04c203403d40c80c990412103d1a00424690007075510860003061912266560b660454001000190130b541c10250b036a003000e13494001c24401590030452120f08030200d11400f0040b551400e40d00f0b02c8512000d8148401c0c00031316003002078115102c1d81c9201141101000700005850705128656240740815120b00005251504251140703005032808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 630154721 1250 630153471 630153479
    0x304060e010c0501150b090301050c030408030402060706140f040317010312031a0406080a03110d1e0e13021b0102040b0421080408031b16140111030f0301050a080601 73
    0x10540c0c2054039000d10740203030007140c2410001c4c0108448000006080802c500000e4034010040281001c040114005c1120340d50710764a4061520017110f00074034002c3d003040020300515000014014140c011140000c001545031880034240c0d406803643e40c0d80940e06410042011350040d00e5295004414540380e09d29407541d90f400341d140c02d481142a05154440c01a5051003129056510515a0040c403d01c40785540f07041c6907850b1201c0040581c00030b4800601803918040028600f5200c00280c0e44820080101048102400ca891100c3c441000301328582c03a40580c0d07402e00e21040c4003183e03210060351381c1056000d01e174501800c0c8110313203203d900510040200450f82c10a5504884030310501c06003030300b003855030720004410b0300c50010300070030001c5404100d0404c0000030300350706030b00300011910a0001004465442003441010320442c10b00500900080b0740e0b80b149502c0c540c0060404060b840780d403030500703400c1d50072403007042410324000b100405c13981c40c209240c00010704103000504429410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 630155971 1250 630154721 630154727
    0x9100f0b0a051e0d14060601050406090e10180501080d0f02152d07081023040e151e07020303130c0b04082b0903021203090901080d11030406 62
    0x5120710351280844102200c3c015120110a403403e4100600c1c458100705680740030400d034151700c91001c00c54030803080010205d50140c0100c1e03041d240c594032a02059460403282e00c00c0b980006068004211503003500041c1d98105080c9064510b00300140400d9643c10000d2140c03a100c5040500c004000c511400b101000d90085009011000d415039215a942e49451b07940302c1860380540200901084c03201286e441030042c0e10400e005403003542c0c840b89140c1f42c03074901104521590143c1801c11200c545002d580c181216a40c10031500b0180c00403030724041441040381007240d500d9801c2104010384c4100b00a0700c00d40c5031038081d1040816030204503400c013124002d590b400010305a140001540910501340305401c200d80005014013100555120389400c0d40c592a80b110707199940740c08070704c4240c1d0b4408a01d40103140e40c661030329aa6a1640740c5c42c580801140c41021000d0b00000e000c10406824a40c6554054502030070b003800c024000040030f104000c00310716440c65410b80540041c00203104803a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 630157221 1250 630155971 630155989
    0x1050c070b09070b0c030c01050601020c13050717010807030302010e030c06180a0c03030f110c03031c060b0a0509031507091403152a0301080601030f170309100f0b 72
    0x18005100c00746581d21040307082e29140883c3c010750440040442d40740844940000241480301a210007800552203c2005a0341c1d01080f416981c0d002001008900c201c80d0a6441181d0140d001e1a101003d1044004850903910080e000300e107040d0000d0b1018800e05809024920002c0300c017000030b41c03070003110351100c0740c40d82400303492081c0d17080c0c844400031854102001181d051542003454046003035a00c0c03601030584407500120302e000c2404041241102034003c280c240d4442d0001d00518580f01c0c6484d51b061079141c1880032100c641c1ea40c0e080c08540b0510388006800307140000d403160f580da1840c0004061401c00c80c8000310312541e4180042007550380d03200e1030700300490300705c4e100032203c0e03240000000f810142c1c84c0026481d801041400c01000b1042c200002d102098240c82c50449481721504070501444240500c9549500540042002a0409204541181c02911003c03075503900304450700695441521300840f56400650b80010307240d040c0c4120403944504020400c204144103021881c1d10f6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 630158471 1250 630157221 630157223
    0x150c03020918190209060f0d061d28090c090903021228210b0a0503121b0307020603090d0806040605180601020f01180c090b03060a15030209190e01050c07 68
    0x50b00405d0402161303c81c0402c0d1280038074116202c0d9100e0b4203003610040100114072403041107404200c84803100c41c5001c0c0d010f0713000710100010020002c50107840e16084058504032443c5155450040300003064075505003c018025011011075501c00505000b403400320682c50700f000307100040003200000c0c0788100a101703480a4800701e861b480c0740c02c140e0a544c003400803c00003a001020004c00d660000c0c0950000c2e4850030212440d50100f0b1702c8205041e510001c519152103511820003071994103045008480c0d585020300e40440c0d05d4844030341e021030010307001507039802c02c290320820b940c4134041e412030303002a40441705030780c20401c580c50040041c1d0300d00780b5404036000f00c0e001400482c3c0e06034030a010607a19030000341e000303000e609207400f02d111446801440c140d4a900c551000420742c41c4d01802842001e0000900502c41e5868000404004113030101c007075031100710440000401a16100c003aa80f0908014510084004412441106450104840d08456403408042200c101d444001341c400781 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 630159721 1250 630158471 630158521
    0x60112090f02061602040f110a0e1309030f091a0306190915050103050915010303082503050402040c020c130b120a2301110307030207150c03020918 65
    0x3400ea401c00290002403040069040900007030f464003200300e950f984010302482518104844030002107100708407805200c940408200130805002c4151282010303091464004012401e41845881030000f1103103c13480072804194140795034454513400a60708801040700c51501603081c520700301003044a1000600c580d1050740d50710950790724000700025020140012079000c12441840c0c165a100c581280e205050020781881c0003d8000000440c00011a030b100001c2c954841c1d095039015941c0020040007001d8500080071082c2d840c2081c07509400740d50a09403070024032420103006010a03503550123041c006560000c007480400e51a203105004100361582c4c40043c2484009001840302d820140318412140304048826040c041040e007000709600c0e004141201e54000c1c06292800e0b11050304030661103034414400514828040e400a180d90340c41009110a04408038034450b0861300c80b8503280c0300182d0b011031161030900344034100c295030b07141503800b540940c40c00103c070101c4003145103a09841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 630160971 1250 630159721 630159731
    0x80303100306020a11011401090f1a12100203040c0f0605031b0901020c04020c2b05030403080601030e0d0206090709200c0f0304120209060a060c0b041b1e050603060112 74
    0x1003441a441c10a1100b101d1009100c0e00e02007c2829041100a0151040007407600300c940d08040c8440c491650388811810710074014079a40c401f00a92101c0d11107e410140c040c9218180300e030107440c801548214031500880c0d000318181691018810942c0d04000103000d0f04000b8032100740e803481c048811305c000c41034240703a0314048100101e06020000c1c108070342090001ca883c659010b000b08a20f00c0c1402c0c0c00112101a10345480b0440c035200c1d03c0141407010402c01c10214001c284036818880c0d2221060401203030403620600342500d401c041703050110040e00b190341448103910050141c0c80085c291544248440303168503a05104010200c1c0d19900c01d0700300042c158141040c14070078201031030001c0c8292901c0356a0358090039402020b81c1401c0b4803824400000403110700d051500340003076620396034901c004296241c0d00e50a00c641d02400c10b071104401551010491048040528090004000d0101c40705840400b412405820350304424440c2c00c040c010031481c0d982c4400c0340c80d100000d107000030031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 630162221 1250 630160971 630160987
    0xd0f06150e0f040f080c0d0509100923041104030b1b34080a02060406060806130602031005060301080d0e0904081c020d02040b0406120603111009090e070f08030310030602 75
    0x82c4504000c0003604d0282d41f00400089070040098107080100382d50110300c0700804d1404941052060084c5036800c00d01c0c3d490350091410100c41001240409800041ca4556003400010141c204c0d07402102e50030352003410051040c40300c011185038250443d50a9040030560f0600c401c0b1094100312400c000c42c0030f5024804024180c5100ca1880e0741c0007007481f541c511410700300a40780c0c041102d080d01d81c10f06050000034400d10000c1c070306108a0380b9142c05d0030391901542d10b60f0080d620192507688412028400400c00d90760340f4001b54000c040741401068403c190290241c501c0207560100b51045280d541040f020810715012a000c941a8003110ba00c113207035002d0001c9c003e004000742c2103282840801c001c20681009070041c010703207600351902d000c082d900e0b13082c660545d551400000c192100c8100508010705252640714540621400c2152841307449800d080c085409982113400140d10044007000003070745865403e8041c141d541e0280d0700d14076105140102c0b0700c0180c80004d1a060380003a5030300c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 630163471 1250 630162221 630162233
    0x1005010b0d110f030412020f0d0813030302120703050105010e1c02040c1206060203070614070e1207030204050408030402100914010518090405010c02010b0301060f03020f0d0f06150e0f040f 83
    0x25000d15160f80c01030f840c0d0800d410310407070510840c101d000240c4680c4521403900392000503010f0603050580d41d440d40640e107642070416540800317a000c800303240d000e101520b1526030904401d8440c00450380c0002d40b5616000c00108107811001005006021078641d5058410400310300a000940580d000b242a6000f80d408440340a0380440c1c00d40001e1800402241c1d1650100c000c025060007018180107038482c00783c4e6084200d400f50303074102c042007502ca0340c0565800e1052160703d8541e205829151170a0f80c1e9008542900d400311411145840300100700821464103400d4507407452070501c1d0405543e824100c4004104280c041c0d40d505005000ca002034072401441003030200241c010f40010a07605080c5489070103443c100d5400c00155081c0303c42c4200600b8140319400c11100d19042d03101d1403918607000d0110302481c8214158101c0104149540480c005440c9019828440c8000068034900318503041c80945868101100307070101c100901041c1d500080780e068001d5040380000256140130300e004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 630164721 1250 630163471 630163477
    0xf16080c103515010c110102010e070b041a030c07150b040c1d1f200111070c08190816050d200309011403190f0c021005010b0d11 57
    0x240351010080000b0008554044075204a091041c1405811a103981c008034070305602065086000400c1c02c51035101045840110100340e01040c000000c4034a0111101800e0206a40000080c03010000d0304001d81c0780300940c90490500c250f80c141e400d41c201102c00c14820f20941001802c9030106601c010125070b5103a200040c0020001e004018a8114440c058540d48210030b04036492145807080701800d0401c50703002610340244040010b005101c410b401e42d800f0740740c2007072095480340001090b140805d003485200004ea010000c101d44421041c034140341003201541282401c1d820143d40c14200880f11a0600076040d80901281d4440c06075504400c030601d0b10a0f4083c20510504105210786500001600038005104017140c0012140004d10313941e91040ca41100e000a1201c0c201c540300540c05005107030403191905940300343e445081000d905841c01c144400824982da41000400c55404105100c9404011802480558904103034100d42d4040d146d003c00030141c6500c400c1400d03621072811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 630165971 1250 630164721 630164747
    0x21c0e10030f060e150307030b0718030f1103060c040f060c0819030209180411090601180303030f0501121a0a0605040e010e0d050c030421050d020f16080c10 69
    0x4025071542c66a41c0c4d6007145003681d82c02040f40d00c0d0202e141c402d05003ca40001502e4001d8054203194540803011070300c62341404565411101c01e4080440040d20400070401c2c2917015080445010022a00701414040050032028160600304400c00c820511215000300b01d030700701d081801800e220303410400824464000e100f039030080084415030200d81c0550203024034640a0340c0314522040e41310103240704c00c4800e4070094032081d4107030fa01940c180b90550525500c40030626120740000707841c0d816100040b1840d00110082a100e0018002d10401032060900400810300d50720700501c03141e16034696030803550039405448003111001034034595060b006140201400780040001c1c000c40c017041c600a185a4a070199030780a8000c5c0740d0040fa00c601d05441d00850128061894503180091540c8154010405130840e000c0110380080402c500344400392804000750041d082c0483c0300e1100a080c0801800320b56010709440000340010324000070403c0d261102034800306041701d00800107451800300101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 630167221 1250 630165971 630166001
    0x50d03090806072a021e040b13091b0302090403031d1204081207020916020106050409030513060f05040902090a0306060f0e0708040206030a0f1b020d021c0e1003 71
    0x1061200d42da500100000c40942e034054007031411302504a0041c815400401c1c0a5405500102030b804a044142540210f145c8014800a0059081808141142c00508060480d2035031039880900b4801107600095240503e0058031806509690029510b00c1014101500309961203489555402c18801e20780745d03051401e001c0781e5882c2c8441d40c88524981c840d0041d044075014006403c8255001003094401881e4010056000340d9181c0c4c203181c03000f41c1d41c0a030a40c2159281c5e0400209521584540000d4034000e80d20f19030356000d000462480b8644d140c0c010010007001c0d22054210300c0c1c0c420305a42c00c0c0c85410401594508044001620400991b000a00050703c0c19000145c11180c49100030101c42d01c05000c031155503036286c02a60000380840d8065002141003001400e0445203a0015082c980b0841c00040c2d02c64426003150070044400c0d02e1407015078450380c68584103e03010019417030190050160f01039080d000107801003090381814201402a008c462120154900a40140c400401100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 630168471 1250 630167221 630167233
    0x40f0203060c04030c1a0f07050a060515102c01020a0c080a0b09120d090203030d090b01050102010b09060307030b040201050f0703030b0a05040216030e120601030b0f0c07050601050d030908 83
    0x2040b42000c1c0e00c1484100d40207200001d00050441618001009a0004100c100d06000240d04560700c82c4e481420200e0b0700b40513400b034010006003684a00c0340141440703c1120301e61100c05041c018189034810640c000d1182c200481c54542841819080328420066607160312000c0400050345001d040b8000200104440c1d01c0214100c840022001080b0307001d40e441c2c0703003039842d1090300d25241e90b030440700c40d04042000c10043c0c050394050f4008441041c409402c4a241000d01d059000071644901e070125105202c0c080108119a03090043c200c480c00116998605418a140020f07078407040c0b480000c00c040c0b07141001030291b80c055015034200c881ea1a15065440c40f407403070010006c0000c81e03405031040081380c0d0082002c1c2003a1080e200301c0c1c078510f007a55040c110983c50503070306410b02d03045a40e0b011079200340035a022a41400590f000318840c031005e074040e0400045020030203100404818064005005181c04030710001802411114207440400c0f10031300900f4111601a690f42103a0320600c661 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 630169721 1250 630168471 630168481
    0x30315030807150c11060c030c0c0102160201020f15040b0601020c10090f0e090618161706010b16080c1216051002130902030a0e0d020a1a011a03040f020306 69
    0x240e400305441914004104001104842c0c2a200417079440401d2400b544140009804040100003c40e0401c10903158070703003080084243c01e03081e40c5c004051480c84820600e028006c40d601004802071021016018000c44450302d002070300c40210003413001c2d01480091000c2080769009108100c541900500154500c42c02800c018090070b03898820754003942104940044c0700906d584100c0e00074501c02c4d014110b1612409030078040c1141640c0d4100b490701410407400b0090250007814001450302d410017030103800801c000282401c0059200340340d4401d042002d40d902c206282e004807140c5a0209610b07480300004141c8900d0030880a10b04807000c200002d1101ea000003d464081304c403807091302241c080038000050b4801f64014118010054094941d09210b140303019005164000482c61002982503851030801707141c162191103900c05a04004101d0703048c080c0410500345078500c0344840ea100755241c00340603068004040b0103001445004000f090030480c600c20485881c0b03400a084030060f00306 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 630170971 1250 630169721 630169733
    0x90307080f30070311090d03022e050117030a0f020c04050a020d050601020a021e010c0609030306170c06030a09080702030d0e040b0406150804020303120c1b0105060904030315030807 80
    0x4a11001e4002d42420780001d06403a12174001c0c0c080c3e88034001030b4103061100c0803052001820746a48200c00b940507418030325548440301c1c04407012080fa0303110540d07003070700c24080c0d45811584180c010b40c560801200c0c2c403040880d4000700325100d00019162820701c000030400100d0402680f4001d07140d01c1814036007840380c41d8405030094000b444900608010903100c00b001aa5200c600d40340003504440f4585503c0d03030803402d036240000300300b04c181440c90715414507a07100f4080300c0c0005030440109598110502c015520300d900c400d09450ac2100030035208000c480080c0240c0401804500840e0b16000c881e410080c0040640f6001540038045603400303003040074050800100104514003c501e80140c400c2c25241c98090041280c4010802105800e002c0d6002c54051100070700a030b07090b220070810741d00501c0b540c103403551040f82d1204144e0380b10031400309915451110049a14040ea040c40e050000e90760301c407101250040c0c2e01d4180000c0303244000d619180a000d11fa44040d00100000c035040c024089 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 630172221 1250 630170971 630171037
    0xd03170a0902100804030e04110f21161d06040314010c0f05090d0f05011b030e060105060a1205180a05031b01020f0703050d060f1203080906090307080f 67
    0xb1085070301103240300c103000c8115410082281d01400041e80d1450040d00c2e030030664404d025055000e20414034204140c104101254454803506802e85003d1000d44540b1a03203803283c541220440200c8075811818010082c64420070a121401c40c94800d541e441240d40e50908803802594019203000449214401e00e90003888480b102c5d03000300701c0320f40200c0000c03031140d401c6624045000b84a02d60900783d0b034503000c0800050a0741118559a1540300640c00c8182913104c201c0c085040e0340100c3d08200c03c014050401070f0680c0194060041400001680c9410228000c0300515071480083c0c9039075031920002810b18510442c076620b008202c50a03040c800c010008102c1d00c00807018844058101100c00c9080307108001402d810004103112040c0000c0c0300700014001c2101e140c0000c030344141c951043e400c8200c515413084030003003025012101010303005803119500248100152110303140107210152244a0800010608940011050820400d000995038004440a40312110030854202026402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 630173471 1250 630172221 630172223
    0x703020703020f0c0102120c030f0c03041811030610021608010b1207030c0b030a06050306010e040516061b0201050c010c260105010c030e041b05032d060d03170a09 72
    0x4050340b43c842400000000307910509071010f9004080c00454034042d100f16401036201038542e13010420148001e100040043c04454000c0c0c03020359a00c52804101d51081988669070011690030140c0550803000502c00780d90f480482521800301884480c1000c906240007500303000c5034844038000101d44154158441c1e007400700159035605181800c650381ca95115124400244124543e81c01844603000410186030401c60814000c14070607120030001c2d00b07001d0260081c1451201d15010001806020815640c0c03101d1100581e4003003e00f0604020030345280c0c958600081501c401c180c46c1164442d82c200c2e101340101c00020003c16109010060882550241c41d41441041c040e0200e0301c20000c00e041812a0b07016156180d411801ccd540c19281c1101ca5241180d100e40c0e560071404409a0803019105880c0745655902c5d03036894400361041c1509280300322040004502103084034119098018140c100c08202d81400008085250490308400003c1210b03401d0380f4124240f09404c040d50f080403000e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 630174721 1250 630173471 630173473
    0x30609130611130f180b0d0c12032c0609060c03030406090506060102030f041404110c151305101805070308040914060616050f0d050909010e01032d0b070302070302 72
    0x4503075403807401ca0401302c2c5014444030764101d41a0001100d813254806a4007400140ca84c05000055450703074503001c180c65200301d05140424107078104040d4444c12102d2590012814200291907040740c3c25085901d50040b503009410004d4010220381e100400d41e08001040b8040760358030300c0c1034505113000d464030312001c1381e0600c40c5a0101c1e90710342c00401600d5042890250719400c0c1468890420b00908000980035045581d0361090350902c020311000f0300326981c01c0c000420074000802d40c200f420386402010589d94410300241c02c2c1c0020000f041c0c0b9480c91210100110308050019840100c5048500d401041d600c1001800008c008c0160042d000f11400c40e036081100c4400c14600c40090042101c0c9a90311200c204000ea443d6203904259058042c003580c00c964080407488100c6161245a00300d80000c12004a2580034918145540a000d42400300a51060f540b43d03580b001d000c142d5070160520010305009043d90218503000c959040d00da0411940081820040e9000c0c0095001580039801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 630175971 1250 630174721 630174757
    0x3603050f0f0114041e02060c0c0109050a06020706080a0608070303120c090e070c0309170109060f0b0f12010b030706050c0c04051501140c0d02010212070311030609130611 75
    0x8040d042c8141e0303140d80e5200a441d07410b5900d541e10642c0144601c41070550807106001c1140141c0c51f4507010b0040f90b4400c80041070032100c50000500042080c0d480b1901c1500758210070f012280d40410f8500442d401810300c06800e0715a1811103020305450303009803071075104941000003490392003202c410b68041c0d810010000000d4a980807140b588481c007804203641e0b82d00c004503118902c50703407020042074003901d8007010301915418024000300c0d25480c0012a42c0d110a1101e060050500c110114031202d0b08c0204482c00818003c204080e00750850f041c4501403015800d007040c01c1c00e4200240c400001801d8a1a16440d50b0003d071a940109014040c18401e6025000083c240351054a01401d1038031081d503030324a141001112400b01c0c0301101c00381f80c0003e0100c014500b1042220b1101300b81d241d000903860351000142508050b0b8003c140300c08041c144100040e801240e101202c1d0846015030342c403202c40d81c8429070074024904e81c1030b00030304143c075000c10585081c4030b4a010381202600400040b074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 630177221 1250 630175971 630175993
    0x5130c02190f02091e010e0c0c07230102060103051e120301080a060b0d0209060f01051317240a02160b040b01090f0c0210020d1103090607090b0a3603050f 68
    0x200c815002c80c0c0406030545c01c014031a02c104141c80395480f074222a002450018a00703107445c14108603a2240c0d41901704800c0711003065015288543d00e24200b03100401d501d40c075584a003a500c0c00581c4c548558940c00d0911280003440c140300c15007103442400517582d83c95968080c0e40d03594441c5c2e650161003491400320950140d19045011840854005010040c0c980755142008840018844220305201c2d042040b078102000b80c440c440f0003442d4988020581d05031050b0540d00304043d070320f18611050f012003130324140000b1286100b9000664843c0040e1102d82001481c9030b0300c122404003078110300040c02080104100004018142c948180c418454903600f00c1d8a070065452000c5900003607000b2903a045580b107001d5010348001017054201050045001c00e174064071f6482075031400c0340350704508200400c064100c0440401041e10f0800140340c071140e1100100341c1018052681e4040e1401c4280c02d00030390150030381d03202c1e8481a002d01c80c034440d901e10340961380740001c451120082c0518a01c050f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 630178471 1250 630177221 630177241
    0xa0503030a05060612060f0604090c0302070b09070503071a040e090d0905030c0604120602070c0b030717010b04030206030414120d0605060412080304030507060c0302180a05130c02190f0209 83
    0x540300d41da55148005c80c540702c500402004101c0580c40d190001020310001446c00080d000d032240c90300f03a5031001a6210103d0405800e621402042000360b684450003c00441d2030010351041242e00220001800c045150025506407007541c2c002c60b42c2030214024440303d0358021420780c40d12065511102d088035903030000c0c542c5403450354209c140d01c044107110030010610508007030346100e44600c0c0018982000e690391a400304025030040d024070540070040258541d000000c000041c2c1c00b25206804540c940003201d02d8034071a41c00002e0003510040003080c00c00c1043c002143d4000181c005407403442050f0f001c0d281c0c054000c0740007200c04c1424028000313642d040401c111000c1d5044000e608600c10030548441c1020307403002c0d104a00304103003041030201145451181c0303501103406a07009a541c20010310415820303082e003600c0d0761268481709800c0116a9503d032812501105507500856140484036040e810844100094031814a00841800410070010080081c07203108840c0c1c400e40d9110103141c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 630179721 1250 630178471 630178477
    0x2907021e1206040b1906050301020d0b090c0301031e031701030308060a1d07030c091e1d06030d030515120706091707090f0204091407020d1412070903050a0503030a050606 75
    0xe0850045640810505c1d48a04902c0603021124000403030016600c0010a0880c3d1282d03044c500c0d100e9a42c03500c840b840c03600c110502e411240721440d079815035046456a4a036451144049000202d040301554209030040c1c105054805103202462110f41c0d503070401512034a011103580d4411a91810b012401c4242e03244154441440c5580032006070707559100036001021003040c0d01090000e002c40002d10f2040e943d07025403401c4c9480380c0702c8400c50300d0828882c0e16500402c1c0318070759043c402030400440340c81c000b03102c040301d03101890045015200c1041d0032901e21385090702c03a9000000030140c0140090f00088100440380b19559400038141d542003181040d91280b245035030b95401c00541040b4a60054100c4800c00e1741e24900185410342e1a000c107400c440700400d034500705004000800c440b090301400101600710305420000b007041441d40c0705881c0c91151a00404990344c40f100411516031084071003801440d8407004070342000486040c8650b0f41c0d0400c444004038182494000f40460800c5020303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630180971 1250 630179721 630179723
    0x30e06090a0501051f0b0d02070c080d02010c030c080417130b030f061c06020d0213080f010c26420a06090b0904090813050301152907021e120604 64
    0x1700001c030b14240031000d00c1a40c44242c00d1070006809120540104024181410052403110001c11020740244c00c06400e440c0d4203000201030515128a120a05400040d00380e4002e078000c0180c1c078441402c0200e07041c580a0310180719840405880c01080780000000114050406080800040d60700c01d41006500d594000690703000c81410f01d04e0b01c002440d107402406c01405c2c03400c005803c2114200b980940c2c0907840e403059481c0d43c8601804090701c0401c0c030803c1d49440041c60185603003114455821202428400108251000b060006900030107800c042c0c0c000226184011017082c080b0011200b4104628110030b8005440361600580d910f00b0900030411115141c4032014510b1a114507041190000c9040a41240d12840b0201c0010007841c02400000f04249609850718201028942190003078420204200c1b0190343c1401007901403c0040d0405040b009080c0e06580c0300380729020300703009031100290412003c408510064145040b454902c441c00d45640361104a1600100d41e10081654 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630182221 1250 630180971 630181021
    0x3030c071205070510050a0f0e0f013006050a09050f1815010303030f0b01020102070c0314121219051510170c0307020f070e0105090601030e06090a050105 68
    0x14040012086548441d80918090380c1511a11940d07080070a45016038103501038002140080c1480c80150021039080f1030294900d806520324011501080f01003001003a0503040c4900483c54a884d4819484c46419000080310320040f000c9a034102c09020300304601415108a403c0302d00800c041342c680c441c41e40f080a1080401700c2d20b0b280e001d208605402d07081c440c80d10030302588401d8002c3e03e400b000b081c0d00951003650001801e281030200c01040b42d0107540034904690042280d0004a00140020310940c2d400c80000406860044c1615240c050131948608070620046003104c03412000381d8440d8070600d4400a80100401d1400e00c01c1c086881c2111400b01c40d1821841140e400c0c1010301d503c4001c0303906030800c151451401c01c620040c030340c000c40f0443c1500800104210380c442c1c0c1032000c880c290f51800c2c000c0003102d041c4400702c070b2070250500406010300e00990000b00700360b200750003031400c82d120002079036201c0c104190700c2521448140005d464540c03c1c0800300d030003044440c80c01020070b0541c43d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630183471 1250 630182221 630182233
    0x60309060a051308071209080a080f130e01120c060c1a101d040212060403050d020f07080c0c040606050915030901091e0b0108031905071713030b010503030c 69
    0x14140c10000d11024000c00d40040c3c40703498500004003880001c001080c0544e41d00b49150300c49150080255030250080000d40c0c0046920f080041c1446043c0d4002ca2601c0014030348506144000f1041400390b40d01c1800c01d41628400050841058040c0503001401200c90000c110385418054604a01c1036030024040790600f40300540124400b11800d0f0081c20b1040360b0100f02d5034402c80c058801d448240307010070034043c11050000b10f142c003c080ca280400300c00042c1105140c50303100a010781c010744822940d1250001034003528480360350212942194008022900c1e4102c01106507500e51041c1081c82c0101d01d0032402041580c0107900391801684010000000800402e1101030b440c3c2000d040310b242c035903d40c0ba41100051050080304c1307071080c80e0f116400c001131080c20148051070040c1d02490aa8008000000141203100034024050415050a030743d210554580f41c0c50f204110059020003d40105090792104240052001142e014041c501d4940e40c1350401c240e141d114540700c540c0a64846c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630184721 1250 630183471 630183481
    0x10e1c0f0e03012909010302100c050a080706060315110d0e100f050403021b010903111c0507051003060503060a15150e0907030c0206071107090609060f0506030906 72
    0x900e031910009006880c0401050446030301090a49100f0102005400842024001d10134884119254078071001c40e00406035514580105001c0140b40315110204045000c52100340201004020451503000341c0d09640d4428500b0300343c0060a2900084910003401010b000c0800c0c103901920420301c00740100b05d483d084600101c000280780c00907a5003201e0050001401143e009481000e02010000c0c10100781031401303190080c141050801b20a080b1070f40100c0c114240d0760b1120f41d07401a2544180e014910840d42170005880310050000250310714107400700441003040108101c0c0032148150307444000029151030603001c2d0360b90b0f030265036003561000000941520241d00074070001d0b0404404000c8031910b50751030340da203400380c1e0a02e400443c440c0c07443d007055424114142030703200103207180c02c000d80303140f04c2ea0082d21600c000c0c000310200031303400d01034410004c0140084002411549400c015960f6a6100d8130f003d00b049100306015030041c00d40002c2d550070280c04882c440d1401e4005061141c2c0c1d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630185971 1250 630184721 630184727
    0x8090c0108011535090d080402091b190305060f1f0309080406210e100f0b061b0f0f07180204031e0b01090204080703030518031509010e1c 61
    0xf00440c04020003281440841c2c00454103400101c080b001c1c020705070344150000890001103600034051114070340c80058580340781076000d0704040c0c200b41e045681e03101945450344080d00328400011680554500040c504034824001074040b40c0b0b807405a00d09000b00e65402d0704205414141d003840d140c022030b11102c2000d0341c0c0d400c03254140b48c0c41d038182000201908a0b899100461308203400603030114054008203180000103508000c03940496120500a01c0000d402944c1c0f640005c90070b4100c919107650f0311800d030403444d41203280e2002c006845580c54483d0055146000304c1e0f2002645c01c00c1c000d039102e5001c0c480e00132450610140104004200c1c80e86071140340a80c1c0c0411126043c8a1075003808040000791404020328036003402103258403840001d42c200080303100300684c49941041c0c030401c02040906400f00310501120b402d0305109403901c2d61200540607040c90481c55035894090001186071900d2004000c600444a02008001c0440182c8585990f480981058a041700d000e810260303880388 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630187221 1250 630185971 630185999
    0x60a1503090c080708030705010501150e09060a0512030405120c0d2607080a0e0103060303020c060f160303020a0f020106050f15130e0105120604020d08090604170a0308090c010801 79
    0x1101c0c014140120f03540f1882c1d14100761581c1c20080300b94200060540511000b401481c3c05000e02b41201840d40c202007101900ba01000c658090180d0072000000d030481d17071103a0078200149070240004078403a4045a000c0e440703511902030940309000d1824903036104c08000510024181000c3e1002183c4401515030941d559170400c107040f6480110560b198207414400080d01f9041d104c0c4a500d6200d0301701c8000600b11722070705d1000c0380c1010b24103d0200086035000480744030419007519019540e0032941e047c101749105011003da0b0741d16146a4280805625038000c01342600950749030050003542c01e80403400d80d040da10070715034051b11801400080d46002c8400c2c80940b00240c80b0300d0728014414403142c010200a50181d540342e0302410041095040c900500c8401d444540301801e845c2c030b0558001100201c015401501d064000720302151641c4230a001c5401910b100d10100140008000d940da0b607a50001d01e040303001a001402007030b010240041c1d0561501c4050b156200260300344400d024400f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630188471 1250 630187221 630187223
    0x8040306111e130503030c10052205060a050606070b0105090a020c010e0a05120f0f07020d050a0c05131a010809190305040504050106180b0a210e06060a150309 70
    0x1400030040b195819058407070302c0c0040e45140c1c000395140d0700c100d100c0c21401011640585d0181c0c108020901d103180d804200303481000070f2400001000c0d00c170f00040d40ca0400100043c50010340180f003211040c000c1c0041c2580c40380d04411001d01482d034511b01801054000e0f0040240380024200051040d850221002d65000c649141e0060400a800e07510b20309681200b055070840742c00484056051040610203a800300600301e1030f40e460b21452540c601c5241c0b20754000c600d100303040881c2450440d541c07a40c0180d682d94026045a03c401e0090401903400e02030b07032140c2803240003d0140d6048211150140c02d000106031105111001d05174001510184401404107001d80549600020590603140d8040310440c003952303440742c5443c2090300384000c951040e084081804400301c032800c60400c5410b0b100007030b030764880f41668641010b140107641481d43c0071000b04420704940d841e074182010700d500181107903003141c04444154841c801406031040d802c1c064200d0345044030100703e00c0940284c020420342 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630189721 1250 630188471 630188501
    0x18030c03020c0d060903030b030c06041202120106150e0307060f0f0c0b09030c10021315020f101e06081b0316030f0b2d0a0f0626030708040306 63
    0x100b4034000009a15100b804001c0b194183d60758118820315905115540c4200401c1d0000c4c8032140403240001e5803401288103459154000b10703011400c5413214446203c3d503904500003449626207130400c52048a0b49010801c000801d1255045554a800079140d01201e060b61151401c00c0c5003c0c5003241e1030032624107010203110342919880c0c005504900d0803803041c1404c001561b21003120301001030914960710042c0c02b206005001e8122090b02c103012580c21036190050300c08100301c5248059060480a080429142c020406170b014100c060f604540c40d102401d01c80000c602c2c00c62007000f022a10140103244881d4880b14440b2000315100140000c0c800c001012038140c0d8003d04001140102c050304100c428403141064801000b21003603c61f50003103a035141c0d400040b41d10680070380c586c0d03985001621803044510045126031840e40e20050041d8840360b02030041e15183e240043c144c83d81102d0210700d468440505a203000350100c1500c5000b580810364600c3d05203140c03140000350900e90241501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630190971 1250 630189721 630189733
    0x1407020a06050a03020c1005070207060c020f1210180b010b1903020904021e09040e06010308030f0402040e0123090705011b0c18061a030603030d050a0b0a0b0d0b0418030c0302 77
    0x40d030201085050701f210804480401c0d14540711000908224103a4400c609110700e10382800300584e00c100c00188030517816244400a4031001102d1442e0010320650303c651503260680b07481c400c00e0500000d0040502540d00f28819076614030341216503114040030320380c100783c48ac42c110002d14071980040462000007040941850040711181251050544030301074102400581c01141e82403501a1030300d4843c01c4c40140c41039614503103504004c2c0c40018890b4005070b0740c4000080840d5203680c8a180080040c000070819680074100e110580e035074449030039107610992000034858050005015081e41d606a4a510b03800421401180140c0040c2c0400c9650042203000400c0050720310140545000ca140c501041440c50130826440100c007420079040e07100c008004200407500c00000b181e0f0b00e248040b40015842c0d540d01048802005d0340410280e018408a900080080448015040280a403901000501c03403003001c000845420109400010300303103080003400700740294030036140f0600078015240707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630192221 1250 630190971 630190987
    0xe090601120218130c360308031806011412030708120106090503010c0f0c020f0a090c090e040b0112030215180c040c080c0904060b1206011407020a06050a0302 70
    0x10b07a04002007942c0c582e081030303541080da4070300300c124030421010036041005075600c014401865821801704042a450b1055986a2283d42a00d9020307250203404070604581c980302d107803031080c0e680180d0381c1c41d40b8450f50442070484c1c03071b80102e617040c100c0710040f80c000780c0c4c4401501440302c01c40c0e61031205409408240441008614528000c03d0071035001c0d04810b082e50304000c009024200540c11850103680f420b0401c0145940021a55005400d01d06000340700300b2081c40002c44070605000c11a401c04454000000d00c1c603070b142c004401c841000c2d01c40910207a11452903c0f40d250b030844015244e410b01c1401000789400342080d0002c003034001e1045d07856581e80380101042c290300035030315400081e0062542c0400035400340818107038884100c0e4240400107804000804c03080780640700c0c1100c5000020300d83d444e83e81d01d81c8044000c0c0f01e07040065440d10b5061418000c1d01008492083c0450358107810002921000000c0381c1000354010401410301e41005c800311041d4120508110516500f000100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630193471 1250 630192221 630192257
    0xf0112110a081602010c0806040b0301020904060315060909050c060c0a0b0c040f0e1015050405031e0f120d0b010c0503160c140d11040b0910140108070e090601 70
    0x20100034801c1c1c5600700e990510a01c441143c142003900c0a0440e450131005d400340d00d40c40010190401c0d001c440202d084102503000900a12a42031610b030321034507028001042261022a144401a00a1040000e2075490800c0010384940301c000500b207821203202c1d03031000c0c42c0240107880d14100301c0d800c4503d2120b086da40c40e812f0b814180ca05130260900842d0030800100450000c1d00030703000c10500b02d05981020cc0c40c680c0300005901030705e080b40c1c8480158128461088050b02d0007060000c00701e81c90340f903240f0307040590462102c0f1410744c1401900603892240303c0000c1e00041580750026401e103802d42c44c41006000300340714101c00e0b04000d8040004004035a04001a00003000c200160b111140f00314941403a070080c940e44032030040302401c0e6614410b82e8401e0b5101420981090840c05100d80010010700140f90703002149500002800600800542074121802501e5100c0c0030a80c924003442c00540d4602c0301190780000003a0008011100c0d428015001908030b0010304012100d201e42503c80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630194721 1250 630193471 630193477
    0x509041b1403190b191b03022d0a0804020a0909050c0f0a14120c22180c03140a0210020123040201091a07080406080103050d0306050f011211 62
    0x7841c0d09018448504405203018018514012800032000486641d6591084d042c0c0000074401c034455400d5a0440c204c0e000290009030f000c0e03040346015081d60310031032070150003134100a403910b03159803130007100f91001160b03001da40320502a02c04503030b410250124000c40c1c1081000380201e0300005040c6000800e0b8640303001e0164024450302c09040302400480038803200c4544006050300c41e12102d8020416055201030401165006454224101c070380e00c0c0741c540c5000310744991940c001c40661032008001803c207610f8100400310305000d00011300c1c4610020100100384c01c0140001c1c504200410014405950502c07104002209491740725500ba00010041442080c41d40c0150351100f481800c1c01004801d00440000341d070010740b2440c140f41e00020000d2a003801401241c0c0d550543d500403200c03040042d10005940910110b41d980e132118001001d050f8203100451f06031194403000c21409000b40901c80c00d5800142254255100480045840050010160024565581460905d640e1141c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630195971 1250 630194721 630194729
    0x50106140c01112a1f020903010e0a080301061106060319030e10030501090b180a0207031b0303021201052e0e0a17060117061b0903010c030b09090f06010509041b 71
    0x140c1d000518812443c0d10502a80040804c180e04180c03040e20f0741e640b2010364180001c141c202c1c016280c28603480802d004200b03460007402a44a8842030404005070b0030f000314140c8485a40e0301071010780310201c00341c0d5002c0c15128a44d154120801c004041c4100350841402c0074060301d05580d81444240104210400004010000a803030f100140303e2020035004000b550701050700c00015900184243c125807140142c8220603075078002038180b0505124071203030500e100031070084102c12203d0f4900500254016005110f001c40c42c1d200008041c41c041100c8046034034106916a215006000c11144100c07850083c0c009001340e4801220f15501c41920200140c00d00d24080c80c5281c019054841c50040c05030300c20403440d80240d0a82c0801d0b10b02080c040e400c449500d80b43c0d40c0405400316600c2c1a4020521312075010f610f0f001c50309180c50f90541180001580580300d490080d16003901494842d5561040015554400001000242001164103506c280901030110720640088100c804514007030388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630197221 1250 630195971 630195997
    0x2370813080c01050406090b0d0e0f06040606060c05150c04080a05011e02030c0f0d06030803090d03050105300f010c05030103110406050a0303031a12010e10050106140c0111 76
    0x28040c86600e2007080459401107003420614102490058000d00901c003a0289040c420030110342203000e0141ea410ad03148124510090b160803411011269a031920120340584009041410014906000381c1c030f0300c200b254102f80940403001a004102440781c0b40900359603241d03902000700041e60b107030a00001107158419400814418200042c43d2003440b02488130380c0ca0305104100740408d803904201158079500c0302141c115255010b400c00074000307040b9a0310107410008004104004c400000c5200c0300480c405d034508001e103036211800d0002d0113a030035000c4500310161407a0305424400d650028900c10f00341008648507511041c403840e080d55200d100007001b00700040014420000059030441320042c0a4400300103c40c038040c0012000b0005200103000d065940d038541110324400310205030481c00240c201185842a0b00b007a90083c9480201201e1030b000306440e20703040c1811402024100d0706240c0d18021070040c4001014180ea00c10380d44298550b603550b000002c400003c1004d0001d80f212aa = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630198471 1250 630197221 630197257
    0x21206040507090306230a0c0504180906050c07050d0c021e0a03050a03031d0109020109030303050603100608070f0b0f040e1305150604110c07060e13050a0c020d023708 74
    0x90000486c1c1480035185c105850f040c016106c41e026070060136901201c41540e046003407101c4280030480101200640600400e05140400520b5420a0010032036135110742c00316040040750601c112074986401000039030002104200901c400b00b080705161001c03030010240950f040c0d507940d4080c6002034050307044021036100c0c040020307000d421036841b140140c41c0d0f03002800000d1003540000c040580c01d0000405060344c4101051841d1400c10003c600c0c4450031400f04201500c1e4001181c1d144028410031041c68000c00f00464100084001e8801034506450710908250506440e0182140000c100c61807400c3c40d5440d41020800c20003401c0000c00c00b5005007501410414284020f58410044c04447c1000400c10720403101d00000308076045900340c3c035210068911603000a1800340210b000c80c002541444180302400c25180d1206050000e503808480c594649890280d0b00c2c4c0001c1010203221800b4040301c010584000040e071410303680c0441000c40d21039681d54807940f06401c0700160b0100030044c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630199721 1250 630198471 630198521
    0x50103231f08100507080921090324060d02010c0816051002030a1a1e030102090303040602060f070c02090723030106080f1b0409090606080106030f15021206040507090306 75
    0x284034068001e03141b407070324400501e05000702c50341d00e000c4000c00d4052103007000c0e440440c0c02400c0e02600c180c100001c1c180d440440c025600480303000b00d1882c2e12840094040046400b518110391007900055040c0c581c0c510413030320303500d50a001c0d42200082c02e1010900002110000320248074800801466240050722405d0248521088840381c13a40c02450690404940b481a6034201403c8c081010480307909165181340720229019010741599547c00d4400030501044590700800c4462280c001c807050841c0316626001e041f51480043c0780069007100c80c010119000d2440740000320201c003c1c48592054212405ea40c451a542c8264001d50000395071605220750f0000011485403c2002c50107281070300004407130100ba003407003903204040c40c040d900c1c2c06820030071441c2d81041004140020003080403a40e00c1c00d144881030305043d4103e80c1900504c001c1550041c1d94400d582c0251a01041121107a803000c0c1480000c160203000c5100340010044000005038031405030511003518141e01501e00018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630200971 1250 630199721 630199753
    0x120605010e130b070903141b0402031509130c032d050d030b0a03020a0e07120c08010504020d1e0f0c0801031e171204020a050103231f08 60
    0x4181c0191960035100024801652980040c11071029085840d004458641d60016a0002181d0740700400f0300d80c0400d220700c0300f040042592894020301244030300118280c101044102c0c80121050a901104052111040e061400d501d41d84042e0307030540181882001c0e02c07440c080d90b40315070044640d9070304514003d240040c074188078202510044640301040000d540d445071104800e407240c000305540c64842c01202e40d1042c100b0302c0110703005003401e14015156130341c58043c49012900c41000c100546803c1c081386800b03114244041880740d48100d800c0e420101044041d505c030000e00c00c000c43d200d103840038007950507038811405d0044800340003942d203800c0011401550407000d0402e0911400e07200420200d01d5140504c1c90036403404907240c0a2038180d14040c60703070171030f9002801c403542d402007410041c2600c0c0101d42800340303000b1501c4102e510f68603801141904d4032400e42c0400004000007540c80c0380401504242c01c4082c17041c5003051207002020490100120b6807188113694040307110a00d072801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630202221 1250 630200971 630200981
    0x60302010f1805090603030d0510080111070308071d18060130020a11030a020d08011a0a120b03010213030213230601030f0e06060102010501060f02341206 68
    0x100d941046034900d00e46006440b020302c02840303200c0c0030b4004480014a1030b501403046440d250100c0d0000c00850030000d56174054081d45000301c40c0258a41004040c09401300c80036502c0c481d516a48210180c0d90341c0798201c3c0c035010031091000078012071468200d516a03a29040d810740a02042c1c00c500d003032504600040c001d00c0000d4a8440c0801a105101c080010032070031120111103900700980c0c1d078504604116500040a5241c1c3c120740400310f68515001e81c0481e4941102855640300420303030740c07240f248a018400c0d0a03040c20f1030881c2000104411030094144140f564039010000403900c2c1448040b9003a83c1c4807245a031038021001400307208500c4c08447d0750174809403914080117045003c04a40c0c681d62100c0d82200d124405040005803181e100b90054503c800e0b040405010b0176201c841d0160b511340c030985507180954202000414018031844c12800c81849a81c0141a032415034031300310308031142d81c02d42c81420700308002844800e200803c92050080c09260740041c007059942c1849001c0321 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630203471 1250 630202221 630202247
    0x70303050c090a090b0a0e1f14130e0c130f06080d022a060d0203090d0806011b05030d1104060f180e060f0d0b070e0d0f0f1401060906030201 62
    0x25800d00c0310820b00d442e04000007065480e5000c000904956000c001503814029910140e101791402c81003107820103a0f000d1030801c21404400810030b451301c640b665003c420b0001007203170700300752100010440340000ba04040300d130915400a0307c1d42200e01101041400400718454000da6807503407280042d02085229000060142e00040c0c11001c81010009455175650210b0480881c21800c0d070a0060075500c0a94081d000300038090707507407050b450300c401011703400860308a0031a0289000b01d011141c0108655071060005139280000c280e646449500300b11190101a1004c3c80305200810700c0a00620840d100f004e150003d0646803840c02c20028600c11101e038140e020400e8061101040300d488850b41004d03185a51814513040e561200810300780e1400c0b040103076001c0c82c1040860b051242e00e005603405111155540d20303903071040009110910540800041403ca0142906000306034414190800244030f030302013210341d0040c41c0c652400c2d12082d81102403c0395880a04104541c0c00c04032010f001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630204721 1250 630203471 630203491
    0xe0a0629030d05030907150f0327022106090f071508070c0f020907080601030510032402120c030a05010611031c0f140a0c0c0209180c09070507030305 66
    0x1542100001c81e89a5414401c29010f1100103c04200b5503182401654003400845038003056010030110000c014484c070329503000c0404d01e064225840d00c4940b010300d0764141403409400410808a600f44040400c4c0300c400b00c840c400c04041011802c2e442804200d01521000c0000e0031000b0801412600f031803290760040024101c4c21100c2c00e81700360080380140d800703007441c1400740c0151003034100b00703c0d83c0100711402544080103408100501d84c008038018010f210aa80070042940c130660428510006400003500700d00c141349100c00c180083c00c0103040000718200f80981400718101c4100c031402d0055558965040021003044440c108900c02d0500420551401102c01600349c1d80d0356841c0c2c880c035080c1c2c5240c03900d110815448041143c0000b0307546044684100701881100101030050681694a11049030819018155041c49a038441000580050a05c4130340d484600f18080d15005201c40700300c5600901e40814101e544401000b480748000c1d0311003076a40c001c00d1800a007280d000030b00440c00c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630205971 1250 630204721 630204791
    0x8100b04090b0f0601021009050d0807050408071a04240807020a0b060d0215030a1d010e0303071218060b10030e030307180e0a150b030106050702060307030e0a06 71
    0x11a000c03815180c0c015000c2220030a031501c81d074004071f08202c2c91581e0301e06201d0800c2504810024006a014090700759640c4070707826034035104001c0307603917204900c68010340e1740c0864401d00c14060045045506049403030303085441e01d980c0c3d07003410403403051004e0712020300040452014890b580009070141d0203000340c409469002c21540c0e07040c414003c05030041c0c2c02000d0b4103c62130f04540714468000c0c08890141c0c1c3d00c40d01c9213011260350024010006c4454501d40c0f801031142080c041c14001d8056a41c800c1c40a5829031391440c0381110840c0c4844241011251120524241180d40014194807907006140104500480741c0900404102c007030a444109481e010311069081404425a13401c042145404c0c080039110040c0206034030030070741084404010340c60501c0131809659100020b190160206081c4159490744014a280070034800c01d0049981000141c0c01071070060010366010b0100e0a0006e42140340010151900c0541031044862603540c452000c45681c01c407640c400100d05000d48100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630207221 1250 630205971 630205973
    0xc1603020306041101020c03060907050112050f0a0b060717070314030f15210703061d120f040e0403120e07050d020d0c120609120509011d0301110408100b0409 70
    0x5a5004010405895190720103032500d04e070b83c0300307004081041c0d900600710307031103400e00c0c2c02c0e815250605441041e02140f020344a058842d25680240d80c071070010745401044560b50048240e019260304009030798040010007440001504e0485041c0a90b4200b603135058480a0a1502900c030f00c0c0d5900703d94a00c0e030000e208001c145a66045181d502a03080360ba2441c8850400000c9503810190150f9031040302413200607407462200005114040341d00987d0f0a1203d04845044041285090960110b0341d0300900d046c501c0e0514100c1c01024030f060040001450b05699850125125000795400c038000740c02446503a03c00704032400750718130702202a000381049a284c00000b4151244040d0001d0083e0344000581e014000e124902c40000c1c1030a040350103130480305160240091940f01412a651003c0c104211201c0d80305009403243c103101a100c03000c500c941003194280702c4e1140c2515503495034823900141c5110003e50040c0000b80071420040c48480039020307241c82039860200485001d03901d0190000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630208471 1250 630207221 630207223
    0x1505060307110730030e040f0e1212070f140a03020c0705040e030d0b0a0b0f030403030e010b06030a020309070807140307150c08070501090506040b04020405061f050c1f020c16030203 80
    0xb590296003e90130603441c01061500741e5828800f040815802460440700c2d080704006608144c08a60080c02981e030310a035030040c500000d020f548c0c10103240c10541400906094050551b119414036181040340c600140c205103240203034003007818500000e0b00440c01c2c07800309d4000c10140c030141c00221703014003030b200414445980d81d0068403c000501602c4140240040c0c5680c45c410b000703440c2c803069043e07444461525000050303209440c210002451b0104864102006108502c0d6641340101500d2440d152651048040c0d0000f600086040c0610440054200c1007080040001c2800c041c80b5a0b00310168820141000c80c1a130003240c0014044000d9021264041e01d03100215a0051400b41c55820a003002401840c011200920521489041c0801d200603d26014415803003250b051016549003024404c0c6800c02030050201c002c480c0c041801c4041c003030000303050030700368030740440e644546601040c12428560b040365100c555030005800c5058041400311005003c1d15040403100246103030302007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630209721 1250 630208471 630208529
    0xa3b040f031b03020606040906090c0b041e15050307020c040e0c0102010f05010b09060c101503060e01200c010b09010f03062d0203100b0c0706080601030c0c0615050603071107 77
    0x300307111f6545e0301c0207181001002d030701030a2141d400c1203040c0441a141d10002c0b12a45c45802544d180800d540340c14092210b2141641c819101070b00114a0304064100040e01e0503000a071510080d405660b8192003103444622910044d0540b100041c415002c828002a00312007150200da80101c0c01e041c01409a00000070845642d5041960303c40d42d40c01d0360400003070400d1880e0913015505824003041c0404d424a100d030b203009403406000d08112502c082c022080c00c8503228001040c0d010008c03207090000e0f24420015004181448001051004800d0300243c1420307801d801404c03442c50440414070174442c0c1c6209c0c41c17281003c0c2005404c40c0c000c143c040c0190010400c1c1441e120310745c0020004011300840d44a6200078000d0560958503070b4101400e40c1d4642c4001e0144400041c0204005003139503200f801407047c0c4c120740703442c0c40c4092541c5803201300141c030044107035159249601d9400511511001d000b184152990f030783c0c1080e0200702040f09130901003254040c0072540c40c0607020b00740e00200d070010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630210971 1250 630209721 630209731
    0x10080103150204031a09011a0d06110d0f051801110409050915040609030201150b180301060b280c030819090512070507050a3b040f031b030206 63
    0x109081c1d190140a4040d12a0740c0004242050a101c43e80b40c029000510900941c00000244511000c19881d00940c1e40741e404010b5100036800ca202c0041007040c4d002c80c0220095108440c98510307958884800d490642c45050403480e0749400300640c0c940b542c003101400140200003400150058407000c00c135806240103a0b86016038400105500b800c0800140c8103641800e05041c0082ca041e0030300c02c0003401503060650240d4280300c0a40078140e240d10a04040d40c50b180c0a6908182100061a50b2480c0214059805642e80c04000c0342c05400708002d48104003400c19500d02d0041d00d203ca816402060200c81410b02a55964040020b500700c004e240d030205442c400d8450043e04000304030041e02c0d0508000d4a80e000c0c04004100c1002110014591140a5030072111090313618028840c0b004054428032203003150404540c0000c80038658548403101080c10300040d807441c0d8500100058200381e400302c03954141c0b444224101034202000c0700605003115120055031140da200a5107a04c0002d003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630212221 1250 630210971 630210983
    0x11b1d01021c0c02030d0c1a0108031606060b1209070602010608060606070f0c091a030303191e05010b0a0905012d090b030906010608061e0f27070e10080103 69
    0x840c015081e44243e464000040c2c00504480c1041607800000c4c15003580d100c0251500343c44025000e40d14604100e13607074100c079010380c0158908002e54016070250365501c80d007220b0807074907000006805641e00c0082c198100503401e04080c00d00f0f040d007190386021760701c4e84484256411700400b000610408501c0c0b660115055540c143c0d145020300e00580704010f002c0c4024007180f420f48011851a01585c8407029003000890500040d000040801d903490004407141e0f1180d0b040350303800f10004211034204604400b26100521a071500c1403204ca002d482d000d030403031b50500304007103a02031050ba440f41000700242020b003014440e600c0e24040440c034a2007030030302980a854206083c1c1101d45d10444542e00100f0300c044030300380c41e81415208a03807036040a01c109000201c001e030100b007051402d000c01d0145505030141c0c0c9601c0c124900c00b44460450300e41c0149078455442c00c01181040800714680081c0103100c08000e0035803900d200090300350b1942003000c5000d140340c0f6404180e0960400d41c0c0e0b03410340750410703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630213471 1250 630212221 630212263
    0x21022104051923010507020c0a05130917030711060a02031e04020a080a0f0203010b060408030d05062b031205100905040501020d020a0206070f0c030801050103021308011b1d0102 78
    0x30521400f4070072218400c2000881d245500e084821040d403141c1d025041c15401e0700e05181d0a41d00300010342d003003806015130003440450010252000f5900c10f00d5114455104814101030625032140e241c0c00031100200401d0918414216040003400110351100040c00b0841c00d5082c90845e2910046208109640380c540d5200842c2c107558940c405500241982d504888075440e85243c80b4071911280030007280250300700200e100300e910701241604c09640041d030040d400c0c8952010940c0107850050000d43e0490107014854a10009a0111940343e8030170700d00c05108081c1c6071800401402202188100f070900c0c15003807090003044115503400f03d608000000c40c0c29122400e1150092061641c04a0164400242d4068880c2c0118146100e030760281c0b640705030b102e1815000c1c0d03400d48508030000c00240e40704006020660090340a00301412040c1d105400641d15961940c0c00c590b078000c03071600880848000d01032010343c00b4010030903144881c202400109542e40010b555050541c5462551081d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630214721 1250 630213471 630213473
    0xa0303050c280f2d020a050d1101050a0306081c08070201051005040b06210910020c030403170d0e0f0c120604030f26010e070f0e0907210221040519 65
    0x8920114801440e910018290030004985020801084030b012401111b034200700040a02e4030904074020150032072584050142c01034011101540022043d4042c10f0340ca800c0801e44180400044520b1701001803006000002c00101406d00340c1c00030400c104580c1840b0030072801c40c0360009044201d031000d440110f07c000d200c81c0050b5043c014241903101d021002c0402101911007002ca41d8040d25214095510b03412030f6100c410243d01c075400ea81d202d0742e03004102c20000291007403a9402c401050320303109410300d001802c01c0026140d900701c901d4015880b5900408070800705100382c10b01040108c400c40d840340783c500f845985070310b4024005010b0189010324103c65501544015040b07441d604026248950700654103290803c0c207025910702002c40d0300000f40c41c1e900901070510000750300e4580b03c8000c403200003004241072008001381c0401080c0d00c03840443d081c1486c0c4c07100542d40c0101703000d600c5014a5500c0180680322131010491420300c90180004105c000c0703646d200c0300c4040c8503664045400307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630215827 1106 630214721 630214733
    0x10f020a0b0115090803120108011a0d121803030f02070911180112060305010504050f030f04140109050d080315031f0504110a0303050c280f 62
    0xd400043c001c125003002400c0c1c44407954038284a58603100c1003400d0940d0040301c502c0503807102d03403401841200d5003802140303103c02160003d0500c0404190020300c809441300d00c0900b5501d072000004804600c24003072074240d81000c0c0b010504456891a00800d20310b003044404005020f00a000b00b00400d55001c0c200305043c8190500e0b00b0306402d04032040d100f0318603142e4141132040c140c022003034070ba0550140c0c1006600074030001500380f5107070500a0914680001510b26604100103180300000b215040e50140d60f1402c6100d501d00c1074680060310030000d681c10541d031043c20203840b0800c12051074001e5104d411807403124040d040700107092603130702c140c411380b070031800c00c3c441c0020b40300c2114503407096030300038025210854281514408550405019081030300000e0000821928043c41041046090f80307940010b83c8443c4440c000340130318002c1084000b028180311103000c0d001d02039 = true := by decide +kernel

theorem cover : BRFrame.Cov 630035971 630215827 := by
  have h0 := BRFrame.cov_init 630035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630035971 ≤ n) (h2 : n < 630215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
